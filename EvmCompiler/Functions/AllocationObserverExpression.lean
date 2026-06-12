import EvmCompiler.Functions.AllocationObserverContext
import EvmCompiler.Functions.AllocationObserverPreservation
import EvmCompiler.Functions.AllocationObserverSafety

namespace EvmCompiler
namespace Functions
namespace AllocationObserverExpression

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open AllocationObserverRelation

/--
Semantic-family interface required after recursively compiling primitive
arguments.

It is stated entirely through the canonical Functions primitive semantics, the
real one-instruction Structured execution, and the allocation result relation.
The canonical no-external-effects instance is proved per primitive family; no
compiler implementation or replay certificate is hidden in this interface.
-/
structure PrimitiveForward (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  simulate :
    ∀ {transcript : Trace}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase frameDepth frameWords : Nat}
      {sourceArgs sourceFinal :
        Functions.ObserverSemantics.State transcript}
      {targetInitial targetArgs :
        Structured.ObserverSemantics.State transcript}
      {values outputs : List Word},
      ScratchExprResultRel contract plan live
          stackOffset frameBase frameDepth frameWords
          (Expressions.Structured.BasicOp.inputs op)
          sourceArgs targetInitial targetArgs values →
        AllocationObserverSafety.PrimitiveMemorySafe contract op
          sourceArgs.source.shared.toMachineState values →
        (Functions.ObserverSemantics.primitiveSemantics transcript).eval
            op sourceArgs values =
          .ok (sourceFinal, outputs) →
        ∃ targetFinal,
          Structured.ObserverSemantics.Code.run [.op op] targetArgs =
              .ok targetFinal ∧
            ScratchExprResultRel contract plan live
              stackOffset frameBase frameDepth frameWords
              (Expressions.Structured.BasicOp.outputs op)
              sourceFinal targetInitial targetFinal outputs

namespace PrimitiveForward

theorem gas (contract : MemoryContract.Contract) :
    PrimitiveForward contract .gas where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel _hMemory hPrim
    have hLength : values.length = 0 := by
      exact hArgsRel.valuesLength
    have hValues : values = [] :=
      List.eq_nil_of_length_eq_zero hLength
    subst values
    cases hConsume :
        Simulation.ResourceReplay.consume? .gas sourceArgs with
    | none =>
        simp [Functions.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.basicOpObserver?,
          Structured.BasicOp.toPrimOp,
          Assembly.ResourceObserver.ofPrimOp?, hConsume] at hPrim
        cases hPrim
    | some result =>
        rcases result with ⟨value, sourceConsumed⟩
        have hResult :
            sourceConsumed = sourceFinal ∧ [value] = outputs := by
          simpa [Functions.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.basicOpObserver?,
            Structured.BasicOp.toPrimOp,
            Assembly.ResourceObserver.ofPrimOp?, hConsume] using hPrim
        rcases hResult with ⟨rfl, rfl⟩
        obtain ⟨targetFinal, _hSource, hTarget, hFinalRel⟩ :=
          AllocationObserverPreservation.Expr.gas_forward_result_scratch
            hArgsRel.state hConsume
        refine ⟨targetFinal, hTarget, hFinalRel.state, rfl, ?_⟩
        rw [hFinalRel.stack, hArgsRel.stack]
        simp

theorem msize (contract : MemoryContract.Contract) :
    PrimitiveForward contract .msize where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel _hMemory hPrim
    have hLength : values.length = 0 := by
      exact hArgsRel.valuesLength
    have hValues : values = [] :=
      List.eq_nil_of_length_eq_zero hLength
    subst values
    cases hConsume :
        Simulation.ResourceReplay.consume? .msize sourceArgs with
    | none =>
        simp [Functions.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.basicOpObserver?,
          Structured.BasicOp.toPrimOp,
          Assembly.ResourceObserver.ofPrimOp?, hConsume] at hPrim
        cases hPrim
    | some result =>
        rcases result with ⟨value, sourceConsumed⟩
        have hResult :
            sourceConsumed = sourceFinal ∧ [value] = outputs := by
          simpa [Functions.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.basicOpObserver?,
            Structured.BasicOp.toPrimOp,
            Assembly.ResourceObserver.ofPrimOp?, hConsume] using hPrim
        rcases hResult with ⟨rfl, rfl⟩
        obtain ⟨targetFinal, _hSource, hTarget, hFinalRel⟩ :=
          AllocationObserverPreservation.Expr.msize_forward_result_scratch
            hArgsRel.state hConsume
        refine ⟨targetFinal, hTarget, hFinalRel.state, rfl, ?_⟩
        rw [hFinalRel.stack, hArgsRel.stack]
        simp

end PrimitiveForward

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
    | _, .cons head tail =>
        exprHeight head + exprSeqHeight tail + 1
end

set_option maxHeartbeats 800000 in
mutual
  theorem forwardExprFuel
      {contract : MemoryContract.Contract}
      (hPrimitive :
        ∀ op : Structured.BasicOp, PrimitiveForward contract op)
      (fuel : Nat)
      {transcript : Trace}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase frameDepth frameWords results : Nat}
      {expr : Functions.Expr results}
      {lowered : Locals.Expr results} {code : Structured.Code}
      {source sourceFinal :
        Functions.ObserverSemantics.State transcript}
      {target : Structured.ObserverSemantics.State transcript}
      {values : List Word}
      (hSafe :
        AllocationObserverSafety.Expr.MemorySafeEval
          contract transcript expr source sourceFinal values)
      (hFuel : exprHeight expr ≤ fuel)
      (hCtx :
        AllocationObserverContext.ExprContext
          lowerCtx lowerState localsCtx plan live frameDepth)
      (hScoped : Functions.Scope.ExprScoped live expr)
      (hLower :
        AllocationLowering.lowerExpr lowerCtx lowerState expr =
          some lowered)
      (hCompile :
        Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
      (hRel :
        ScratchStateRel contract plan live
          stackOffset frameBase frameDepth frameWords source target) :
      ∃ targetFinal,
        Structured.ObserverSemantics.Code.run code target =
            .ok targetFinal ∧
          ScratchExprResultRel contract plan live
            stackOffset frameBase frameDepth frameWords results
            sourceFinal target targetFinal values := by
    cases hSafe with
    | @lit value state =>
        subst_vars
        have hLowered : lowered = .lit value := by
          simpa [AllocationLowering.lowerExpr] using hLower.symm
        subst lowered
        have hCode : code = [.push value] := by
          simpa [Locals.Expr.compileCode] using hCompile.symm
        subst code
        obtain ⟨targetFinal, _hSource, hTarget, hFinalRel⟩ :=
          AllocationObserverPreservation.Expr.literal_forward_result_scratch
            value hRel
        exact ⟨targetFinal, hTarget, hFinalRel⟩
    | @var name value state hValue =>
        subst_vars
        have hLive : name ∈ live := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        cases
            AllocationObserverContext.classify_var
              hCtx hLive hLower hCompile with
        | stack planDepth depth op hLocation hCurrentDepth hDup =>
            obtain ⟨targetFinal, _hSource, hTarget, hFinalRel⟩ :=
              AllocationObserverPreservation.Expr.stackVar_forward_result_scratch
                hRel hLive hLocation hCurrentDepth hValue hDup
            exact ⟨targetFinal, hTarget, hFinalRel⟩
        | scratch slot op hLocation hDup =>
            obtain ⟨targetFinal, _hSource, hTarget, hFinalRel⟩ :=
              AllocationObserverPreservation.Expr.scratchVar_forward_result
                hRel hLive hLocation hValue hDup
            exact ⟨targetFinal, hTarget, hFinalRel⟩
    | @prim op args source afterArgs final values outputs
        hArgsSafe hMemory hPrim =>
        subst_vars
        have hArgsScoped :
            Functions.Scope.ExprSeqScoped live args := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        cases hLowerArgs :
            AllocationLowering.lowerExprSeq lowerCtx lowerState args with
        | none =>
            simp [AllocationLowering.lowerExpr, hLowerArgs] at hLower
        | some loweredArgs =>
            have hLowered : lowered = .prim op loweredArgs := by
              simpa [AllocationLowering.lowerExpr, hLowerArgs] using
                hLower.symm
            subst lowered
            cases hArgsCode :
                Locals.ExprSeq.compileCode
                  localsCtx stackOffset loweredArgs with
            | none =>
                simp [Locals.Expr.compileCode, hArgsCode] at hCompile
            | some argsCode =>
                have hCode : code = argsCode ++ [.op op] := by
                  simpa [Locals.Expr.compileCode, hArgsCode] using
                    hCompile.symm
                subst code
                obtain ⟨targetArgs, hArgsRun, hArgsRel⟩ :=
                  forwardExprSeqFuel hPrimitive (fuel - 1)
                    hArgsSafe (by
                      simp only [exprHeight] at hFuel
                      omega)
                    hCtx hArgsScoped hLowerArgs hArgsCode hRel
                obtain ⟨targetFinal, hOpRun, hFinalRel⟩ :=
                  (hPrimitive op).simulate hArgsRel hMemory hPrim
                refine ⟨targetFinal, ?_, hFinalRel⟩
                rw [AllocationObserverPreservation.ObserverCode.run_append,
                  hArgsRun]
                exact hOpRun
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega

  theorem forwardExprSeqFuel
      {contract : MemoryContract.Contract}
      (hPrimitive :
        ∀ op : Structured.BasicOp, PrimitiveForward contract op)
      (fuel : Nat)
      {transcript : Trace}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase frameDepth frameWords results : Nat}
      {exprs : Locals.ExprSeq results}
      {lowered : Locals.ExprSeq results} {code : Structured.Code}
      {source sourceFinal :
        Functions.ObserverSemantics.State transcript}
      {target : Structured.ObserverSemantics.State transcript}
      {values : List Word}
      (hSafe :
        AllocationObserverSafety.ExprSeq.MemorySafeEval
          contract transcript exprs source sourceFinal values)
      (hFuel : exprSeqHeight exprs ≤ fuel)
      (hCtx :
        AllocationObserverContext.ExprContext
          lowerCtx lowerState localsCtx plan live frameDepth)
      (hScoped : Functions.Scope.ExprSeqScoped live exprs)
      (hLower :
        AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
          some lowered)
      (hCompile :
        Locals.ExprSeq.compileCode localsCtx stackOffset lowered =
          some code)
      (hRel :
        ScratchStateRel contract plan live
          stackOffset frameBase frameDepth frameWords source target) :
      ∃ targetFinal,
        Structured.ObserverSemantics.Code.run code target =
            .ok targetFinal ∧
          ScratchExprResultRel contract plan live
            stackOffset frameBase frameDepth frameWords results
            sourceFinal target targetFinal values := by
    cases hSafe with
    | @nil state =>
        subst_vars
        have hLowered : lowered = .nil := by
          simpa [AllocationLowering.lowerExprSeq] using hLower.symm
        subst lowered
        have hCode : code = [] := by
          simpa [Locals.ExprSeq.compileCode] using hCompile.symm
        subst code
        exact ⟨target, rfl, ScratchExprResultRel.nil hRel⟩
    | @cons left right head tail source afterHead final
        headValues tailValues hHeadSafe hTailSafe =>
        subst_vars
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
                have hLowered :
                    lowered = .cons loweredHead loweredTail := by
                  simpa [AllocationLowering.lowerExprSeq, hLowerHead,
                    hLowerTail] using hLower.symm
                subst lowered
                cases hHeadCode :
                    Locals.Expr.compileCode
                      localsCtx stackOffset loweredHead with
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
                        obtain ⟨targetHead, hHeadRun, hHeadRel⟩ :=
                          forwardExprFuel hPrimitive (fuel - 1)
                            hHeadSafe (by
                              simp only [exprSeqHeight] at hFuel
                              omega)
                            hCtx
                            hScopedParts.1 hLowerHead hHeadCode hRel
                        obtain ⟨targetFinal, hTailRun, hTailRel⟩ :=
                          forwardExprSeqFuel hPrimitive (fuel - 1)
                            hTailSafe (by
                              simp only [exprSeqHeight] at hFuel
                              omega)
                            hCtx
                            hScopedParts.2 hLowerTail hTailCode
                            hHeadRel.state
                        refine ⟨targetFinal, ?_, ?_⟩
                        · rw [
                            AllocationObserverPreservation.ObserverCode.run_append,
                            hHeadRun]
                          exact hTailRun
                        · exact
                            ScratchExprResultRel.append hHeadRel hTailRel
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega
end

theorem forwardExpr
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp, PrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords results : Nat}
    {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ScratchExprResultRel contract plan live
          stackOffset frameBase frameDepth frameWords results
          sourceFinal target targetFinal values :=
  forwardExprFuel hPrimitive (exprHeight expr) hSafe (by rfl)
    hCtx hScoped hLower hCompile hRel

theorem forwardExprSeq
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp, PrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords results : Nat}
    {exprs : Locals.ExprSeq results}
    {lowered : Locals.ExprSeq results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript exprs source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hLower :
      AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ScratchExprResultRel contract plan live
          stackOffset frameBase frameDepth frameWords results
          sourceFinal target targetFinal values :=
  forwardExprSeqFuel hPrimitive (exprSeqHeight exprs) hSafe (by rfl)
    hCtx hScoped hLower hCompile hRel

theorem Expr.backward_of_safeEval
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp, PrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {results : Nat} {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered =
        some code)
    (hRel :
      ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        expr source =
      .ok (sourceFinal, values) ∧
    ScratchExprResultRel contract plan live
      stackOffset frameBase frameDepth frameWords results
      sourceFinal target targetFinal values := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forwardExpr hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSafe.eval_eq, hExpectedRel⟩

theorem ExprSeq.backward_of_safeEval
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp, PrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {results : Nat} {exprs : Locals.ExprSeq results}
    {lowered : Locals.ExprSeq results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hSafe :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript exprs source sourceFinal values)
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hLower :
      AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset lowered =
        some code)
    (hRel :
      ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Locals.Source.Effectful.Expr.ExprSeq.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        exprs source =
      .ok (sourceFinal, values) ∧
    ScratchExprResultRel contract plan live
      stackOffset frameBase frameDepth frameWords results
      sourceFinal target targetFinal values := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forwardExprSeq hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSafe.eval_eq, hExpectedRel⟩

end AllocationObserverExpression
end Functions
end EvmCompiler
