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

/--
Primitive preservation for an activation with no live scratch locals.

Memory-changing primitives need preserve only the shared-state relation and
the concrete stack suffix in this mode; `LiveStackOnly` makes every scratch
lookup obligation vacuous.
-/
structure StackPrimitiveForward (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  simulate :
    ∀ {transcript : Trace}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase : Nat}
      {sourceArgs sourceFinal :
        Functions.ObserverSemantics.State transcript}
      {targetInitial targetArgs :
        Structured.ObserverSemantics.State transcript}
      {values outputs : List Word},
      LiveStackOnly plan live →
        targetArgs.source.evm.activeWords.toNat *
            MemoryContract.wordBytes <
          EvmYul.UInt256.size →
        ExprResultRel contract plan live
          stackOffset frameBase
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
            targetFinal.source.evm.activeWords.toNat *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size ∧
            ExprResultRel contract plan live
              stackOffset frameBase
              (Expressions.Structured.BasicOp.outputs op)
              sourceFinal targetInitial targetFinal outputs

/--
Allocator-metadata preservation for one canonical primitive.

This companion interface is intentionally separate from the ordinary
expression result relation. The local allocation proof does not own the global
recursive-frame allocator, while the recursive Functions proof needs to know
that ordinary source effects leave its metadata word intact.
-/
structure ActivationAllocatorPrimitiveForward
    (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  preserve :
    ∀ {globalFrameWords : Nat}
      {config : AllocationObserverRelation.Frame.Config}
      {allocatorDepth : Nat}
      {transcript : Trace}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase : Nat}
      {mode : ActivationMode}
      {sourceArgs sourceFinal :
        Functions.ObserverSemantics.State transcript}
      {targetInitial targetArgs targetFinal :
        Structured.ObserverSemantics.State transcript}
      {values outputs : List Word},
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config →
      ActivationExprResultRel contract plan live
          stackOffset frameBase
          (Expressions.Structured.BasicOp.inputs op)
          mode sourceArgs targetInitial targetArgs values →
      AllocationObserverSafety.PrimitiveMemorySafe contract op
          sourceArgs.source.shared.toMachineState values →
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          op sourceArgs values =
        .ok (sourceFinal, outputs) →
      AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth targetArgs →
      Structured.ObserverSemantics.Code.run [.op op] targetArgs =
          .ok targetFinal →
      AllocationObserverRelation.Frame.AllocatorEffect
        config allocatorDepth targetArgs targetFinal

/--
One primitive interface consumed by the recursive expression theorem.

The stack and scratch proofs remain pass-owned semantic-family theorems. This
record merely packages them so recursion does not split into two proof
corridors.
-/
structure ActivationPrimitiveForward (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  stack : StackPrimitiveForward contract op
  scratch : PrimitiveForward contract op
  allocator : ActivationAllocatorPrimitiveForward contract op

namespace ActivationPrimitiveForward

theorem simulate
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (hPrimitive : ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {sourceArgs sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {targetInitial targetArgs :
      Structured.ObserverSemantics.State transcript}
    {values outputs : List Word}
    (hArgsRel :
      ActivationExprResultRel contract plan live
        stackOffset frameBase
        (Expressions.Structured.BasicOp.inputs op)
        mode sourceArgs targetInitial targetArgs values)
    (hMemory :
      AllocationObserverSafety.PrimitiveMemorySafe contract op
        sourceArgs.source.shared.toMachineState values)
    (hEval :
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          op sourceArgs values =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run [.op op] targetArgs =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase
          (Expressions.Structured.BasicOp.outputs op)
          mode sourceFinal targetInitial targetFinal outputs := by
  cases hArgsRel.state with
  | stack hOnly activeNoWrap state =>
      have hBaseArgs :
          ExprResultRel contract plan live stackOffset frameBase
            (Expressions.Structured.BasicOp.inputs op)
            sourceArgs targetInitial targetArgs values :=
        ⟨state, hArgsRel.valuesLength, hArgsRel.stack⟩
      obtain ⟨targetFinal, hRun, hFinalNoWrap, hFinalRel⟩ :=
        hPrimitive.stack.simulate
          hOnly activeNoWrap hBaseArgs hMemory hEval
      exact
        ⟨targetFinal, hRun,
          .stack hOnly hFinalNoWrap hFinalRel.state,
          hFinalRel.valuesLength, hFinalRel.stack⟩
  | scratch state =>
      let hScratchArgs :=
        ScratchExprResultRel.mk
          state hArgsRel.valuesLength hArgsRel.stack
      obtain ⟨targetFinal, hRun, hFinalRel⟩ :=
        hPrimitive.scratch.simulate hScratchArgs hMemory hEval
      exact
        ⟨targetFinal, hRun,
          .scratch hFinalRel.state,
          hFinalRel.valuesLength, hFinalRel.stack⟩

/--
Primitive simulation strengthened with the recursive-frame allocator
invariant. The semantic result still comes from the ordinary adjacent
primitive proof; the companion theorem only transports allocator ownership.
-/
theorem simulateRuntime
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (hPrimitive : ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {sourceArgs sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {targetInitial targetArgs :
      Structured.ObserverSemantics.State transcript}
    {values outputs : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hArgsRel :
      ActivationExprResultRel contract plan live
        stackOffset frameBase
        (Expressions.Structured.BasicOp.inputs op)
        mode sourceArgs targetInitial targetArgs values)
    (hMemory :
      AllocationObserverSafety.PrimitiveMemorySafe contract op
        sourceArgs.source.shared.toMachineState values)
    (hEval :
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          op sourceArgs values =
        .ok (sourceFinal, outputs))
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth targetArgs) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run [.op op] targetArgs =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase
          (Expressions.Structured.BasicOp.outputs op)
          mode sourceFinal targetInitial targetFinal outputs ∧
        AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth targetFinal := by
  obtain ⟨targetFinal, hRun, hFinalRel⟩ :=
    hPrimitive.simulate hArgsRel hMemory hEval
  exact
    ⟨targetFinal, hRun, hFinalRel,
      hPrimitive.allocator.preserve
        hConfig hArgsRel hMemory hEval hReady hRun |>.ready⟩

end ActivationPrimitiveForward

namespace StackPrimitiveForward

theorem gas (contract : MemoryContract.Contract) :
    StackPrimitiveForward contract .gas where
  simulate := by
    intro transcript plan live stackOffset frameBase
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hOnly hActiveNoWrap hArgsRel _hMemory hPrim
    have hValues : values = [] :=
      List.eq_nil_of_length_eq_zero hArgsRel.valuesLength
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
        have hState :
          ActivationStateRel contract plan live stackOffset frameBase
              .stack sourceArgs targetArgs :=
          .stack hOnly hActiveNoWrap (by simpa using hArgsRel.state)
        obtain ⟨targetFinal, hRun, hFinalRel⟩ :=
          AllocationObserverPreservation.Expr.observer_forward_result_activation
            hState (Or.inl ⟨rfl, rfl⟩) hConsume
        have hFinalStack := hFinalRel.stack
        rw [hArgsRel.stack] at hFinalStack
        exact
          ⟨targetFinal, hRun, hFinalRel.state.activeNoWrap,
            hFinalRel.state.base, hFinalRel.valuesLength,
            hFinalStack⟩

theorem msize (contract : MemoryContract.Contract) :
    StackPrimitiveForward contract .msize where
  simulate := by
    intro transcript plan live stackOffset frameBase
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hOnly hActiveNoWrap hArgsRel _hMemory hPrim
    have hValues : values = [] :=
      List.eq_nil_of_length_eq_zero hArgsRel.valuesLength
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
        have hState :
          ActivationStateRel contract plan live stackOffset frameBase
              .stack sourceArgs targetArgs :=
          .stack hOnly hActiveNoWrap (by simpa using hArgsRel.state)
        obtain ⟨targetFinal, hRun, hFinalRel⟩ :=
          AllocationObserverPreservation.Expr.observer_forward_result_activation
            hState (Or.inr ⟨rfl, rfl⟩) hConsume
        have hFinalStack := hFinalRel.stack
        rw [hArgsRel.stack] at hFinalStack
        exact
          ⟨targetFinal, hRun, hFinalRel.state.activeNoWrap,
            hFinalRel.state.base, hFinalRel.valuesLength,
            hFinalStack⟩

end StackPrimitiveForward

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
        ∀ op : Structured.BasicOp,
          ActivationPrimitiveForward contract op)
      (fuel : Nat)
      {transcript : Trace}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat}
      {mode : ActivationMode}
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
        AllocationObserverContext.ActivationExprContext
          lowerCtx lowerState localsCtx plan live mode)
      (hScoped : Functions.Scope.ExprScoped live expr)
      (hLower :
        AllocationLowering.lowerExpr lowerCtx lowerState expr =
          some lowered)
      (hCompile :
        Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
      (hRel :
        ActivationStateRel contract plan live
          stackOffset frameBase mode source target) :
      ∃ targetFinal,
        Structured.ObserverSemantics.Code.run code target =
            .ok targetFinal ∧
          ActivationExprResultRel contract plan live
            stackOffset frameBase results mode
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
          AllocationObserverPreservation.Expr.literal_forward_result_activation
            value hRel
        exact ⟨targetFinal, hTarget, hFinalRel⟩
    | @var name value state hValue =>
        subst_vars
        have hLive : name ∈ live := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        cases
            AllocationObserverContext.classify_activation_var
              hCtx hLive hLower hCompile with
        | stack planDepth depth op hLocation hCurrentDepth
            _hDepthValid hDup =>
            obtain ⟨targetFinal, _hSource, hTarget, hFinalRel⟩ :=
              AllocationObserverPreservation.Expr.stackVar_forward_result_activation
                hRel hLive hLocation hCurrentDepth hValue hDup
            exact ⟨targetFinal, hTarget, hFinalRel⟩
        | scratch frameDepth frameWords slot op hLocation hDup =>
            obtain ⟨targetFinal, _hSource, hTarget, hFinalRel⟩ :=
              AllocationObserverPreservation.Expr.scratchVar_forward_result_activation
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
        ∀ op : Structured.BasicOp,
          ActivationPrimitiveForward contract op)
      (fuel : Nat)
      {transcript : Trace}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat}
      {mode : ActivationMode}
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
        AllocationObserverContext.ActivationExprContext
          lowerCtx lowerState localsCtx plan live mode)
      (hScoped : Functions.Scope.ExprSeqScoped live exprs)
      (hLower :
        AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
          some lowered)
      (hCompile :
        Locals.ExprSeq.compileCode localsCtx stackOffset lowered =
          some code)
      (hRel :
        ActivationStateRel contract plan live
          stackOffset frameBase mode source target) :
      ∃ targetFinal,
        Structured.ObserverSemantics.Code.run code target =
            .ok targetFinal ∧
          ActivationExprResultRel contract plan live
            stackOffset frameBase results mode
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
        exact ⟨target, rfl, ActivationExprResultRel.nil hRel⟩
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
                            ActivationExprResultRel.append hHeadRel hTailRel
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega
end

set_option maxHeartbeats 800000 in
mutual
  /--
  The established expression simulation preserves the recursive scratch-frame
  allocator. This side theorem follows the real lowering and target run but
  leaves semantic result construction to `forwardExprFuel`.
  -/
  theorem allocatorReadyExprFuel
      {contract : MemoryContract.Contract}
      (hPrimitive :
        ∀ op : Structured.BasicOp,
          ActivationPrimitiveForward contract op)
      (fuel : Nat)
      {globalFrameWords : Nat}
      {config : AllocationObserverRelation.Frame.Config}
      {allocatorDepth : Nat}
      {transcript : Trace}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat}
      {mode : ActivationMode}
      {expr : Functions.Expr results}
      {lowered : Locals.Expr results} {code : Structured.Code}
      {source sourceFinal :
        Functions.ObserverSemantics.State transcript}
      {target targetFinal :
        Structured.ObserverSemantics.State transcript}
      {values : List Word}
      (hConfig :
        AllocationSupport.scratchFrameConfig?
            contract globalFrameWords =
          some config)
      (hSafe :
        AllocationObserverSafety.Expr.MemorySafeEval
          contract transcript expr source sourceFinal values)
      (hFuel : exprHeight expr ≤ fuel)
      (hCtx :
        AllocationObserverContext.ActivationExprContext
          lowerCtx lowerState localsCtx plan live mode)
      (hScoped : Functions.Scope.ExprScoped live expr)
      (hLower :
        AllocationLowering.lowerExpr lowerCtx lowerState expr =
          some lowered)
      (hCompile :
        Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
      (hRel :
        ActivationStateRel contract plan live
          stackOffset frameBase mode source target)
      (hReady :
        AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth target)
      (hRun :
        Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal) :
      AllocationObserverRelation.Frame.AllocatorEffect
        config allocatorDepth target targetFinal := by
    cases hSafe with
    | @lit value state =>
        subst_vars
        have hLowered : lowered = .lit value := by
          simpa [AllocationLowering.lowerExpr] using hLower.symm
        subst lowered
        have hCode : code = [.push value] := by
          simpa [Locals.Expr.compileCode] using hCompile.symm
        subst code
        let expected :=
          AllocationObserverRelation.StateRel.pushTargetBy 33 value target
        have hExpectedRun :
            Structured.ObserverSemantics.Code.run [.push value] target =
              .ok expected :=
          AllocationObserverPreservation.ObserverCode.run_push value target
        have hFinalEq : targetFinal = expected :=
          Except.ok.inj (hRun.symm.trans hExpectedRun)
        have hMachine :
            expected.source.evm.toMachineState =
              target.source.evm.toMachineState := by
          simp [expected,
            AllocationObserverRelation.StateRel.pushTargetBy,
            Simulation.ResourceReplay.State.withSource,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        rw [hFinalEq]
        exact
          AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
            hReady hMachine
    | @var name value state hValue =>
        subst_vars
        have hLive : name ∈ live := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        cases
            AllocationObserverContext.classify_activation_var
              hCtx hLive hLower hCompile with
        | stack planDepth depth op hLocation hCurrentDepth
            _hDepthValid hDup =>
            have hTargetGet :
                target.source.evm.stack[stackOffset + depth]? =
                  some value := by
              rw [hRel.base.core.store.stack_at
                hLive hLocation hCurrentDepth, hValue]
            let expected :=
              AllocationObserverRelation.StateRel.pushTarget value target
            have hExpectedRun :
                Structured.ObserverSemantics.Code.run [.op op] target =
                  .ok expected :=
              AllocationObserverPreservation.ObserverCode.run_dup
                hDup hTargetGet
            have hFinalEq : targetFinal = expected :=
              Except.ok.inj (hRun.symm.trans hExpectedRun)
            have hMachine :
                expected.source.evm.toMachineState =
                  target.source.evm.toMachineState := by
              simp [expected,
                AllocationObserverRelation.StateRel.pushTarget,
                AllocationObserverRelation.StateRel.pushTargetBy,
                Simulation.ResourceReplay.State.withSource,
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
            rw [hFinalEq]
            exact
              AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
                hReady hMachine
        | scratch frameDepth frameWords slot op hLocation hDup =>
            cases hRel with
            | scratch state =>
                obtain
                    ⟨expected, _hSourceEval, hExpectedRun, _hFinalRel,
                      _hStack, hMachine⟩ :=
                  AllocationObserverPreservation.Expr.scratchVar_forward
                    state hLive hLocation hValue hDup
                have hFinalEq : targetFinal = expected :=
                  Except.ok.inj (hRun.symm.trans hExpectedRun)
                rw [hFinalEq]
                exact
                  AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
                    hReady hMachine
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
                have hArgsResources :=
                  allocatorReadyExprSeqFuel hPrimitive (fuel - 1)
                    hConfig hArgsSafe (by
                      simp only [exprHeight] at hFuel
                      omega)
                    hCtx hArgsScoped hLowerArgs hArgsCode hRel
                    hReady hArgsRun
                rw [AllocationObserverPreservation.ObserverCode.run_append,
                  hArgsRun] at hRun
                have hOpEffect :=
                  (hPrimitive op).allocator.preserve
                    hConfig hArgsRel hMemory hPrim
                    hArgsResources.ready hRun
                exact hArgsResources.trans hOpEffect
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega

  theorem allocatorReadyExprSeqFuel
      {contract : MemoryContract.Contract}
      (hPrimitive :
        ∀ op : Structured.BasicOp,
          ActivationPrimitiveForward contract op)
      (fuel : Nat)
      {globalFrameWords : Nat}
      {config : AllocationObserverRelation.Frame.Config}
      {allocatorDepth : Nat}
      {transcript : Trace}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Locals.Allocation.Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat}
      {mode : ActivationMode}
      {exprs : Locals.ExprSeq results}
      {lowered : Locals.ExprSeq results} {code : Structured.Code}
      {source sourceFinal :
        Functions.ObserverSemantics.State transcript}
      {target targetFinal :
        Structured.ObserverSemantics.State transcript}
      {values : List Word}
      (hConfig :
        AllocationSupport.scratchFrameConfig?
            contract globalFrameWords =
          some config)
      (hSafe :
        AllocationObserverSafety.ExprSeq.MemorySafeEval
          contract transcript exprs source sourceFinal values)
      (hFuel : exprSeqHeight exprs ≤ fuel)
      (hCtx :
        AllocationObserverContext.ActivationExprContext
          lowerCtx lowerState localsCtx plan live mode)
      (hScoped : Functions.Scope.ExprSeqScoped live exprs)
      (hLower :
        AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
          some lowered)
      (hCompile :
        Locals.ExprSeq.compileCode localsCtx stackOffset lowered =
          some code)
      (hRel :
        ActivationStateRel contract plan live
          stackOffset frameBase mode source target)
      (hReady :
        AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth target)
      (hRun :
        Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal) :
      AllocationObserverRelation.Frame.AllocatorEffect
        config allocatorDepth target targetFinal := by
    cases hSafe with
    | @nil state =>
        subst_vars
        have hLowered : lowered = .nil := by
          simpa [AllocationLowering.lowerExprSeq] using hLower.symm
        subst lowered
        have hCode : code = [] := by
          simpa [Locals.ExprSeq.compileCode] using hCompile.symm
        subst code
        change Except.ok target = Except.ok targetFinal at hRun
        have hFinalEq : targetFinal = target :=
          (Except.ok.inj hRun).symm
        rw [hFinalEq]
        exact
          AllocationObserverRelation.Frame.AllocatorEffect.refl hReady
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
                            hCtx hScopedParts.1 hLowerHead hHeadCode hRel
                        have hHeadResources :=
                          allocatorReadyExprFuel hPrimitive (fuel - 1)
                            hConfig hHeadSafe (by
                              simp only [exprSeqHeight] at hFuel
                              omega)
                            hCtx hScopedParts.1 hLowerHead hHeadCode hRel
                            hReady hHeadRun
                        rw [
                          AllocationObserverPreservation.ObserverCode.run_append,
                          hHeadRun] at hRun
                        have hTailResources :=
                          allocatorReadyExprSeqFuel hPrimitive (fuel - 1)
                            hConfig hTailSafe (by
                              simp only [exprSeqHeight] at hFuel
                              omega)
                            hCtx hScopedParts.2 hLowerTail hTailCode
                            hHeadRel.state hHeadResources.ready hRun
                        exact hHeadResources.trans hTailResources
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega
end

theorem forwardExpr
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat}
    {mode : ActivationMode}
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
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase results mode
          sourceFinal target targetFinal values :=
  forwardExprFuel hPrimitive (exprHeight expr) hSafe (by rfl)
    hCtx hScoped hLower hCompile hRel

theorem forwardExprSeq
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat}
    {mode : ActivationMode}
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
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hLower :
      AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase results mode
          sourceFinal target targetFinal values :=
  forwardExprSeqFuel hPrimitive (exprSeqHeight exprs) hSafe (by rfl)
    hCtx hScoped hLower hCompile hRel

/--
Allocator-aware adjacent expression preservation used by recursive Functions
calls. The ordinary expression relation remains the semantic boundary; this
wrapper additionally carries the global frame allocator invariant.
-/
theorem forwardExprRuntime
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase results mode
          sourceFinal target targetFinal values ∧
        AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth targetFinal := by
  obtain ⟨targetFinal, hRun, hResult⟩ :=
    forwardExpr hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  exact
    ⟨targetFinal, hRun, hResult,
      allocatorReadyExprFuel hPrimitive (exprHeight expr)
        hConfig hSafe (by rfl) hCtx hScoped hLower hCompile hRel
        hReady hRun |>.ready⟩

/--
Allocator-aware expression preservation with its complete compositional
resource effect.

This strengthens the same canonical expression simulation with allocator
readiness, monotone growth, and budget-indexed protected-prefix preservation.
-/
theorem forwardExprRuntime_with_effect
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase results mode
          sourceFinal target targetFinal values ∧
        AllocationObserverRelation.Frame.AllocatorEffect
          config allocatorDepth target targetFinal := by
  obtain ⟨targetFinal, hRun, hResult, _hFinalReady⟩ :=
    forwardExprRuntime hPrimitive hConfig hSafe hCtx hScoped hLower
      hCompile hRel hReady
  have hResources :=
    allocatorReadyExprFuel hPrimitive (exprHeight expr)
      hConfig hSafe (by rfl) hCtx hScoped hLower hCompile hRel
      hReady hRun
  exact
    ⟨targetFinal, hRun, hResult, hResources⟩

/--
Compatibility projection exposing only allocator readiness and target growth.
-/
theorem forwardExprRuntime_with_growth
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase results mode
          sourceFinal target targetFinal values ∧
        AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth targetFinal ∧
        AllocationObserverRelation.Frame.TargetGrowth
          target targetFinal := by
  obtain ⟨targetFinal, hRun, hResult, hEffect⟩ :=
    forwardExprRuntime_with_effect hPrimitive hConfig hSafe hCtx hScoped
      hLower hCompile hRel hReady
  exact
    ⟨targetFinal, hRun, hResult, hEffect.ready, hEffect.growth⟩

/--
Allocator-aware preservation for argument/result sequences.
-/
theorem forwardExprSeqRuntime
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat}
    {mode : ActivationMode}
    {exprs : Locals.ExprSeq results}
    {lowered : Locals.ExprSeq results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript exprs source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hLower :
      AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase results mode
          sourceFinal target targetFinal values ∧
        AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth targetFinal := by
  obtain ⟨targetFinal, hRun, hResult⟩ :=
    forwardExprSeq hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  exact
    ⟨targetFinal, hRun, hResult,
      allocatorReadyExprSeqFuel hPrimitive (exprSeqHeight exprs)
        hConfig hSafe (by rfl) hCtx hScoped hLower hCompile hRel
        hReady hRun |>.ready⟩

/--
Allocator-aware expression-sequence preservation with monotone target-memory
growth.
-/
theorem forwardExprSeqRuntime_with_growth
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat}
    {mode : ActivationMode}
    {exprs : Locals.ExprSeq results}
    {lowered : Locals.ExprSeq results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript exprs source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hLower :
      AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        ActivationExprResultRel contract plan live
          stackOffset frameBase results mode
          sourceFinal target targetFinal values ∧
        AllocationObserverRelation.Frame.AllocatorReady
          config allocatorDepth targetFinal ∧
        AllocationObserverRelation.Frame.TargetGrowth
          target targetFinal := by
  obtain ⟨targetFinal, hRun, hResult, _hFinalReady⟩ :=
    forwardExprSeqRuntime hPrimitive hConfig hSafe hCtx hScoped hLower
      hCompile hRel hReady
  have hResources :=
    allocatorReadyExprSeqFuel hPrimitive (exprSeqHeight exprs)
      hConfig hSafe (by rfl) hCtx hScoped hLower hCompile hRel
      hReady hRun
  exact
    ⟨targetFinal, hRun, hResult,
      hResources.ready, hResources.growth⟩

/--
A zero-result expression preserves the complete statement-boundary activation
invariant. Expression safety keeps named variables unchanged, while the result
relation says that no value was added to the exact active stack.
-/
theorem Expr.invariant_zero
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source target)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hResult :
      ActivationExprResultRel contract plan live 0 frameBase 0 mode
        sourceFinal target targetFinal values) :
    AllocationObserverContext.ActivationInvariant
      contract lowerCtx lowerState localsCtx plan live frameBase mode
      sourceFinal targetFinal := by
  have hValues : values = [] :=
    List.eq_nil_of_length_eq_zero hResult.valuesLength
  subst values
  refine
    ⟨hInvariant.compiler, hInvariant.planWF, ?_, ?_, ?_⟩
  · intro name hLive
    rw [hSafe.vars_eq]
    exact hInvariant.defined name hLive
  · simpa using hResult.state
  · rw [hResult.stack]
    simpa using hInvariant.stackLength

/--
Zero-result expressions preserve the complete recursive runtime invariant once
their allocator side condition has been transported by the expression theorem.
-/
theorem Expr.runtimeInvariant_zero
    {contract : MemoryContract.Contract}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hResult :
      ActivationExprResultRel contract plan live 0 frameBase 0 mode
        sourceFinal target targetFinal values)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth targetFinal) :
    AllocationObserverContext.ActivationRuntimeInvariant
      contract config allocatorDepth lowerCtx lowerState localsCtx
      plan live frameBase mode sourceFinal targetFinal :=
  { activation :=
      Expr.invariant_zero hInvariant.activation hSafe hResult
    allocator := hReady
    frame := hInvariant.frame }

/--
Evaluate one source expression result through the real lowerer and compiler,
then pop that result exactly as Structured `switch` and condition execution do.
-/
theorem Expr.one_forward
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 1}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source target)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal [value])
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx 0 lowered = some code) :
    ∃ targetWithValue targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetWithValue ∧
        targetWithValue.source.evm.stack.pop =
          some (target.source.evm.stack, value) ∧
        targetFinal =
          StateRel.popTarget target.source.evm.stack targetWithValue ∧
        AllocationObserverContext.ActivationInvariant
          contract lowerCtx lowerState localsCtx plan live frameBase mode
          sourceFinal targetFinal := by
  obtain ⟨targetWithValue, hRun, hResult⟩ :=
    forwardExpr hPrimitive
      hSafe hInvariant.compiler hScoped hLower hCompile hInvariant.state
  have hStack :
      targetWithValue.source.evm.stack =
        value :: target.source.evm.stack := by
    simpa using hResult.stack
  let targetFinal :=
    StateRel.popTarget target.source.evm.stack targetWithValue
  have hPop :
      targetWithValue.source.evm.stack.pop =
        some (target.source.evm.stack, value) := by
    rw [hStack]
    rfl
  refine
    ⟨targetWithValue, targetFinal, hRun, hPop, rfl,
      hInvariant.compiler, hInvariant.planWF, ?_,
      hResult.state.pop_target hStack, ?_⟩
  · intro name hLive
    rw [hSafe.vars_eq]
    exact hInvariant.defined name hLive
  · simpa [targetFinal, StateRel.popTarget] using hInvariant.stackLength

/--
Allocator-aware one-result evaluation and result consumption.
-/
theorem Expr.one_forward_runtime
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 1}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal [value])
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx 0 lowered = some code) :
    ∃ targetWithValue targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetWithValue ∧
        targetWithValue.source.evm.stack.pop =
          some (target.source.evm.stack, value) ∧
        targetFinal =
          StateRel.popTarget target.source.evm.stack targetWithValue ∧
        AllocationObserverContext.ActivationRuntimeInvariant
          contract config allocatorDepth lowerCtx lowerState localsCtx
          plan live frameBase mode sourceFinal targetFinal := by
  obtain
      ⟨targetWithValue, targetFinal, hRun, hPop, hFinal,
        hActivation⟩ :=
    Expr.one_forward hPrimitive hInvariant.activation hSafe hScoped
      hLower hCompile
  subst targetFinal
  have hReadyWithValue :=
    allocatorReadyExprFuel hPrimitive (exprHeight expr)
      hConfig hSafe (by rfl) hInvariant.activation.compiler hScoped
      hLower hCompile hInvariant.activation.state hInvariant.allocator
      hRun |>.ready
  have hMachine :
      (StateRel.popTarget
          target.source.evm.stack targetWithValue).source.evm.toMachineState =
        targetWithValue.source.evm.toMachineState := by
    simp [StateRel.popTarget,
      Simulation.ResourceReplay.State.withSource,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  exact
    ⟨targetWithValue,
      StateRel.popTarget target.source.evm.stack targetWithValue,
      hRun, hPop, rfl,
      { activation := hActivation
        allocator := hReadyWithValue.of_machine_eq hMachine
        frame := hInvariant.frame }⟩

/--
Evaluate one source condition through the real allocation and Locals
compilers, then consume the target result exactly as Structured control flow
does. The returned state is again at the statement-boundary activation
invariant.
-/
theorem Expr.condition_forward
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 1}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source target)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal [value])
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx 0 lowered = some code) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.runCondition code target =
          .ok (targetFinal, value != EvmYul.UInt256.ofNat 0) ∧
        AllocationObserverContext.ActivationInvariant
          contract lowerCtx lowerState localsCtx plan live frameBase mode
          sourceFinal targetFinal := by
  obtain ⟨targetWithValue, hRun, hResult⟩ :=
    forwardExpr hPrimitive
      hSafe hInvariant.compiler hScoped hLower hCompile hInvariant.state
  have hStack :
      targetWithValue.source.evm.stack =
        value :: target.source.evm.stack := by
    simpa using hResult.stack
  let targetFinal :=
    StateRel.popTarget target.source.evm.stack targetWithValue
  have hCondition :
      Structured.ObserverSemantics.Code.runCondition code target =
        .ok (targetFinal, value != EvmYul.UInt256.ofNat 0) := by
    unfold Structured.ObserverSemantics.Code.runCondition
    unfold Structured.EffectSemantics.Code.runCondition
    change
      Structured.EffectSemantics.Code.run
          (Structured.ObserverSemantics.stateModel transcript)
          (Structured.ObserverSemantics.handler transcript)
          code target =
        .ok targetWithValue at hRun
    rw [hRun]
    simp [Structured.EffectSemantics.Code.popCondition, hStack,
      EvmYul.Stack.pop, targetFinal, StateRel.popTarget]
  refine ⟨targetFinal, hCondition, ?_⟩
  refine
    ⟨hInvariant.compiler, hInvariant.planWF, ?_,
      hResult.state.pop_target hStack, ?_⟩
  · intro name hLive
    rw [hSafe.vars_eq]
    exact hInvariant.defined name hLive
  · simpa [targetFinal, StateRel.popTarget] using hInvariant.stackLength

/--
Allocator-aware condition evaluation used by recursive control proofs.
-/
theorem Expr.condition_forward_runtime
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 1}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal [value])
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx 0 lowered = some code) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.runCondition code target =
          .ok (targetFinal, value != EvmYul.UInt256.ofNat 0) ∧
        AllocationObserverContext.ActivationRuntimeInvariant
          contract config allocatorDepth lowerCtx lowerState localsCtx
          plan live frameBase mode sourceFinal targetFinal := by
  obtain
      ⟨targetWithValue, targetFinal, hRun, hPop, rfl, hFinalInvariant⟩ :=
    Expr.one_forward_runtime hPrimitive hConfig hInvariant hSafe hScoped
      hLower hCompile
  have hCondition :
      Structured.ObserverSemantics.Code.runCondition code target =
        .ok
          (StateRel.popTarget target.source.evm.stack targetWithValue,
            value != EvmYul.UInt256.ofNat 0) := by
    unfold Structured.ObserverSemantics.Code.runCondition
    unfold Structured.EffectSemantics.Code.runCondition
    change
      Structured.EffectSemantics.Code.run
          (Structured.ObserverSemantics.stateModel transcript)
          (Structured.ObserverSemantics.handler transcript)
          code target =
        .ok targetWithValue at hRun
    rw [hRun]
    simp [Structured.EffectSemantics.Code.popCondition, hPop,
      StateRel.popTarget]
  exact ⟨_, hCondition, hFinalInvariant⟩

theorem Expr.backward_of_safeEval
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {results : Nat} {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
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
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        expr source =
      .ok (sourceFinal, values) ∧
    ActivationExprResultRel contract plan live
      stackOffset frameBase results mode
      sourceFinal target targetFinal values := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forwardExpr hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSafe.eval_eq, hExpectedRel⟩

theorem ExprSeq.backward_of_safeEval
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {results : Nat} {exprs : Locals.ExprSeq results}
    {lowered : Locals.ExprSeq results} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
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
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Locals.Source.Effectful.Expr.ExprSeq.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        exprs source =
      .ok (sourceFinal, values) ∧
    ActivationExprResultRel contract plan live
      stackOffset frameBase results mode
      sourceFinal target targetFinal values := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forwardExprSeq hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSafe.eval_eq, hExpectedRel⟩

end AllocationObserverExpression
end Functions
end EvmCompiler
