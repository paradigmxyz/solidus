import EvmCompiler.Functions.AllocationObserverStatement

namespace EvmCompiler
namespace Functions
namespace AllocationObserverStatement

open AllocationObserverRelation

namespace Sequence
namespace RegularStmtInvariantForward

/--
Forward preservation for a `for` whose initializer completes regularly and
whose first condition is false.

The theorem composes the real open initializer, condition compiler, canonical
loop semantics, and compiler-emitted outer cleanup. Recursive iterations remain
a separate loop-owned theorem.
-/
theorem for_false_of_components
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx loopSourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {outerPlan loopPlan : Locals.Allocation.Plan}
    {outerLive loopLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode loopMode : ActivationMode}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterInit sourceAfterCond :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript cond sourceAfterInit sourceAfterCond [value])
    (hFalse : value = EvmYul.UInt256.ofNat 0)
    (hInitScoped : Functions.Scope.Block.Scoped outerLive init)
    (hCondScoped : Functions.Scope.ExprScoped loopLive cond)
    (hSourceScope : sourceCtx.scope = outerLive)
    (hLoopSourceScope : loopSourceCtx.scope = loopLive)
    (hSubset :
      ∀ name, name ∈ outerLive → name ∈ loopLive)
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx outerPlan outerLive
        frameBase outerMode source target)
    (hInit :
      ∀ {loweredInit : Locals.Block}
        {loopState : AllocationLowering.State}
        {initCode : List Expressions.Stmt}
        {initLocals : Locals.Ctx},
        AllocationLowering.lowerBlockOpen
            lowerCtx returns lowerState init =
          some (loweredInit, loopState) →
        Locals.Block.compileOpen localsCtx.withoutLoopControl loweredInit =
          some (initCode, initLocals) →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx lowerState localsCtx.withoutLoopControl
            outerPlan outerLive frameBase outerMode source target →
        ∃ targetAfterInit,
          RegularBlockInvariantForward
            contract transcript lowerCtx loopState initLocals loopPlan
            loopLive frameBase outerMode loopMode sourceProgram
            sourceCtx.withoutLoopControl init source targetProgram
            { stmts := Expressions.StmtList.toStructured initCode }
            target sourceAfterInit targetAfterInit loopSourceCtx)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.for_ init cond post body) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      RegularStmtInvariantForward
        contract transcript lowerCtx lowerFinal localsFinal outerPlan
        outerLive frameBase outerMode outerMode sourceProgram sourceCtx
        (.for_ init cond post body) source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            loopLive sourceAfterCond))
        targetFinal sourceCtx := by
  obtain
      ⟨loweredInit, loopState, loweredCond, loweredPost, afterPost,
        loweredBody, afterBody, hLowerInit, hLowerCond, hLowerPost,
        hLowerBody, hLoweredShape, hLowerFinal⟩ :=
    AllocationLowering.lowerStmt_for_components hLower
  subst loweredStmts
  obtain
      ⟨initCode, initLocals, condCode,
        postCode, postLocals, compiledPost,
        bodyCode, bodyLocals, compiledBody, cleanup,
        hCompileInit, hCompileCond, _hCompilePost, _hFinishPost,
        _hCompileBody, _hFinishBody, hCleanup,
        hCompiledShape, hLocalsFinal⟩ :=
    Locals.Block.compileOpen_single_for_components hCompile
  have hInitialLoopInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx.withoutLoopControl
        outerPlan outerLive frameBase outerMode source target :=
    hInvariant.transport_locals_layout rfl
  obtain ⟨targetAfterInit, hInitForward⟩ :=
    hInit hLowerInit hCompileInit hInitialLoopInvariant
  rcases hInitForward with
    ⟨initSourceFuel, initTargetFuel,
      hSourceInit, hTargetInit, hInitInvariant, hInitMode⟩
  obtain ⟨targetAfterCond, hTargetCond, hCondInvariant⟩ :=
    AllocationObserverExpression.Expr.condition_forward
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hInitInvariant hSafe hCondScoped hLowerCond hCompileCond
  have hSourceCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          cond sourceAfterInit =
        .ok (sourceAfterCond, false) := by
    simpa [hFalse] using hSafe.evalCondition_eq
  have hTargetCondFalse :
      Structured.ObserverSemantics.Code.runCondition condCode
          targetAfterInit =
        .ok (targetAfterCond, false) := by
    simpa [hFalse] using hTargetCond
  have hLoopInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx loopState initLocals loopPlan loopLive
        frameBase loopMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          loopLive sourceAfterCond)
        targetAfterCond :=
    hCondInvariant.restrict_source_live
  have hExtends :=
    AllocationLowering.lowerBlockOpen_stateExtends
      hInitScoped hLowerInit
  obtain ⟨hTransition, hLayout, hSlots⟩ :=
    AllocationObserverCleanup.Plain.transition_of_stateExtends
      hLoopInvariant.compiler hInvariant.compiler hSubset
      hInitMode.symm rfl hExtends
  obtain ⟨_hRestoredCompiler, hPlanAgree⟩ :=
    AllocationObserverCleanup.Plain.restore_context
      hLoopInvariant.compiler hInvariant.compiler hTransition
      hLayout hSlots
  obtain
      ⟨targetFinal, hCleanupRun, hFinalLoopRel, hFinalLength⟩ :=
    AllocationObserverCleanup.Plain.forward_exact
      hLoopInvariant.compiler hTransition hLoopInvariant.planWF
      hLoopInvariant.defined hLoopInvariant.state
      hLoopInvariant.stackLength hCleanup
  have hFinalRel :
      ActivationStateRel contract outerPlan outerLive 0 frameBase
        outerMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            loopLive sourceAfterCond))
        targetFinal :=
    hFinalLoopRel.transport_plan hPlanAgree
  have hFinalDefined :
      LiveDefined outerLive
        (((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            loopLive sourceAfterCond)).source) := by
    simpa [Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.restrictTo] using
      hLoopInvariant.defined.restrictTo hTransition.subset
  have hFinalInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerFinal localsFinal outerPlan outerLive
          frameBase outerMode
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            outerLive
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              loopLive sourceAfterCond))
          targetFinal :=
    by
      rw [hLowerFinal, hLocalsFinal]
      exact
        { compiler := hInvariant.compiler.transport_state rfl rfl
          planWF := hInvariant.planWF
          defined := hFinalDefined
          state := hFinalRel
          stackLength := hFinalLength }
  have hSourceInit' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx.withoutLoopControl
          (initSourceFuel + 1) init source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceAfterInit,
            loopSourceCtx) :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (Nat.le_succ initSourceFuel) hSourceInit
  have hSource :=
    Functions.Source.Effectful.Stmt.run_for_false_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := initSourceFuel)
      (post := post) (body := body)
      hSourceInit' hSourceCond
  have hTargetInit' :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (initTargetFuel + 1)
        { stmts := Expressions.StmtList.toStructured initCode }
        target
        (Structured.EffectSemantics.Outcome.regular targetAfterInit) :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetInit (Nat.le_succ initTargetFuel)
  have hTargetFor :
      Structured.ObserverSemantics.For.Eval
        targetProgram (initTargetFuel + 1)
        condCode
        { stmts := Expressions.StmtList.toStructured compiledPost.stmts }
        { stmts := Expressions.StmtList.toStructured compiledBody.stmts }
        targetAfterInit
        (Structured.EffectSemantics.Outcome.regular targetAfterCond) :=
    Structured.EffectSemantics.For.Eval.false
      (fuel := initTargetFuel) hTargetCondFalse
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (initTargetFuel + 2)
        (.for_
          { stmts := Expressions.StmtList.toStructured initCode }
          condCode
          { stmts := Expressions.StmtList.toStructured compiledPost.stmts }
          { stmts := Expressions.StmtList.toStructured compiledBody.stmts })
        target
        (Structured.EffectSemantics.Outcome.regular targetAfterCond) :=
    Structured.EffectSemantics.Stmt.Eval.for_init_regular
      hTargetInit' hTargetFor
  have hTargetForBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (initTargetFuel + 3)
        { stmts :=
            [(.for_
              { stmts := Expressions.StmtList.toStructured initCode }
              condCode
              { stmts :=
                  Expressions.StmtList.toStructured compiledPost.stmts }
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts })] }
        target
        (Structured.EffectSemantics.Outcome.regular targetAfterCond) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCleanupBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := [Structured.Stmt.code cleanup] }
        targetAfterCond
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hCleanupRun)
      Structured.EffectSemantics.Block.Eval.nil
  obtain ⟨targetFuel, hTarget⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hTargetForBlock hCleanupBlock
  refine
    ⟨targetFinal, initSourceFuel + 2, targetFuel, ?_, ?_,
      hFinalInvariant, SameFrame.refl outerMode⟩
  · simpa [hSourceScope, hLoopSourceScope] using hSource
  · have hCondCompile :
        Expressions.Expr.compile
            (Expressions.Expr.code (results := 1) condCode) =
          condCode := by
      rfl
    have hPostCompile :
        Expressions.Block.toStructured compiledPost =
          { stmts :=
              Expressions.StmtList.toStructured compiledPost.stmts } := by
      cases compiledPost
      rfl
    have hBodyCompile :
        Expressions.Block.toStructured compiledBody =
          { stmts :=
              Expressions.StmtList.toStructured compiledBody.stmts } := by
      cases compiledBody
      rfl
    rw [hCompiledShape, Expressions.StmtList.toStructured_append]
    simp only [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured]
    rw [hCondCompile, hPostCompile, hBodyCompile]
    simpa [Locals.codeStmt, Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget

end RegularStmtInvariantForward
end Sequence
end AllocationObserverStatement
end Functions
end EvmCompiler
