import EvmCompiler.Functions.AllocationObserverStatement

namespace EvmCompiler
namespace Functions
namespace AllocationObserverStatement

open AllocationObserverRelation

namespace ForLoop

/--
Restore the outer activation after a regular loop result.

The initializer's open lowering determines the lexical stack prefix. The real
Locals cleanup removes that prefix, and plan agreement transports the surviving
locals back to the outer allocation plan.
-/
theorem finish_regular_outer
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState loopState : AllocationLowering.State}
    {localsCtx initLocals : Locals.Ctx}
    {outerPlan loopPlan : Locals.Allocation.Plan}
    {outerLive loopLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode loopMode : ActivationMode}
    {init : Functions.Block}
    {loweredInit : Locals.Block}
    {cleanup : Structured.Code}
    {source sourceLoop :
      Functions.ObserverSemantics.State transcript}
    {target targetLoop :
      Structured.ObserverSemantics.State transcript}
    (hOuter :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx outerPlan outerLive
        frameBase outerMode source target)
    (hLoop :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx loopState initLocals loopPlan loopLive
        frameBase loopMode sourceLoop targetLoop)
    (hSameFrame : SameFrame outerMode loopMode)
    (hInitScoped : Functions.Scope.Block.Scoped outerLive init)
    (hSubset :
      ∀ name, name ∈ outerLive → name ∈ loopLive)
    (hLowerInit :
      AllocationLowering.lowerBlockOpen
          lowerCtx returns lowerState init =
        some (loweredInit, loopState))
    (hCleanup :
      initLocals.cleanupTo? localsCtx.layout.length =
        some cleanup) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run cleanup targetLoop =
          .ok targetFinal ∧
        AllocationObserverContext.ActivationInvariant
          contract lowerCtx lowerState localsCtx outerPlan outerLive
          frameBase outerMode
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            outerLive sourceLoop)
          targetFinal := by
  have hExtends :=
    AllocationLowering.lowerBlockOpen_stateExtends
      hInitScoped hLowerInit
  obtain ⟨hTransition, hLayout, hSlots⟩ :=
    AllocationObserverCleanup.Plain.transition_of_stateExtends
      hLoop.compiler hOuter.compiler hSubset hSameFrame.symm
      rfl hExtends
  obtain ⟨_hRestoredCompiler, hPlanAgree⟩ :=
    AllocationObserverCleanup.Plain.restore_context
      hLoop.compiler hOuter.compiler hTransition hLayout hSlots
  obtain
      ⟨targetFinal, hCleanupRun, hFinalLoopRel, hFinalLength⟩ :=
    AllocationObserverCleanup.Plain.forward_exact
      hLoop.compiler hTransition hLoop.planWF hLoop.defined hLoop.state
      hLoop.stackLength hCleanup
  have hFinalRel :
      ActivationStateRel contract outerPlan outerLive 0 frameBase
        outerMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceLoop)
        targetFinal :=
    hFinalLoopRel.transport_plan hPlanAgree
  have hFinalDefined :
      LiveDefined outerLive
        (((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceLoop).source) := by
    simpa [Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.restrictTo] using
      hLoop.defined.restrictTo hTransition.subset
  exact
    ⟨targetFinal, hCleanupRun,
      { compiler := hOuter.compiler
        planWF := hOuter.planWF
        defined := hFinalDefined
        state := hFinalRel
        stackLength := hFinalLength }⟩

/--
A loop body that exits through `break`, retaining the complete continuing
activation invariant after the body compiler's scoped block.
-/
def BreakScopedBlockInvariantForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Locals.Allocation.Plan)
    (live : List Locals.Name)
    (frameBase : Nat)
    (mode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (sourceBlock : Functions.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (targetBlock : Structured.Block)
    (target : Structured.ObserverSemantics.State transcript)
    (sourceFinal : Functions.ObserverSemantics.State transcript)
    (targetFinal : Structured.ObserverSemantics.State transcript) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceBlock sourceFuel source =
        .ok (Functions.Source.Effectful.Outcome.brk sourceFinal) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel targetBlock target
          (Structured.EffectSemantics.Outcome.brk targetFinal) ∧
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        sourceFinal targetFinal

end ForLoop

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
  obtain
      ⟨targetFinal, hCleanupRun, hFinalBaseInvariant⟩ :=
    ForLoop.finish_regular_outer
      hInvariant hLoopInvariant hInitMode hInitScoped hSubset
      hLowerInit hCleanup
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
      exact hFinalBaseInvariant.transport_state rfl rfl
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

/--
Forward preservation for a `for` whose initializer completes regularly, whose
first condition is true, and whose body exits through `break`.
-/
theorem for_body_brk_of_components
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
    {source sourceAfterInit sourceAfterCond sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript cond sourceAfterInit sourceAfterCond [value])
    (hTrue : (value != EvmYul.UInt256.ofNat 0) = true)
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
    (hBody :
      ∀ {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {targetAfterCond :
          Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerBlockScoped
            lowerCtx returns loopState post =
          some (loweredPost, afterPost) →
        AllocationLowering.lowerBlockScoped
            lowerCtx returns afterPost body =
          some (loweredBody, afterBody) →
        Locals.Block.compileOpen
            (initLocals.withLoopControl initLocals.layout.length)
            loweredBody =
          some (bodyCode, bodyLocals) →
        Locals.finishScoped
            (initLocals.withLoopControl initLocals.layout.length)
            bodyLocals bodyCode =
          some compiledBody →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode
            sourceAfterCond targetAfterCond →
        ∃ targetBodyFinal,
          ForLoop.BreakScopedBlockInvariantForward
            contract transcript lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode sourceProgram
            (loopSourceCtx.withLoopControl loopLive loopLive)
            body sourceAfterCond targetProgram compiledBody.toStructured
            targetAfterCond sourceBodyFinal targetBodyFinal)
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
          outerLive sourceBodyFinal)
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
        hCompileBody, hFinishBody, hCleanup,
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
  have hPostShape :=
    AllocationLowering.lowerBlockScoped_state_shape hLowerPost
  have hBodyStartInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx afterPost
        (initLocals.withLoopControl initLocals.layout.length)
        loopPlan loopLive frameBase loopMode
        sourceAfterCond targetAfterCond :=
    (hCondInvariant.transport_state hPostShape.1 hPostShape.2)
      |>.transport_locals_layout rfl
  obtain ⟨targetBodyFinal, hBodyForward⟩ :=
    hBody hLowerPost hLowerBody hCompileBody hFinishBody
      hBodyStartInvariant
  rcases hBodyForward with
    ⟨bodySourceFuel, bodyTargetFuel,
      hSourceBody, hTargetBody, hBodyInvariant⟩
  have hBodyStructured :
      Expressions.Block.toStructured compiledBody =
        { stmts :=
            Expressions.StmtList.toStructured compiledBody.stmts } := by
    cases compiledBody
    rfl
  have hTargetBody' :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyTargetFuel
        { stmts :=
            Expressions.StmtList.toStructured compiledBody.stmts }
        targetAfterCond
        (Structured.EffectSemantics.Outcome.brk targetBodyFinal) := by
    rw [hBodyStructured] at hTargetBody
    exact hTargetBody
  have hLoopResultInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx loopState initLocals loopPlan loopLive
        frameBase loopMode sourceBodyFinal targetBodyFinal :=
    (hBodyInvariant.transport_state hPostShape.1.symm hPostShape.2.symm)
      |>.transport_locals_layout rfl
  obtain
      ⟨targetFinal, hCleanupRun, hFinalBaseInvariant⟩ :=
    ForLoop.finish_regular_outer
      hInvariant hLoopResultInvariant hInitMode hInitScoped hSubset
      hLowerInit hCleanup
  have hFinalInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerFinal localsFinal outerPlan outerLive
        frameBase outerMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceBodyFinal)
        targetFinal := by
    rw [hLowerFinal, hLocalsFinal]
    exact hFinalBaseInvariant.transport_state rfl rfl
  have hSourceCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          cond sourceAfterInit =
        .ok (sourceAfterCond, true) := by
    simpa [hTrue] using hSafe.evalCondition_eq
  let sourceFuel := Nat.max initSourceFuel bodySourceFuel
  have hSourceInit' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx.withoutLoopControl
          (sourceFuel + 1) init source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceAfterInit,
            loopSourceCtx) :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _))
      hSourceInit
  have hSourceBody' :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram
          (loopSourceCtx.withLoopControl loopLive loopLive)
          body sourceFuel sourceAfterCond =
        .ok (Functions.Source.Effectful.Outcome.brk sourceBodyFinal) :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (Nat.le_max_right _ _) hSourceBody
  have hSourceBodyCanonical :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram
          (loopSourceCtx.withLoopControl
            loopSourceCtx.scope loopSourceCtx.scope)
          body sourceFuel sourceAfterCond =
        .ok (Functions.Source.Effectful.Outcome.brk sourceBodyFinal) := by
    simpa [hLoopSourceScope] using hSourceBody'
  have hSource :=
    Functions.Source.Effectful.Stmt.run_for_body_brk_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := sourceFuel)
      (post := post) hSourceInit' hSourceCond hSourceBodyCanonical
  have hTargetCondTrue :
      Structured.ObserverSemantics.Code.runCondition condCode
          targetAfterInit =
        .ok (targetAfterCond, true) := by
    simpa [hTrue] using hTargetCond
  have hTargetForBase :
      Structured.ObserverSemantics.For.Eval
        targetProgram (bodyTargetFuel + 1)
        condCode
        { stmts := Expressions.StmtList.toStructured compiledPost.stmts }
        { stmts :=
            Expressions.StmtList.toStructured compiledBody.stmts }
        targetAfterInit
        (Structured.EffectSemantics.Outcome.regular targetBodyFinal) :=
    Structured.EffectSemantics.For.Eval.body_brk
      hTargetCondTrue hTargetBody'
  let targetLoopFuel := Nat.max initTargetFuel (bodyTargetFuel + 1)
  have hTargetInit' :
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetLoopFuel
        { stmts := Expressions.StmtList.toStructured initCode }
        target
        (Structured.EffectSemantics.Outcome.regular targetAfterInit) :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetInit (Nat.le_max_left _ _)
  have hTargetFor :
      Structured.ObserverSemantics.For.Eval
        targetProgram targetLoopFuel
        condCode
        { stmts := Expressions.StmtList.toStructured compiledPost.stmts }
        { stmts :=
            Expressions.StmtList.toStructured compiledBody.stmts }
        targetAfterInit
        (Structured.EffectSemantics.Outcome.regular targetBodyFinal) :=
    Structured.EffectSemantics.For.Eval.mono
      hTargetForBase (Nat.le_max_right _ _)
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (targetLoopFuel + 1)
        (.for_
          { stmts := Expressions.StmtList.toStructured initCode }
          condCode
          { stmts := Expressions.StmtList.toStructured compiledPost.stmts }
          { stmts :=
              Expressions.StmtList.toStructured compiledBody.stmts })
        target
        (Structured.EffectSemantics.Outcome.regular targetBodyFinal) :=
    Structured.EffectSemantics.Stmt.Eval.for_init_regular
      hTargetInit' hTargetFor
  have hTargetForBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetLoopFuel + 2)
        { stmts :=
            [(.for_
              { stmts := Expressions.StmtList.toStructured initCode }
              condCode
              { stmts :=
                  Expressions.StmtList.toStructured compiledPost.stmts }
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts })] }
        target
        (Structured.EffectSemantics.Outcome.regular targetBodyFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCleanupBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := [Structured.Stmt.code cleanup] }
        targetBodyFinal
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hCleanupRun)
      Structured.EffectSemantics.Block.Eval.nil
  obtain ⟨targetFuel, hTarget⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hTargetForBlock hCleanupBlock
  refine
    ⟨targetFinal, sourceFuel + 2, targetFuel, ?_, ?_,
      hFinalInvariant, SameFrame.refl outerMode⟩
  · simpa [hSourceScope] using hSource
  · have hCondCompile :
        Expressions.Expr.compile
            (Expressions.Expr.code (results := 1) condCode) =
          condCode := by
      rfl
    have hInitCompile :
        Expressions.Block.toStructured { stmts := initCode } =
          { stmts := Expressions.StmtList.toStructured initCode } := by
      rfl
    have hPostCompile :
        Expressions.Block.toStructured compiledPost =
          { stmts :=
              Expressions.StmtList.toStructured compiledPost.stmts } := by
      cases compiledPost
      rfl
    rw [hCompiledShape, Expressions.StmtList.toStructured_append]
    simp only [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured]
    rw [hInitCompile, hCondCompile, hPostCompile, hBodyStructured]
    simpa [Locals.codeStmt, Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget

end RegularStmtInvariantForward
end Sequence
end AllocationObserverStatement
end Functions
end EvmCompiler
