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

/--
A loop body that exits through `continue`, retaining the complete continuing
activation invariant after the body compiler's scoped block.
-/
def ContinueScopedBlockInvariantForward
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
        .ok (Functions.Source.Effectful.Outcome.cont sourceFinal) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel targetBlock target
          (Structured.EffectSemantics.Outcome.cont targetFinal) ∧
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        sourceFinal targetFinal

/--
Regular loop execution at the adjacent Functions/Structured boundary.

The relation hides fuel while retaining the complete allocation invariant
needed by the next recursive iteration or by outer-scope cleanup.
-/
def RegularInvariantForward
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
    (loopCtx : Functions.Source.Ctx)
    (cond : Functions.Expr 1)
    (postBase : Functions.Source.Ctx)
    (post : Functions.Block)
    (bodyBase : Functions.Source.Ctx)
    (body : Functions.Block)
    (targetProgram : Structured.Program)
    (condCode : Structured.Code)
    (postBlock bodyBlock : Structured.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (target : Structured.ObserverSemantics.State transcript)
    (sourceFinal : Functions.ObserverSemantics.State transcript)
    (targetFinal : Structured.ObserverSemantics.State transcript) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram loopCtx cond postBase post bodyBase body
          sourceFuel source =
        .ok (Functions.Source.Effectful.Outcome.regular sourceFinal) ∧
      Structured.ObserverSemantics.For.Eval
        targetProgram targetFuel condCode postBlock bodyBlock target
          (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        sourceFinal targetFinal

/--
A false condition is the regular loop base case.
-/
theorem RegularInvariantForward.false
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond :
      Structured.ObserverSemantics.State transcript}
    (hLoopScope : loopCtx.scope = live)
    (hSourceCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          cond source =
        .ok (sourceAfterCond, false))
    (hTargetCond :
      Structured.ObserverSemantics.Code.runCondition condCode target =
        .ok (targetAfterCond, false))
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        sourceAfterCond targetAfterCond) :
    RegularInvariantForward
      contract transcript lowerCtx lowerState localsCtx plan live
      frameBase mode sourceProgram loopCtx cond postBase post bodyBase body
      targetProgram condCode postBlock bodyBlock source target
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        live sourceAfterCond)
      targetAfterCond := by
  have hSource :=
    Functions.Source.Effectful.Stmt.runForLoop_false_of_eval
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (loopCtx := loopCtx) (fuel := 0)
      (postBase := postBase) (post := post)
      (bodyBase := bodyBase) (body := body) hSourceCond
  exact
    ⟨1, 1,
      by simpa [hLoopScope] using hSource,
      Structured.EffectSemantics.For.Eval.false
        (fuel := 0) hTargetCond,
      hInvariant.restrict_source_live⟩

/--
A breaking body is the other regular loop base case.
-/
theorem RegularInvariantForward.body_brk
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceAfterBody :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetAfterBody :
      Structured.ObserverSemantics.State transcript}
    (hSourceCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          cond source =
        .ok (sourceAfterCond, true))
    (hTargetCond :
      Structured.ObserverSemantics.Code.runCondition condCode target =
        .ok (targetAfterCond, true))
    (hBody :
      BreakScopedBlockInvariantForward
        contract transcript lowerCtx lowerState localsCtx plan live
        frameBase mode sourceProgram bodyBase body sourceAfterCond
        targetProgram bodyBlock targetAfterCond
        sourceAfterBody targetAfterBody) :
    RegularInvariantForward
      contract transcript lowerCtx lowerState localsCtx plan live
      frameBase mode sourceProgram loopCtx cond postBase post bodyBase body
      targetProgram condCode postBlock bodyBlock source target
      sourceAfterBody targetAfterBody := by
  rcases hBody with
    ⟨sourceFuel, targetFuel,
      hSourceBody, hTargetBody, hFinalInvariant⟩
  have hSource :=
    Functions.Source.Effectful.Stmt.runForLoop_body_brk_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (loopCtx := loopCtx) (fuel := sourceFuel)
      (postBase := postBase) (post := post)
      hSourceCond hSourceBody
  have hTarget :
      Structured.ObserverSemantics.For.Eval
        targetProgram (targetFuel + 1) condCode postBlock bodyBlock
        target
        (Structured.EffectSemantics.Outcome.regular targetAfterBody) :=
    Structured.EffectSemantics.For.Eval.body_brk
      hTargetCond hTargetBody
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      hSource, hTarget, hFinalInvariant⟩

/--
A continuing body, regular post, and regular recursive result preserve the
regular loop relation.
-/
theorem RegularInvariantForward.cont_post_regular
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState bodyLowerState postLowerState :
      AllocationLowering.State}
    {localsCtx bodyLocals postLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceAfterBody sourceAfterPost sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetAfterBody targetAfterPost targetFinal :
      Structured.ObserverSemantics.State transcript}
    (hSourceCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          cond source =
        .ok (sourceAfterCond, true))
    (hTargetCond :
      Structured.ObserverSemantics.Code.runCondition condCode target =
        .ok (targetAfterCond, true))
    (hBody :
      ContinueScopedBlockInvariantForward
        contract transcript lowerCtx bodyLowerState bodyLocals plan live
        frameBase mode sourceProgram bodyBase body sourceAfterCond
        targetProgram bodyBlock targetAfterCond
        sourceAfterBody targetAfterBody)
    (hPost :
      Sequence.RegularScopedBlockInvariantForward
        contract transcript lowerCtx postLowerState postLocals plan live
        frameBase mode sourceProgram postBase post sourceAfterBody
        targetProgram postBlock targetAfterBody
        sourceAfterPost targetAfterPost)
    (hLoop :
      RegularInvariantForward
        contract transcript lowerCtx lowerState localsCtx plan live
        frameBase mode sourceProgram loopCtx cond postBase post
        bodyBase body targetProgram condCode postBlock bodyBlock
        sourceAfterPost targetAfterPost sourceFinal targetFinal) :
    RegularInvariantForward
      contract transcript lowerCtx lowerState localsCtx plan live
      frameBase mode sourceProgram loopCtx cond postBase post
      bodyBase body targetProgram condCode postBlock bodyBlock
      source target sourceFinal targetFinal := by
  rcases hBody with
    ⟨bodySourceFuel, bodyTargetFuel,
      hSourceBody, hTargetBody, _hBodyInvariant⟩
  rcases hPost with
    ⟨postSourceFuel, postTargetFuel,
      hSourcePost, hTargetPost, _hPostInvariant⟩
  rcases hLoop with
    ⟨loopSourceFuel, loopTargetFuel,
      hSourceLoop, hTargetLoop, hFinalInvariant⟩
  let sourceFuel :=
    Nat.max bodySourceFuel (Nat.max postSourceFuel loopSourceFuel)
  have hBodySourceLe : bodySourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hPostSourceLe : postSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hLoopSourceLe : loopSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hSourceBody' :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hBodySourceLe hSourceBody
  have hSourcePost' :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hPostSourceLe hSourcePost
  have hSourceLoop' :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hLoopSourceLe hSourceLoop
  have hSource :=
    Functions.Source.Effectful.Stmt.runForLoop_cont_post_regular_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (fuel := sourceFuel)
      hSourceCond hSourceBody' hSourcePost' hSourceLoop'
  let targetFuel :=
    Nat.max bodyTargetFuel (Nat.max postTargetFuel loopTargetFuel)
  have hBodyTargetLe : bodyTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hPostTargetLe : postTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hLoopTargetLe : loopTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetBody' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetBody hBodyTargetLe
  have hTargetPost' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetPost hPostTargetLe
  have hTargetLoop' :=
    Structured.EffectSemantics.For.Eval.mono
      hTargetLoop hLoopTargetLe
  have hTarget :
      Structured.ObserverSemantics.For.Eval
        targetProgram (targetFuel + 1) condCode postBlock bodyBlock target
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.For.Eval.cont_post_regular
      hTargetCond hTargetBody' hTargetPost' hTargetLoop'
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      hSource, hTarget, hFinalInvariant⟩

/--
One regular body/post iteration preserves a regular recursive loop result.
-/
theorem RegularInvariantForward.regular_post_regular
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState bodyLowerState postLowerState :
      AllocationLowering.State}
    {localsCtx bodyLocals postLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceAfterBody sourceAfterPost sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetAfterBody targetAfterPost targetFinal :
      Structured.ObserverSemantics.State transcript}
    (hSourceCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          cond source =
        .ok (sourceAfterCond, true))
    (hTargetCond :
      Structured.ObserverSemantics.Code.runCondition condCode target =
        .ok (targetAfterCond, true))
    (hBody :
      Sequence.RegularScopedBlockInvariantForward
          contract transcript lowerCtx bodyLowerState bodyLocals plan live
          frameBase mode sourceProgram bodyBase body sourceAfterCond
          targetProgram bodyBlock targetAfterCond
          sourceAfterBody targetAfterBody)
    (hPost :
      Sequence.RegularScopedBlockInvariantForward
          contract transcript lowerCtx postLowerState postLocals plan live
          frameBase mode sourceProgram postBase post sourceAfterBody
          targetProgram postBlock targetAfterBody
          sourceAfterPost targetAfterPost)
    (hLoop :
      RegularInvariantForward
        contract transcript lowerCtx lowerState localsCtx plan live
        frameBase mode sourceProgram loopCtx cond postBase post
        bodyBase body targetProgram condCode postBlock bodyBlock
        sourceAfterPost targetAfterPost sourceFinal targetFinal) :
    RegularInvariantForward
      contract transcript lowerCtx lowerState localsCtx plan live
      frameBase mode sourceProgram loopCtx cond postBase post
      bodyBase body targetProgram condCode postBlock bodyBlock
      source target sourceFinal targetFinal := by
  rcases hBody with
    ⟨bodySourceFuel, bodyTargetFuel,
      hSourceBody, hTargetBody, _hBodyInvariant⟩
  rcases hPost with
    ⟨postSourceFuel, postTargetFuel,
      hSourcePost, hTargetPost, _hPostInvariant⟩
  rcases hLoop with
    ⟨loopSourceFuel, loopTargetFuel,
      hSourceLoop, hTargetLoop, hFinalInvariant⟩
  let sourceFuel :=
    Nat.max bodySourceFuel (Nat.max postSourceFuel loopSourceFuel)
  have hBodySourceLe : bodySourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hPostSourceLe : postSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hLoopSourceLe : loopSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hSourceBody' :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hBodySourceLe hSourceBody
  have hSourcePost' :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hPostSourceLe hSourcePost
  have hSourceLoop' :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hLoopSourceLe hSourceLoop
  have hSource :=
    Functions.Source.Effectful.Stmt.runForLoop_regular_post_regular_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (fuel := sourceFuel)
      hSourceCond hSourceBody' hSourcePost' hSourceLoop'
  let targetFuel :=
    Nat.max bodyTargetFuel (Nat.max postTargetFuel loopTargetFuel)
  have hBodyTargetLe : bodyTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hPostTargetLe : postTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hLoopTargetLe : loopTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetBody' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetBody hBodyTargetLe
  have hTargetPost' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetPost hPostTargetLe
  have hTargetLoop' :=
    Structured.EffectSemantics.For.Eval.mono
      hTargetLoop hLoopTargetLe
  have hTarget :
      Structured.ObserverSemantics.For.Eval
        targetProgram (targetFuel + 1) condCode postBlock bodyBlock target
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.For.Eval.regular_post_regular
      hTargetCond hTargetBody' hTargetPost' hTargetLoop'
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      hSource, hTarget, hFinalInvariant⟩

/--
Canonical source-fuel induction for regular loop executions.

The recursive loop obligation is discharged internally from
`runForLoop_regular_cases`. Callers supply only source-facing condition safety
and adjacent preservation for one body or post block execution over the fixed
compiler artifacts.
-/
theorem RegularInvariantForward.of_source_run
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState bodyLowerState : AllocationLowering.State}
    {localsCtx bodyLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {loweredCond : Locals.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source final : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceFuel : Nat}
    (hLoopScope : loopCtx.scope = live)
    (hCondScoped : Functions.Scope.ExprScoped live cond)
    (hLowerCond :
      AllocationLowering.lowerExpr lowerCtx lowerState cond =
        some loweredCond)
    (hCompileCond :
      Locals.Expr.compileCode localsCtx 0 loweredCond = some condCode)
    (hCondSafe :
      ∀ {conditionSource conditionFinal :
            Functions.ObserverSemantics.State transcript}
        {conditionTrue : Bool},
        Functions.Source.Effectful.Expr.evalCondition
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            cond conditionSource =
          .ok (conditionFinal, conditionTrue) →
        ∃ value,
          AllocationObserverSafety.Expr.MemorySafeEval
              contract transcript cond conditionSource conditionFinal
              [value] ∧
            (value != EvmYul.UInt256.ofNat 0) = conditionTrue)
    (hBodyRegular :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx lowerState localsCtx plan live frameBase mode
            bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.regular bodyFinal) →
        ∃ bodyTargetFinal,
          Sequence.RegularScopedBlockInvariantForward
            contract transcript lowerCtx bodyLowerState bodyLocals plan live
            frameBase mode sourceProgram bodyBase body bodySource
            targetProgram bodyBlock bodyTarget bodyFinal bodyTargetFinal)
    (hBodyBreak :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx lowerState localsCtx plan live frameBase mode
            bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.brk bodyFinal) →
        ∃ bodyTargetFinal,
          BreakScopedBlockInvariantForward
            contract transcript lowerCtx lowerState localsCtx plan live
            frameBase mode sourceProgram bodyBase body bodySource
            targetProgram bodyBlock bodyTarget bodyFinal bodyTargetFinal)
    (hBodyContinue :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx lowerState localsCtx plan live frameBase mode
            bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.cont bodyFinal) →
        ∃ bodyTargetFinal,
          ContinueScopedBlockInvariantForward
            contract transcript lowerCtx bodyLowerState bodyLocals plan live
            frameBase mode sourceProgram bodyBase body bodySource
            targetProgram bodyBlock bodyTarget bodyFinal bodyTargetFinal)
    (hPostRegular :
      ∀ {postFuel : Nat}
        {postSource postFinal :
          Functions.ObserverSemantics.State transcript}
        {postTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx bodyLowerState bodyLocals plan live
            frameBase mode postSource postTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram postBase post postFuel postSource =
          .ok (Functions.Source.Effectful.Outcome.regular postFinal) →
        ∃ postTargetFinal,
          Sequence.RegularScopedBlockInvariantForward
            contract transcript lowerCtx lowerState localsCtx plan live
            frameBase mode sourceProgram postBase post postSource
            targetProgram postBlock postTarget postFinal postTargetFinal)
    (hSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram loopCtx cond postBase post bodyBase body
          sourceFuel source =
        .ok (Functions.Source.Effectful.Outcome.regular final))
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source target) :
    ∃ targetFinal,
      RegularInvariantForward
        contract transcript lowerCtx lowerState localsCtx plan live
        frameBase mode sourceProgram loopCtx cond postBase post bodyBase body
        targetProgram condCode postBlock bodyBlock source target
        final targetFinal := by
  induction sourceFuel using Nat.strong_induction_on generalizing
      source target final with
  | h sourceFuel ih =>
      obtain ⟨stepFuel, rfl, hCases⟩ :=
        Functions.Source.Effectful.Stmt.runForLoop_regular_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram hSource
      rcases hCases with
        hFalse | hBreak | hRegular | hContinue
      · obtain ⟨sourceAfterCond, hSourceCond, rfl⟩ := hFalse
        obtain ⟨value, hSafe, hValue⟩ := hCondSafe hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant⟩ :=
          AllocationObserverExpression.Expr.condition_forward
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hInvariant hSafe hCondScoped hLowerCond hCompileCond
        refine
          ⟨targetAfterCond, ?_⟩
        simpa [hLoopScope] using
          (RegularInvariantForward.false
            hLoopScope hSourceCond
            (by simpa [hValue] using hTargetCond)
            hCondInvariant)
      · obtain
            ⟨sourceAfterCond, sourceAfterBody,
              hSourceCond, hSourceBody, rfl⟩ :=
          hBreak
        obtain ⟨value, hSafe, hValue⟩ := hCondSafe hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant⟩ :=
          AllocationObserverExpression.Expr.condition_forward
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hInvariant hSafe hCondScoped hLowerCond hCompileCond
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyBreak hCondInvariant hSourceBody
        refine
          ⟨targetAfterBody,
            RegularInvariantForward.body_brk hSourceCond ?_
              hBodyForward⟩
        simpa [hValue] using hTargetCond
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hRegular
        obtain ⟨value, hSafe, hValue⟩ := hCondSafe hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant⟩ :=
          AllocationObserverExpression.Expr.condition_forward
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hInvariant hSafe hCondScoped hLowerCond hCompileCond
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyRegular hCondInvariant hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hBodyInvariant⟩
        obtain ⟨targetAfterPost, hPostForward⟩ :=
          hPostRegular hBodyInvariant hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hPostInvariant⟩
        have hRecursive :=
          ih stepFuel (Nat.lt_succ_self stepFuel)
            (source := sourceAfterPost)
            (target := targetAfterPost)
            (final := final)
            hSourceLoop
        obtain ⟨targetFinal, hLoopForward⟩ :=
          hRecursive hPostInvariant
        refine
          ⟨targetFinal,
            RegularInvariantForward.regular_post_regular
              hSourceCond ?_
              ⟨bodySourceFuel, bodyTargetFuel,
                hSourceBody', hTargetBody, hBodyInvariant⟩
              ⟨postSourceFuel, postTargetFuel,
                hSourcePost', hTargetPost, hPostInvariant⟩
              hLoopForward⟩
        simpa [hValue] using hTargetCond
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hContinue
        obtain ⟨value, hSafe, hValue⟩ := hCondSafe hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant⟩ :=
          AllocationObserverExpression.Expr.condition_forward
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hInvariant hSafe hCondScoped hLowerCond hCompileCond
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyContinue hCondInvariant hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hBodyInvariant⟩
        obtain ⟨targetAfterPost, hPostForward⟩ :=
          hPostRegular hBodyInvariant hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hPostInvariant⟩
        have hRecursive :=
          ih stepFuel (Nat.lt_succ_self stepFuel)
            (source := sourceAfterPost)
            (target := targetAfterPost)
            (final := final)
            hSourceLoop
        obtain ⟨targetFinal, hLoopForward⟩ :=
          hRecursive hPostInvariant
        refine
          ⟨targetFinal,
            RegularInvariantForward.cont_post_regular
              hSourceCond ?_
              ⟨bodySourceFuel, bodyTargetFuel,
                hSourceBody', hTargetBody, hBodyInvariant⟩
              ⟨postSourceFuel, postTargetFuel,
                hSourcePost', hTargetPost, hPostInvariant⟩
              hLoopForward⟩
        simpa [hValue] using hTargetCond

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
Forward preservation for a `for` from a regular initializer and a checked
regular loop execution over the actual condition/post/body compiler artifacts.
-/
private theorem for_regular_of_components
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
    {source sourceAfterInit sourceLoopFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hInitScoped : Functions.Scope.Block.Scoped outerLive init)
    (hSourceScope : sourceCtx.scope = outerLive)
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
    (hLoop :
      ∀ {loopState afterPost afterBody : AllocationLowering.State}
        {loweredCond : Locals.Expr 1}
        {loweredPost loweredBody : Locals.Block}
        {initLocals postLocals bodyLocals : Locals.Ctx}
        {condCode : Structured.Code}
        {postCode bodyCode : List Expressions.Stmt}
        {compiledPost compiledBody : Expressions.Block}
        {targetAfterInit :
          Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerExpr lowerCtx loopState cond =
          some loweredCond →
        AllocationLowering.lowerBlockScoped
            lowerCtx returns loopState post =
          some (loweredPost, afterPost) →
        AllocationLowering.lowerBlockScoped
            lowerCtx returns afterPost body =
          some (loweredBody, afterBody) →
        Locals.Expr.compileCode initLocals 0 loweredCond =
          some condCode →
        Locals.Block.compileOpen initLocals.withoutLoopControl
            loweredPost =
          some (postCode, postLocals) →
        Locals.finishScoped initLocals.withoutLoopControl
            postLocals postCode =
          some compiledPost →
        Locals.Block.compileOpen
            (initLocals.withLoopControl initLocals.layout.length)
            loweredBody =
          some (bodyCode, bodyLocals) →
        Locals.finishScoped
            (initLocals.withLoopControl initLocals.layout.length)
            bodyLocals bodyCode =
          some compiledBody →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx loopState initLocals loopPlan loopLive
            frameBase loopMode sourceAfterInit targetAfterInit →
        ∃ targetLoopFinal,
          ForLoop.RegularInvariantForward
            contract transcript lowerCtx loopState initLocals loopPlan
            loopLive frameBase loopMode sourceProgram loopSourceCtx
            cond loopSourceCtx.withoutLoopControl post
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body targetProgram condCode compiledPost.toStructured
            compiledBody.toStructured sourceAfterInit targetAfterInit
            sourceLoopFinal targetLoopFinal)
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
          outerLive sourceLoopFinal)
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
        hCompileInit, hCompileCond, hCompilePost, hFinishPost,
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
  obtain ⟨targetLoopFinal, hLoopForward⟩ :=
    hLoop hLowerCond hLowerPost hLowerBody hCompileCond
      hCompilePost hFinishPost hCompileBody hFinishBody hInitInvariant
  rcases hLoopForward with
    ⟨loopSourceFuel, loopTargetFuel,
      hSourceLoop, hTargetLoop, hLoopFinalInvariant⟩
  obtain
      ⟨targetFinal, hCleanupRun, hFinalBaseInvariant⟩ :=
    ForLoop.finish_regular_outer
      hInvariant hLoopFinalInvariant hInitMode hInitScoped hSubset
      hLowerInit hCleanup
  have hFinalInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerFinal localsFinal outerPlan outerLive
        frameBase outerMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceLoopFinal)
        targetFinal := by
    rw [hLowerFinal, hLocalsFinal]
    exact hFinalBaseInvariant.transport_state rfl rfl
  let sourceFuel := Nat.max initSourceFuel loopSourceFuel
  have hInitSourceLe : initSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hLoopSourceLe : loopSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hSourceInit' :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hInitSourceLe hSourceInit
  have hSourceLoop' :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hLoopSourceLe hSourceLoop
  have hSource :=
    Functions.Source.Effectful.Stmt.run_for_regular_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := sourceFuel)
      hSourceInit' hSourceLoop'
  let targetLoopFuel := Nat.max initTargetFuel loopTargetFuel
  have hInitTargetLe : initTargetFuel ≤ targetLoopFuel := by
    simp [targetLoopFuel]
  have hLoopTargetLe : loopTargetFuel ≤ targetLoopFuel := by
    simp [targetLoopFuel]
  have hTargetInit' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetInit hInitTargetLe
  have hTargetLoop' :=
    Structured.EffectSemantics.For.Eval.mono
      hTargetLoop hLoopTargetLe
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (targetLoopFuel + 1)
        (.for_
          { stmts := Expressions.StmtList.toStructured initCode }
          condCode compiledPost.toStructured compiledBody.toStructured)
        target
        (Structured.EffectSemantics.Outcome.regular targetLoopFinal) :=
    Structured.EffectSemantics.Stmt.Eval.for_init_regular
      hTargetInit' hTargetLoop'
  have hTargetForBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetLoopFuel + 2)
        { stmts :=
            [(.for_
              { stmts := Expressions.StmtList.toStructured initCode }
              condCode compiledPost.toStructured
              compiledBody.toStructured)] }
        target
        (Structured.EffectSemantics.Outcome.regular targetLoopFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCleanupBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := [Structured.Stmt.code cleanup] }
        targetLoopFinal
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hCleanupRun)
      Structured.EffectSemantics.Block.Eval.nil
  obtain ⟨targetFuel, hTarget⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hTargetForBlock hCleanupBlock
  refine
    ⟨targetFinal, sourceFuel + 1, targetFuel, ?_, ?_,
      hFinalInvariant, SameFrame.refl outerMode⟩
  · simpa [hSourceScope] using hSource
  · have hInitCompile :
        Expressions.Block.toStructured { stmts := initCode } =
          { stmts := Expressions.StmtList.toStructured initCode } := by
      rfl
    have hCondCompile :
        Expressions.Expr.compile
            (Expressions.Expr.code (results := 1) condCode) =
          condCode := by
      rfl
    rw [hCompiledShape, Expressions.StmtList.toStructured_append]
    simp only [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured]
    rw [hInitCompile, hCondCompile]
    simpa [Locals.codeStmt, Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget

/--
Forward preservation for a regular `for` from its canonical source loop run.

Unlike `for_regular_of_components`, this interface does not accept a complete
loop proof. It derives that proof by source-fuel induction and asks recursive
statement preservation only for one body or post execution at a time.
-/
theorem for_regular_of_source_run
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
    {source sourceAfterInit sourceLoopFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {loopSourceFuel : Nat}
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
    (hCondSafe :
      ∀ {conditionSource conditionFinal :
            Functions.ObserverSemantics.State transcript}
        {conditionTrue : Bool},
        Functions.Source.Effectful.Expr.evalCondition
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            cond conditionSource =
          .ok (conditionFinal, conditionTrue) →
        ∃ value,
          AllocationObserverSafety.Expr.MemorySafeEval
              contract transcript cond conditionSource conditionFinal
              [value] ∧
            (value != EvmYul.UInt256.ofNat 0) = conditionTrue)
    (hBodyRegular :
      ∀ {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
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
            contract lowerCtx loopState initLocals loopPlan loopLive
            frameBase loopMode bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.regular bodyFinal) →
        ∃ bodyTargetFinal,
          RegularScopedBlockInvariantForward
            contract transcript lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodySource targetProgram compiledBody.toStructured
            bodyTarget bodyFinal bodyTargetFinal)
    (hBodyBreak :
      ∀ {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
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
            contract lowerCtx loopState initLocals loopPlan loopLive
            frameBase loopMode bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.brk bodyFinal) →
        ∃ bodyTargetFinal,
          ForLoop.BreakScopedBlockInvariantForward
            contract transcript lowerCtx loopState initLocals loopPlan
            loopLive frameBase loopMode sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodySource targetProgram compiledBody.toStructured
            bodyTarget bodyFinal bodyTargetFinal)
    (hBodyContinue :
      ∀ {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
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
            contract lowerCtx loopState initLocals loopPlan loopLive
            frameBase loopMode bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.cont bodyFinal) →
        ∃ bodyTargetFinal,
          ForLoop.ContinueScopedBlockInvariantForward
            contract transcript lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodySource targetProgram compiledBody.toStructured
            bodyTarget bodyFinal bodyTargetFinal)
    (hPostRegular :
      ∀ {loopState afterPost : AllocationLowering.State}
        {loweredPost : Locals.Block}
        {initLocals postLocals : Locals.Ctx}
        {postCode : List Expressions.Stmt}
        {compiledPost : Expressions.Block}
        {postFuel : Nat}
        {postSource postFinal :
          Functions.ObserverSemantics.State transcript}
        {postTarget : Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerBlockScoped
            lowerCtx returns loopState post =
          some (loweredPost, afterPost) →
        Locals.Block.compileOpen initLocals.withoutLoopControl
            loweredPost =
          some (postCode, postLocals) →
        Locals.finishScoped initLocals.withoutLoopControl
            postLocals postCode =
          some compiledPost →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode postSource postTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram loopSourceCtx.withoutLoopControl post
            postFuel postSource =
          .ok (Functions.Source.Effectful.Outcome.regular postFinal) →
        ∃ postTargetFinal,
          RegularScopedBlockInvariantForward
            contract transcript lowerCtx loopState initLocals loopPlan
            loopLive frameBase loopMode sourceProgram
            loopSourceCtx.withoutLoopControl post postSource
            targetProgram compiledPost.toStructured postTarget
            postFinal postTargetFinal)
    (hSourceLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram loopSourceCtx cond
          loopSourceCtx.withoutLoopControl post
          (loopSourceCtx.withLoopControl
            loopSourceCtx.scope loopSourceCtx.scope)
          body loopSourceFuel sourceAfterInit =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceLoopFinal))
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
          outerLive sourceLoopFinal)
        targetFinal sourceCtx := by
  apply
    for_regular_of_components
      hInitScoped hSourceScope hSubset hInvariant hInit
  · intro loopState afterPost afterBody loweredCond loweredPost
      loweredBody initLocals postLocals bodyLocals condCode postCode
      bodyCode compiledPost compiledBody targetAfterInit
      hLowerCond hLowerPost hLowerBody hCompileCond hCompilePost
      hFinishPost hCompileBody hFinishBody hLoopInvariant
    exact
      ForLoop.RegularInvariantForward.of_source_run
        hLoopSourceScope hCondScoped hLowerCond hCompileCond hCondSafe
        (fun hInvariant hRun =>
          hBodyRegular hLowerPost hLowerBody hCompileBody hFinishBody
            hInvariant hRun)
        (fun hInvariant hRun =>
          hBodyBreak hLowerPost hLowerBody hCompileBody hFinishBody
            hInvariant hRun)
        (fun hInvariant hRun =>
          hBodyContinue hLowerPost hLowerBody hCompileBody hFinishBody
            hInvariant hRun)
        (fun hInvariant hRun =>
          hPostRegular hLowerPost hCompilePost hFinishPost hInvariant hRun)
        hSourceLoop hLoopInvariant
  · exact hLower
  · exact hCompile

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
