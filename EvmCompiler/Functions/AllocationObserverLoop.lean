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
      ⟨targetFinal, hCleanupRun, hFinalLoopRel, hFinalLength,
        _hFinalMachine⟩ :=
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
Restore the outer activation after a regular loop result while retaining the
global recursive-frame allocator.
-/
theorem finish_regular_outer_runtime
    {contract : MemoryContract.Contract}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        outerPlan outerLive frameBase outerMode source target)
    (hLoop :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx loopState initLocals
        loopPlan loopLive frameBase loopMode sourceLoop targetLoop)
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
        AllocationObserverContext.ActivationRuntimeInvariant
          contract config allocatorDepth lowerCtx lowerState localsCtx
          outerPlan outerLive frameBase outerMode
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            outerLive sourceLoop)
          targetFinal ∧
        AllocationObserverRelation.Frame.ActivationEffect
          config allocatorDepth outerMode targetLoop targetFinal := by
  have hExtends :=
    AllocationLowering.lowerBlockOpen_stateExtends
      hInitScoped hLowerInit
  obtain ⟨hTransition, hLayout, hSlots⟩ :=
    AllocationObserverCleanup.Plain.transition_of_stateExtends
      hLoop.activation.compiler hOuter.activation.compiler hSubset
      hSameFrame.symm rfl hExtends
  obtain ⟨_hRestoredCompiler, hPlanAgree⟩ :=
    AllocationObserverCleanup.Plain.restore_context
      hLoop.activation.compiler hOuter.activation.compiler
      hTransition hLayout hSlots
  obtain
      ⟨targetFinal, hCleanupRun, hFinalLoopRel, hFinalLength,
        hFinalMachine⟩ :=
    AllocationObserverCleanup.Plain.forward_exact
      hLoop.activation.compiler hTransition hLoop.activation.planWF
      hLoop.activation.defined hLoop.activation.state
      hLoop.activation.stackLength hCleanup
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
      hLoop.activation.defined.restrictTo hTransition.subset
  exact
    ⟨targetFinal, hCleanupRun,
      { activation :=
          { compiler := hOuter.activation.compiler
            planWF := hOuter.activation.planWF
            defined := hFinalDefined
            state := hFinalRel
            stackLength := hFinalLength }
        allocator := hLoop.allocator.of_machine_eq hFinalMachine
        frame := hLoop.frame.sameFrame hSameFrame.symm },
      AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
        (AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
          hLoop.allocator hFinalMachine)⟩

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
Regular loop execution retaining the recursive scratch allocator and the
mode-indexed effect of the complete iteration sequence.
-/
def RegularRuntimeInvariantForward
    (contract : MemoryContract.Contract)
    (config : AllocationObserverRelation.Frame.Config)
    (allocatorDepth : Nat)
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode sourceFinal targetFinal ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode target targetFinal

/--
A scoped loop body ending in `break`, with allocator readiness and suspended
frame protection preserved for the next loop boundary.
-/
def BreakScopedBlockRuntimeInvariantForward
    (contract : MemoryContract.Contract)
    (config : AllocationObserverRelation.Frame.Config)
    (allocatorDepth : Nat)
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode sourceFinal targetFinal ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode target targetFinal

/--
A scoped loop body ending in `continue`, with allocator readiness and
suspended frame protection preserved for the post block.
-/
def ContinueScopedBlockRuntimeInvariantForward
    (contract : MemoryContract.Contract)
    (config : AllocationObserverRelation.Frame.Config)
    (allocatorDepth : Nat)
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode sourceFinal targetFinal ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode target targetFinal

/--
Abrupt loop execution at the adjacent Functions/Structured boundary.

The result live set is interpreted by `ActivationOutcomeRel`: ordered return
names for `leave`, and otherwise irrelevant local realization for terminal
halts.
-/
def NonregularForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (resultLive : List Locals.Name)
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
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram loopCtx cond postBase post bodyBase body
          sourceFuel source =
        .ok sourceOutcome ∧
      Structured.ObserverSemantics.For.Eval
        targetProgram targetFuel condCode postBlock bodyBlock target
          targetOutcome ∧
      ActivationOutcomeRel contract plan resultLive 0 frameBase mode
        sourceOutcome targetOutcome

/--
Abrupt loop execution retaining the recursive allocator effect.

Activation exits erase local representation, so the outcome relation is
indexed by the loop-entry mode while the effect records the complete target
execution from that same mode.
-/
def NonregularRuntimeForward
    (contract : MemoryContract.Contract)
    (config : AllocationObserverRelation.Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (resultLive : List Locals.Name)
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
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)) : Prop :=
  NonregularForward contract transcript plan resultLive frameBase mode
      sourceProgram loopCtx cond postBase post bodyBase body targetProgram
      condCode postBlock bodyBlock source target sourceOutcome
      targetOutcome ∧
    AllocationObserverRelation.Frame.ActivationEffect
      config allocatorDepth mode target targetOutcome.state

/--
A leaving loop body propagates the activation-exit outcome directly.
-/
theorem NonregularForward.body_leave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {resultLive : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetFinal :
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
      Sequence.ScopedBlockForward
        contract transcript plan resultLive frameBase mode sourceProgram
        bodyBase body sourceAfterCond targetProgram bodyBlock targetAfterCond
        (Functions.Source.Effectful.Outcome.leave sourceFinal)
        (Structured.EffectSemantics.Outcome.leave targetFinal)) :
    NonregularForward
      contract transcript plan resultLive frameBase mode sourceProgram
      loopCtx cond postBase post bodyBase body targetProgram condCode
      postBlock bodyBlock source target
      (Functions.Source.Effectful.Outcome.leave sourceFinal)
      (Structured.EffectSemantics.Outcome.leave targetFinal) := by
  rcases hBody with
    ⟨sourceFuel, targetFuel, hSourceBody, hTargetBody, hRel⟩
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      Functions.Source.Effectful.Stmt.runForLoop_body_leave_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSourceCond hSourceBody,
      Structured.EffectSemantics.For.Eval.body_leave
        hTargetCond hTargetBody,
      hRel⟩

/--
A halting loop body propagates the terminal outcome directly.
-/
theorem NonregularForward.body_halt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {resultLive : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetFinal :
      Structured.ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
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
      Sequence.ScopedBlockForward
        contract transcript plan resultLive frameBase mode sourceProgram
        bodyBase body sourceAfterCond targetProgram bodyBlock targetAfterCond
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)) :
    NonregularForward
      contract transcript plan resultLive frameBase mode sourceProgram
      loopCtx cond postBase post bodyBase body targetProgram condCode
      postBlock bodyBlock source target
      (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
      (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
  rcases hBody with
    ⟨sourceFuel, targetFuel, hSourceBody, hTargetBody, hRel⟩
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      Functions.Source.Effectful.Stmt.runForLoop_body_halt_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSourceCond hSourceBody,
      Structured.EffectSemantics.For.Eval.body_halt
        hTargetCond hTargetBody,
      hRel⟩

/--
A regular body followed by a leaving post propagates the activation exit.
-/
theorem NonregularForward.regular_post_leave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {bodyLowerState : AllocationLowering.State}
    {bodyLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {loopLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceAfterBody sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetAfterBody targetFinal :
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
        contract transcript lowerCtx bodyLowerState bodyLocals plan
        loopLive frameBase mode sourceProgram bodyBase body
        sourceAfterCond targetProgram bodyBlock targetAfterCond
        sourceAfterBody targetAfterBody)
    (hPost :
      Sequence.ScopedBlockForward
        contract transcript plan resultLive frameBase mode sourceProgram
        postBase post sourceAfterBody targetProgram postBlock
        targetAfterBody
        (Functions.Source.Effectful.Outcome.leave sourceFinal)
        (Structured.EffectSemantics.Outcome.leave targetFinal)) :
    NonregularForward
      contract transcript plan resultLive frameBase mode sourceProgram
      loopCtx cond postBase post bodyBase body targetProgram condCode
      postBlock bodyBlock source target
      (Functions.Source.Effectful.Outcome.leave sourceFinal)
      (Structured.EffectSemantics.Outcome.leave targetFinal) := by
  rcases hBody with
    ⟨bodySourceFuel, bodyTargetFuel,
      hSourceBody, hTargetBody, _hBodyInvariant⟩
  rcases hPost with
    ⟨postSourceFuel, postTargetFuel,
      hSourcePost, hTargetPost, hRel⟩
  let sourceFuel := Nat.max bodySourceFuel postSourceFuel
  have hBodySourceLe : bodySourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hPostSourceLe : postSourceFuel ≤ sourceFuel := by
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
  let targetFuel := Nat.max bodyTargetFuel postTargetFuel
  have hBodyTargetLe : bodyTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hPostTargetLe : postTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetBody' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetBody hBodyTargetLe
  have hTargetPost' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetPost hPostTargetLe
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      Functions.Source.Effectful.Stmt.runForLoop_regular_post_leave_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSourceCond hSourceBody' hSourcePost',
      Structured.EffectSemantics.For.Eval.regular_post_leave
        hTargetCond hTargetBody' hTargetPost',
      hRel⟩

/--
A continuing body followed by a leaving post propagates the activation exit.
-/
theorem NonregularForward.cont_post_leave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {bodyLowerState : AllocationLowering.State}
    {bodyLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {loopLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceAfterBody sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetAfterBody targetFinal :
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
        contract transcript lowerCtx bodyLowerState bodyLocals plan
        loopLive frameBase mode sourceProgram bodyBase body
        sourceAfterCond targetProgram bodyBlock targetAfterCond
        sourceAfterBody targetAfterBody)
    (hPost :
      Sequence.ScopedBlockForward
        contract transcript plan resultLive frameBase mode sourceProgram
        postBase post sourceAfterBody targetProgram postBlock
        targetAfterBody
        (Functions.Source.Effectful.Outcome.leave sourceFinal)
        (Structured.EffectSemantics.Outcome.leave targetFinal)) :
    NonregularForward
      contract transcript plan resultLive frameBase mode sourceProgram
      loopCtx cond postBase post bodyBase body targetProgram condCode
      postBlock bodyBlock source target
      (Functions.Source.Effectful.Outcome.leave sourceFinal)
      (Structured.EffectSemantics.Outcome.leave targetFinal) := by
  rcases hBody with
    ⟨bodySourceFuel, bodyTargetFuel,
      hSourceBody, hTargetBody, _hBodyInvariant⟩
  rcases hPost with
    ⟨postSourceFuel, postTargetFuel,
      hSourcePost, hTargetPost, hRel⟩
  let sourceFuel := Nat.max bodySourceFuel postSourceFuel
  have hBodySourceLe : bodySourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hPostSourceLe : postSourceFuel ≤ sourceFuel := by
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
  let targetFuel := Nat.max bodyTargetFuel postTargetFuel
  have hBodyTargetLe : bodyTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hPostTargetLe : postTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetBody' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetBody hBodyTargetLe
  have hTargetPost' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetPost hPostTargetLe
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      Functions.Source.Effectful.Stmt.runForLoop_cont_post_leave_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSourceCond hSourceBody' hSourcePost',
      Structured.EffectSemantics.For.Eval.cont_post_leave
        hTargetCond hTargetBody' hTargetPost',
      hRel⟩

/--
A regular body followed by a halting post propagates the terminal outcome.
-/
theorem NonregularForward.regular_post_halt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {bodyLowerState : AllocationLowering.State}
    {bodyLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {loopLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceAfterBody sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetAfterBody targetFinal :
      Structured.ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
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
        contract transcript lowerCtx bodyLowerState bodyLocals plan
        loopLive frameBase mode sourceProgram bodyBase body
        sourceAfterCond targetProgram bodyBlock targetAfterCond
        sourceAfterBody targetAfterBody)
    (hPost :
      Sequence.ScopedBlockForward
        contract transcript plan resultLive frameBase mode sourceProgram
        postBase post sourceAfterBody targetProgram postBlock
        targetAfterBody
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)) :
    NonregularForward
      contract transcript plan resultLive frameBase mode sourceProgram
      loopCtx cond postBase post bodyBase body targetProgram condCode
      postBlock bodyBlock source target
      (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
      (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
  rcases hBody with
    ⟨bodySourceFuel, bodyTargetFuel,
      hSourceBody, hTargetBody, _hBodyInvariant⟩
  rcases hPost with
    ⟨postSourceFuel, postTargetFuel,
      hSourcePost, hTargetPost, hRel⟩
  let sourceFuel := Nat.max bodySourceFuel postSourceFuel
  have hBodySourceLe : bodySourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hPostSourceLe : postSourceFuel ≤ sourceFuel := by
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
  let targetFuel := Nat.max bodyTargetFuel postTargetFuel
  have hBodyTargetLe : bodyTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hPostTargetLe : postTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetBody' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetBody hBodyTargetLe
  have hTargetPost' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetPost hPostTargetLe
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      Functions.Source.Effectful.Stmt.runForLoop_regular_post_halt_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSourceCond hSourceBody' hSourcePost',
      Structured.EffectSemantics.For.Eval.regular_post_halt
        hTargetCond hTargetBody' hTargetPost',
      hRel⟩

/--
A continuing body followed by a halting post propagates the terminal outcome.
-/
theorem NonregularForward.cont_post_halt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {bodyLowerState : AllocationLowering.State}
    {bodyLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {loopLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetProgram : Structured.Program}
    {condCode : Structured.Code}
    {postBlock bodyBlock : Structured.Block}
    {source sourceAfterCond sourceAfterBody sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetAfterCond targetAfterBody targetFinal :
      Structured.ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
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
        contract transcript lowerCtx bodyLowerState bodyLocals plan
        loopLive frameBase mode sourceProgram bodyBase body
        sourceAfterCond targetProgram bodyBlock targetAfterCond
        sourceAfterBody targetAfterBody)
    (hPost :
      Sequence.ScopedBlockForward
        contract transcript plan resultLive frameBase mode sourceProgram
        postBase post sourceAfterBody targetProgram postBlock
        targetAfterBody
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)) :
    NonregularForward
      contract transcript plan resultLive frameBase mode sourceProgram
      loopCtx cond postBase post bodyBase body targetProgram condCode
      postBlock bodyBlock source target
      (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
      (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
  rcases hBody with
    ⟨bodySourceFuel, bodyTargetFuel,
      hSourceBody, hTargetBody, _hBodyInvariant⟩
  rcases hPost with
    ⟨postSourceFuel, postTargetFuel,
      hSourcePost, hTargetPost, hRel⟩
  let sourceFuel := Nat.max bodySourceFuel postSourceFuel
  have hBodySourceLe : bodySourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hPostSourceLe : postSourceFuel ≤ sourceFuel := by
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
  let targetFuel := Nat.max bodyTargetFuel postTargetFuel
  have hBodyTargetLe : bodyTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hPostTargetLe : postTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetBody' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetBody hBodyTargetLe
  have hTargetPost' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetPost hPostTargetLe
  exact
    ⟨sourceFuel + 1, targetFuel + 1,
      Functions.Source.Effectful.Stmt.runForLoop_cont_post_halt_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSourceCond hSourceBody' hSourcePost',
      Structured.EffectSemantics.For.Eval.cont_post_halt
        hTargetCond hTargetBody' hTargetPost',
      hRel⟩

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

/--
Canonical source-fuel induction for regular loop executions under the guarded
no-external-effects semantics.

The theorem reconstructs the ordinary Functions execution while retaining the
global allocator invariant and composing the exact mode-indexed effect across
conditions, body/post blocks, and recursive iterations.
-/
theorem RegularRuntimeInvariantForward.of_safe_source_run
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
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
    (hLoopScope :
      ∀ name, name ∈ loopCtx.scope ↔ name ∈ live)
    (hCondScoped : Functions.Scope.ExprScoped live cond)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hLowerCond :
      AllocationLowering.lowerExpr lowerCtx lowerState cond =
        some loweredCond)
    (hCompileCond :
      Locals.Expr.compileCode localsCtx 0 loweredCond = some condCode)
    (hLoopReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable loopCtx target)
    (hPostReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable postBase target)
    (hBodyReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable bodyBase target)
    (hBodyRegular :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState localsCtx
            plan live frameBase mode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            bodyBase bodyTarget →
        bodyFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.regular bodyFinal) →
        ∃ bodyTargetFinal,
          Sequence.RegularScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx
            bodyLowerState bodyLocals plan live frameBase mode
            sourceProgram bodyBase body bodySource targetProgram bodyBlock
            bodyTarget bodyFinal bodyTargetFinal)
    (hBodyBreak :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState localsCtx
            plan live frameBase mode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            bodyBase bodyTarget →
        bodyFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.brk bodyFinal) →
        ∃ bodyTargetFinal,
          BreakScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx lowerState
            localsCtx plan live frameBase mode sourceProgram bodyBase body
            bodySource targetProgram bodyBlock bodyTarget bodyFinal
            bodyTargetFinal)
    (hBodyContinue :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState localsCtx
            plan live frameBase mode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            bodyBase bodyTarget →
        bodyFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.cont bodyFinal) →
        ∃ bodyTargetFinal,
          ContinueScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx
            bodyLowerState bodyLocals plan live frameBase mode
            sourceProgram bodyBase body bodySource targetProgram bodyBlock
            bodyTarget bodyFinal bodyTargetFinal)
    (hPostRegular :
      ∀ {postFuel : Nat}
        {postSource postFinal :
          Functions.ObserverSemantics.State transcript}
        {postTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx bodyLowerState
            bodyLocals plan live frameBase mode postSource postTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            postBase postTarget →
        postFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram postBase post postFuel postSource =
          .ok (Functions.Source.Effectful.Outcome.regular postFinal) →
        ∃ postTargetFinal,
          Sequence.RegularScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx lowerState
            localsCtx plan live frameBase mode sourceProgram postBase post
            postSource targetProgram postBlock postTarget postFinal
            postTargetFinal)
    (hSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceProgram loopCtx cond postBase post bodyBase body
          sourceFuel source =
        .ok (Functions.Source.Effectful.Outcome.regular final))
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target) :
    ∃ targetFinal,
      RegularRuntimeInvariantForward
        contract config allocatorDepth transcript lowerCtx lowerState
        localsCtx plan live frameBase mode sourceProgram loopCtx cond
        postBase post bodyBase body targetProgram condCode postBlock
        bodyBlock source target final targetFinal := by
  induction sourceFuel using Nat.strong_induction_on generalizing
      source target final with
  | h sourceFuel ih =>
      obtain ⟨stepFuel, rfl, hCases⟩ :=
        Functions.Source.Effectful.Stmt.runForLoop_regular_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceProgram hSource
      rcases hCases with
        hFalse | hBreak | hRegular | hContinue
      · obtain ⟨sourceAfterCond, hSourceCond, rfl⟩ := hFalse
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hSourceOrdinary :=
          Functions.Source.Effectful.Stmt.runForLoop_false_of_eval
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram (loopCtx := loopCtx) (fuel := 0)
            (postBase := postBase) (post := post)
            (bodyBase := bodyBase) (body := body)
            (by simpa [hValue] using hSafe.evalCondition_eq)
        have hRestrict :
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
                loopCtx.scope sourceAfterCond =
              (Functions.ObserverSemantics.stateModel transcript).restrictTo
                live sourceAfterCond :=
          Locals.Source.Effectful.StateModel.restrictTo_congr
            (Functions.ObserverSemantics.stateModel transcript)
            hLoopScope
        rw [hRestrict] at hSourceOrdinary
        rw [hRestrict]
        exact
          ⟨targetAfterCond, 1, 1,
            hSourceOrdinary,
            Structured.EffectSemantics.For.Eval.false
              (fuel := 0) (by simpa [hValue] using hTargetCond),
            hCondInvariant.restrict_source_live,
            AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
              hCondEffect⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody,
              hSourceCond, hSourceBody, rfl⟩ :=
          hBreak
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyBreak hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel) hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBodyOrdinary, hTargetBody, hBodyInvariant,
            hBodyEffect⟩
        exact
          ⟨targetAfterBody, bodySourceFuel + 1, bodyTargetFuel + 1,
            Functions.Source.Effectful.Stmt.runForLoop_body_brk_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSemantics.primitiveSemantics transcript)
              sourceProgram
              (by simpa [hValue] using hSafe.evalCondition_eq)
              hSourceBodyOrdinary,
            Structured.EffectSemantics.For.Eval.body_brk
              (by simpa [hValue] using hTargetCond) hTargetBody,
            hBodyInvariant,
            (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
              hCondEffect).trans hBodyEffect⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hRegular
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyRegular hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel) hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBodyOrdinary, hTargetBody, hBodyInvariant,
            hBodyEffect⟩
        have hPostFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterBody :=
          hPostReturnFrame.transport_target
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        obtain ⟨targetAfterPost, hPostForward⟩ :=
          hPostRegular hBodyInvariant hPostFrame
            (Nat.lt_succ_self stepFuel) hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePostOrdinary, hTargetPost, hPostInvariant,
            hPostEffect⟩
        have hReturnsAfterPost :
            targetAfterPost.source.returns = target.source.returns :=
          (Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hTargetPost
            (by
              simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        have hLoopFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              loopCtx targetAfterPost :=
          hLoopReturnFrame.transport_target hReturnsAfterPost
        have hPostRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterPost :=
          hPostReturnFrame.transport_target hReturnsAfterPost
        have hBodyRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterPost :=
          hBodyReturnFrame.transport_target hReturnsAfterPost
        obtain ⟨targetFinal, hLoopForward⟩ :=
          ih stepFuel (Nat.lt_succ_self stepFuel)
            (source := sourceAfterPost)
            (target := targetAfterPost)
            (final := final)
            hLoopFrame hPostRecursiveFrame hBodyRecursiveFrame
            (fun hInv hFrame hFuel hRun =>
              hBodyRegular hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hBodyBreak hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hBodyContinue hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hPostRegular hInv hFrame (by omega) hRun)
            hSourceLoop hPostInvariant
        rcases hLoopForward with
          ⟨loopSourceFuel, loopTargetFuel,
            hSourceLoopOrdinary, hTargetLoop, hLoopInvariant,
            hLoopEffect⟩
        let sourceJoinFuel :=
          Nat.max bodySourceFuel
            (Nat.max postSourceFuel loopSourceFuel)
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hLoopSourceLe : loopSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        let targetJoinFuel :=
          Nat.max bodyTargetFuel
            (Nat.max postTargetFuel loopTargetFuel)
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hLoopTargetLe : loopTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        exact
          ⟨targetFinal, sourceJoinFuel + 1, targetJoinFuel + 1,
            Functions.Source.Effectful.Stmt.runForLoop_regular_post_regular_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSemantics.primitiveSemantics transcript)
              sourceProgram
              (by simpa [hValue] using hSafe.evalCondition_eq)
              (Functions.Source.Effectful.Block.runScoped_mono
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram hBodySourceLe hSourceBodyOrdinary)
              (Functions.Source.Effectful.Block.runScoped_mono
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram hPostSourceLe hSourcePostOrdinary)
              (Functions.Source.Effectful.Stmt.runForLoop_mono
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram hLoopSourceLe hSourceLoopOrdinary),
            Structured.EffectSemantics.For.Eval.regular_post_regular
              (by simpa [hValue] using hTargetCond)
              (Structured.EffectSemantics.Block.Eval.mono
                hTargetBody hBodyTargetLe)
              (Structured.EffectSemantics.Block.Eval.mono
                hTargetPost hPostTargetLe)
              (Structured.EffectSemantics.For.Eval.mono
                hTargetLoop hLoopTargetLe),
            hLoopInvariant,
            (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
              hCondEffect).trans
              (hBodyEffect.trans
                (hPostEffect.trans hLoopEffect))⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hContinue
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyContinue hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel)
            hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBodyOrdinary, hTargetBody, hBodyInvariant,
            hBodyEffect⟩
        have hPostFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterBody :=
          hPostReturnFrame.transport_target
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        obtain ⟨targetAfterPost, hPostForward⟩ :=
          hPostRegular hBodyInvariant hPostFrame
            (Nat.lt_succ_self stepFuel) hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePostOrdinary, hTargetPost, hPostInvariant,
            hPostEffect⟩
        have hReturnsAfterPost :
            targetAfterPost.source.returns = target.source.returns :=
          (Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hTargetPost
            (by
              simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        have hLoopFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              loopCtx targetAfterPost :=
          hLoopReturnFrame.transport_target hReturnsAfterPost
        have hPostRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterPost :=
          hPostReturnFrame.transport_target hReturnsAfterPost
        have hBodyRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterPost :=
          hBodyReturnFrame.transport_target hReturnsAfterPost
        obtain ⟨targetFinal, hLoopForward⟩ :=
          ih stepFuel (Nat.lt_succ_self stepFuel)
            (source := sourceAfterPost)
            (target := targetAfterPost)
            (final := final)
            hLoopFrame hPostRecursiveFrame hBodyRecursiveFrame
            (fun hInv hFrame hFuel hRun =>
              hBodyRegular hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hBodyBreak hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hBodyContinue hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hPostRegular hInv hFrame (by omega) hRun)
            hSourceLoop hPostInvariant
        rcases hLoopForward with
          ⟨loopSourceFuel, loopTargetFuel,
            hSourceLoopOrdinary, hTargetLoop, hLoopInvariant,
            hLoopEffect⟩
        let sourceJoinFuel :=
          Nat.max bodySourceFuel
            (Nat.max postSourceFuel loopSourceFuel)
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hLoopSourceLe : loopSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        let targetJoinFuel :=
          Nat.max bodyTargetFuel
            (Nat.max postTargetFuel loopTargetFuel)
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hLoopTargetLe : loopTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        exact
          ⟨targetFinal, sourceJoinFuel + 1, targetJoinFuel + 1,
            Functions.Source.Effectful.Stmt.runForLoop_cont_post_regular_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSemantics.primitiveSemantics transcript)
              sourceProgram
              (by simpa [hValue] using hSafe.evalCondition_eq)
              (Functions.Source.Effectful.Block.runScoped_mono
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram hBodySourceLe hSourceBodyOrdinary)
              (Functions.Source.Effectful.Block.runScoped_mono
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram hPostSourceLe hSourcePostOrdinary)
              (Functions.Source.Effectful.Stmt.runForLoop_mono
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram hLoopSourceLe hSourceLoopOrdinary),
            Structured.EffectSemantics.For.Eval.cont_post_regular
              (by simpa [hValue] using hTargetCond)
              (Structured.EffectSemantics.Block.Eval.mono
                hTargetBody hBodyTargetLe)
              (Structured.EffectSemantics.Block.Eval.mono
                hTargetPost hPostTargetLe)
              (Structured.EffectSemantics.For.Eval.mono
                hTargetLoop hLoopTargetLe),
            hLoopInvariant,
            (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
              hCondEffect).trans
              (hBodyEffect.trans
                (hPostEffect.trans hLoopEffect))⟩

/--
Canonical source-fuel induction for allocator-aware loop exits.

Every recursive block callback consumes a strict sub-fuel of the enclosing
loop run. The theorem reconstructs the ordinary Functions execution and
composes the exact target allocator effect across the condition, body, post,
and recursive loop phases.
-/
theorem NonregularRuntimeForward.of_safe_source_run
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState bodyLowerState : AllocationLowering.State}
    {localsCtx bodyLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {loopLive resultLive : List Locals.Name}
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
    {source : Functions.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceFuel : Nat}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hCondScoped : Functions.Scope.ExprScoped loopLive cond)
    (hLowerCond :
      AllocationLowering.lowerExpr lowerCtx lowerState cond =
        some loweredCond)
    (hCompileCond :
      Locals.Expr.compileCode localsCtx 0 loweredCond = some condCode)
    (hLoopReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable loopCtx target)
    (hPostReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable postBase target)
    (hBodyReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable bodyBase target)
    (hBodyRegular :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState localsCtx
            plan loopLive frameBase mode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            bodyBase bodyTarget →
        bodyFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.regular bodyFinal) →
        ∃ bodyTargetFinal,
          Sequence.RegularScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx
            bodyLowerState bodyLocals plan loopLive frameBase mode
            sourceProgram bodyBase body bodySource targetProgram bodyBlock
            bodyTarget bodyFinal bodyTargetFinal)
    (hBodyContinue :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState localsCtx
            plan loopLive frameBase mode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            bodyBase bodyTarget →
        bodyFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.cont bodyFinal) →
        ∃ bodyTargetFinal,
          ContinueScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx
            bodyLowerState bodyLocals plan loopLive frameBase mode
            sourceProgram bodyBase body bodySource targetProgram bodyBlock
            bodyTarget bodyFinal bodyTargetFinal)
    (hBodyExit :
      ∀ {bodyFuel : Nat}
        {bodySource : Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        Functions.Source.Effectful.Outcome.IsExit bodyOutcome →
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState localsCtx
            plan loopLive frameBase mode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            bodyBase bodyTarget →
        bodyFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok bodyOutcome →
        ∃ targetOutcome finalMode,
          AllocationObserverOutcome.ScopedBlockRuntimeForward
            contract config allocatorDepth transcript plan resultLive
            frameBase mode finalMode sourceProgram bodyBase body bodySource
            targetProgram bodyBlock bodyTarget bodyOutcome targetOutcome)
    (hPostRegular :
      ∀ {postFuel : Nat}
        {postSource postFinal :
          Functions.ObserverSemantics.State transcript}
        {postTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx bodyLowerState
            bodyLocals plan loopLive frameBase mode postSource postTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            postBase postTarget →
        postFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram postBase post postFuel postSource =
          .ok (Functions.Source.Effectful.Outcome.regular postFinal) →
        ∃ postTargetFinal,
          Sequence.RegularScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx lowerState
            localsCtx plan loopLive frameBase mode sourceProgram postBase
            post postSource targetProgram postBlock postTarget postFinal
            postTargetFinal)
    (hPostExit :
      ∀ {postFuel : Nat}
        {postSource : Functions.ObserverSemantics.State transcript}
        {postOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {postTarget : Structured.ObserverSemantics.State transcript},
        Functions.Source.Effectful.Outcome.IsExit postOutcome →
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx bodyLowerState
            bodyLocals plan loopLive frameBase mode postSource postTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            postBase postTarget →
        postFuel < sourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram postBase post postFuel postSource =
          .ok postOutcome →
        ∃ targetOutcome finalMode,
          AllocationObserverOutcome.ScopedBlockRuntimeForward
            contract config allocatorDepth transcript plan resultLive
            frameBase mode finalMode sourceProgram postBase post postSource
            targetProgram postBlock postTarget postOutcome targetOutcome)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceOutcome)
    (hSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceProgram loopCtx cond postBase post bodyBase body
          sourceFuel source =
        .ok sourceOutcome)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan loopLive frameBase mode source target) :
    ∃ targetOutcome,
      NonregularRuntimeForward
        contract config allocatorDepth transcript plan resultLive
        frameBase mode sourceProgram loopCtx cond postBase post bodyBase
        body targetProgram condCode postBlock bodyBlock source target
        sourceOutcome targetOutcome := by
  induction sourceFuel using Nat.strong_induction_on generalizing
      source target sourceOutcome with
  | h sourceFuel ih =>
      obtain ⟨stepFuel, rfl, hCases⟩ :=
        Functions.Source.Effectful.Stmt.runForLoop_exit_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceProgram hExit hSource
      rcases hCases with
        hBodyCase | hRegularPost | hContinuePost |
        hRegularRecurse | hContinueRecurse
      · obtain ⟨sourceAfterCond, hSourceCond, hSourceBody⟩ :=
          hBodyCase
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetOutcome, finalMode, hBodyForward⟩ :=
          hBodyExit hExit hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel)
            hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hRel, _hSame, hBodyEffect⟩
        have hRel' :
            ActivationOutcomeRel contract plan resultLive 0 frameBase mode
              sourceOutcome targetOutcome :=
          hRel.reframe_of_isExit hExit
        cases hRel with
        | regular _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hExit
        | brk _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.brk,
              Locals.Source.Effectful.Outcome.brk] at hExit
        | cont _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.cont,
              Locals.Source.Effectful.Outcome.cont] at hExit
        | leave hLeave =>
            refine
              ⟨_, ?_,
                (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
                  hCondEffect).trans hBodyEffect⟩
            exact
              ⟨bodySourceFuel + 1, bodyTargetFuel + 1,
                Functions.Source.Effectful.Stmt.runForLoop_body_leave_of_runs
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSemantics.primitiveSemantics transcript)
                  sourceProgram
                  (by simpa [hValue] using hSafe.evalCondition_eq)
                  hSourceBody',
                Structured.EffectSemantics.For.Eval.body_leave
                  (by simpa [hValue] using hTargetCond)
                  hTargetBody,
                hRel'⟩
        | halt kind hHalt =>
            refine
              ⟨_, ?_,
                (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
                  hCondEffect).trans hBodyEffect⟩
            exact
              ⟨bodySourceFuel + 1, bodyTargetFuel + 1,
                Functions.Source.Effectful.Stmt.runForLoop_body_halt_of_runs
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSemantics.primitiveSemantics transcript)
                  sourceProgram
                  (by simpa [hValue] using hSafe.evalCondition_eq)
                  hSourceBody',
                Structured.EffectSemantics.For.Eval.body_halt
                  (by simpa [hValue] using hTargetCond)
                  hTargetBody,
                hRel'⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody,
              hSourceCond, hSourceBody, hSourcePost⟩ :=
          hRegularPost
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyRegular hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel)
            hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hBodyInvariant, hBodyEffect⟩
        have hPostFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterBody :=
          hPostReturnFrame.transport_target
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        obtain ⟨targetOutcome, finalMode, hPostForward⟩ :=
          hPostExit hExit hBodyInvariant hPostFrame
            (Nat.lt_succ_self stepFuel)
            hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hRel, _hSame, hPostEffect⟩
        have hRel' :
            ActivationOutcomeRel contract plan resultLive 0 frameBase mode
              sourceOutcome targetOutcome :=
          hRel.reframe_of_isExit hExit
        let sourceJoinFuel := Nat.max bodySourceFuel postSourceFuel
        let targetJoinFuel := Nat.max bodyTargetFuel postTargetFuel
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hSourceBody'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hBodySourceLe hSourceBody'
        have hSourcePost'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hPostSourceLe hSourcePost'
        have hTargetBody' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetBody hBodyTargetLe
        have hTargetPost' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetPost hPostTargetLe
        cases hRel with
        | regular _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hExit
        | brk _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.brk,
              Locals.Source.Effectful.Outcome.brk] at hExit
        | cont _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.cont,
              Locals.Source.Effectful.Outcome.cont] at hExit
        | leave hLeave =>
            refine
              ⟨_, ?_,
                (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
                  hCondEffect).trans
                  (hBodyEffect.trans hPostEffect)⟩
            exact
              ⟨sourceJoinFuel + 1, targetJoinFuel + 1,
                Functions.Source.Effectful.Stmt.runForLoop_regular_post_leave_of_runs
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSemantics.primitiveSemantics transcript)
                  sourceProgram
                  (by simpa [hValue] using hSafe.evalCondition_eq)
                  hSourceBody'' hSourcePost'',
                Structured.EffectSemantics.For.Eval.regular_post_leave
                  (by simpa [hValue] using hTargetCond)
                  hTargetBody' hTargetPost',
                hRel'⟩
        | halt kind hHalt =>
            refine
              ⟨_, ?_,
                (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
                  hCondEffect).trans
                  (hBodyEffect.trans hPostEffect)⟩
            exact
              ⟨sourceJoinFuel + 1, targetJoinFuel + 1,
                Functions.Source.Effectful.Stmt.runForLoop_regular_post_halt_of_runs
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSemantics.primitiveSemantics transcript)
                  sourceProgram
                  (by simpa [hValue] using hSafe.evalCondition_eq)
                  hSourceBody'' hSourcePost'',
                Structured.EffectSemantics.For.Eval.regular_post_halt
                  (by simpa [hValue] using hTargetCond)
                  hTargetBody' hTargetPost',
                hRel'⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody,
              hSourceCond, hSourceBody, hSourcePost⟩ :=
          hContinuePost
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyContinue hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel)
            hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hBodyInvariant, hBodyEffect⟩
        have hPostFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterBody :=
          hPostReturnFrame.transport_target
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        obtain ⟨targetOutcome, finalMode, hPostForward⟩ :=
          hPostExit hExit hBodyInvariant hPostFrame
            (Nat.lt_succ_self stepFuel)
            hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hRel, _hSame, hPostEffect⟩
        have hRel' :
            ActivationOutcomeRel contract plan resultLive 0 frameBase mode
              sourceOutcome targetOutcome :=
          hRel.reframe_of_isExit hExit
        let sourceJoinFuel := Nat.max bodySourceFuel postSourceFuel
        let targetJoinFuel := Nat.max bodyTargetFuel postTargetFuel
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hSourceBody'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hBodySourceLe hSourceBody'
        have hSourcePost'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hPostSourceLe hSourcePost'
        have hTargetBody' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetBody hBodyTargetLe
        have hTargetPost' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetPost hPostTargetLe
        cases hRel with
        | regular _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hExit
        | brk _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.brk,
              Locals.Source.Effectful.Outcome.brk] at hExit
        | cont _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.cont,
              Locals.Source.Effectful.Outcome.cont] at hExit
        | leave hLeave =>
            refine
              ⟨_, ?_,
                (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
                  hCondEffect).trans
                  (hBodyEffect.trans hPostEffect)⟩
            exact
              ⟨sourceJoinFuel + 1, targetJoinFuel + 1,
                Functions.Source.Effectful.Stmt.runForLoop_cont_post_leave_of_runs
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSemantics.primitiveSemantics transcript)
                  sourceProgram
                  (by simpa [hValue] using hSafe.evalCondition_eq)
                  hSourceBody'' hSourcePost'',
                Structured.EffectSemantics.For.Eval.cont_post_leave
                  (by simpa [hValue] using hTargetCond)
                  hTargetBody' hTargetPost',
                hRel'⟩
        | halt kind hHalt =>
            refine
              ⟨_, ?_,
                (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
                  hCondEffect).trans
                  (hBodyEffect.trans hPostEffect)⟩
            exact
              ⟨sourceJoinFuel + 1, targetJoinFuel + 1,
                Functions.Source.Effectful.Stmt.runForLoop_cont_post_halt_of_runs
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSemantics.primitiveSemantics transcript)
                  sourceProgram
                  (by simpa [hValue] using hSafe.evalCondition_eq)
                  hSourceBody'' hSourcePost'',
                Structured.EffectSemantics.For.Eval.cont_post_halt
                  (by simpa [hValue] using hTargetCond)
                  hTargetBody' hTargetPost',
                hRel'⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hRegularRecurse
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyRegular hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel)
            hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hBodyInvariant, hBodyEffect⟩
        have hPostFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterBody :=
          hPostReturnFrame.transport_target
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        obtain ⟨targetAfterPost, hPostForward⟩ :=
          hPostRegular hBodyInvariant hPostFrame
            (Nat.lt_succ_self stepFuel)
            hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hPostInvariant, hPostEffect⟩
        have hReturnsAfterPost :
            targetAfterPost.source.returns = target.source.returns :=
          (Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hTargetPost
            (by
              simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        have hLoopFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              loopCtx targetAfterPost :=
          hLoopReturnFrame.transport_target hReturnsAfterPost
        have hPostRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterPost :=
          hPostReturnFrame.transport_target hReturnsAfterPost
        have hBodyRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterPost :=
          hBodyReturnFrame.transport_target hReturnsAfterPost
        obtain ⟨targetOutcome, hLoopForward, hLoopEffect⟩ :=
          ih stepFuel (Nat.lt_succ_self stepFuel)
            (source := sourceAfterPost)
            (target := targetAfterPost)
            (sourceOutcome := sourceOutcome)
            hLoopFrame hPostRecursiveFrame hBodyRecursiveFrame
            (fun hInv hFrame hFuel hRun =>
              hBodyRegular hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hBodyContinue hInv hFrame (by omega) hRun)
            (fun hExitBody hInv hFrame hFuel hRun =>
              hBodyExit hExitBody hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hPostRegular hInv hFrame (by omega) hRun)
            (fun hExitPost hInv hFrame hFuel hRun =>
              hPostExit hExitPost hInv hFrame (by omega) hRun)
            hExit hSourceLoop hPostInvariant
        rcases hLoopForward with
          ⟨loopSourceFuel, loopTargetFuel,
            hSourceLoop', hTargetLoop, hRel⟩
        let sourceJoinFuel :=
          Nat.max bodySourceFuel
            (Nat.max postSourceFuel loopSourceFuel)
        let targetJoinFuel :=
          Nat.max bodyTargetFuel
            (Nat.max postTargetFuel loopTargetFuel)
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hLoopSourceLe : loopSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hLoopTargetLe : loopTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hSourceBody'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hBodySourceLe hSourceBody'
        have hSourcePost'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hPostSourceLe hSourcePost'
        have hSourceLoop'' :=
          Functions.Source.Effectful.Stmt.runForLoop_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hLoopSourceLe hSourceLoop'
        have hTargetBody' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetBody hBodyTargetLe
        have hTargetPost' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetPost hPostTargetLe
        have hTargetLoop' :=
          Structured.EffectSemantics.For.Eval.mono
            hTargetLoop hLoopTargetLe
        exact
          ⟨targetOutcome,
            ⟨sourceJoinFuel + 1, targetJoinFuel + 1,
              Functions.Source.Effectful.Stmt.runForLoop_regular_post_recurse_of_runs
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram
                (by simpa [hValue] using hSafe.evalCondition_eq)
                hSourceBody'' hSourcePost'' hSourceLoop'',
              Structured.EffectSemantics.For.Eval.regular_post_regular
                (by simpa [hValue] using hTargetCond)
                hTargetBody' hTargetPost' hTargetLoop',
              hRel⟩,
            (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
              hCondEffect).trans
              (hBodyEffect.trans
                (hPostEffect.trans hLoopEffect))⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hContinueRecurse
        obtain ⟨value, hSafe, hValue⟩ :=
          AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
            hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
          AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hConfig hInvariant hSafe hCondScoped hLowerCond hCompileCond
        have hBodyFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterCond :=
          hBodyReturnFrame.transport_target
            (Structured.ObserverSemantics.Code.runCondition_returns_eq
              hTargetCond)
        obtain ⟨targetAfterBody, hBodyForward⟩ :=
          hBodyContinue hCondInvariant hBodyFrame
            (Nat.lt_succ_self stepFuel)
            hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hBodyInvariant, hBodyEffect⟩
        have hPostFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterBody :=
          hPostReturnFrame.transport_target
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        obtain ⟨targetAfterPost, hPostForward⟩ :=
          hPostRegular hBodyInvariant hPostFrame
            (Nat.lt_succ_self stepFuel)
            hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hPostInvariant, hPostEffect⟩
        have hReturnsAfterPost :
            targetAfterPost.source.returns = target.source.returns :=
          (Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hTargetPost
            (by
              simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
            ((Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
              hTargetBody
              (by
                simp [Structured.ObserverSemantics.Outcome.Nonhalting])).trans
              (Structured.ObserverSemantics.Code.runCondition_returns_eq
                hTargetCond))
        have hLoopFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              loopCtx targetAfterPost :=
          hLoopReturnFrame.transport_target hReturnsAfterPost
        have hPostRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              postBase targetAfterPost :=
          hPostReturnFrame.transport_target hReturnsAfterPost
        have hBodyRecursiveFrame :
            AllocationObserverOutcome.ReturnFrameAvailable
              bodyBase targetAfterPost :=
          hBodyReturnFrame.transport_target hReturnsAfterPost
        obtain ⟨targetOutcome, hLoopForward, hLoopEffect⟩ :=
          ih stepFuel (Nat.lt_succ_self stepFuel)
            (source := sourceAfterPost)
            (target := targetAfterPost)
            (sourceOutcome := sourceOutcome)
            hLoopFrame hPostRecursiveFrame hBodyRecursiveFrame
            (fun hInv hFrame hFuel hRun =>
              hBodyRegular hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hBodyContinue hInv hFrame (by omega) hRun)
            (fun hExitBody hInv hFrame hFuel hRun =>
              hBodyExit hExitBody hInv hFrame (by omega) hRun)
            (fun hInv hFrame hFuel hRun =>
              hPostRegular hInv hFrame (by omega) hRun)
            (fun hExitPost hInv hFrame hFuel hRun =>
              hPostExit hExitPost hInv hFrame (by omega) hRun)
            hExit hSourceLoop hPostInvariant
        rcases hLoopForward with
          ⟨loopSourceFuel, loopTargetFuel,
            hSourceLoop', hTargetLoop, hRel⟩
        let sourceJoinFuel :=
          Nat.max bodySourceFuel
            (Nat.max postSourceFuel loopSourceFuel)
        let targetJoinFuel :=
          Nat.max bodyTargetFuel
            (Nat.max postTargetFuel loopTargetFuel)
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hLoopSourceLe : loopSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hLoopTargetLe : loopTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hSourceBody'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hBodySourceLe hSourceBody'
        have hSourcePost'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hPostSourceLe hSourcePost'
        have hSourceLoop'' :=
          Functions.Source.Effectful.Stmt.runForLoop_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hLoopSourceLe hSourceLoop'
        have hTargetBody' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetBody hBodyTargetLe
        have hTargetPost' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetPost hPostTargetLe
        have hTargetLoop' :=
          Structured.EffectSemantics.For.Eval.mono
            hTargetLoop hLoopTargetLe
        exact
          ⟨targetOutcome,
            ⟨sourceJoinFuel + 1, targetJoinFuel + 1,
              Functions.Source.Effectful.Stmt.runForLoop_cont_post_recurse_of_runs
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSemantics.primitiveSemantics transcript)
                sourceProgram
                (by simpa [hValue] using hSafe.evalCondition_eq)
                hSourceBody'' hSourcePost'' hSourceLoop'',
              Structured.EffectSemantics.For.Eval.cont_post_regular
                (by simpa [hValue] using hTargetCond)
                hTargetBody' hTargetPost' hTargetLoop',
              hRel⟩,
            (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
              hCondEffect).trans
              (hBodyEffect.trans
                (hPostEffect.trans hLoopEffect))⟩

/--
Canonical source-fuel induction for loop exits.

The theorem is generic over activation `leave` and terminal `halt` outcomes.
Direct body/post exits are related by the shared outcome-indexed block
interface; recursive exits descend strictly through a regular post.
-/
theorem NonregularForward.of_source_run
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState bodyLowerState : AllocationLowering.State}
    {localsCtx bodyLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {loopLive resultLive : List Locals.Name}
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
    {source : Functions.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceFuel : Nat}
    (hCondScoped : Functions.Scope.ExprScoped loopLive cond)
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
            contract lowerCtx lowerState localsCtx plan loopLive
            frameBase mode bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.regular bodyFinal) →
        ∃ bodyTargetFinal,
          Sequence.RegularScopedBlockInvariantForward
            contract transcript lowerCtx bodyLowerState bodyLocals plan
            loopLive frameBase mode sourceProgram bodyBase body bodySource
            targetProgram bodyBlock bodyTarget bodyFinal bodyTargetFinal)
    (hBodyContinue :
      ∀ {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx lowerState localsCtx plan loopLive
            frameBase mode bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.cont bodyFinal) →
        ∃ bodyTargetFinal,
          ContinueScopedBlockInvariantForward
            contract transcript lowerCtx bodyLowerState bodyLocals plan
            loopLive frameBase mode sourceProgram bodyBase body bodySource
            targetProgram bodyBlock bodyTarget bodyFinal bodyTargetFinal)
    (hBodyExit :
      ∀ {bodyFuel : Nat}
        {bodySource : Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        Functions.Source.Effectful.Outcome.IsExit bodyOutcome →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx lowerState localsCtx plan loopLive
            frameBase mode bodySource bodyTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram bodyBase body bodyFuel bodySource =
          .ok bodyOutcome →
        ∃ targetOutcome,
          Sequence.ScopedBlockForward
            contract transcript plan resultLive frameBase mode sourceProgram
            bodyBase body bodySource targetProgram bodyBlock bodyTarget
            bodyOutcome targetOutcome)
    (hPostRegular :
      ∀ {postFuel : Nat}
        {postSource postFinal :
          Functions.ObserverSemantics.State transcript}
        {postTarget : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx bodyLowerState bodyLocals plan loopLive
            frameBase mode postSource postTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram postBase post postFuel postSource =
          .ok (Functions.Source.Effectful.Outcome.regular postFinal) →
        ∃ postTargetFinal,
          Sequence.RegularScopedBlockInvariantForward
            contract transcript lowerCtx lowerState localsCtx plan loopLive
            frameBase mode sourceProgram postBase post postSource
            targetProgram postBlock postTarget postFinal postTargetFinal)
    (hPostExit :
      ∀ {postFuel : Nat}
        {postSource : Functions.ObserverSemantics.State transcript}
        {postOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {postTarget : Structured.ObserverSemantics.State transcript},
        Functions.Source.Effectful.Outcome.IsExit postOutcome →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx bodyLowerState bodyLocals plan loopLive
            frameBase mode postSource postTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram postBase post postFuel postSource =
          .ok postOutcome →
        ∃ targetOutcome,
          Sequence.ScopedBlockForward
            contract transcript plan resultLive frameBase mode sourceProgram
            postBase post postSource targetProgram postBlock postTarget
            postOutcome targetOutcome)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceOutcome)
    (hSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram loopCtx cond postBase post bodyBase body
          sourceFuel source =
        .ok sourceOutcome)
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan loopLive frameBase mode
        source target) :
    ∃ targetOutcome,
      NonregularForward
        contract transcript plan resultLive frameBase mode sourceProgram
        loopCtx cond postBase post bodyBase body targetProgram condCode
        postBlock bodyBlock source target sourceOutcome targetOutcome := by
  induction sourceFuel using Nat.strong_induction_on generalizing
      source target sourceOutcome with
  | h sourceFuel ih =>
      obtain ⟨stepFuel, rfl, hCases⟩ :=
        Functions.Source.Effectful.Stmt.runForLoop_exit_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram hExit hSource
      rcases hCases with
        hBodyCase | hRegularPost | hContinuePost |
        hRegularRecurse | hContinueRecurse
      · obtain ⟨sourceAfterCond, hSourceCond, hSourceBody⟩ := hBodyCase
        obtain ⟨value, hSafe, hValue⟩ := hCondSafe hSourceCond
        obtain
            ⟨targetAfterCond, hTargetCond, hCondInvariant⟩ :=
          AllocationObserverExpression.Expr.condition_forward
            (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
              contract)
            hInvariant hSafe hCondScoped hLowerCond hCompileCond
        obtain ⟨targetOutcome, hBodyForward⟩ :=
          hBodyExit hExit hCondInvariant hSourceBody
        rcases hBodyForward with
          ⟨bodySourceFuel, bodyTargetFuel,
            hSourceBody', hTargetBody, hRel⟩
        cases hRel with
        | regular _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hExit
        | brk _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.brk,
              Locals.Source.Effectful.Outcome.brk] at hExit
        | cont _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.cont,
              Locals.Source.Effectful.Outcome.cont] at hExit
        | @leave sourceExit targetExit hLeave =>
            refine
              ⟨Structured.EffectSemantics.Outcome.leave targetExit,
                NonregularForward.body_leave hSourceCond
                  (by simpa [hValue] using hTargetCond) ?_⟩
            exact
              ⟨bodySourceFuel, bodyTargetFuel,
                hSourceBody', hTargetBody, .leave hLeave⟩
        | @halt kind sourceExit targetExit hHalt =>
            refine
              ⟨Structured.EffectSemantics.Outcome.halt kind targetExit,
                NonregularForward.body_halt hSourceCond
                  (by simpa [hValue] using hTargetCond) ?_⟩
            exact
              ⟨bodySourceFuel, bodyTargetFuel,
                hSourceBody', hTargetBody, .halt kind hHalt⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody,
              hSourceCond, hSourceBody, hSourcePost⟩ :=
          hRegularPost
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
        obtain ⟨targetOutcome, hPostForward⟩ :=
          hPostExit hExit hBodyInvariant hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hRel⟩
        cases hRel with
        | regular _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hExit
        | brk _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.brk,
              Locals.Source.Effectful.Outcome.brk] at hExit
        | cont _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.cont,
              Locals.Source.Effectful.Outcome.cont] at hExit
        | @leave sourceExit targetExit hLeave =>
            refine
              ⟨Structured.EffectSemantics.Outcome.leave targetExit,
                NonregularForward.regular_post_leave hSourceCond
                  (lowerCtx := lowerCtx)
                  (bodyLowerState := bodyLowerState)
                  (bodyLocals := bodyLocals)
                  (loopLive := loopLive)
                  (sourceAfterBody := sourceAfterBody)
                  (targetAfterBody := targetAfterBody)
                  (by simpa [hValue] using hTargetCond)
                  ?_ ?_⟩
            · exact
                ⟨bodySourceFuel, bodyTargetFuel,
                  hSourceBody', hTargetBody, hBodyInvariant⟩
            · exact
                ⟨postSourceFuel, postTargetFuel,
                  hSourcePost', hTargetPost, .leave hLeave⟩
        | @halt kind sourceExit targetExit hHalt =>
            refine
              ⟨Structured.EffectSemantics.Outcome.halt kind targetExit,
                NonregularForward.regular_post_halt hSourceCond
                  (lowerCtx := lowerCtx)
                  (bodyLowerState := bodyLowerState)
                  (bodyLocals := bodyLocals)
                  (loopLive := loopLive)
                  (sourceAfterBody := sourceAfterBody)
                  (targetAfterBody := targetAfterBody)
                  (by simpa [hValue] using hTargetCond)
                  ?_ ?_⟩
            · exact
                ⟨bodySourceFuel, bodyTargetFuel,
                  hSourceBody', hTargetBody, hBodyInvariant⟩
            · exact
                ⟨postSourceFuel, postTargetFuel,
                  hSourcePost', hTargetPost, .halt kind hHalt⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody,
              hSourceCond, hSourceBody, hSourcePost⟩ :=
          hContinuePost
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
        obtain ⟨targetOutcome, hPostForward⟩ :=
          hPostExit hExit hBodyInvariant hSourcePost
        rcases hPostForward with
          ⟨postSourceFuel, postTargetFuel,
            hSourcePost', hTargetPost, hRel⟩
        cases hRel with
        | regular _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hExit
        | brk _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.brk,
              Locals.Source.Effectful.Outcome.brk] at hExit
        | cont _ =>
            simp [Functions.Source.Effectful.Outcome.IsExit,
              Functions.Source.Effectful.Outcome.cont,
              Locals.Source.Effectful.Outcome.cont] at hExit
        | @leave sourceExit targetExit hLeave =>
            refine
              ⟨Structured.EffectSemantics.Outcome.leave targetExit,
                NonregularForward.cont_post_leave hSourceCond
                  (lowerCtx := lowerCtx)
                  (bodyLowerState := bodyLowerState)
                  (bodyLocals := bodyLocals)
                  (loopLive := loopLive)
                  (sourceAfterBody := sourceAfterBody)
                  (targetAfterBody := targetAfterBody)
                  (by simpa [hValue] using hTargetCond)
                  ?_ ?_⟩
            · exact
                ⟨bodySourceFuel, bodyTargetFuel,
                  hSourceBody', hTargetBody, hBodyInvariant⟩
            · exact
                ⟨postSourceFuel, postTargetFuel,
                  hSourcePost', hTargetPost, .leave hLeave⟩
        | @halt kind sourceExit targetExit hHalt =>
            refine
              ⟨Structured.EffectSemantics.Outcome.halt kind targetExit,
                NonregularForward.cont_post_halt hSourceCond
                  (lowerCtx := lowerCtx)
                  (bodyLowerState := bodyLowerState)
                  (bodyLocals := bodyLocals)
                  (loopLive := loopLive)
                  (sourceAfterBody := sourceAfterBody)
                  (targetAfterBody := targetAfterBody)
                  (by simpa [hValue] using hTargetCond)
                  ?_ ?_⟩
            · exact
                ⟨bodySourceFuel, bodyTargetFuel,
                  hSourceBody', hTargetBody, hBodyInvariant⟩
            · exact
                ⟨postSourceFuel, postTargetFuel,
                  hSourcePost', hTargetPost, .halt kind hHalt⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hRegularRecurse
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
            (sourceOutcome := sourceOutcome)
            hExit hSourceLoop
        obtain ⟨targetOutcome, hLoopForward⟩ :=
          hRecursive hPostInvariant
        rcases hLoopForward with
          ⟨loopSourceFuel, loopTargetFuel,
            hSourceLoop', hTargetLoop, hRel⟩
        let sourceJoinFuel :=
          Nat.max bodySourceFuel
            (Nat.max postSourceFuel loopSourceFuel)
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hLoopSourceLe : loopSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hSourceBody'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hBodySourceLe hSourceBody'
        have hSourcePost'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hPostSourceLe hSourcePost'
        have hSourceLoop'' :=
          Functions.Source.Effectful.Stmt.runForLoop_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hLoopSourceLe hSourceLoop'
        let targetJoinFuel :=
          Nat.max bodyTargetFuel
            (Nat.max postTargetFuel loopTargetFuel)
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hLoopTargetLe : loopTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hTargetBody' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetBody hBodyTargetLe
        have hTargetPost' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetPost hPostTargetLe
        have hTargetLoop' :=
          Structured.EffectSemantics.For.Eval.mono
            hTargetLoop hLoopTargetLe
        exact
          ⟨targetOutcome, sourceJoinFuel + 1, targetJoinFuel + 1,
            Functions.Source.Effectful.Stmt.runForLoop_regular_post_recurse_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSemantics.primitiveSemantics transcript)
              sourceProgram hSourceCond hSourceBody'' hSourcePost''
              hSourceLoop'',
            Structured.EffectSemantics.For.Eval.regular_post_regular
              (by simpa [hValue] using hTargetCond)
              hTargetBody' hTargetPost' hTargetLoop',
            hRel⟩
      · obtain
            ⟨sourceAfterCond, sourceAfterBody, sourceAfterPost,
              hSourceCond, hSourceBody, hSourcePost, hSourceLoop⟩ :=
          hContinueRecurse
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
            (sourceOutcome := sourceOutcome)
            hExit hSourceLoop
        obtain ⟨targetOutcome, hLoopForward⟩ :=
          hRecursive hPostInvariant
        rcases hLoopForward with
          ⟨loopSourceFuel, loopTargetFuel,
            hSourceLoop', hTargetLoop, hRel⟩
        let sourceJoinFuel :=
          Nat.max bodySourceFuel
            (Nat.max postSourceFuel loopSourceFuel)
        have hBodySourceLe : bodySourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hPostSourceLe : postSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hLoopSourceLe : loopSourceFuel ≤ sourceJoinFuel := by
          simp [sourceJoinFuel]
        have hSourceBody'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hBodySourceLe hSourceBody'
        have hSourcePost'' :=
          Functions.Source.Effectful.Block.runScoped_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hPostSourceLe hSourcePost'
        have hSourceLoop'' :=
          Functions.Source.Effectful.Stmt.runForLoop_mono
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram hLoopSourceLe hSourceLoop'
        let targetJoinFuel :=
          Nat.max bodyTargetFuel
            (Nat.max postTargetFuel loopTargetFuel)
        have hBodyTargetLe : bodyTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hPostTargetLe : postTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hLoopTargetLe : loopTargetFuel ≤ targetJoinFuel := by
          simp [targetJoinFuel]
        have hTargetBody' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetBody hBodyTargetLe
        have hTargetPost' :=
          Structured.EffectSemantics.Block.Eval.mono
            hTargetPost hPostTargetLe
        have hTargetLoop' :=
          Structured.EffectSemantics.For.Eval.mono
            hTargetLoop hLoopTargetLe
        exact
          ⟨targetOutcome, sourceJoinFuel + 1, targetJoinFuel + 1,
            Functions.Source.Effectful.Stmt.runForLoop_cont_post_recurse_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSemantics.primitiveSemantics transcript)
              sourceProgram hSourceCond hSourceBody'' hSourcePost''
              hSourceLoop'',
            Structured.EffectSemantics.For.Eval.cont_post_regular
              (by simpa [hValue] using hTargetCond)
              hTargetBody' hTargetPost' hTargetLoop',
            hRel⟩

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

namespace RegularStmtRuntimeInvariantForward

/--
Allocator-aware preservation for a `for` whose initializer is regular and
whose first condition is false.
-/
theorem for_false_of_components
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
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
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        outerPlan outerLive frameBase outerMode source target)
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState
            localsCtx.withoutLoopControl outerPlan outerLive frameBase
            outerMode source target →
        ∃ targetAfterInit,
          RegularBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx loopState
            initLocals loopPlan loopLive frameBase outerMode loopMode
            sourceProgram sourceCtx.withoutLoopControl init source
            targetProgram
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
      RegularStmtRuntimeInvariantForward
        contract config allocatorDepth transcript lowerCtx lowerFinal
        localsFinal outerPlan outerLive frameBase outerMode outerMode
        sourceProgram sourceCtx (.for_ init cond post body) source
        targetProgram target
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState
        localsCtx.withoutLoopControl outerPlan outerLive frameBase
        outerMode source target :=
    hInvariant.transport_locals_layout rfl
  obtain ⟨targetAfterInit, hInitForward⟩ :=
    hInit hLowerInit hCompileInit hInitialLoopInvariant
  rcases hInitForward with
    ⟨initSourceFuel, initTargetFuel,
      hSourceInit, hTargetInit, hInitInvariant, hInitMode, hInitEffect⟩
  obtain
      ⟨targetAfterCond, hTargetCond, hCondInvariant, hCondEffect⟩ :=
    AllocationObserverExpression.Expr.condition_forward_runtime_with_effect
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hInitInvariant hSafe hCondScoped hLowerCond hCompileCond
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx loopState initLocals
        loopPlan loopLive frameBase loopMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          loopLive sourceAfterCond)
        targetAfterCond :=
    hCondInvariant.restrict_source_live
  obtain
      ⟨targetFinal, hCleanupRun, hFinalBaseInvariant, hCleanupEffect⟩ :=
    ForLoop.finish_regular_outer_runtime
      hInvariant hLoopInvariant hInitMode hInitScoped hSubset
      hLowerInit hCleanup
  have hFinalInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerFinal localsFinal
        outerPlan outerLive frameBase outerMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            loopLive sourceAfterCond))
        targetFinal := by
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
      hFinalInvariant, SameFrame.refl outerMode,
      hInitEffect.trans
        ((AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
          hCondEffect).trans hCleanupEffect)⟩
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
Allocator-aware preservation for a regular `for` from its canonical guarded
source loop run.

The loop-owned source-fuel induction handles every iteration. Callers supply
only the adjacent initializer, body, and post block results at the strictly
smaller fuels exposed by that induction.
-/
theorem for_regular_of_safe_source_run
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
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
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hInitScoped : Functions.Scope.Block.Scoped outerLive init)
    (hCondScoped : Functions.Scope.ExprScoped loopLive cond)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ outerLive)
    (hLoopSourceScope :
      ∀ name, name ∈ loopSourceCtx.scope ↔ name ∈ loopLive)
    (hSubset :
      ∀ name, name ∈ outerLive → name ∈ loopLive)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        outerPlan outerLive frameBase outerMode source target)
    (hReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable sourceCtx target)
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState
            localsCtx.withoutLoopControl outerPlan outerLive frameBase
            outerMode source target →
        ∃ targetAfterInit,
          RegularBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx loopState
            initLocals loopPlan loopLive frameBase outerMode loopMode
            sourceProgram sourceCtx.withoutLoopControl init source
            targetProgram
            { stmts := Expressions.StmtList.toStructured initCode }
            target sourceAfterInit targetAfterInit loopSourceCtx ∧
          AllocationObserverOutcome.SameControl
            sourceCtx.withoutLoopControl loopSourceCtx)
    (hBodyRegular :
      ∀ {loweredInit : Locals.Block}
        {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {initCode bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerBlockOpen
            lowerCtx returns lowerState init =
          some (loweredInit, loopState) →
        Locals.Block.compileOpen localsCtx.withoutLoopControl loweredInit =
          some (initCode, initLocals) →
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx loopState initLocals
            loopPlan loopLive frameBase loopMode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            bodyTarget →
        bodyFuel < loopSourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.regular bodyFinal) →
        ∃ bodyTargetFinal,
          RegularScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodySource targetProgram compiledBody.toStructured
            bodyTarget bodyFinal bodyTargetFinal)
    (hBodyBreak :
      ∀ {loweredInit : Locals.Block}
        {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {initCode bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerBlockOpen
            lowerCtx returns lowerState init =
          some (loweredInit, loopState) →
        Locals.Block.compileOpen localsCtx.withoutLoopControl loweredInit =
          some (initCode, initLocals) →
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx loopState initLocals
            loopPlan loopLive frameBase loopMode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            bodyTarget →
        bodyFuel < loopSourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.brk bodyFinal) →
        ∃ bodyTargetFinal,
          ForLoop.BreakScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx loopState
            initLocals loopPlan loopLive frameBase loopMode sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodySource targetProgram compiledBody.toStructured
            bodyTarget bodyFinal bodyTargetFinal)
    (hBodyContinue :
      ∀ {loweredInit : Locals.Block}
        {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {initCode bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {bodyFuel : Nat}
        {bodySource bodyFinal :
          Functions.ObserverSemantics.State transcript}
        {bodyTarget : Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerBlockOpen
            lowerCtx returns lowerState init =
          some (loweredInit, loopState) →
        Locals.Block.compileOpen localsCtx.withoutLoopControl loweredInit =
          some (initCode, initLocals) →
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx loopState initLocals
            loopPlan loopLive frameBase loopMode bodySource bodyTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            bodyTarget →
        bodyFuel < loopSourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodyFuel bodySource =
          .ok (Functions.Source.Effectful.Outcome.cont bodyFinal) →
        ∃ bodyTargetFinal,
          ForLoop.ContinueScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodySource targetProgram compiledBody.toStructured
            bodyTarget bodyFinal bodyTargetFinal)
    (hPostRegular :
      ∀ {loweredInit : Locals.Block}
        {loopState afterPost : AllocationLowering.State}
        {loweredPost : Locals.Block}
        {initLocals postLocals : Locals.Ctx}
        {initCode postCode : List Expressions.Stmt}
        {compiledPost : Expressions.Block}
        {postFuel : Nat}
        {postSource postFinal :
          Functions.ObserverSemantics.State transcript}
        {postTarget : Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerBlockOpen
            lowerCtx returns lowerState init =
          some (loweredInit, loopState) →
        Locals.Block.compileOpen localsCtx.withoutLoopControl loweredInit =
          some (initCode, initLocals) →
        AllocationLowering.lowerBlockScoped
            lowerCtx returns loopState post =
          some (loweredPost, afterPost) →
        Locals.Block.compileOpen initLocals.withoutLoopControl
            loweredPost =
          some (postCode, postLocals) →
        Locals.finishScoped initLocals.withoutLoopControl
            postLocals postCode =
          some compiledPost →
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode postSource postTarget →
        AllocationObserverOutcome.ReturnFrameAvailable
            loopSourceCtx.withoutLoopControl postTarget →
        postFuel < loopSourceFuel →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceProgram loopSourceCtx.withoutLoopControl post
            postFuel postSource =
          .ok (Functions.Source.Effectful.Outcome.regular postFinal) →
        ∃ postTargetFinal,
          RegularScopedBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx loopState
            initLocals loopPlan loopLive frameBase loopMode sourceProgram
            loopSourceCtx.withoutLoopControl post postSource
            targetProgram compiledPost.toStructured postTarget
            postFinal postTargetFinal)
    (hSourceLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
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
      RegularStmtRuntimeInvariantForward
        contract config allocatorDepth transcript lowerCtx lowerFinal
        localsFinal outerPlan outerLive frameBase outerMode outerMode
        sourceProgram sourceCtx (.for_ init cond post body) source
        targetProgram target
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
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState
        localsCtx.withoutLoopControl outerPlan outerLive frameBase
        outerMode source target :=
    hInvariant.transport_locals_layout rfl
  obtain ⟨targetAfterInit, hInitForward, hInitControl⟩ :=
    hInit hLowerInit hCompileInit hInitialLoopInvariant
  rcases hInitForward with
    ⟨initSourceFuel, initTargetFuel,
      hSourceInit, hTargetInit, hInitInvariant, hInitMode, hInitEffect⟩
  have hTargetInitReturns :
      targetAfterInit.source.returns = target.source.returns :=
    Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
      hTargetInit
      (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
  have hLoopReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        loopSourceCtx targetAfterInit :=
    AllocationObserverOutcome.ReturnFrameAvailable.transport_target
      (AllocationObserverOutcome.ReturnFrameAvailable.of_sameControl
        hReturnFrame.withoutLoopControl hInitControl)
      hTargetInitReturns
  have hPostReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        loopSourceCtx.withoutLoopControl targetAfterInit :=
    hLoopReturnFrame.withoutLoopControl
  have hBodyReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        (loopSourceCtx.withLoopControl
          loopSourceCtx.scope loopSourceCtx.scope)
        targetAfterInit :=
    hLoopReturnFrame.withLoopControl
  obtain ⟨targetLoopFinal, hLoopForward⟩ :=
    ForLoop.RegularRuntimeInvariantForward.of_safe_source_run
      hLoopSourceScope hCondScoped hConfig hLowerCond hCompileCond
      hLoopReturnFrame hPostReturnFrame hBodyReturnFrame
      (fun hInv hFrame hFuel hRun =>
        hBodyRegular hLowerInit hCompileInit
          hLowerPost hLowerBody hCompileBody hFinishBody
          hInv hFrame hFuel hRun)
      (fun hInv hFrame hFuel hRun =>
        hBodyBreak hLowerInit hCompileInit
          hLowerPost hLowerBody hCompileBody hFinishBody
          hInv hFrame hFuel hRun)
      (fun hInv hFrame hFuel hRun =>
        hBodyContinue hLowerInit hCompileInit
          hLowerPost hLowerBody hCompileBody hFinishBody
          hInv hFrame hFuel hRun)
      (fun hInv hFrame hFuel hRun =>
        hPostRegular hLowerInit hCompileInit
          hLowerPost hCompilePost hFinishPost
          hInv hFrame hFuel hRun)
      hSourceLoop hInitInvariant
  rcases hLoopForward with
    ⟨loopSourceFuel', loopTargetFuel,
      hSourceLoop', hTargetLoop, hLoopFinalInvariant, hLoopEffect⟩
  obtain
      ⟨targetFinal, hCleanupRun, hFinalBaseInvariant, hCleanupEffect⟩ :=
    ForLoop.finish_regular_outer_runtime
      hInvariant hLoopFinalInvariant hInitMode hInitScoped hSubset
      hLowerInit hCleanup
  have hFinalInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerFinal localsFinal
        outerPlan outerLive frameBase outerMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceLoopFinal)
        targetFinal := by
    rw [hLowerFinal, hLocalsFinal]
    exact hFinalBaseInvariant.transport_state rfl rfl
  let sourceFuel := Nat.max initSourceFuel loopSourceFuel'
  have hInitSourceLe : initSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hLoopSourceLe : loopSourceFuel' ≤ sourceFuel := by
    simp [sourceFuel]
  have hSourceInit' :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hInitSourceLe hSourceInit
  have hSourceLoop'' :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hLoopSourceLe hSourceLoop'
  have hSource :=
    Functions.Source.Effectful.Stmt.run_for_regular_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := sourceFuel)
      hSourceInit' hSourceLoop''
  have hRestrict :
      (Functions.ObserverSemantics.stateModel transcript).restrictTo
          sourceCtx.scope sourceLoopFinal =
        (Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceLoopFinal :=
    Locals.Source.Effectful.StateModel.restrictTo_congr
      (Functions.ObserverSemantics.stateModel transcript)
      hSourceScope
  rw [hRestrict] at hSource
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
      hFinalInvariant, SameFrame.refl outerMode,
      hInitEffect.trans_of_sameFrame hInitMode
        (hLoopEffect.trans_of_sameFrame hInitMode.symm hCleanupEffect)⟩
  · exact hSource
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

end RegularStmtRuntimeInvariantForward

namespace NonregularStmtForward

/--
Forward preservation for a `for` whose initializer completes regularly and
whose canonical loop execution leaves the activation or halts.

Recursive loop preservation is discharged internally by source-fuel induction.
The compiler-emitted outer cleanup is present in the real artifact but is
unreachable after the nonregular loop outcome.
-/
theorem for_exit_of_source_run
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
    {outerLive loopLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode loopMode : ActivationMode}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterInit :
      Functions.ObserverSemantics.State transcript}
    {sourceLoopOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Structured.ObserverSemantics.State transcript}
    {loopSourceFuel : Nat}
    (hCondScoped : Functions.Scope.ExprScoped loopLive cond)
    (hLoopSourceScope : loopSourceCtx.scope = loopLive)
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
    (hBodyExit :
      ∀ {loopState afterPost afterBody : AllocationLowering.State}
        {loweredPost loweredBody : Locals.Block}
        {initLocals bodyLocals : Locals.Ctx}
        {bodyCode : List Expressions.Stmt}
        {compiledBody : Expressions.Block}
        {bodyFuel : Nat}
        {bodySource : Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
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
        Functions.Source.Effectful.Outcome.IsExit bodyOutcome →
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
          .ok bodyOutcome →
        ∃ targetOutcome,
          ScopedBlockForward
            contract transcript loopPlan resultLive frameBase loopMode
            sourceProgram
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body bodySource targetProgram compiledBody.toStructured
            bodyTarget bodyOutcome targetOutcome)
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
    (hPostExit :
      ∀ {loopState afterPost : AllocationLowering.State}
        {loweredPost : Locals.Block}
        {initLocals postLocals : Locals.Ctx}
        {postCode : List Expressions.Stmt}
        {compiledPost : Expressions.Block}
        {postFuel : Nat}
        {postSource : Functions.ObserverSemantics.State transcript}
        {postOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
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
        Functions.Source.Effectful.Outcome.IsExit postOutcome →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx afterPost
            (initLocals.withLoopControl initLocals.layout.length)
            loopPlan loopLive frameBase loopMode postSource postTarget →
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSemantics.primitiveSemantics transcript)
            sourceProgram loopSourceCtx.withoutLoopControl post
            postFuel postSource =
          .ok postOutcome →
        ∃ targetOutcome,
          ScopedBlockForward
            contract transcript loopPlan resultLive frameBase loopMode
            sourceProgram loopSourceCtx.withoutLoopControl post postSource
            targetProgram compiledPost.toStructured postTarget
            postOutcome targetOutcome)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceLoopOutcome)
    (hSourceLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram loopSourceCtx cond
          loopSourceCtx.withoutLoopControl post
          (loopSourceCtx.withLoopControl
            loopSourceCtx.scope loopSourceCtx.scope)
          body loopSourceFuel sourceAfterInit =
        .ok sourceLoopOutcome)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.for_ init cond post body) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetOutcome,
      NonregularStmtForward
        contract transcript loopPlan resultLive frameBase loopMode
        sourceProgram sourceCtx (.for_ init cond post body) source
        targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceLoopOutcome targetOutcome sourceCtx := by
  obtain
      ⟨loweredInit, loopState, loweredCond, loweredPost, afterPost,
        loweredBody, afterBody, hLowerInit, hLowerCond, hLowerPost,
        hLowerBody, hLoweredShape, _hLowerFinal⟩ :=
    AllocationLowering.lowerStmt_for_components hLower
  subst loweredStmts
  obtain
      ⟨initCode, initLocals, condCode,
        postCode, postLocals, compiledPost,
        bodyCode, bodyLocals, compiledBody, cleanup,
        hCompileInit, hCompileCond, hCompilePost, hFinishPost,
        hCompileBody, hFinishBody, _hCleanup,
        hCompiledShape, _hLocalsFinal⟩ :=
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
      hSourceInit, hTargetInit, hInitInvariant, _hInitMode⟩
  obtain ⟨targetOutcome, hLoopForward⟩ :=
    ForLoop.NonregularForward.of_source_run
      hCondScoped hLowerCond hCompileCond hCondSafe
      (fun hInvariant hRun =>
        hBodyRegular hLowerPost hLowerBody hCompileBody hFinishBody
          hInvariant hRun)
      (fun hInvariant hRun =>
        hBodyContinue hLowerPost hLowerBody hCompileBody hFinishBody
          hInvariant hRun)
      (fun hExitBody hInvariant hRun =>
        hBodyExit hLowerPost hLowerBody hCompileBody hFinishBody
          hExitBody hInvariant hRun)
      (fun hInvariant hRun =>
        hPostRegular hLowerPost hCompilePost hFinishPost hInvariant hRun)
      (fun hExitPost hInvariant hRun =>
        hPostExit hLowerPost hCompilePost hFinishPost
          hExitPost hInvariant hRun)
      hExit hSourceLoop hInitInvariant
  rcases hLoopForward with
    ⟨loopSourceFuel', loopTargetFuel,
      hSourceLoop', hTargetLoop, hOutcomeRel⟩
  let sourceFuel := Nat.max initSourceFuel loopSourceFuel'
  have hInitSourceLe : initSourceFuel ≤ sourceFuel := by
    simp [sourceFuel]
  have hLoopSourceLe : loopSourceFuel' ≤ sourceFuel := by
    simp [sourceFuel]
  have hSourceInit' :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hInitSourceLe hSourceInit
  have hSourceLoop'' :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hLoopSourceLe hSourceLoop'
  have hSource :=
    Functions.Source.Effectful.Stmt.run_for_exit_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := sourceFuel)
      hExit hSourceInit' hSourceLoop''
  let targetFuel := Nat.max initTargetFuel loopTargetFuel
  have hInitTargetLe : initTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hLoopTargetLe : loopTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetInit' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetInit hInitTargetLe
  have hTargetLoop' :=
    Structured.EffectSemantics.For.Eval.mono
      hTargetLoop hLoopTargetLe
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (targetFuel + 1)
        (.for_
          { stmts := Expressions.StmtList.toStructured initCode }
          condCode compiledPost.toStructured compiledBody.toStructured)
        target targetOutcome :=
    Structured.EffectSemantics.Stmt.Eval.for_init_regular
      hTargetInit' hTargetLoop'
  have hSourceMode : sourceLoopOutcome.mode ≠ .regular := by
    rcases sourceLoopOutcome with ⟨final, outcomeMode⟩
    cases outcomeMode with
    | regular =>
        simp [Functions.Source.Effectful.Outcome.IsExit,
          Functions.Source.Effectful.Outcome.regular,
          Locals.Source.Effectful.Outcome.regular] at hExit
    | brk =>
        simp [Functions.Source.Effectful.Outcome.brk,
          Locals.Source.Effectful.Outcome.brk]
    | cont =>
        simp [Functions.Source.Effectful.Outcome.cont,
          Locals.Source.Effectful.Outcome.cont]
    | leave =>
        simp [Functions.Source.Effectful.Outcome.leave,
          Locals.Source.Effectful.Outcome.leave]
    | halt kind =>
        simp [Functions.Source.Effectful.Outcome.halt,
          Locals.Source.Effectful.Outcome.halt]
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hOutcomeRel.target_nonregular hSourceMode
  have hTargetBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts :=
            [ (.for_
                { stmts := Expressions.StmtList.toStructured initCode }
                condCode compiledPost.toStructured
                compiledBody.toStructured),
              Structured.Stmt.code cleanup ] }
        target targetOutcome :=
    Structured.EffectSemantics.Block.Eval.cons_nonregular
      hTargetStmt hTargetMode
  refine
    ⟨targetOutcome,
      NonregularStmtForward.of_runs
        (targetFuel := targetFuel + 2)
        hSource ?_ hSourceMode hOutcomeRel⟩
  have hInitCompile :
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
    Expressions.Stmt.toStructured] using hTargetBlock

/--
Forward preservation for a `for` whose initializer leaves the activation or
halts before the condition is evaluated.

The initializer proof is supplied by the adjacent recursive open-block
interface. Both the loop and compiler-emitted outer cleanup are unreachable.
-/
theorem for_init_exit_of_components
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {outerPlan exitPlan : Locals.Allocation.Plan}
    {outerLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode exitMode : ActivationMode}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {sourceInitOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Structured.ObserverSemantics.State transcript}
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
        ∃ initCtx targetOutcome,
          BlockForward
            contract transcript exitPlan resultLive frameBase exitMode
            sourceProgram sourceCtx.withoutLoopControl init source
            targetProgram
            { stmts := Expressions.StmtList.toStructured initCode }
            target sourceInitOutcome targetOutcome initCtx)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceInitOutcome)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.for_ init cond post body) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetOutcome,
      NonregularStmtForward
        contract transcript exitPlan resultLive frameBase exitMode
        sourceProgram sourceCtx (.for_ init cond post body) source
        targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceInitOutcome targetOutcome sourceCtx := by
  obtain
      ⟨loweredInit, _loopState, _loweredCond, _loweredPost, _afterPost,
        _loweredBody, _afterBody, hLowerInit, _hLowerCond, _hLowerPost,
        _hLowerBody, hLoweredShape, _hLowerFinal⟩ :=
    AllocationLowering.lowerStmt_for_components hLower
  subst loweredStmts
  obtain
      ⟨initCode, _initLocals, condCode,
        _postCode, _postLocals, compiledPost,
        _bodyCode, _bodyLocals, compiledBody, cleanup,
        hCompileInit, _hCompileCond, _hCompilePost, _hFinishPost,
        _hCompileBody, _hFinishBody, _hCleanup,
        hCompiledShape, _hLocalsFinal⟩ :=
    Locals.Block.compileOpen_single_for_components hCompile
  have hInitialInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx.withoutLoopControl
        outerPlan outerLive frameBase outerMode source target :=
    hInvariant.transport_locals_layout rfl
  obtain ⟨initCtx, targetOutcome, hInitForward⟩ :=
    hInit hLowerInit hCompileInit hInitialInvariant
  rcases hInitForward with
    ⟨initSourceFuel, initTargetFuel,
      hSourceInit, hTargetInit, hOutcomeRel⟩
  have hSource :=
    Functions.Source.Effectful.Stmt.run_for_init_exit_of_runOpen
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (cond := cond)
      (post := post) (body := body) hExit hSourceInit
  have hTargetExit :
      Structured.EffectSemantics.Outcome.IsExit targetOutcome :=
    hOutcomeRel.target_isExit hExit
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (initTargetFuel + 1)
        (.for_
          { stmts := Expressions.StmtList.toStructured initCode }
          condCode compiledPost.toStructured compiledBody.toStructured)
        target targetOutcome :=
    Structured.EffectSemantics.Stmt.Eval.for_init_exit
      hTargetInit hTargetExit
  have hSourceMode : sourceInitOutcome.mode ≠ .regular := by
    rcases sourceInitOutcome with ⟨final, outcomeMode⟩
    cases outcomeMode with
    | regular =>
        simp [Functions.Source.Effectful.Outcome.IsExit,
          Functions.Source.Effectful.Outcome.regular,
          Locals.Source.Effectful.Outcome.regular] at hExit
    | brk =>
        simp [Functions.Source.Effectful.Outcome.brk,
          Locals.Source.Effectful.Outcome.brk]
    | cont =>
        simp [Functions.Source.Effectful.Outcome.cont,
          Locals.Source.Effectful.Outcome.cont]
    | leave =>
        simp [Functions.Source.Effectful.Outcome.leave,
          Locals.Source.Effectful.Outcome.leave]
    | halt kind =>
        simp [Functions.Source.Effectful.Outcome.halt,
          Locals.Source.Effectful.Outcome.halt]
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hOutcomeRel.target_nonregular hSourceMode
  have hTargetBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (initTargetFuel + 2)
        { stmts :=
            [ (.for_
                { stmts := Expressions.StmtList.toStructured initCode }
                condCode compiledPost.toStructured
                compiledBody.toStructured),
              Structured.Stmt.code cleanup ] }
        target targetOutcome :=
    Structured.EffectSemantics.Block.Eval.cons_nonregular
      hTargetStmt hTargetMode
  refine
    ⟨targetOutcome,
      NonregularStmtForward.of_runs
        (targetFuel := initTargetFuel + 2)
        hSource ?_ hSourceMode hOutcomeRel⟩
  have hInitCompile :
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
    Expressions.Stmt.toStructured] using hTargetBlock

end NonregularStmtForward
end Sequence
end AllocationObserverStatement

namespace AllocationObserverOutcome
namespace NonregularStmtRuntimeForward

open AllocationObserverRelation
open AllocationObserverStatement
open AllocationObserverStatement.Sequence

/--
Allocator-aware preservation for a `for` whose initializer completes
regularly and whose loop leaves the activation or halts.

The statement theorem owns the real compiler decomposition and the unreachable
outer cleanup. The loop callback is instantiated only with those checked
artifacts; source-fuel induction remains owned by `ForLoop`.
-/
theorem for_exit_of_components
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx loopSourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {outerPlan loopPlan : Locals.Allocation.Plan}
    {outerLive loopLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode loopMode : ActivationMode}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterInit :
      Functions.ObserverSemantics.State transcript}
    {sourceLoopOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        outerPlan outerLive frameBase outerMode source target)
    (hReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable sourceCtx target)
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState
            localsCtx.withoutLoopControl outerPlan outerLive frameBase
            outerMode source target →
        ∃ targetAfterInit,
          RegularBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx loopState
            initLocals loopPlan loopLive frameBase outerMode loopMode
            sourceProgram sourceCtx.withoutLoopControl init source
            targetProgram
            { stmts := Expressions.StmtList.toStructured initCode }
            target sourceAfterInit targetAfterInit loopSourceCtx ∧
          AllocationObserverOutcome.SameControl
            sourceCtx.withoutLoopControl loopSourceCtx)
    (hLoop :
      ∀ {loopState afterPost afterBody : AllocationLowering.State}
        {loweredCond : Locals.Expr 1}
        {loweredPost loweredBody : Locals.Block}
        {initLocals postLocals bodyLocals : Locals.Ctx}
        {condCode : Structured.Code}
        {postCode bodyCode : List Expressions.Stmt}
        {compiledPost compiledBody : Expressions.Block}
        {targetAfterInit : Structured.ObserverSemantics.State transcript},
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx loopState initLocals
            loopPlan loopLive frameBase loopMode sourceAfterInit
            targetAfterInit →
        AllocationObserverOutcome.ReturnFrameAvailable
            loopSourceCtx targetAfterInit →
        AllocationObserverOutcome.ReturnFrameAvailable
            loopSourceCtx.withoutLoopControl targetAfterInit →
        AllocationObserverOutcome.ReturnFrameAvailable
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            targetAfterInit →
        ∃ targetOutcome,
          AllocationObserverStatement.ForLoop.NonregularRuntimeForward
            contract config allocatorDepth transcript loopPlan resultLive
            frameBase loopMode sourceProgram loopSourceCtx cond
            loopSourceCtx.withoutLoopControl post
            (loopSourceCtx.withLoopControl
              loopSourceCtx.scope loopSourceCtx.scope)
            body targetProgram condCode compiledPost.toStructured
            compiledBody.toStructured sourceAfterInit targetAfterInit
            sourceLoopOutcome targetOutcome)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceLoopOutcome)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.for_ init cond post body) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetOutcome,
      NonregularStmtRuntimeForward
        contract config allocatorDepth transcript loopPlan resultLive
        frameBase outerMode loopMode sourceProgram sourceCtx
        (.for_ init cond post body) source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceLoopOutcome targetOutcome sourceCtx := by
  obtain
      ⟨loweredInit, loopState, loweredCond, loweredPost, afterPost,
        loweredBody, afterBody, hLowerInit, hLowerCond, hLowerPost,
        hLowerBody, hLoweredShape, _hLowerFinal⟩ :=
    AllocationLowering.lowerStmt_for_components hLower
  subst loweredStmts
  obtain
      ⟨initCode, initLocals, condCode,
        postCode, postLocals, compiledPost,
        bodyCode, bodyLocals, compiledBody, cleanup,
        hCompileInit, hCompileCond, hCompilePost, hFinishPost,
        hCompileBody, hFinishBody, _hCleanup,
        hCompiledShape, _hLocalsFinal⟩ :=
    Locals.Block.compileOpen_single_for_components hCompile
  have hInitialLoopInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState
        localsCtx.withoutLoopControl outerPlan outerLive frameBase
        outerMode source target :=
    hInvariant.transport_locals_layout rfl
  obtain ⟨targetAfterInit, hInitForward, hInitControl⟩ :=
    hInit hLowerInit hCompileInit hInitialLoopInvariant
  rcases hInitForward with
    ⟨initSourceFuel, initTargetFuel,
      hSourceInit, hTargetInit, hInitInvariant, hInitMode, hInitEffect⟩
  have hTargetInitReturns :
      targetAfterInit.source.returns = target.source.returns :=
    Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
      hTargetInit
      (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
  have hLoopReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        loopSourceCtx targetAfterInit :=
    AllocationObserverOutcome.ReturnFrameAvailable.transport_target
      (AllocationObserverOutcome.ReturnFrameAvailable.of_sameControl
        hReturnFrame.withoutLoopControl hInitControl)
      hTargetInitReturns
  have hPostReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        loopSourceCtx.withoutLoopControl targetAfterInit :=
    hLoopReturnFrame.withoutLoopControl
  have hBodyReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        (loopSourceCtx.withLoopControl
          loopSourceCtx.scope loopSourceCtx.scope)
        targetAfterInit :=
    hLoopReturnFrame.withLoopControl
  obtain ⟨targetOutcome, hLoopForward⟩ :=
    hLoop hLowerCond hLowerPost hLowerBody hCompileCond
      hCompilePost hFinishPost hCompileBody hFinishBody hInitInvariant
      hLoopReturnFrame hPostReturnFrame hBodyReturnFrame
  rcases hLoopForward with
    ⟨⟨loopSourceFuel, loopTargetFuel,
        hSourceLoop, hTargetLoop, hOutcomeRel⟩, hLoopEffect⟩
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
    Functions.Source.Effectful.Stmt.run_for_exit_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := sourceFuel)
      hExit hSourceInit' hSourceLoop'
  let targetFuel := Nat.max initTargetFuel loopTargetFuel
  have hInitTargetLe : initTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hLoopTargetLe : loopTargetFuel ≤ targetFuel := by
    simp [targetFuel]
  have hTargetInit' :=
    Structured.EffectSemantics.Block.Eval.mono
      hTargetInit hInitTargetLe
  have hTargetLoop' :=
    Structured.EffectSemantics.For.Eval.mono
      hTargetLoop hLoopTargetLe
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (targetFuel + 1)
        (.for_
          { stmts := Expressions.StmtList.toStructured initCode }
          condCode compiledPost.toStructured compiledBody.toStructured)
        target targetOutcome :=
    Structured.EffectSemantics.Stmt.Eval.for_init_regular
      hTargetInit' hTargetLoop'
  have hSourceMode : sourceLoopOutcome.mode ≠ .regular := by
    rcases sourceLoopOutcome with ⟨final, outcomeMode⟩
    cases outcomeMode with
    | regular =>
        simp [Functions.Source.Effectful.Outcome.IsExit,
          Functions.Source.Effectful.Outcome.regular,
          Locals.Source.Effectful.Outcome.regular] at hExit
    | brk =>
        simp [Functions.Source.Effectful.Outcome.brk,
          Locals.Source.Effectful.Outcome.brk]
    | cont =>
        simp [Functions.Source.Effectful.Outcome.cont,
          Locals.Source.Effectful.Outcome.cont]
    | leave =>
        simp [Functions.Source.Effectful.Outcome.leave,
          Locals.Source.Effectful.Outcome.leave]
    | halt kind =>
        simp [Functions.Source.Effectful.Outcome.halt,
          Locals.Source.Effectful.Outcome.halt]
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hOutcomeRel.target_nonregular hSourceMode
  have hTargetBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts :=
            [ (.for_
                { stmts := Expressions.StmtList.toStructured initCode }
                condCode compiledPost.toStructured
                compiledBody.toStructured),
              Structured.Stmt.code cleanup ] }
        target targetOutcome :=
    Structured.EffectSemantics.Block.Eval.cons_nonregular
      hTargetStmt hTargetMode
  refine
    ⟨targetOutcome, sourceFuel + 1, targetFuel + 2, hSource, ?_,
      hSourceMode, hOutcomeRel, hInitMode,
      hInitEffect.trans_of_sameFrame hInitMode hLoopEffect⟩
  have hInitCompile :
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
    Expressions.Stmt.toStructured] using hTargetBlock

/--
Allocator-aware preservation for a `for` whose initializer exits before the
condition is evaluated. The loop and outer cleanup are unreachable, so the
initializer's outcome relation, mode transition, and allocator effect are the
complete statement result.
-/
theorem for_init_exit_of_components
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {outerPlan exitPlan : Locals.Allocation.Plan}
    {outerLive resultLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode : ActivationMode}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {sourceInitOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        outerPlan outerLive frameBase outerMode source target)
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
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx lowerState
            localsCtx.withoutLoopControl outerPlan outerLive frameBase
            outerMode source target →
        ∃ initCtx targetOutcome finalMode,
          BlockRuntimeForward
            contract config allocatorDepth transcript exitPlan resultLive
            frameBase outerMode finalMode sourceProgram
            sourceCtx.withoutLoopControl init source targetProgram
            { stmts := Expressions.StmtList.toStructured initCode }
            target sourceInitOutcome targetOutcome initCtx)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceInitOutcome)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.for_ init cond post body) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetOutcome finalMode,
      NonregularStmtRuntimeForward
        contract config allocatorDepth transcript exitPlan resultLive
        frameBase outerMode finalMode sourceProgram sourceCtx
        (.for_ init cond post body) source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceInitOutcome targetOutcome sourceCtx := by
  obtain
      ⟨loweredInit, _loopState, _loweredCond, _loweredPost, _afterPost,
        _loweredBody, _afterBody, hLowerInit, _hLowerCond, _hLowerPost,
        _hLowerBody, hLoweredShape, _hLowerFinal⟩ :=
    AllocationLowering.lowerStmt_for_components hLower
  subst loweredStmts
  obtain
      ⟨initCode, _initLocals, condCode,
        _postCode, _postLocals, compiledPost,
        _bodyCode, _bodyLocals, compiledBody, cleanup,
        hCompileInit, _hCompileCond, _hCompilePost, _hFinishPost,
        _hCompileBody, _hFinishBody, _hCleanup,
        hCompiledShape, _hLocalsFinal⟩ :=
    Locals.Block.compileOpen_single_for_components hCompile
  have hInitialInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState
        localsCtx.withoutLoopControl outerPlan outerLive frameBase
        outerMode source target :=
    hInvariant.transport_locals_layout rfl
  obtain
      ⟨initCtx, targetOutcome, finalMode, hInitForward⟩ :=
    hInit hLowerInit hCompileInit hInitialInvariant
  rcases hInitForward with
    ⟨initSourceFuel, initTargetFuel, hSourceInit, hTargetInit,
      hOutcomeRel, hSame, hEffect⟩
  have hSource :=
    Functions.Source.Effectful.Stmt.run_for_init_exit_of_runOpen
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (cond := cond)
      (post := post) (body := body) hExit hSourceInit
  have hTargetExit :
      Structured.EffectSemantics.Outcome.IsExit targetOutcome :=
    hOutcomeRel.target_isExit hExit
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (initTargetFuel + 1)
        (.for_
          { stmts := Expressions.StmtList.toStructured initCode }
          condCode compiledPost.toStructured compiledBody.toStructured)
        target targetOutcome :=
    Structured.EffectSemantics.Stmt.Eval.for_init_exit
      hTargetInit hTargetExit
  have hSourceMode : sourceInitOutcome.mode ≠ .regular := by
    rcases sourceInitOutcome with ⟨final, outcomeMode⟩
    cases outcomeMode with
    | regular =>
        simp [Functions.Source.Effectful.Outcome.IsExit,
          Functions.Source.Effectful.Outcome.regular,
          Locals.Source.Effectful.Outcome.regular] at hExit
    | brk =>
        simp [Functions.Source.Effectful.Outcome.brk,
          Locals.Source.Effectful.Outcome.brk]
    | cont =>
        simp [Functions.Source.Effectful.Outcome.cont,
          Locals.Source.Effectful.Outcome.cont]
    | leave =>
        simp [Functions.Source.Effectful.Outcome.leave,
          Locals.Source.Effectful.Outcome.leave]
    | halt kind =>
        simp [Functions.Source.Effectful.Outcome.halt,
          Locals.Source.Effectful.Outcome.halt]
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hOutcomeRel.target_nonregular hSourceMode
  have hTargetBlock :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (initTargetFuel + 2)
        { stmts :=
            [ (.for_
                { stmts := Expressions.StmtList.toStructured initCode }
                condCode compiledPost.toStructured
                compiledBody.toStructured),
              Structured.Stmt.code cleanup ] }
        target targetOutcome :=
    Structured.EffectSemantics.Block.Eval.cons_nonregular
      hTargetStmt hTargetMode
  refine
    ⟨targetOutcome, finalMode, initSourceFuel + 1, initTargetFuel + 2,
      hSource, ?_, hSourceMode, hOutcomeRel, hSame, hEffect⟩
  have hInitCompile :
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
    Expressions.Stmt.toStructured] using hTargetBlock

end NonregularStmtRuntimeForward
end AllocationObserverOutcome
end Functions
end EvmCompiler
