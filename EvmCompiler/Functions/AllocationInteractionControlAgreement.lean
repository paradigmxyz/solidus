import EvmCompiler.Functions.AllocationInteractionCleanup

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionControlAgreement

open AllocationInteractionRelation
open AllocationInteractionCleanup

/--
Pass-owned agreement between source control destinations and the allocated
Locals cleanup depths implementing them.

This is static/runtime boundary data for one adjacent pass. It contains no
source evaluator, target execution, observer transcript, or compiler evidence
outside the ordinary allocation plan and Locals context.
-/
structure Agreement
    (plan : Plan) (returns live : List Functions.Name)
    (mode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (localsCtx : Locals.Ctx) (target : TargetState) : Prop where
  brk :
    ∀ {afterLive}, sourceCtx.breakScope? = some afterLive →
      ∃ targetDepth afterMode,
        localsCtx.breakDepth? = some targetDepth ∧
          Nonempty
            (Transition plan live afterLive targetDepth mode afterMode)
  cont :
    ∀ {afterLive}, sourceCtx.continueScope? = some afterLive →
      ∃ targetDepth afterMode,
        localsCtx.continueDepth? = some targetDepth ∧
          Nonempty
            (Transition plan live afterLive targetDepth mode afterMode)
  leave :
    ∀ {functionScope}, sourceCtx.leaveScope? = some functionScope →
      localsCtx.leaveDepth? = some 0 ∧
        localsCtx.leaveRetc = returns.length ∧ target.returns ≠ []

namespace Agreement

/-- Construct agreement for a context with no abrupt control destinations. -/
def noControl
    {plan : Plan} {returns live : List Functions.Name}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {localsCtx : Locals.Ctx} {target : TargetState}
    (hBreak : sourceCtx.breakScope? = none)
    (hContinue : sourceCtx.continueScope? = none)
    (hLeave : sourceCtx.leaveScope? = none) :
    Agreement plan returns live mode sourceCtx localsCtx target := by
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · intro afterLive hScope
    rw [hBreak] at hScope
    contradiction
  · intro afterLive hScope
    rw [hContinue] at hScope
    contradiction
  · intro functionScope hScope
    rw [hLeave] at hScope
    contradiction

/-- Construct function-body agreement before loop control is installed. -/
def functionBody
    {plan : Plan} {returns live : List Functions.Name}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {localsCtx : Locals.Ctx} {target : TargetState}
    (hBreak : sourceCtx.breakScope? = none)
    (hContinue : sourceCtx.continueScope? = none)
    (hDepth : localsCtx.leaveDepth? = some 0)
    (hRetc : localsCtx.leaveRetc = returns.length)
    (hReturnFrame : target.returns ≠ []) :
    Agreement plan returns live mode sourceCtx localsCtx target := by
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · intro afterLive hScope
    rw [hBreak] at hScope
    contradiction
  · intro afterLive hScope
    rw [hContinue] at hScope
    contradiction
  · intro functionScope hScope
    exact ⟨hDepth, hRetc, hReturnFrame⟩

/-- Transport control agreement across source scope-only edits and Locals
layout-only edits. -/
def transport_context
    {plan : Plan} {returns live : List Functions.Name}
    {mode : ActivationMode}
    {beforeSource afterSource : Functions.Source.Ctx}
    {beforeLocals afterLocals : Locals.Ctx}
    {target : TargetState}
    (hAgreement :
      Agreement plan returns live mode beforeSource beforeLocals target)
    (hSource : Functions.Source.Ctx.SameControl beforeSource afterSource)
    (hLocals : Locals.Ctx.SameControl beforeLocals afterLocals) :
    Agreement plan returns live mode afterSource afterLocals target := by
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · intro afterLive hScope
    obtain ⟨targetDepth, afterMode, hDepth, hTransition⟩ :=
      hAgreement.brk (hSource.breakScope.trans hScope)
    exact
      ⟨targetDepth, afterMode,
        hLocals.breakDepth.symm.trans hDepth, hTransition⟩
  · intro afterLive hScope
    obtain ⟨targetDepth, afterMode, hDepth, hTransition⟩ :=
      hAgreement.cont (hSource.continueScope.trans hScope)
    exact
      ⟨targetDepth, afterMode,
        hLocals.continueDepth.symm.trans hDepth, hTransition⟩
  · intro functionScope hScope
    obtain ⟨hDepth, hRetc, hFrame⟩ :=
      hAgreement.leave (hSource.leaveScope.trans hScope)
    exact
      ⟨hLocals.leaveDepth.symm.trans hDepth,
        hLocals.leaveRetc.symm.trans hRetc, hFrame⟩

/-- Reindex every control cleanup across an allocation plan agreeing on the
whole current live scope. -/
def transport_plan
    {leftPlan rightPlan : Plan} {returns live : List Functions.Name}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {localsCtx : Locals.Ctx} {target : TargetState}
    (hAgreement :
      Agreement leftPlan returns live mode sourceCtx localsCtx target)
    (hAgree : PlanAgreesOn leftPlan rightPlan live) :
    Agreement rightPlan returns live mode sourceCtx localsCtx target := by
  refine { brk := ?_, cont := ?_, leave := hAgreement.leave }
  · intro afterLive hScope
    obtain ⟨targetDepth, afterMode, hDepth, ⟨hTransition⟩⟩ :=
      hAgreement.brk hScope
    exact
      ⟨targetDepth, afterMode, hDepth,
        ⟨hTransition.transport_plan hAgree⟩⟩
  · intro afterLive hScope
    obtain ⟨targetDepth, afterMode, hDepth, ⟨hTransition⟩⟩ :=
      hAgreement.cont hScope
    exact
      ⟨targetDepth, afterMode, hDepth,
        ⟨hTransition.transport_plan hAgree⟩⟩

/-- External interactions and ordinary emitted code may update the target
state while preserving the procedure-return stack. -/
def transport_target
    {plan : Plan} {returns live : List Functions.Name}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {localsCtx : Locals.Ctx} {before after : TargetState}
    (hAgreement :
      Agreement plan returns live mode sourceCtx localsCtx before)
    (hReturns : after.returns = before.returns) :
    Agreement plan returns live mode sourceCtx localsCtx after := by
  refine { brk := hAgreement.brk, cont := hAgreement.cont, leave := ?_ }
  intro functionScope hScope
  obtain ⟨hDepth, hRetc, hFrame⟩ := hAgreement.leave hScope
  exact ⟨hDepth, hRetc, by simpa [hReturns] using hFrame⟩

/-- Reindex a loop-free context across arbitrary live-set and mode changes.
Only function `leave` can remain active, and its destination is independent of
the current local stack layout. -/
def reindexNoLoop
    {plan : Plan} {returns beforeLive afterLive : List Functions.Name}
    {beforeMode afterMode : ActivationMode}
    {beforeSource afterSource : Functions.Source.Ctx}
    {beforeLocals afterLocals : Locals.Ctx}
    {beforeTarget afterTarget : TargetState}
    (hAgreement :
      Agreement plan returns beforeLive beforeMode beforeSource beforeLocals
        beforeTarget)
    (hSource : Functions.Source.Ctx.SameControl beforeSource afterSource)
    (hLocals : Locals.Ctx.SameControl beforeLocals afterLocals)
    (hBreak : afterSource.breakScope? = none)
    (hContinue : afterSource.continueScope? = none)
    (hReturns : afterTarget.returns = beforeTarget.returns) :
    Agreement plan returns afterLive afterMode afterSource afterLocals
      afterTarget := by
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · intro live hScope
    rw [hBreak] at hScope
    contradiction
  · intro live hScope
    rw [hContinue] at hScope
    contradiction
  · intro functionScope hScope
    obtain ⟨hDepth, hRetc, hFrame⟩ :=
      hAgreement.leave (hSource.leaveScope.trans hScope)
    exact
      ⟨hLocals.leaveDepth.symm.trans hDepth,
        hLocals.leaveRetc.symm.trans hRetc,
        by simpa [hReturns] using hFrame⟩

/-- Removing loop control leaves function-return agreement unchanged. -/
def withoutLoopControl
    {plan : Plan} {returns live : List Functions.Name}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {localsCtx : Locals.Ctx} {target : TargetState}
    (hAgreement :
      Agreement plan returns live mode sourceCtx localsCtx target) :
    Agreement plan returns live mode sourceCtx.withoutLoopControl
      localsCtx.withoutLoopControl target := by
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · simp [Functions.Source.Ctx.withoutLoopControl]
  · simp [Functions.Source.Ctx.withoutLoopControl]
  · intro functionScope hScope
    have hOldScope : sourceCtx.leaveScope? = some functionScope := by
      simpa [Functions.Source.Ctx.withoutLoopControl] using hScope
    simpa [Locals.Ctx.withoutLoopControl] using hAgreement.leave hOldScope

/-- Install the current activation as both loop-control destinations. -/
def withLoopControl
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {plan : Plan} {returns live : List Functions.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx} {localsCtx : Locals.Ctx}
    {source : SourceState} {target : TargetState}
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hAgreement :
      Agreement plan returns live mode sourceCtx localsCtx target) :
    Agreement plan returns live mode
      (sourceCtx.withLoopControl live live)
      (localsCtx.withLoopControl localsCtx.layout.length) target := by
  have hLoopTransition :
      Nonempty
        (Transition plan live live localsCtx.layout.length mode mode) := by
    cases hCompiler : hInvariant.compiler with
    | stack hStack =>
        exact ⟨
          { dropped := []
            subset := fun _ hName => hName
            stackOrder := by simp
            mode := .stack (by
              rw [hStack.layout, ← hStack.stackOrder]) }⟩
    | @scratch frameDepth frameWords hScratch =>
        exact ⟨
          { dropped := []
            subset := fun _ hName => hName
            stackOrder := by simp
            mode := .scratch frameDepth frameDepth frameWords
              hScratch.currentStackOrder_length.symm
              (by rw [hScratch.layout, hScratch.frameBottom]) }⟩
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · intro afterLive hScope
    have hAfter : afterLive = live := by
      simpa [Functions.Source.Ctx.withLoopControl] using hScope.symm
    subst afterLive
    exact
      ⟨localsCtx.layout.length, mode,
        by simp [Locals.Ctx.withLoopControl], hLoopTransition⟩
  · intro afterLive hScope
    have hAfter : afterLive = live := by
      simpa [Functions.Source.Ctx.withLoopControl] using hScope.symm
    subst afterLive
    exact
      ⟨localsCtx.layout.length, mode,
        by simp [Locals.Ctx.withLoopControl], hLoopTransition⟩
  · intro functionScope hScope
    have hOldScope : sourceCtx.leaveScope? = some functionScope := by
      simpa [Functions.Source.Ctx.withLoopControl] using hScope
    simpa [Locals.Ctx.withLoopControl] using hAgreement.leave hOldScope

/-- A stack-resident declaration adds one cleanup entry in front of every
existing control destination. -/
def after_stack_declaration
    {plan : Plan} {returns live : List Functions.Name}
    {name : Functions.Name} {beforeMode afterMode : ActivationMode}
    {sourceCtx nextCtx : Functions.Source.Ctx}
    {beforeLocals afterLocals : Locals.Ctx} {target : TargetState}
    (hAgreement :
      Agreement plan returns live beforeMode sourceCtx beforeLocals target)
    (hSource : Functions.Source.Ctx.SameControl sourceCtx nextCtx)
    (hLocals : Locals.Ctx.SameControl beforeLocals afterLocals)
    (hMode : afterMode = beforeMode.afterStackDeclaration)
    (hOrder :
      currentStackOrder plan (name :: live) =
        name :: currentStackOrder plan live) :
    Agreement plan returns (name :: live) afterMode nextCtx afterLocals
      target := by
  subst afterMode
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · intro afterLive hScope
    obtain ⟨targetDepth, finalMode, hDepth, ⟨hTransition⟩⟩ :=
      hAgreement.brk (hSource.breakScope.trans hScope)
    exact
      ⟨targetDepth, finalMode,
        hLocals.breakDepth.symm.trans hDepth,
        ⟨hTransition.after_stack_declaration hOrder⟩⟩
  · intro afterLive hScope
    obtain ⟨targetDepth, finalMode, hDepth, ⟨hTransition⟩⟩ :=
      hAgreement.cont (hSource.continueScope.trans hScope)
    exact
      ⟨targetDepth, finalMode,
        hLocals.continueDepth.symm.trans hDepth,
        ⟨hTransition.after_stack_declaration hOrder⟩⟩
  · intro functionScope hScope
    obtain ⟨hDepth, hRetc, hFrame⟩ :=
      hAgreement.leave (hSource.leaveScope.trans hScope)
    exact
      ⟨hLocals.leaveDepth.symm.trans hDepth,
        hLocals.leaveRetc.symm.trans hRetc, hFrame⟩

/-- A scratch-resident declaration changes no control cleanup depth. -/
def after_scratch_declaration
    {plan : Plan} {returns live : List Functions.Name}
    {name : Functions.Name} {mode : ActivationMode}
    {sourceCtx nextCtx : Functions.Source.Ctx}
    {beforeLocals afterLocals : Locals.Ctx} {target : TargetState}
    (hAgreement :
      Agreement plan returns live mode sourceCtx beforeLocals target)
    (hSource : Functions.Source.Ctx.SameControl sourceCtx nextCtx)
    (hLocals : Locals.Ctx.SameControl beforeLocals afterLocals)
    (hOrder :
      currentStackOrder plan (name :: live) =
        currentStackOrder plan live) :
    Agreement plan returns (name :: live) mode nextCtx afterLocals target := by
  refine { brk := ?_, cont := ?_, leave := ?_ }
  · intro afterLive hScope
    obtain ⟨targetDepth, finalMode, hDepth, ⟨hTransition⟩⟩ :=
      hAgreement.brk (hSource.breakScope.trans hScope)
    exact
      ⟨targetDepth, finalMode,
        hLocals.breakDepth.symm.trans hDepth,
        ⟨hTransition.after_scratch_declaration hOrder⟩⟩
  · intro afterLive hScope
    obtain ⟨targetDepth, finalMode, hDepth, ⟨hTransition⟩⟩ :=
      hAgreement.cont (hSource.continueScope.trans hScope)
    exact
      ⟨targetDepth, finalMode,
        hLocals.continueDepth.symm.trans hDepth,
        ⟨hTransition.after_scratch_declaration hOrder⟩⟩
  · intro functionScope hScope
    obtain ⟨hDepth, hRetc, hFrame⟩ :=
      hAgreement.leave (hSource.leaveScope.trans hScope)
    exact
      ⟨hLocals.leaveDepth.symm.trans hDepth,
        hLocals.leaveRetc.symm.trans hRetc, hFrame⟩

end Agreement
end AllocationInteractionControlAgreement
end Functions
end EvmCompiler
