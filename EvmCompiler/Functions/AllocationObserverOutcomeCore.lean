import EvmCompiler.Functions.AllocationObserverContext

namespace EvmCompiler
namespace Functions
namespace AllocationObserverOutcome

open AllocationObserverRelation

abbrev Trace := Assembly.ResourceTrace

/--
Allocator-aware preservation for one source statement that exits nonregularly.

This shared interface is independent of statement-specific proof modules. The
final activation mode describes the related abrupt outcome, while `SameFrame`
and `ActivationEffect` retain the representation and allocator facts needed by
enclosing source-fuel recursion.
-/
def NonregularStmtRuntimeForward
    (contract : MemoryContract.Contract)
    (config : Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (finalLive : List Locals.Name)
    (frameBase : Nat)
    (initialMode finalMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (stmt : Functions.Stmt)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (target : Structured.ObserverSemantics.State transcript)
    (compiled : List Structured.Stmt)
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript))
    (stmtCtx : Functions.Source.Ctx) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel stmt source =
        .ok (sourceOutcome, stmtCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel { stmts := compiled } target
          targetOutcome ∧
      sourceOutcome.mode ≠ .regular ∧
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome ∧
      SameFrame initialMode finalMode ∧
      Frame.ActivationEffect config allocatorDepth initialMode
        target targetOutcome.state

/--
Outcome-indexed block preservation with the recursive allocator invariant.
-/
def BlockRuntimeForward
    (contract : MemoryContract.Contract)
    (config : Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (finalLive : List Locals.Name)
    (frameBase : Nat)
    (initialMode finalMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (sourceBlock : Functions.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (targetBlock : Structured.Block)
    (target : Structured.ObserverSemantics.State transcript)
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript))
    (finalCtx : Functions.Source.Ctx) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel sourceBlock source =
        .ok (sourceOutcome, finalCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel targetBlock target targetOutcome ∧
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome ∧
      SameFrame initialMode finalMode ∧
      Frame.ActivationEffect config allocatorDepth initialMode
        target targetOutcome.state

/--
Outcome-indexed preservation for a lexically scoped source block while
retaining the recursive allocator effect.

Unlike `BlockRuntimeForward`, this interface records the canonical scoped
source execution and therefore has no outgoing source context. It is the
adjacent boundary consumed by loop bodies and posts after the statement pass
has accounted for lexical cleanup.
-/
def ScopedBlockRuntimeForward
    (contract : MemoryContract.Contract)
    (config : Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (finalLive : List Locals.Name)
    (frameBase : Nat)
    (initialMode finalMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (sourceBlock : Functions.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (targetBlock : Structured.Block)
    (target : Structured.ObserverSemantics.State transcript)
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceBlock sourceFuel source =
        .ok sourceOutcome ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel targetBlock target targetOutcome ∧
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome ∧
      SameFrame initialMode finalMode ∧
      Frame.ActivationEffect config allocatorDepth initialMode
        target targetOutcome.state

/--
The source-visible live set associated with a statement outcome.
-/
def outcomeLive
    (returns regularLive : List Functions.Name)
    (ctx : Functions.Source.Ctx) :
    Locals.Source.Mode → List Functions.Name
  | .regular => regularLive
  | .brk => ctx.breakScope?.getD []
  | .cont => ctx.continueScope?.getD []
  | .leave => returns
  | .halt _ => regularLive

/--
Two source contexts agree on the control destinations visible to abrupt
statement outcomes.
-/
structure SameControl
    (before after : Functions.Source.Ctx) : Prop where
  breakScope : before.breakScope? = after.breakScope?
  continueScope : before.continueScope? = after.continueScope?
  leaveScope : before.leaveScope? = after.leaveScope?

namespace SameControl

theorem refl (ctx : Functions.Source.Ctx) : SameControl ctx ctx :=
  ⟨rfl, rfl, rfl⟩

theorem trans
    {first second third : Functions.Source.Ctx}
    (hFirst : SameControl first second)
    (hSecond : SameControl second third) :
    SameControl first third :=
  ⟨hFirst.breakScope.trans hSecond.breakScope,
    hFirst.continueScope.trans hSecond.continueScope,
    hFirst.leaveScope.trans hSecond.leaveScope⟩

end SameControl

/--
A source context that may execute `leave` has a concrete target return frame.

This is control-stack availability, not part of the allocation state relation:
ordinary target execution preserves it extensionally through equality of the
Structured return stack.
-/
def ReturnFrameAvailable
    {transcript : Trace}
    (ctx : Functions.Source.Ctx)
    (target : Structured.ObserverSemantics.State transcript) : Prop :=
  ∀ functionScope,
    ctx.leaveScope? = some functionScope →
      target.source.returns ≠ []

namespace ReturnFrameAvailable

theorem transport_target
    {transcript : Trace}
    {ctx : Functions.Source.Ctx}
    {before after : Structured.ObserverSemantics.State transcript}
    (hAvailable : ReturnFrameAvailable ctx before)
    (hReturns : after.source.returns = before.source.returns) :
    ReturnFrameAvailable ctx after := by
  intro functionScope hLeave
  rw [hReturns]
  exact hAvailable functionScope hLeave

theorem withoutLoopControl
    {transcript : Trace}
    {ctx : Functions.Source.Ctx}
    {target : Structured.ObserverSemantics.State transcript}
    (hAvailable : ReturnFrameAvailable ctx target) :
    ReturnFrameAvailable ctx.withoutLoopControl target := by
  intro functionScope hLeave
  exact
    hAvailable functionScope
      (by
        simpa [Functions.Source.Ctx.withoutLoopControl] using hLeave)

theorem withLoopControl
    {transcript : Trace}
    {ctx : Functions.Source.Ctx}
    {breakScope continueScope : List Functions.Name}
    {target : Structured.ObserverSemantics.State transcript}
    (hAvailable : ReturnFrameAvailable ctx target) :
    ReturnFrameAvailable
      (ctx.withLoopControl breakScope continueScope) target := by
  intro functionScope hLeave
  exact
    hAvailable functionScope
      (by
        simpa [Functions.Source.Ctx.withLoopControl] using hLeave)

theorem of_sameControl
    {transcript : Trace}
    {beforeCtx afterCtx : Functions.Source.Ctx}
    {target : Structured.ObserverSemantics.State transcript}
    (hAvailable : ReturnFrameAvailable beforeCtx target)
    (hControl : SameControl beforeCtx afterCtx) :
    ReturnFrameAvailable afterCtx target := by
  intro functionScope hLeave
  exact
    hAvailable functionScope
      (hControl.leaveScope.trans hLeave)

end ReturnFrameAvailable

end AllocationObserverOutcome
end Functions
end EvmCompiler
