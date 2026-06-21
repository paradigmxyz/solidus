import EvmCompiler.Functions.StackExpressionPreservation
import EvmCompiler.Functions.StackAccessLowering
import EvmCompiler.Functions.StackLowering
import EvmCompiler.Functions.StackTransitionCompilation
import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Expressions.TargetFuel
import EvmCompiler.Locals.InteractionCleanupPreservation

namespace EvmCompiler
namespace Functions
namespace StackStatementPreservation

open StackRelation

@[simp] private theorem openEvalSeq_cast
    {left right : Nat} (h : left = right)
    (exprs : Locals.ExprSeq left) (state : Locals.Source.State) :
    Locals.InteractionSemantics.ExprSeq.openEval
        (cast (congrArg Locals.ExprSeq h) exprs) state =
      Locals.InteractionSemantics.ExprSeq.openEval exprs state := by
  cases h
  rfl

@[simp] theorem returnWord_openEval
    {name : Name} {state : Locals.Source.State} {value : Word}
    (hValue : state.vars name = some value) :
    Locals.InteractionSemantics.Expr.openEval
        (StackLowering.returnWord name) state =
      Simulation.Interaction.pure (state, [value]) := by
  cases value with
  | mk raw =>
      unfold StackLowering.returnWord
        Locals.InteractionSemantics.Expr.openEval
      simp [Locals.Source.Effectful.Expr.Control.eval,
        Locals.Source.Effectful.Expr.Control.ExprSeq.eval,
        Locals.InteractionSemantics.primitiveSemantics,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.vars,
        EvmCompiler.Simulation.Interaction.instMonad,
        Simulation.Interaction.pure, Simulation.Interaction.bind,
        Simulation.Interaction.bind_done_ok,
        hValue, Lower.zero, EvmYul.UInt256.add,
        EvmYul.UInt256.ofNat, Id.run]

theorem returnWords_openEval :
    ∀ (names : List Name) (state : Locals.Source.State)
      (values : List Word),
      Functions.Source.Store.lookupMany names state.vars = some values →
      Locals.InteractionSemantics.ExprSeq.openEval
          (StackLowering.returnWords names) state =
        Simulation.Interaction.pure (state, values)
  | [], state, values, hLookup => by
      simp [Functions.Source.Store.lookupMany] at hLookup
      subst values
      rfl
  | name :: rest, state, values, hLookup => by
      unfold Functions.Source.Store.lookupMany at hLookup
      cases hValue : state.vars name with
      | none => simp [hValue] at hLookup
      | some value =>
          cases hRest : Functions.Source.Store.lookupMany rest state.vars with
          | none => simp [hValue, hRest] at hLookup
          | some restValues =>
              simp [hValue, hRest] at hLookup
              subst values
              unfold StackLowering.returnWords
              let exprs : Locals.ExprSeq (1 + rest.length) :=
                Locals.ExprSeq.cons (StackLowering.returnWord name)
                  (StackLowering.returnWords rest)
              have hLen : 1 + rest.length = rest.length + 1 := by omega
              change
                Locals.InteractionSemantics.ExprSeq.openEval
                    (cast (congrArg Locals.ExprSeq hLen) exprs) state =
                  .done (.ok (state, value :: restValues))
              rw [openEvalSeq_cast hLen]
              have hHeadOpen := returnWord_openEval hValue
              have hTailOpen :=
                returnWords_openEval rest state restValues hRest
              unfold Locals.InteractionSemantics.Expr.openEval at hHeadOpen
              unfold Locals.InteractionSemantics.ExprSeq.openEval at hTailOpen ⊢
              simp only [exprs,
                Locals.Source.Effectful.Expr.Control.ExprSeq.eval,
                Locals.Source.Effectful.Expr.Control.eval]
              change
                (do
                  let headResult ←
                    Locals.Source.Effectful.Expr.Control.eval
                      Locals.InteractionSemantics.stateModel
                      Locals.InteractionSemantics.primitiveSemantics
                      (StackLowering.returnWord name) state
                  let tailResult ←
                    Locals.Source.Effectful.Expr.Control.ExprSeq.eval
                      Locals.InteractionSemantics.stateModel
                      Locals.InteractionSemantics.primitiveSemantics
                      (StackLowering.returnWords rest) headResult.1
                  pure (tailResult.1, headResult.2 ++ tailResult.2)) =
                    .done (.ok (state, value :: restValues))
              rw [hHeadOpen]
              change
                (do
                  let tailResult ←
                    Locals.Source.Effectful.Expr.Control.ExprSeq.eval
                      Locals.InteractionSemantics.stateModel
                      Locals.InteractionSemantics.primitiveSemantics
                      (StackLowering.returnWords rest) state
                  pure (tailResult.1, [value] ++ tailResult.2)) =
                    .done (.ok (state, value :: restValues))
              rw [hTailOpen]
              rfl

private theorem returnWords_openSupported_cast
    {left right : Nat} (h : left = right)
    {exprs : Locals.ExprSeq left}
    (hSupported :
      Locals.InteractionSemantics.ExprSeq.OpenSupported exprs) :
    Locals.InteractionSemantics.ExprSeq.OpenSupported
      (cast (congrArg Locals.ExprSeq h) exprs) := by
  cases h
  exact hSupported

theorem returnWords_openSupported :
    ∀ (names : List Name),
      Locals.InteractionSemantics.ExprSeq.OpenSupported
        (StackLowering.returnWords names)
  | [] => trivial
  | head :: tail => by
      unfold StackLowering.returnWords
      let exprs : Locals.ExprSeq (1 + tail.length) :=
        Locals.ExprSeq.cons (StackLowering.returnWord head)
          (StackLowering.returnWords tail)
      have hLen : 1 + tail.length = tail.length + 1 := by omega
      change
        Locals.InteractionSemantics.ExprSeq.OpenSupported
          (cast (congrArg Locals.ExprSeq hLen) exprs)
      apply returnWords_openSupported_cast hLen
      refine ⟨?_, returnWords_openSupported tail⟩
      simp [StackLowering.returnWord,
        Locals.InteractionSemantics.Expr.OpenSupported,
        Locals.InteractionSemantics.ExprSeq.OpenSupported,
        Locals.InteractionSemantics.Primitive.supportsOpen,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?]

abbrev FuelTruncated :=
  Locals.InteractionPreservation.Block.FuelTruncated

structure CtxCovers (source : Functions.Source.Ctx)
    (target : Locals.Ctx) : Prop where
  scope : ∀ {name : Name}, name ∈ target.layout → name ∈ source.scope

namespace CtxCovers

theorem prepend
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    (hCtx : CtxCovers source target) (name : Name) :
    CtxCovers { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) := by
  constructor
  intro candidate hCandidate
  rcases List.mem_cons.mp hCandidate with hName | hTail
  · exact List.mem_cons.mpr (.inl hName)
  · exact List.mem_cons.mpr (.inr (hCtx.scope hTail))

theorem afterTransition
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    (hCtx : CtxCovers source target)
    (transition : AllocationLayout.Transition)
    (hSource : target.layout = transition.source) :
    CtxCovers source
      (target.withLayout transition.schedule.target) := by
  constructor
  intro name hName
  have hTarget : name ∈ transition.schedule.target := by
    simpa [Locals.Ctx.withLayout] using hName
  have hRetained :
      name ∈ AllocationLayout.retained transition.source transition.live := by
    rwa [← transition.valid.2.1]
  have hOriginal : name ∈ transition.source :=
    (List.mem_filter.mp hRetained).1
  apply hCtx.scope
  rwa [hSource]

theorem afterOrdering
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    (hCtx : CtxCovers source target)
    (ordering : AllocationLayout.Ordering)
    (hSource : target.layout = ordering.source) :
    CtxCovers source (target.withLayout ordering.target) := by
  constructor
  intro name hName
  apply hCtx.scope
  have hTarget : name ∈ ordering.target := by
    simpa [Locals.Ctx.withLayout] using hName
  have hOrderingSource : name ∈ ordering.source :=
    ordering.target_mem_iff.mp hTarget
  rwa [← hSource] at hOrderingSource

end CtxCovers

structure BreakCtxCovers (source : Functions.Source.Ctx)
    (target : Locals.Ctx) (layout : Locals.Layout) : Prop where
  context : CtxCovers source target
  targetDepth : target.breakDepth? = some layout.length
  sourceCovers :
    ∃ scope,
      source.breakScope? = some scope ∧
        ∀ {name : Name}, name ∈ layout → name ∈ scope

structure ContinueCtxCovers (source : Functions.Source.Ctx)
    (target : Locals.Ctx) (layout : Locals.Layout) : Prop where
  context : CtxCovers source target
  targetDepth : target.continueDepth? = some layout.length
  sourceCovers :
    ∃ scope,
      source.continueScope? = some scope ∧
        ∀ {name : Name}, name ∈ layout → name ∈ scope

structure ControlCtxCovers (source : Functions.Source.Ctx)
    (target : Locals.Ctx) (targets : StackSchedule.ControlTargets) : Prop where
  context : CtxCovers source target
  breakTarget :
    ∀ {layout : Locals.Layout}, targets.brk? = some layout →
      BreakCtxCovers source target layout
  continueTarget :
    ∀ {layout : Locals.Layout}, targets.cont? = some layout →
      ContinueCtxCovers source target layout

namespace ControlCtxCovers

theorem afterOrdering
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    (hCtx : ControlCtxCovers source target targets)
    (ordering : AllocationLayout.Ordering)
    (hSource : target.layout = ordering.source) :
    ControlCtxCovers source (target.withLayout ordering.target) targets := by
  constructor
  · exact hCtx.context.afterOrdering ordering hSource
  · intro layout hTarget
    have hBreak := hCtx.breakTarget hTarget
    exact
      { context := hBreak.context.afterOrdering ordering hSource
        targetDepth := by
          simpa [Locals.Ctx.withLayout] using hBreak.targetDepth
        sourceCovers := hBreak.sourceCovers }
  · intro layout hTarget
    have hContinue := hCtx.continueTarget hTarget
    exact
      { context := hContinue.context.afterOrdering ordering hSource
        targetDepth := by
          simpa [Locals.Ctx.withLayout] using hContinue.targetDepth
        sourceCovers := hContinue.sourceCovers }

theorem afterTransition
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    (hCtx : ControlCtxCovers source target targets)
    (transition : AllocationLayout.Transition)
    (hSource : target.layout = transition.source) :
    ControlCtxCovers source
      (target.withLayout transition.schedule.target) targets := by
  constructor
  · exact hCtx.context.afterTransition transition hSource
  · intro layout hTarget
    have hBreak := hCtx.breakTarget hTarget
    exact
      { context := hBreak.context.afterTransition transition hSource
        targetDepth := by
          simpa [Locals.Ctx.withLayout] using hBreak.targetDepth
        sourceCovers := hBreak.sourceCovers }
  · intro layout hTarget
    have hContinue := hCtx.continueTarget hTarget
    exact
      { context := hContinue.context.afterTransition transition hSource
        targetDepth := by
          simpa [Locals.Ctx.withLayout] using hContinue.targetDepth
        sourceCovers := hContinue.sourceCovers }

theorem ofSameControlLayout
    {source : Functions.Source.Ctx} {before after : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    (hCtx : ControlCtxCovers source before targets)
    (hControl : Locals.Ctx.SameControl before after)
    (hLayout : after.layout = before.layout) :
    ControlCtxCovers source after targets := by
  have hContext : CtxCovers source after := by
    constructor
    intro name hName
    apply hCtx.context.scope
    rwa [hLayout] at hName
  constructor
  · exact hContext
  · intro layout hTarget
    have hBreak := hCtx.breakTarget hTarget
    exact
      { context := hContext
        targetDepth := by
          rw [← hControl.breakDepth]
          exact hBreak.targetDepth
        sourceCovers := hBreak.sourceCovers }
  · intro layout hTarget
    have hContinue := hCtx.continueTarget hTarget
    exact
      { context := hContext
        targetDepth := by
          rw [← hControl.continueDepth]
          exact hContinue.targetDepth
        sourceCovers := hContinue.sourceCovers }

theorem prepend
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    (hCtx : ControlCtxCovers source target targets) (name : Name) :
    ControlCtxCovers { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) targets := by
  constructor
  · exact hCtx.context.prepend name
  · intro layout hTarget
    have hBreak := hCtx.breakTarget hTarget
    exact
      { context := hBreak.context.prepend name
        targetDepth := by
          simpa [Locals.Ctx.withLayout] using hBreak.targetDepth
        sourceCovers := by
          simpa using hBreak.sourceCovers }
  · intro layout hTarget
    have hContinue := hCtx.continueTarget hTarget
    exact
      { context := hContinue.context.prepend name
        targetDepth := by
          simpa [Locals.Ctx.withLayout] using hContinue.targetDepth
        sourceCovers := by
          simpa using hContinue.sourceCovers }

end ControlCtxCovers

structure ReturnCtxCovers (source : Functions.Source.Ctx)
    (target : Locals.Ctx) (returnNames : List Name) : Prop where
  availability : target.leaveDepth?.isSome = source.leaveScope?.isSome
  sourceScope :
    ∀ {scope : List Name}, source.leaveScope? = some scope →
      ∀ {name : Name}, name ∈ returnNames → name ∈ scope
  targetDepth :
    source.leaveScope?.isSome → target.leaveDepth? = some 0
  targetRetc :
    source.leaveScope?.isSome → target.leaveRetc = returnNames.length

namespace ReturnCtxCovers

theorem afterLayout
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returnNames : List Name}
    (hCtx : ReturnCtxCovers source target returnNames)
    (layout : Locals.Layout) :
    ReturnCtxCovers source (target.withLayout layout) returnNames := by
  exact
    { availability := by
        simpa [Locals.Ctx.withLayout] using hCtx.availability
      sourceScope := hCtx.sourceScope
      targetDepth := by
        intro hLeave
        simpa [Locals.Ctx.withLayout] using hCtx.targetDepth hLeave
      targetRetc := by
        intro hLeave
        simpa [Locals.Ctx.withLayout] using hCtx.targetRetc hLeave }

theorem ofSameControl
    {source : Functions.Source.Ctx} {before after : Locals.Ctx}
    {returnNames : List Name}
    (hCtx : ReturnCtxCovers source before returnNames)
    (hControl : Locals.Ctx.SameControl before after) :
    ReturnCtxCovers source after returnNames := by
  exact
    { availability := by
        rw [← hControl.leaveDepth]
        exact hCtx.availability
      sourceScope := hCtx.sourceScope
      targetDepth := by
        intro hLeave
        rw [← hControl.leaveDepth]
        exact hCtx.targetDepth hLeave
      targetRetc := by
        intro hLeave
        rw [← hControl.leaveRetc]
        exact hCtx.targetRetc hLeave }

theorem prepend
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returnNames : List Name}
    (hCtx : ReturnCtxCovers source target returnNames) (name : Name) :
    ReturnCtxCovers { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) returnNames := by
  exact
    { availability := by
        simpa [Locals.Ctx.withLayout] using hCtx.availability
      sourceScope := by
        intro scope hScope candidate hCandidate
        exact hCtx.sourceScope (by simpa using hScope) hCandidate
      targetDepth := by
        intro hLeave
        simpa [Locals.Ctx.withLayout] using
          hCtx.targetDepth (by simpa using hLeave)
      targetRetc := by
        intro hLeave
        simpa [Locals.Ctx.withLayout] using
          hCtx.targetRetc (by simpa using hLeave) }

theorem withoutLoopControl
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returnNames : List Name}
    (hCtx : ReturnCtxCovers source target returnNames) :
    ReturnCtxCovers source.withoutLoopControl target.withoutLoopControl
      returnNames := by
  exact
    { availability := by
        simpa [Functions.Source.Ctx.withoutLoopControl,
          Locals.Ctx.withoutLoopControl] using hCtx.availability
      sourceScope := by
        intro scope hScope name hName
        exact hCtx.sourceScope (by simpa [Functions.Source.Ctx.withoutLoopControl]
          using hScope) hName
      targetDepth := by
        intro hLeave
        simpa [Functions.Source.Ctx.withoutLoopControl,
          Locals.Ctx.withoutLoopControl] using
          hCtx.targetDepth (by simpa [Functions.Source.Ctx.withoutLoopControl]
            using hLeave)
      targetRetc := by
        intro hLeave
        simpa [Functions.Source.Ctx.withoutLoopControl,
          Locals.Ctx.withoutLoopControl] using
          hCtx.targetRetc (by simpa [Functions.Source.Ctx.withoutLoopControl]
            using hLeave) }

theorem withLoopControl
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returnNames : List Name}
    (hCtx : ReturnCtxCovers source target returnNames) :
    ReturnCtxCovers
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) returnNames := by
  exact
    { availability := by
        simpa [Functions.Source.Ctx.withLoopControl,
          Locals.Ctx.withLoopControl] using hCtx.availability
      sourceScope := by
        intro scope hScope name hName
        exact hCtx.sourceScope (by simpa [Functions.Source.Ctx.withLoopControl]
          using hScope) hName
      targetDepth := by
        intro hLeave
        simpa [Functions.Source.Ctx.withLoopControl,
          Locals.Ctx.withLoopControl] using
          hCtx.targetDepth (by simpa [Functions.Source.Ctx.withLoopControl]
            using hLeave)
      targetRetc := by
        intro hLeave
        simpa [Functions.Source.Ctx.withLoopControl,
          Locals.Ctx.withLoopControl] using
          hCtx.targetRetc (by simpa [Functions.Source.Ctx.withLoopControl]
            using hLeave) }

end ReturnCtxCovers

structure RuntimeCtxCovers (source : Functions.Source.Ctx)
    (target : Locals.Ctx) (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (returns : List Structured.ReturnDest) : Prop where
  control : ControlCtxCovers source target targets
  returnContext : ReturnCtxCovers source target returnNames
  leaveReady : source.leaveScope?.isSome → returns ≠ []

namespace RuntimeCtxCovers

theorem context
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns) :
    CtxCovers source target :=
  hCtx.control.context

theorem breakTarget
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns)
    {layout : Locals.Layout} (hTarget : targets.brk? = some layout) :
    BreakCtxCovers source target layout :=
  hCtx.control.breakTarget hTarget

theorem continueTarget
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns)
    {layout : Locals.Layout} (hTarget : targets.cont? = some layout) :
    ContinueCtxCovers source target layout :=
  hCtx.control.continueTarget hTarget

theorem afterOrdering
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns)
    (ordering : AllocationLayout.Ordering)
    (hSource : target.layout = ordering.source) :
    RuntimeCtxCovers source (target.withLayout ordering.target) targets
      returnNames returns :=
  ⟨hCtx.control.afterOrdering ordering hSource,
    hCtx.returnContext.afterLayout ordering.target, hCtx.leaveReady⟩

theorem afterTransition
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns)
    (transition : AllocationLayout.Transition)
    (hSource : target.layout = transition.source) :
    RuntimeCtxCovers source
      (target.withLayout transition.schedule.target) targets returnNames
      returns :=
  ⟨hCtx.control.afterTransition transition hSource,
    hCtx.returnContext.afterLayout transition.schedule.target,
    hCtx.leaveReady⟩

theorem afterJoin
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns)
    (join : AllocationLayout.Join)
    (hSource : target.layout = join.source) :
    RuntimeCtxCovers source (target.withLayout join.target) targets returnNames
      returns := by
  have hRetainSource : target.layout = join.retain.source :=
    hSource.trans join.retainSource.symm
  have hRetained := hCtx.afterTransition join.retain hRetainSource
  have hOrderSource :
      (target.withLayout join.retain.target).layout = join.order.source := by
    simpa [Locals.Ctx.withLayout] using join.orderSource.symm
  have hOrdered := hRetained.afterOrdering join.order hOrderSource
  simpa [Locals.Ctx.withLayout, join.orderTarget] using hOrdered

theorem ofSameControlLayout
    {source : Functions.Source.Ctx} {before after : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source before targets returnNames returns)
    (hControl : Locals.Ctx.SameControl before after)
    (hLayout : after.layout = before.layout) :
    RuntimeCtxCovers source after targets returnNames returns :=
  ⟨hCtx.control.ofSameControlLayout hControl hLayout,
    hCtx.returnContext.ofSameControl hControl, hCtx.leaveReady⟩

theorem prepend
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns)
    (name : Name) :
    RuntimeCtxCovers { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) targets returnNames
      returns := by
  refine ⟨hCtx.control.prepend name, hCtx.returnContext.prepend name, ?_⟩
  simpa using hCtx.leaveReady

theorem withoutLoopControl
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns) :
    RuntimeCtxCovers source.withoutLoopControl target.withoutLoopControl {}
      returnNames returns := by
  refine ⟨?_, hCtx.returnContext.withoutLoopControl, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      intro name hName
      exact hCtx.context.scope hName
    · intro layout hTarget
      simp at hTarget
    · intro layout hTarget
      simp at hTarget
  · simpa [Functions.Source.Ctx.withoutLoopControl] using hCtx.leaveReady

theorem withLoopControl
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers source target targets returnNames returns) :
    RuntimeCtxCovers
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length)
      { brk? := some target.layout, cont? := some target.layout }
      returnNames returns := by
  have hContext :
      CtxCovers (source.withLoopControl source.scope source.scope)
        (target.withLoopControl target.layout.length) := by
    constructor
    intro name hName
    exact hCtx.context.scope hName
  refine ⟨?_, hCtx.returnContext.withLoopControl, ?_⟩
  · refine ⟨hContext, ?_, ?_⟩
    · intro layout hTarget
      have hLayout : target.layout = layout := Option.some.inj hTarget
      subst layout
      exact
        { context := hContext
          targetDepth := rfl
          sourceCovers := ⟨source.scope, rfl, hCtx.context.scope⟩ }
    · intro layout hTarget
      have hLayout : target.layout = layout := Option.some.inj hTarget
      subst layout
      exact
        { context := hContext
          targetDepth := rfl
          sourceCovers := ⟨source.scope, rfl, hCtx.context.scope⟩ }
  · simpa [Functions.Source.Ctx.withLoopControl] using hCtx.leaveReady

end RuntimeCtxCovers

structure RegularResultRel (targetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Functions.Source.Ctx)
    (target : Structured.Outcome) : Prop where
  sourceMode : source.1.mode = .regular
  targetMode : target.mode = .regular
  context : CtxCovers source.2 targetCtx
  state :
    StateRel targetCtx.layout suffix returns source.1.state target.state

abbrev RegularOutcomeRel (targetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (RegularResultRel targetCtx suffix returns)

inductive OpenResultRel (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    (Locals.Source.Effectful.Outcome Locals.Source.State ×
      Functions.Source.Ctx) →
    Structured.Outcome → Prop
  | regular {source sourceCtx target} :
      CtxCovers sourceCtx finalCtx →
      StateRel finalCtx.layout suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
        (Structured.Outcome.regular target)
  | brk {source sourceCtx target} :
      StateRel finalCtx.layout suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.brk source, sourceCtx)
        (Structured.Outcome.brk target)
  | cont {source sourceCtx target} :
      StateRel finalCtx.layout suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.cont source, sourceCtx)
        (Structured.Outcome.cont target)
  | leave {source sourceCtx target layout} :
      StateRel layout suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.leave source, sourceCtx)
        (Structured.Outcome.leave target)
  | halt {kind source sourceCtx target} :
      source.shared = target.evm.toSharedState →
      target.returns = returns →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.halt kind source, sourceCtx)
        (Structured.Outcome.halt kind target)

abbrev OpenOutcomeRel (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (OpenResultRel finalCtx suffix returns)

inductive ControlOpenResultRel (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    (Locals.Source.Effectful.Outcome Locals.Source.State ×
      Functions.Source.Ctx) →
    Structured.Outcome → Prop
  | regular {source sourceCtx target} :
      RuntimeCtxCovers sourceCtx finalCtx targets returnNames returns →
      StateRel finalCtx.layout suffix returns source target →
      ControlOpenResultRel targets returnNames finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
        (Structured.Outcome.regular target)
  | brk {source sourceCtx target layout} :
      targets.brk? = some layout →
      StateRel layout suffix returns source target →
      ControlOpenResultRel targets returnNames finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.brk source, sourceCtx)
        (Structured.Outcome.brk target)
  | cont {source sourceCtx target layout} :
      targets.cont? = some layout →
      StateRel layout suffix returns source target →
      ControlOpenResultRel targets returnNames finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.cont source, sourceCtx)
        (Structured.Outcome.cont target)
  | leave {source sourceCtx target} :
      StateRel returnNames.reverse suffix returns source target →
      ControlOpenResultRel targets returnNames finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.leave source, sourceCtx)
        (Structured.Outcome.leave target)
  | halt {kind source sourceCtx target} :
      source.shared = target.evm.toSharedState →
      target.returns = returns →
      ControlOpenResultRel targets returnNames finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.halt kind source, sourceCtx)
        (Structured.Outcome.halt kind target)

abbrev ControlOpenOutcomeRel (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (ControlOpenResultRel targets returnNames finalCtx suffix returns)

abbrev ControlScopedOutcomeRel (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (sourceCtx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (fun sourceOutcome targetOutcome =>
      ControlOpenResultRel targets returnNames finalCtx suffix returns
        (sourceOutcome, sourceCtx) targetOutcome)

/-- Re-expose a compiled lexical block over the canonical scoped-block
semantics used by recursive source control. -/
theorem controlBlockToScoped
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {body : Functions.Block}
    {code : List Expressions.Stmt}
    {finalCtx : Locals.Ctx}
    {returnNames : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hRun :
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
        (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
          sourceFuel (.block body) source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target)) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlScopedOutcomeRel targets returnNames finalCtx suffix returns sourceCtx)
      (Functions.InteractionSemantics.Block.openRunScoped sourceProgram
        sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel { stmts := code } target) := by
  rw [Functions.InteractionSemantics.Stmt.openRun_block_eq_scoped_pair] at hRun
  apply Simulation.Interaction.ForwardRel.mono
    (Simulation.Interaction.ForwardRel.bind_pure_left_inv hRun)
  intro sourceDone targetDone hDone
  cases sourceDone with
  | error _ =>
      cases targetDone with
      | error _ =>
          change ControlOpenOutcomeRel targets returnNames finalCtx suffix returns
            (.error _) (.error _) at hDone
          cases hDone with
          | error hError => exact .error hError
      | ok _ => cases hDone
  | ok _ =>
      cases targetDone with
      | error _ => cases hDone
      | ok _ =>
          change ControlOpenOutcomeRel targets returnNames finalCtx suffix returns
            (.ok (_, sourceCtx)) (.ok _) at hDone
          cases hDone with
          | ok hResult => exact .ok hResult

theorem controlBlockToScopedBlock
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {body : Functions.Block}
    {code : List Expressions.Stmt}
    {targetBody : Expressions.Block}
    {finalCtx : Locals.Ctx}
    {returnNames : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCode : code = targetBody.stmts)
    (hRun :
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
        (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
          sourceFuel (.block body) source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target)) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlScopedOutcomeRel targets returnNames finalCtx suffix returns sourceCtx)
      (Functions.InteractionSemantics.Block.openRunScoped sourceProgram
        sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel targetBody target) := by
  subst code
  cases targetBody
  exact controlBlockToScoped hRun

def ControlBlockPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (sourceBody : Functions.Block)
    (targetBody : Expressions.Block) : Prop :=
  ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState},
    Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
      targetBody.stmts →
    RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns →
    StateRel targetCtx.layout suffix returns source target →
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
      (Functions.InteractionSemantics.Block.openRun sourceProgram sourceCtx
        sourceFuel sourceBody source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        targetBody target)

inductive ForCoreResultRel (sourceCtx : Functions.Source.Ctx)
    (returnNames : List Name) (loopTargetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    (Locals.Source.Effectful.Outcome Locals.Source.State ×
      Functions.Source.Ctx) →
    Structured.Outcome → Prop
  | regular {sourceBefore sourceAfter target} :
      sourceAfter = sourceBefore.restrictTo sourceCtx.scope →
      StateRel loopTargetCtx.layout suffix returns sourceBefore target →
      ForCoreResultRel sourceCtx returnNames loopTargetCtx suffix returns
        (Locals.Source.Effectful.Outcome.regular sourceAfter, sourceCtx)
        (Structured.Outcome.regular target)
  | leave {source target} :
      StateRel returnNames.reverse suffix returns source target →
      ForCoreResultRel sourceCtx returnNames loopTargetCtx suffix returns
        (Locals.Source.Effectful.Outcome.leave source, sourceCtx)
        (Structured.Outcome.leave target)
  | halt {kind source target} :
      source.shared = target.evm.toSharedState →
      target.returns = returns →
      ForCoreResultRel sourceCtx returnNames loopTargetCtx suffix returns
        (Locals.Source.Effectful.Outcome.halt kind source, sourceCtx)
        (Structured.Outcome.halt kind target)

abbrev ForCoreOutcomeRel (sourceCtx : Functions.Source.Ctx)
    (returnNames : List Name) (loopTargetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (ForCoreResultRel sourceCtx returnNames loopTargetCtx suffix returns)

def ControlPointPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (code : List Expressions.Stmt) : Prop :=
  ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState},
    Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel code →
    RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns →
    StateRel targetCtx.layout suffix returns source target →
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel stmt source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel { stmts := code } target)

structure CompiledControlPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (code : List Expressions.Stmt)
    (finalLayout : Locals.Layout) : Prop where
  layout : finalCtx.layout = finalLayout
  preserves :
    ControlPointPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx stmt code

/-- Ordinary `leave` with an emitted return vector. Return expressions are
evaluated once, their exact values are preserved while the active local layout
is removed, and the resulting stack prefix is related to the source return
scope in canonical order. -/
theorem openRun_leave_returnCode
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetExtra : Nat)
    (returnNames scope : List Name)
    (returnCode cleanup : Structured.Code)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSourceScope : sourceCtx.leaveScope? = some scope)
    (hReturnsScope : ∀ name, name ∈ returnNames → name ∈ scope)
    (hAccess :
      StackAccess.ExprSeq.check? targetCtx.layout 0
          (StackLowering.returnWords returnNames) = some ())
    (hReturnCompile :
      Locals.ExprSeq.compileCode targetCtx 0
          (StackLowering.returnWords returnNames) = some returnCode)
    (hCleanup :
      targetCtx.cleanupToPreserving? returnNames.length 0 = some cleanup)
    (hReturnFrame : returns ≠ [])
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetExtra + 4)
        { stmts := [.code returnCode, .code cleanup, .leave] } target) := by
  have hNamesLayout :
      ∀ name : Name, name ∈ returnNames → name ∈ targetCtx.layout := by
    intro name hName
    exact StackLowering.returnWords_names_mem_of_check hAccess hName
  obtain ⟨values, hLookup⟩ :=
    hInitial.lookupMany_of_subset hNamesLayout
  have hReturnRel :=
    StackExpressionPreservation.openEvalSeq_compileCode
      (StackLowering.returnWords returnNames) targetCtx
      (StackLowering.returnWords_localsScoped hNamesLayout)
      (returnWords_openSupported returnNames) hReturnCompile hInitial
  have hReturnEval := returnWords_openEval returnNames source values hLookup
  rw [hReturnEval] at hReturnRel
  obtain ⟨targetAfterReturns, hReturnRun, hReturnDone⟩ :=
    Simulation.Interaction.Rel.done_left hReturnRel
  cases hReturnDone with
  | @ok sourceResult targetAfterReturns hReturnResult =>
      have hCleanupMany :
          Locals.Ctx.cleanupManyPreserving? targetCtx.layout.length
              returnNames.length = some cleanup := by
        unfold Locals.Ctx.cleanupToPreserving? at hCleanup
        simpa using hCleanup
      have hValuesLength : values.reverse.length = returnNames.length := by
        simpa using Functions.Source.Store.lookupMany_length hLookup
      have hDiscardedLength :
          (StackRelation.values source targetCtx.layout).length =
            targetCtx.layout.length := by
        simp [StackRelation.values]
      have hAfterStack :
          targetAfterReturns.evm.stack =
            values.reverse ++ StackRelation.values source targetCtx.layout ++
              suffix := by
        rw [hReturnResult.stack, hInitial.stack]
        simp [List.append_assoc]
      obtain
          ⟨targetFinal, hCleanupRun, hFinalStack,
            hCleanupShared, hCleanupReturns⟩ :=
        Locals.InteractionCleanupPreservation.openRun_cleanupManyPreserving?
          hCleanupMany hValuesLength hDiscardedLength hAfterStack
      have hRestrictedLookup :
          Functions.Source.Store.lookupMany returnNames
              (source.restrictTo scope).vars = some values := by
        simpa [Locals.Source.State.restrictTo] using
          Functions.Source.Store.lookupMany_restrictTo_of_mem
            hReturnsScope hLookup
      have hReverseLookup :
          Functions.Source.Store.lookupMany returnNames.reverse
              (source.restrictTo scope).vars = some values.reverse :=
        Functions.Source.Store.lookupMany_reverse hRestrictedLookup
      have hFinalRel :
          StateRel returnNames.reverse suffix returns
            (source.restrictTo scope) targetFinal := by
        apply StateRel.of_lookupMany
        · rw [hCleanupShared, hReturnResult.shared]
          rfl
        · exact
            hCleanupReturns.trans
              (hReturnResult.returns.trans hInitial.returns)
        · exact hReverseLookup
        · exact hFinalStack
      have hSourceRun :
          Functions.InteractionSemantics.Stmt.openRun
              sourceProgram sourceCtx sourceFuel .leave source =
            .done
              (.ok
                (Locals.Source.Effectful.Outcome.leave
                    (source.restrictTo scope),
                  sourceCtx)) := by
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
        simp only [Functions.Source.Effectful.Control.Stmt.run]
        rw [hSourceScope]
        simp [Functions.InteractionSemantics.stateModel,
          Locals.InteractionSemantics.stateModel,
          Locals.Source.Effectful.Ordinary.stateModel,
          Locals.Source.Effectful.StateModel.restrictTo,
          Simulation.Interaction.pure]
        rfl
      have hTargetRun :
          Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetExtra + 4)
              { stmts := [.code returnCode, .code cleanup, .leave] }
              target =
            .done (.ok (Structured.Outcome.leave targetFinal)) := by
        unfold Expressions.InteractionSemantics.Block.openRun
        simp only [Expressions.EffectSemantics.Control.Block.run,
          Expressions.EffectSemantics.Control.Stmt.run]
        unfold Structured.InteractionSemantics.Code.openRun at hReturnRun
        rw [hReturnRun]
        change
          Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetExtra + 3)
              { stmts := [.code cleanup, .leave] } targetAfterReturns =
            .done (.ok (Structured.Outcome.leave targetFinal))
        exact
          Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_leave
            targetProgram targetExtra cleanup targetAfterReturns targetFinal
              hCleanupRun (by
                rw [hCleanupReturns, hReturnResult.returns, hInitial.returns]
                exact hReturnFrame)
      rw [hSourceRun, hTargetRun]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact ControlOpenResultRel.leave hFinalRel

/-- Zero-result `leave` omits the return-expression statement and removes the
entire active local layout before executing the adjacent target `leave`. -/
theorem openRun_leave_noReturns
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetExtra : Nat)
    (scope : List Name) (cleanup : Structured.Code)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSourceScope : sourceCtx.leaveScope? = some scope)
    (hCleanup : targetCtx.cleanupToPreserving? 0 0 = some cleanup)
    (hReturnFrame : returns ≠ [])
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (ControlOpenOutcomeRel targets [] targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetExtra + 3)
        { stmts := [.code cleanup, .leave] } target) := by
  have hCleanupMany :
      Locals.Ctx.cleanupManyPreserving? targetCtx.layout.length 0 =
        some cleanup := by
    unfold Locals.Ctx.cleanupToPreserving? at hCleanup
    simpa using hCleanup
  have hDiscardedLength :
      (StackRelation.values source targetCtx.layout).length =
        targetCtx.layout.length := by
    simp [StackRelation.values]
  obtain
      ⟨targetFinal, hCleanupRun, hFinalStack,
        hCleanupShared, hCleanupReturns⟩ :=
    Locals.InteractionCleanupPreservation.openRun_cleanupManyPreserving?
      (values := [])
      (discarded := StackRelation.values source targetCtx.layout)
      (suffix := suffix) (target := target)
      hCleanupMany rfl hDiscardedLength (by
        simpa using hInitial.stack)
  have hFinalRel :
      StateRel [] suffix returns (source.restrictTo scope) targetFinal := by
    apply StateRel.of_lookupMany
    · rw [hCleanupShared, hInitial.shared]
      rfl
    · exact hCleanupReturns.trans hInitial.returns
    · rfl
    · simpa using hFinalStack
  have hSourceRun :
      Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .leave source =
        .done
          (.ok
            (Locals.Source.Effectful.Outcome.leave
                (source.restrictTo scope),
              sourceCtx)) := by
    unfold Functions.InteractionSemantics.Stmt.openRun
      Functions.Source.Canonical.Stmt.run
    simp only [Functions.Source.Effectful.Control.Stmt.run]
    rw [hSourceScope]
    simp [Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Locals.Source.Effectful.StateModel.restrictTo,
      Simulation.Interaction.pure]
    rfl
  have hTargetRun :
      Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetExtra + 3) { stmts := [.code cleanup, .leave] } target =
        .done (.ok (Structured.Outcome.leave targetFinal)) :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_leave
      targetProgram targetExtra cleanup target targetFinal hCleanupRun (by
        rw [hCleanupReturns, hInitial.returns]
        exact hReturnFrame)
  rw [hSourceRun, hTargetRun]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact ControlOpenResultRel.leave hFinalRel

/-- Compiler-owned ordinary `leave` preservation. The checked lowerer chooses
the canonical return-expression sequence, and ordinary Locals compilation
computes both its code and the preserving frame cleanup. -/
theorem compiledLeaveControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hAccess :
      StackAccess.ExprSeq.check? targetCtx.layout 0
          (StackLowering.returnWords returnNames) = some ())
    (hLowered :
      lowered = StackLowering.pushWordReturns returnNames ++ [.leave])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx finalCtx .leave code targetCtx.layout := by
  cases returnNames with
  | nil =>
      simp [StackLowering.pushWordReturns, Lower.pushReturns] at hLowered
      subst lowered
      have hLeaveCompile :=
        Locals.Block.compileOpen_single_components hCompile
      obtain ⟨depth, cleanup, hDepth, hCleanup, hCode, hFinal⟩ :=
        Locals.Stmt.compile_leave_components hLeaveCompile
      subst finalCtx
      refine ⟨rfl, ?_⟩
      unfold ControlPointPreserves
      intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
        hCtx hInitial
      cases hSourceScope : sourceCtx.leaveScope? with
      | none =>
          have hAvailability := hCtx.returnContext.availability
          rw [hDepth, hSourceScope] at hAvailability
          simp at hAvailability
      | some scope =>
          have hDepthZero :=
            hCtx.returnContext.targetDepth (by simp [hSourceScope])
          have hDepthEq : depth = 0 := by
            rw [hDepth] at hDepthZero
            exact Option.some.inj hDepthZero
          subst depth
          have hRetc :=
            hCtx.returnContext.targetRetc (by simp [hSourceScope])
          have hCleanupZero :
              targetCtx.cleanupToPreserving? 0 0 = some cleanup := by
            simpa [hRetc] using hCleanup
          have hLength := Expressions.TargetFuel.Covers.length_lt hFuel
          rw [hCode] at hLength
          simp [Locals.codeStmt] at hLength
          let targetExtra := targetFuel - 3
          have hFuelEq : targetFuel = targetExtra + 3 := by omega
          apply Simulation.Interaction.ForwardRel.ofRel
          rw [hCode, hFuelEq]
          simpa [Locals.codeStmt] using
            openRun_leave_noReturns sourceProgram targetProgram targets
              sourceCtx targetCtx sourceFuel targetExtra scope cleanup
              hSourceScope hCleanupZero
              (hCtx.leaveReady (by simp [hSourceScope])) hInitial
  | cons head tail =>
      obtain ⟨returnCode, hReturnCompile⟩ :=
        StackAccessLowering.ExprSeq.compileCode_of_check hAccess targetCtx rfl
      have hReturnBlock :
          Locals.Block.compileOpen targetCtx
              { stmts :=
                  [.exprs
                    (StackLowering.returnWords (head :: tail))] } =
            some ([.code returnCode], targetCtx) := by
        simp [Locals.Block.compileOpen, Locals.Stmt.compile, hReturnCompile,
          Locals.codeStmt]
      have hLoweredShape :
          lowered =
            [.exprs (StackLowering.returnWords (head :: tail))] ++
              [.leave] := by
        simpa [StackLowering.pushWordReturns, Lower.pushReturns] using hLowered
      rw [hLoweredShape] at hCompile
      obtain
          ⟨returnStmts, middleCtx, leaveStmts,
            hReturnBlock', hLeaveBlock, hWholeCode⟩ :=
        Locals.Block.compileOpen_append_components hCompile
      have hReturnPair :=
        Option.some.inj (hReturnBlock.symm.trans hReturnBlock')
      have hReturnStmts : [.code returnCode] = returnStmts :=
        congrArg Prod.fst hReturnPair
      have hMiddle : targetCtx = middleCtx :=
        congrArg Prod.snd hReturnPair
      subst returnStmts
      subst middleCtx
      have hLeaveCompile :=
        Locals.Block.compileOpen_single_components hLeaveBlock
      obtain ⟨depth, cleanup, hDepth, hCleanup, hLeaveCode, hFinal⟩ :=
        Locals.Stmt.compile_leave_components hLeaveCompile
      subst finalCtx
      have hCode :
          code = [.code returnCode, .code cleanup, .leave] := by
        rw [hWholeCode, hLeaveCode]
        simp [Locals.codeStmt]
      refine ⟨rfl, ?_⟩
      unfold ControlPointPreserves
      intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
        hCtx hInitial
      cases hSourceScope : sourceCtx.leaveScope? with
      | none =>
          have hAvailability := hCtx.returnContext.availability
          rw [hDepth, hSourceScope] at hAvailability
          simp at hAvailability
      | some scope =>
          have hDepthZero :=
            hCtx.returnContext.targetDepth (by simp [hSourceScope])
          have hDepthEq : depth = 0 := by
            rw [hDepth] at hDepthZero
            exact Option.some.inj hDepthZero
          subst depth
          have hRetc :=
            hCtx.returnContext.targetRetc (by simp [hSourceScope])
          have hCleanupReturns :
              targetCtx.cleanupToPreserving? (head :: tail).length 0 =
                some cleanup := by
            simpa [hRetc] using hCleanup
          have hLength := Expressions.TargetFuel.Covers.length_lt hFuel
          rw [hCode] at hLength
          simp at hLength
          let targetExtra := targetFuel - 4
          have hFuelEq : targetFuel = targetExtra + 4 := by omega
          apply Simulation.Interaction.ForwardRel.ofRel
          rw [hCode, hFuelEq]
          exact
            openRun_leave_returnCode sourceProgram targetProgram targets
              sourceCtx targetCtx sourceFuel targetExtra (head :: tail) scope
              returnCode cleanup hSourceScope
              (fun name hName =>
                hCtx.returnContext.sourceScope hSourceScope hName) hAccess
              hReturnCompile hCleanupReturns
              (hCtx.leaveReady (by simp [hSourceScope])) hInitial

/-- The semantic loop kernel composes the condition, scoped body, scoped post,
and the smaller recursive iteration. Compiler-owned scheduling and lowering
remain outside this statement-owner theorem. -/
theorem controlForLoop
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (returnNames : List Name)
    (sourceLoopCtx : Functions.Source.Ctx)
    (targetLoopCtx : Locals.Ctx)
    (cond : Functions.Expr 1) (condCode : Structured.Code)
    (post body : Functions.Block)
    (targetInit targetPost targetBody : Expressions.Block)
    (hCondScoped : Locals.Scope.ExprScoped targetLoopCtx.layout cond)
    (hCondSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode targetLoopCtx 0 cond = some condCode)
    (hBody :
      ControlPointPreserves sourceProgram targetProgram
        { brk? := some targetLoopCtx.layout,
          cont? := some targetLoopCtx.layout }
        returnNames
        (targetLoopCtx.withLoopControl targetLoopCtx.layout.length)
        (targetLoopCtx.withLoopControl targetLoopCtx.layout.length)
        (.block body) targetBody.stmts)
    (hPost :
      ControlPointPreserves sourceProgram targetProgram {}
        returnNames
        targetLoopCtx.withoutLoopControl
        targetLoopCtx.withoutLoopControl
        (.block post) targetPost.stmts) :
    ∀ (sourceFuel targetFuel : Nat)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        [.for_ targetInit (.code condCode) targetPost targetBody] →
      RuntimeCtxCovers sourceLoopCtx targetLoopCtx {} returnNames returns →
      StateRel targetLoopCtx.layout suffix returns source target →
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlScopedOutcomeRel {} returnNames targetLoopCtx suffix returns sourceLoopCtx)
        (Functions.InteractionSemantics.Stmt.openRunForLoop sourceProgram
          sourceLoopCtx cond sourceLoopCtx.withoutLoopControl post
          (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
            sourceLoopCtx.scope)
          body sourceFuel source)
        (Expressions.InteractionSemantics.Stmt.openRunForLoop targetProgram
          targetFuel (.code condCode) targetPost targetBody target) := by
  intro sourceFuel
  induction sourceFuel with
  | zero =>
      intro targetFuel suffix returns source target hFuel hCtx hInitial
      unfold Functions.InteractionSemantics.Stmt.openRunForLoop
        Functions.Source.Canonical.Stmt.runForLoop
        Functions.Source.Effectful.Control.Stmt.runForLoop
      exact .truncated rfl
  | succ fuel ih =>
      intro targetFuel suffix returns source target hFuel hCtx hInitial
      have hTargetLength := hFuel.length_lt
      have hTargetEq : targetFuel = (targetFuel - 1) + 1 := by omega
      rw [Functions.InteractionSemantics.Stmt.openRunForLoop_succ,
        hTargetEq,
        Expressions.InteractionSemantics.Stmt.openRunForLoop_succ]
      have hCondition :=
        StackExpressionPreservation.openEvalCondition_compileCode cond
          targetLoopCtx hCondScoped hCondSupported hCondCompile hInitial
      apply Simulation.Interaction.ForwardRel.bind
        (Simulation.Interaction.ForwardRel.ofRel hCondition)
      intro sourceCondition targetCondition hConditionResult
      rcases sourceCondition with ⟨sourceAfterCondition, sourceTrue⟩
      rcases targetCondition with ⟨targetAfterCondition, targetTrue⟩
      cases hConditionResult.condition
      cases sourceTrue with
      | false =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .regular hCtx
            (hConditionResult.state.restrictTo hCtx.context.scope)
      | true =>
          simp only [Prod.snd, if_true, Prod.fst]
          have hBodyFuel :=
            Expressions.TargetFuel.Covers.for_body_after_one hFuel
          have hPostFuel :=
            Expressions.TargetFuel.Covers.for_post_after_one hFuel
          have hLoopFuel :=
            Expressions.TargetFuel.Covers.for_loop_after_one hFuel
          have hBodyCtx := hCtx.withLoopControl
          have hBodyInitial :
              StateRel
                (targetLoopCtx.withLoopControl
                  targetLoopCtx.layout.length).layout
                suffix returns sourceAfterCondition targetAfterCondition := by
            simpa [Locals.Ctx.withLoopControl] using hConditionResult.state
          have hBodyRun :=
            controlBlockToScopedBlock (targetBody := targetBody)
              rfl
              (hBody
                (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
                  sourceLoopCtx.scope)
                fuel (targetFuel - 1) hBodyFuel hBodyCtx hBodyInitial)
          apply Simulation.Interaction.ForwardRel.bind
            (targetRel := fun sourceOutcome targetOutcome =>
              ControlOpenResultRel {} returnNames targetLoopCtx suffix returns
                (sourceOutcome, sourceLoopCtx) targetOutcome)
            (leftNext := fun bodyOutcome =>
              match bodyOutcome.mode with
              | .brk =>
                  Simulation.Interaction.pure
                    (Locals.Source.Effectful.Outcome.regular
                      bodyOutcome.state)
              | .regular | .cont =>
                  Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Block.openRunScoped
                      sourceProgram sourceLoopCtx.withoutLoopControl post fuel
                      bodyOutcome.state)
                    (fun postOutcome =>
                      match postOutcome.mode with
                      | .regular =>
                          Functions.InteractionSemantics.Stmt.openRunForLoop
                            sourceProgram sourceLoopCtx cond
                            sourceLoopCtx.withoutLoopControl post
                            (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
                              sourceLoopCtx.scope)
                            body fuel postOutcome.state
                      | .brk | .cont =>
                          Simulation.Interaction.error .InvalidInstruction
                      | .leave | .halt _ =>
                          Simulation.Interaction.pure postOutcome)
              | .leave | .halt _ =>
                  Simulation.Interaction.pure bodyOutcome)
            (rightNext := fun bodyOutcome =>
              match bodyOutcome.mode with
              | .brk =>
                  Simulation.Interaction.pure
                    (Structured.Outcome.regular bodyOutcome.state)
              | .regular | .cont =>
                  Simulation.Interaction.bind
                    (Expressions.InteractionSemantics.Block.openRun
                      targetProgram (targetFuel - 1) targetPost
                      bodyOutcome.state)
                    (fun postOutcome =>
                      match postOutcome.mode with
                      | .regular =>
                          Expressions.InteractionSemantics.Stmt.openRunForLoop
                            targetProgram (targetFuel - 1) (.code condCode)
                            targetPost targetBody postOutcome.state
                      | .brk | .cont =>
                          Simulation.Interaction.error .InvalidInstruction
                      | .leave | .halt _ =>
                          Simulation.Interaction.pure postOutcome)
              | .leave | .halt _ =>
                  Simulation.Interaction.pure bodyOutcome)
            hBodyRun
          intro sourceBody targetBodyOutcome hBodyResult
          have continueAfterBody :
              ∀ {sourceAfterBody : Locals.Source.State}
                {targetAfterBody : Structured.RunState},
                StateRel targetLoopCtx.layout suffix returns
                  sourceAfterBody targetAfterBody →
                Simulation.Interaction.ForwardRel FuelTruncated
                  (ControlScopedOutcomeRel {} returnNames targetLoopCtx suffix returns
                    sourceLoopCtx)
                  (Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Block.openRunScoped
                      sourceProgram sourceLoopCtx.withoutLoopControl post fuel
                      sourceAfterBody)
                    (fun postOutcome =>
                      match postOutcome.mode with
                      | .regular =>
                          Functions.InteractionSemantics.Stmt.openRunForLoop
                            sourceProgram sourceLoopCtx cond
                            sourceLoopCtx.withoutLoopControl post
                            (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
                              sourceLoopCtx.scope)
                            body fuel postOutcome.state
                      | .brk | .cont =>
                          Simulation.Interaction.error .InvalidInstruction
                      | .leave | .halt _ =>
                          Simulation.Interaction.pure postOutcome))
                  (Simulation.Interaction.bind
                    (Expressions.InteractionSemantics.Block.openRun
                      targetProgram (targetFuel - 1) targetPost
                      targetAfterBody)
                    (fun postOutcome =>
                      match postOutcome.mode with
                      | .regular =>
                          Expressions.InteractionSemantics.Stmt.openRunForLoop
                            targetProgram (targetFuel - 1) (.code condCode)
                            targetPost targetBody postOutcome.state
                      | .brk | .cont =>
                          Simulation.Interaction.error .InvalidInstruction
                      | .leave | .halt _ =>
                          Simulation.Interaction.pure postOutcome)) := by
            intro sourceAfterBody targetAfterBody hAfterBody
            have hPostCtx := hCtx.withoutLoopControl
            have hPostInitial :
                StateRel targetLoopCtx.withoutLoopControl.layout suffix returns
                  sourceAfterBody targetAfterBody := by
              simpa [Locals.Ctx.withoutLoopControl] using hAfterBody
            have hPostRun :=
              controlBlockToScopedBlock (targetBody := targetPost)
                rfl
                (hPost sourceLoopCtx.withoutLoopControl fuel
                  (targetFuel - 1) hPostFuel hPostCtx hPostInitial)
            apply Simulation.Interaction.ForwardRel.bind hPostRun
            intro sourcePost targetPostOutcome hPostResult
            cases hPostResult with
            | regular _hPostCtx hPostState =>
                apply ih (targetFuel - 1) hLoopFuel hCtx
                simpa [Locals.Ctx.withoutLoopControl] using hPostState
            | brk hNoTarget _hPostState => simp at hNoTarget
            | cont hNoTarget _hPostState => simp at hNoTarget
            | leave hPostState =>
                exact .done (.ok (.leave hPostState))
            | halt hShared hReturns =>
                exact .done (.ok (.halt hShared hReturns))
          cases hBodyResult with
          | regular _hBodyCtx hBodyState =>
              apply continueAfterBody
              simpa [Locals.Ctx.withLoopControl] using hBodyState
          | brk hBreakTarget hBodyState =>
              have hLayout := Option.some.inj hBreakTarget
              subst hLayout
              exact .done (.ok (.regular hCtx hBodyState))
          | cont hContinueTarget hBodyState =>
              have hLayout := Option.some.inj hContinueTarget
              subst hLayout
              apply continueAfterBody hBodyState
          | leave hBodyState =>
              exact .done (.ok (.leave hBodyState))
          | halt hShared hReturns =>
              exact .done (.ok (.halt hShared hReturns))

/-- The outer `for` wrapper composes initializer execution with the recursive
loop kernel. Its regular result deliberately retains a pre-restriction source
witness until the allocator-owned exit transition removes initializer locals. -/
theorem controlForCore
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (sourceCtx : Functions.Source.Ctx)
    (targetCtx loopTargetCtx : Locals.Ctx)
    (init : Functions.Block)
    (cond : Functions.Expr 1) (condCode : Structured.Code)
    (post body : Functions.Block)
    (targetInit targetPost targetBody : Expressions.Block)
    (hCondScoped : Locals.Scope.ExprScoped loopTargetCtx.layout cond)
    (hCondSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode loopTargetCtx 0 cond = some condCode)
    (hInit :
      ControlBlockPreserves sourceProgram targetProgram {} returnNames
        targetCtx.withoutLoopControl loopTargetCtx init targetInit)
    (hBody :
      ControlPointPreserves sourceProgram targetProgram
        { brk? := some loopTargetCtx.layout,
          cont? := some loopTargetCtx.layout }
        returnNames
        (loopTargetCtx.withLoopControl loopTargetCtx.layout.length)
        (loopTargetCtx.withLoopControl loopTargetCtx.layout.length)
        (.block body) targetBody.stmts)
    (hPost :
      ControlPointPreserves sourceProgram targetProgram {}
        returnNames
        loopTargetCtx.withoutLoopControl loopTargetCtx.withoutLoopControl
        (.block post) targetPost.stmts) :
    ∀ (sourceFuel targetFuel : Nat)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        [.for_ targetInit (.code condCode) targetPost targetBody] →
      RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.ForwardRel FuelTruncated
        (ForCoreOutcomeRel sourceCtx returnNames loopTargetCtx suffix returns)
        (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
          sourceFuel (.for_ init cond post body) source)
        (Expressions.InteractionSemantics.Stmt.openRun targetProgram targetFuel
          (.for_ targetInit (.code condCode) targetPost targetBody) target) := by
  intro sourceFuel
  cases sourceFuel with
  | zero =>
      intro targetFuel suffix returns source target hFuel hCtx hInitial
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run
        Functions.Source.Effectful.Control.Stmt.run
      exact .truncated rfl
  | succ fuel =>
      intro targetFuel suffix returns source target hFuel hCtx hInitial
      have hTargetLength := hFuel.length_lt
      have hTargetEq : targetFuel = (targetFuel - 1) + 1 := by omega
      rw [Functions.InteractionSemantics.Stmt.openRun_for, hTargetEq,
        Expressions.InteractionSemantics.Stmt.openRun_for]
      have hInitFuelSmall :=
        Expressions.TargetFuel.Covers.for_init_after_two hFuel
      have hInitFuel :
          Expressions.TargetFuel.Covers targetProgram fuel (targetFuel - 1)
            targetInit.stmts :=
        hInitFuelSmall.weaken_target (by omega)
      have hLoopFuelSmall :=
        Expressions.TargetFuel.Covers.for_loop_after_two hFuel
      have hLoopFuel :
          Expressions.TargetFuel.Covers targetProgram fuel (targetFuel - 1)
            [.for_ targetInit (.code condCode) targetPost targetBody] :=
        hLoopFuelSmall.weaken_target (by omega)
      have hInitCtx := hCtx.withoutLoopControl
      have hInitInitial :
          StateRel targetCtx.withoutLoopControl.layout suffix returns
            source target := by
        simpa [Locals.Ctx.withoutLoopControl] using hInitial
      have hInitRun :=
        hInit sourceCtx.withoutLoopControl fuel (targetFuel - 1) hInitFuel
          hInitCtx hInitInitial
      apply Simulation.Interaction.ForwardRel.bind hInitRun
      intro sourceInit targetInitOutcome hInitResult
      cases hInitResult with
      | @regular _sourceAfterInit sourceAfterInitCtx _targetAfterInit hLoopCtx
          hInitState =>
          simp only [Locals.Source.Effectful.Outcome.regular,
            Structured.Outcome.regular, Structured.OutcomeT.regular]
          have hLoopRun :=
            controlForLoop sourceProgram targetProgram returnNames
              sourceAfterInitCtx
              loopTargetCtx cond condCode post body targetInit targetPost
              targetBody hCondScoped hCondSupported hCondCompile hBody hPost
              fuel (targetFuel - 1) hLoopFuel hLoopCtx hInitState
          change Simulation.Interaction.ForwardRel FuelTruncated
            (ForCoreOutcomeRel sourceCtx returnNames loopTargetCtx suffix returns) _
            (Expressions.InteractionSemantics.Stmt.openRunForLoop targetProgram
              (targetFuel - 1) (.code condCode) targetPost targetBody
              _targetAfterInit)
          rw [← Simulation.Interaction.bind_pure
            (Expressions.InteractionSemantics.Stmt.openRunForLoop targetProgram
              (targetFuel - 1) (.code condCode) targetPost targetBody
              _targetAfterInit)]
          apply Simulation.Interaction.ForwardRel.bind hLoopRun
          intro sourceLoop targetLoop hLoopResult
          cases hLoopResult with
          | regular _hFinalCtx hLoopState =>
              exact .done (.ok (.regular rfl hLoopState))
          | brk hNoTarget _hLoopState => simp at hNoTarget
          | cont hNoTarget _hLoopState => simp at hNoTarget
          | leave hLoopState =>
              exact .done (.ok (.leave hLoopState))
          | halt hShared hReturns =>
              exact .done (.ok (.halt hShared hReturns))
      | brk hNoTarget _hInitState => simp at hNoTarget
      | cont hNoTarget _hInitState => simp at hNoTarget
      | leave hInitState =>
          exact .done (.ok (.leave hInitState))
      | halt hShared hReturns =>
          exact .done (.ok (.halt hShared hReturns))

/-- Discharge the compiler's lexical cleanup after a complete `for`, removing
initializer locals and restoring the enclosing runtime context. -/
theorem controlFor
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx loopTargetCtx : Locals.Ctx)
    (init : Functions.Block)
    (cond : Functions.Expr 1) (condCode : Structured.Code)
    (post body : Functions.Block)
    (targetInit targetPost targetBody : Expressions.Block)
    (outerCleanup : Structured.Code)
    (hOuterLayout :
      ∃ pre, loopTargetCtx.layout = pre ++ targetCtx.layout)
    (hOuterCleanup :
      loopTargetCtx.cleanupTo? targetCtx.layout.length = some outerCleanup)
    (hCondScoped : Locals.Scope.ExprScoped loopTargetCtx.layout cond)
    (hCondSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode loopTargetCtx 0 cond = some condCode)
    (hInit :
      ControlBlockPreserves sourceProgram targetProgram {} returnNames
        targetCtx.withoutLoopControl loopTargetCtx init targetInit)
    (hBody :
      ControlPointPreserves sourceProgram targetProgram
        { brk? := some loopTargetCtx.layout,
          cont? := some loopTargetCtx.layout }
        returnNames
        (loopTargetCtx.withLoopControl loopTargetCtx.layout.length)
        (loopTargetCtx.withLoopControl loopTargetCtx.layout.length)
        (.block body) targetBody.stmts)
    (hPost :
      ControlPointPreserves sourceProgram targetProgram {}
        returnNames
        loopTargetCtx.withoutLoopControl loopTargetCtx.withoutLoopControl
        (.block post) targetPost.stmts) :
    ControlPointPreserves sourceProgram targetProgram targets returnNames
      targetCtx targetCtx (.for_ init cond post body)
      ([.for_ targetInit (.code condCode) targetPost targetBody] ++
        Locals.codeStmt outerCleanup) := by
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel hCtx
    hInitial
  have hTargetLength := hFuel.length_lt
  have hTargetLength' : 2 < targetFuel := by
    simpa [Locals.codeStmt] using hTargetLength
  have hCoreFuel :=
    Expressions.TargetFuel.Covers.head_after_one_append
      (left := [.for_ targetInit (.code condCode) targetPost targetBody])
      (right := Locals.codeStmt outerCleanup)
      (by simp [Locals.codeStmt]) hFuel
  have hCore :=
    controlForCore sourceProgram targetProgram targets returnNames sourceCtx
      targetCtx
      loopTargetCtx init cond condCode post body targetInit targetPost targetBody
      hCondScoped hCondSupported hCondCompile hInit hBody hPost sourceFuel
      (targetFuel - 1) hCoreFuel hCtx hInitial
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  have hTargetEq : targetFuel = (targetFuel - 2) + 2 := by omega
  have hInnerEq : (targetFuel - 2) + 1 = targetFuel - 1 := by omega
  rw [hTargetEq,
    Expressions.InteractionSemantics.Block.openRun_single_stmt, hInnerEq]
  apply Simulation.Interaction.ForwardRel.bind_right hCore
  intro sourceDone targetDone hResult
  cases hResult with
  | error hError =>
      exact .done (.error hError)
  | ok hCoreResult =>
      cases hCoreResult with
      | @regular sourceBefore sourceAfter targetAfter hRestricted hState =>
          simp only [Structured.Outcome.regular,
            Structured.OutcomeT.regular]
          have hResidualFuel :
              targetFuel - 2 + 2 -
                  [Expressions.Stmt.for_ targetInit (.code condCode) targetPost
                    targetBody].length =
                targetFuel - 1 := by
            simp only [List.length_singleton]
            omega
          rw [hResidualFuel]
          change Simulation.Interaction.ForwardRel FuelTruncated
            (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
            (Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular sourceAfter, sourceCtx))
            (Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetFuel - 1) { stmts := Locals.codeStmt outerCleanup }
              targetAfter)
          obtain ⟨pre, hLayout⟩ := hOuterLayout
          have hSuffix :
              targetCtx.layout =
                loopTargetCtx.layout.drop
                  (loopTargetCtx.layout.length - targetCtx.layout.length) := by
            rw [hLayout]
            simp
          obtain ⟨finalTarget, hCleanupRun, hFinalState⟩ :=
            StackTransitionPreservation.Cleanup.openRun rfl hSuffix
              hOuterCleanup hState
          have hCleanupFuel : 2 ≤ targetFuel - 1 := by omega
          have hTargetCleanup :=
            Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
              targetProgram (targetFuel - 1)
                outerCleanup _ finalTarget hCleanupFuel hCleanupRun
          have hTargetCleanup' :
              Expressions.InteractionSemantics.Block.openRun targetProgram
                  (targetFuel - 1)
                  { stmts := Locals.codeStmt outerCleanup } targetAfter =
                .done (.ok (Structured.Outcome.regular finalTarget)) := by
            simpa [Locals.codeStmt] using hTargetCleanup
          rw [hTargetCleanup']
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          rw [hRestricted]
          exact .regular hCtx
            (hFinalState.restrictTo hCtx.context.scope)
      | leave hState =>
          simp only [Structured.Outcome.leave,
            Structured.OutcomeT.leave]
          exact .done (.ok (.leave hState))
      | halt hShared hReturns =>
          simp only [Structured.Outcome.halt,
            Structured.OutcomeT.halt]
          exact .done (.ok (.halt hShared hReturns))

theorem RegularResultRel.toOpen
    {targetCtx : Locals.Ctx} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Functions.Source.Ctx}
    {target : Structured.Outcome}
    (hRel : RegularResultRel targetCtx suffix returns source target) :
    OpenResultRel targetCtx suffix returns source target := by
  rcases source with ⟨⟨sourceState, sourceMode⟩, sourceCtx⟩
  rcases target with ⟨targetState, targetMode⟩
  cases hRel.sourceMode
  cases hRel.targetMode
  exact .regular hRel.context hRel.state

theorem regularRelToControl
    {targets : StackSchedule.ControlTargets}
    {finalCtx : Locals.Ctx} {suffix : List Word}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx)}
    {targetRun : Simulation.Interaction EVMException Structured.Outcome}
    (hRun :
      Simulation.Interaction.Rel
        (RegularOutcomeRel finalCtx suffix returns) sourceRun targetRun)
    (hControl :
      Simulation.Interaction.AllDone
        (fun result =>
          match result with
          | .error _ => True
          | .ok sourceResult =>
              RuntimeCtxCovers sourceResult.2 finalCtx targets returnNames returns)
        sourceRun) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
      sourceRun targetRun := by
  apply Simulation.Interaction.ForwardRel.ofRel
  apply Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.strengthen_left hRun hControl)
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRegular, hSourceControl⟩
  cases hRegular with
  | error hError =>
      exact Simulation.Interaction.ExceptRel.error hError
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨⟨source, sourceMode⟩, sourceCtx⟩
      rcases targetResult with ⟨target, targetMode⟩
      cases hResult.sourceMode
      cases hResult.targetMode
      exact Simulation.Interaction.ExceptRel.ok
        (.regular hSourceControl hResult.state)

theorem openRelToControl
    {targets : StackSchedule.ControlTargets}
    {finalCtx : Locals.Ctx} {suffix : List Word}
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx)}
    {targetRun : Simulation.Interaction EVMException Structured.Outcome}
    (hRun :
      Simulation.Interaction.Rel
        (OpenOutcomeRel finalCtx suffix returns) sourceRun targetRun)
    (hControl :
      Simulation.Interaction.AllDone
        (fun result =>
          match result with
          | .error _ => True
          | .ok sourceResult =>
              match sourceResult.1.mode with
              | .regular =>
                  RuntimeCtxCovers sourceResult.2 finalCtx targets returnNames returns
              | .brk | .cont => False
              | .leave => False
              | .halt _ => True)
        sourceRun) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
      sourceRun targetRun := by
  apply Simulation.Interaction.ForwardRel.ofRel
  apply Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.strengthen_left hRun hControl)
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hOpen, hSourceControl⟩
  cases hOpen with
  | error hError => exact Simulation.Interaction.ExceptRel.error hError
  | ok hResult =>
      apply Simulation.Interaction.ExceptRel.ok
      cases hResult with
      | regular _hContext hState => exact .regular hSourceControl hState
      | brk _hState => exact False.elim hSourceControl
      | cont _hState => exact False.elim hSourceControl
      | leave _hState => exact False.elim hSourceControl
      | halt hShared hReturns => exact .halt hShared hReturns

theorem openRun_expr_controlCtx
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx) (sourceFuel : Nat)
    (expr : Functions.Expr 0) (source : Locals.Source.State)
    (targets : StackSchedule.ControlTargets) (finalCtx : Locals.Ctx)
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers sourceCtx finalCtx targets returnNames returns) :
    Simulation.Interaction.AllDone
      (fun result =>
        match result with
        | .error _ => True
        | .ok sourceResult =>
            RuntimeCtxCovers sourceResult.2 finalCtx targets returnNames returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Functions.InteractionSemantics.stateModel
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial
      (Locals.InteractionSemantics.Expr.openEval expr source))
  · intro _error _hTrivial
    trivial
  · intro _result _hTrivial
    exact .done hCtx

theorem openRun_let_controlCtx
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx) (sourceFuel : Nat)
    (name : Name) (value : Functions.Expr 1)
    (source : Locals.Source.State)
    (targets : StackSchedule.ControlTargets) (finalCtx : Locals.Ctx)
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx :
      RuntimeCtxCovers
        { sourceCtx with scope := name :: sourceCtx.scope }
        finalCtx targets returnNames returns) :
    Simulation.Interaction.AllDone
      (fun result =>
        match result with
        | .error _ => True
        | .ok sourceResult =>
            RuntimeCtxCovers sourceResult.2 finalCtx targets returnNames returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name value) source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial
      (Locals.InteractionSemantics.Expr.openEvalOne value source))
  · intro _error _hTrivial
    trivial
  · intro _result _hTrivial
    exact .done hCtx

theorem openRun_assign_controlCtx
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx) (sourceFuel : Nat)
    (name : Name) (value : Functions.Expr 1)
    (source : Locals.Source.State)
    (targets : StackSchedule.ControlTargets) (finalCtx : Locals.Ctx)
    {returnNames : List Name}
    {returns : List Structured.ReturnDest}
    (hCtx : RuntimeCtxCovers sourceCtx finalCtx targets returnNames returns) :
    Simulation.Interaction.AllDone
      (fun result =>
        match result with
        | .error _ => True
        | .ok sourceResult =>
            RuntimeCtxCovers sourceResult.2 finalCtx targets returnNames returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name value) source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  by_cases hContains :
      (Functions.InteractionSemantics.stateModel.vars source).contains name
  · simp only [hContains, Bool.true_eq, ↓reduceIte]
    apply Simulation.Interaction.AllDone.bind
      (Simulation.Interaction.AllDone.trivial
        (Locals.InteractionSemantics.Expr.openEvalOne value source))
    · intro _error _hTrivial
      trivial
    · intro _result _hTrivial
      exact .done hCtx
  · simp [hContains]
    exact .done trivial

theorem controlThenTransition
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx)}
    {coreCode : List Expressions.Stmt}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (targetFuel : Nat)
    (hSource : targetCtx.layout = transition.source)
    (hFuel :
      coreCode.length + transition.schedule.promotions.length + 1 <
        targetFuel)
    (hCore :
      Simulation.Interaction.Rel
        (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := coreCode } target)) :
    ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
      Simulation.Interaction.Rel
        (ControlOpenOutcomeRel targets returnNames
          (targetCtx.withLayout transition.schedule.target) suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel
          { stmts :=
              coreCode ++
                (artifact.promotionCodes.map Expressions.Stmt.code ++
                  [Expressions.Stmt.code artifact.cleanup]) }
          target) := by
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition hSource
  refine ⟨artifact, ?_⟩
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  rw [← Simulation.Interaction.bind_pure sourceRun]
  apply Simulation.Interaction.Rel.bind hCore
  intro sourceResult targetResult hResult
  cases hResult with
  | regular hCtx hState =>
      have hTransitionFuel :
          artifact.promotionCodes.length + 1 <
            targetFuel - coreCode.length := by
        rw [artifact.codes.code_length]
        omega
      obtain ⟨finalTarget, hTransitionRun, hFinalState⟩ :=
        artifact.blockOpenRun targetProgram
          (targetFuel - coreCode.length) hTransitionFuel hState
      simp only [Locals.Source.Effectful.Outcome.regular,
        Structured.Outcome.regular, Structured.OutcomeT.regular]
      rw [hTransitionRun]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .regular (hCtx.afterTransition transition hSource) hFinalState
  | brk hTarget hState =>
      simp only [Locals.Source.Effectful.Outcome.brk,
        Structured.Outcome.brk, Structured.OutcomeT.brk]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .brk hTarget hState
  | cont hTarget hState =>
      simp only [Locals.Source.Effectful.Outcome.cont,
        Structured.Outcome.cont, Structured.OutcomeT.cont]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .cont hTarget hState
  | leave hState =>
      simp only [Locals.Source.Effectful.Outcome.leave,
        Structured.Outcome.leave, Structured.OutcomeT.leave]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .leave hState
  | halt hShared hReturns =>
      simp only [Locals.Source.Effectful.Outcome.halt,
        Structured.Outcome.halt, Structured.OutcomeT.halt]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .halt hShared hReturns

theorem controlThenTransitionForward
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx)}
    {coreCode : List Expressions.Stmt}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (targetFuel : Nat)
    (hSource : targetCtx.layout = transition.source)
    (hFuel :
      coreCode.length + transition.schedule.promotions.length + 1 <
        targetFuel)
    (hCore :
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := coreCode } target)) :
    ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames
          (targetCtx.withLayout transition.schedule.target) suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel
          { stmts :=
              coreCode ++
                (artifact.promotionCodes.map Expressions.Stmt.code ++
                  [Expressions.Stmt.code artifact.cleanup]) }
          target) := by
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition hSource
  refine ⟨artifact, ?_⟩
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_right hCore
  intro sourceDone targetDone hResult
  cases hResult with
  | error hError =>
      apply Simulation.Interaction.ForwardRel.done
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hResult =>
      cases hResult with
      | regular hCtx hState =>
          simp only [Locals.Source.Effectful.Outcome.regular,
            Structured.Outcome.regular, Structured.OutcomeT.regular]
          have hTransitionFuel :
              artifact.promotionCodes.length + 1 <
                targetFuel - coreCode.length := by
            rw [artifact.codes.code_length]
            omega
          obtain ⟨finalTarget, hTransitionRun, hFinalState⟩ :=
            artifact.blockOpenRun targetProgram
              (targetFuel - coreCode.length) hTransitionFuel hState
          rw [hTransitionRun]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .regular (hCtx.afterTransition transition hSource) hFinalState
      | brk hTarget hState =>
          simp only [Locals.Source.Effectful.Outcome.brk,
            Structured.Outcome.brk, Structured.OutcomeT.brk]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .brk hTarget hState
      | cont hTarget hState =>
          simp only [Locals.Source.Effectful.Outcome.cont,
            Structured.Outcome.cont, Structured.OutcomeT.cont]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .cont hTarget hState
      | leave hState =>
          simp only [Locals.Source.Effectful.Outcome.leave,
            Structured.Outcome.leave, Structured.OutcomeT.leave]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .leave hState
      | halt hShared hReturns =>
          simp only [Locals.Source.Effectful.Outcome.halt,
            Structured.Outcome.halt, Structured.OutcomeT.halt]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .halt hShared hReturns

theorem controlAppendEmptyCode
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx : Locals.Ctx)
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx)}
    {code : List Expressions.Stmt}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (targetFuel : Nat)
    (hFuel : code.length + 1 < targetFuel)
    (hRun :
      Simulation.Interaction.Rel
        (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target)) :
    Simulation.Interaction.Rel
      (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
      sourceRun
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel { stmts := code ++ [.code []] } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  rw [← Simulation.Interaction.bind_pure sourceRun]
  apply Simulation.Interaction.Rel.bind hRun
  intro sourceResult targetResult hResult
  cases hResult with
  | @regular sourceState sourceContext targetState hCtx hState =>
      simp only [Locals.Source.Effectful.Outcome.regular,
        Structured.Outcome.regular, Structured.OutcomeT.regular]
      have hEmpty :=
        Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
          targetProgram (targetFuel - code.length) [] targetState targetState
          (by omega) (by rfl)
      rw [hEmpty]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .regular hCtx hState
  | brk hTarget hState =>
      simp only [Locals.Source.Effectful.Outcome.brk,
        Structured.Outcome.brk, Structured.OutcomeT.brk]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .brk hTarget hState
  | cont hTarget hState =>
      simp only [Locals.Source.Effectful.Outcome.cont,
        Structured.Outcome.cont, Structured.OutcomeT.cont]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .cont hTarget hState
  | leave hState =>
      simp only [Locals.Source.Effectful.Outcome.leave,
        Structured.Outcome.leave, Structured.OutcomeT.leave]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .leave hState
  | halt hShared hReturns =>
      simp only [Locals.Source.Effectful.Outcome.halt,
        Structured.Outcome.halt, Structured.OutcomeT.halt]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .halt hShared hReturns

theorem controlAppendEmptyCodeForward
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx : Locals.Ctx)
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx)}
    {code : List Expressions.Stmt}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (targetFuel : Nat)
    (hFuel : code.length + 1 < targetFuel)
    (hRun :
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target)) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
      sourceRun
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel { stmts := code ++ [.code []] } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_right hRun
  intro sourceDone targetDone hResult
  cases hResult with
  | error hError =>
      apply Simulation.Interaction.ForwardRel.done
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hResult =>
      cases hResult with
      | @regular sourceState sourceContext targetState hCtx hState =>
          simp only [Locals.Source.Effectful.Outcome.regular,
            Structured.Outcome.regular, Structured.OutcomeT.regular]
          have hEmpty :=
            Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
              targetProgram (targetFuel - code.length) [] targetState targetState
              (by omega) (by rfl)
          rw [hEmpty]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .regular hCtx hState
      | brk hTarget hState =>
          simp only [Locals.Source.Effectful.Outcome.brk,
            Structured.Outcome.brk, Structured.OutcomeT.brk]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .brk hTarget hState
      | cont hTarget hState =>
          simp only [Locals.Source.Effectful.Outcome.cont,
            Structured.Outcome.cont, Structured.OutcomeT.cont]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .cont hTarget hState
      | leave hState =>
          simp only [Locals.Source.Effectful.Outcome.leave,
            Structured.Outcome.leave, Structured.OutcomeT.leave]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .leave hState
      | halt hShared hReturns =>
          simp only [Locals.Source.Effectful.Outcome.halt,
            Structured.Outcome.halt, Structured.OutcomeT.halt]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .halt hShared hReturns

theorem controlIf
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (cond : Functions.Expr 1) (body : Functions.Block)
    (condCode : Structured.Code) (targetBody : Expressions.Block)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCtx : RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns)
    (hCondScoped : Locals.Scope.ExprScoped targetCtx.layout cond)
    (hCondSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode targetCtx 0 cond = some condCode)
    (hInitial : StateRel targetCtx.layout suffix returns source target)
    (hBody :
      ∀ {sourceAfter : Locals.Source.State}
        {targetAfter : Structured.RunState},
        StateRel targetCtx.layout suffix returns sourceAfter targetAfter →
          Simulation.Interaction.ForwardRel FuelTruncated
            (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
            (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
              sourceFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetFuel - 2) targetBody targetAfter)) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
        (sourceFuel + 1) (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := [.if_ (.code condCode) targetBody] } target) := by
  have hTargetFuelEq : targetFuel = (targetFuel - 2) + 2 := by omega
  rw [hTargetFuelEq,
    Expressions.InteractionSemantics.Block.openRun_single_if]
  rw [Functions.InteractionSemantics.Stmt.openRun_if]
  have hCond :=
    StackExpressionPreservation.openEvalCondition_compileCode
      cond targetCtx hCondScoped hCondSupported hCondCompile hInitial
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel hCond)
  intro sourceResult targetResult hResult
  rcases sourceResult with ⟨sourceAfter, sourceCond⟩
  rcases targetResult with ⟨targetAfter, targetCond⟩
  cases hResult.condition
  cases sourceCond with
  | false =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .regular hCtx hResult.state
  | true =>
      exact hBody hResult.state

def SwitchBranchesPreserve
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block)
    (returnNames : List Name) (suffix : List Word)
    (returns : List Structured.ReturnDest) : Prop :=
  ∀ value,
    match Functions.Source.Switch.select value cases defaultBody,
        Expressions.EffectSemantics.Switch.select value compiledCases
          compiledDefault with
    | none, none => True
    | some sourceBody, some targetBody =>
        ∀ {sourceAfter : Locals.Source.State}
          {targetAfter : Structured.RunState},
          StateRel targetCtx.layout suffix returns sourceAfter targetAfter →
            Simulation.Interaction.ForwardRel FuelTruncated
              (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
              (Functions.InteractionSemantics.Stmt.openRun sourceProgram
                sourceCtx sourceFuel (.block sourceBody) sourceAfter)
              (Expressions.InteractionSemantics.Block.openRun targetProgram
                targetFuel targetBody targetAfter)
    | _, _ => False

theorem controlSwitch
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (scrutineeCode : Structured.Code)
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCtx : RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns)
    (hScrutineeScoped : Locals.Scope.ExprScoped targetCtx.layout scrutinee)
    (hScrutineeSupported :
      Locals.InteractionSemantics.Expr.OpenSupported scrutinee)
    (hScrutineeCompile :
      Locals.Expr.compileCode targetCtx 0 scrutinee = some scrutineeCode)
    (hInitial : StateRel targetCtx.layout suffix returns source target)
    (hBranches :
      SwitchBranchesPreserve sourceProgram targetProgram targets sourceCtx
        targetCtx sourceFuel (targetFuel - 2) cases defaultBody compiledCases
        compiledDefault returnNames suffix returns) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
        (sourceFuel + 1) (.switch scrutinee cases defaultBody) source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            [.switch (.code scrutineeCode) compiledCases compiledDefault] }
        target) := by
  have hTargetFuelEq : targetFuel = (targetFuel - 2) + 2 := by omega
  rw [hTargetFuelEq,
    Expressions.InteractionSemantics.Block.openRun_single_switch]
  rw [Functions.InteractionSemantics.Stmt.openRun_switch]
  have hScrutinee :=
    StackExpressionPreservation.openEvalOnePop_compileCode
      scrutinee targetCtx hScrutineeScoped hScrutineeSupported
      hScrutineeCompile hInitial
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel (by
      simpa [Functions.InteractionSemantics.Expr.openEvalOne] using hScrutinee))
  intro sourceResult targetResult hResult
  rcases sourceResult with ⟨sourceAfter, value⟩
  rcases targetResult with ⟨targetAfter, targetValue⟩
  cases hResult.value
  cases hSourceSelect :
      Functions.Source.Switch.select value cases defaultBody with
  | none =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault with
      | none =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .regular hCtx hResult.state
      | some targetBody =>
          have hBranch := hBranches value
          rw [hSourceSelect, hTargetSelect] at hBranch
          contradiction
  | some sourceBody =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault with
      | none =>
          have hBranch := hBranches value
          rw [hSourceSelect, hTargetSelect] at hBranch
          contradiction
      | some targetBody =>
          have hBranch := hBranches value
          rw [hSourceSelect, hTargetSelect] at hBranch
          exact hBranch hResult.state

theorem openRun_brk_join_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (join : AllocationLayout.Join)
    (artifact : StackTransitionCompilation.JoinArtifact targetCtx join)
    {scope : List Name} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScope : sourceCtx.breakScope? = some scope)
    (hScopeCovers :
      ∀ {name : Name}, name ∈ join.target → name ∈ scope)
    (hFuel :
      artifact.retainArtifact.promotionCodes.length + 1 +
          artifact.orderArtifact.promotionCodes.length + 2 < targetFuel)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel (targetCtx.withLayout join.target) suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .brk source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            artifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
              artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
              [.code [], .brk] }
        target) := by
  let joinLength :=
    artifact.retainArtifact.promotionCodes.length + 1 +
      artifact.orderArtifact.promotionCodes.length
  apply artifact.thenBlock targetProgram targetFuel
      (by omega) hInitial
  intro joinedTarget hJoinedRel
  let tailExtra := targetFuel - joinLength - 3
  have hTarget :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_brk
      targetProgram tailExtra [] joinedTarget joinedTarget (by rfl)
  rw [show
      targetFuel -
          (artifact.retainArtifact.promotionCodes.length + 1 +
            artifact.orderArtifact.promotionCodes.length) = tailExtra + 3 by
      simp only [joinLength, tailExtra]
      omega]
  rw [Functions.InteractionSemantics.Stmt.openRun_brk
    sourceProgram sourceCtx sourceFuel source hScope]
  rw [hTarget]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact .brk (hJoinedRel.restrictTo hScopeCovers)

theorem openRun_cont_join_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (join : AllocationLayout.Join)
    (artifact : StackTransitionCompilation.JoinArtifact targetCtx join)
    {scope : List Name} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScope : sourceCtx.continueScope? = some scope)
    (hScopeCovers :
      ∀ {name : Name}, name ∈ join.target → name ∈ scope)
    (hFuel :
      artifact.retainArtifact.promotionCodes.length + 1 +
          artifact.orderArtifact.promotionCodes.length + 2 < targetFuel)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel (targetCtx.withLayout join.target) suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .cont source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            artifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
              artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
              [.code [], .cont] }
        target) := by
  let joinLength :=
    artifact.retainArtifact.promotionCodes.length + 1 +
      artifact.orderArtifact.promotionCodes.length
  apply artifact.thenBlock targetProgram targetFuel
      (by omega) hInitial
  intro joinedTarget hJoinedRel
  let tailExtra := targetFuel - joinLength - 3
  have hTarget :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_cont
      targetProgram tailExtra [] joinedTarget joinedTarget (by rfl)
  rw [show
      targetFuel -
          (artifact.retainArtifact.promotionCodes.length + 1 +
            artifact.orderArtifact.promotionCodes.length) = tailExtra + 3 by
      simp only [joinLength, tailExtra]
      omega]
  rw [Functions.InteractionSemantics.Stmt.openRun_cont
    sourceProgram sourceCtx sourceFuel source hScope]
  rw [hTarget]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact .cont (hJoinedRel.restrictTo hScopeCovers)

theorem compiledBrkJoinPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (join : AllocationLayout.Join)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hSource : targetCtx.layout = join.source)
    (hTargetDepth : targetCtx.breakDepth? = some join.target.length)
    (hLowered : lowered = join.statements ++ [.brk])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ∃ artifact : StackTransitionCompilation.JoinArtifact targetCtx join,
      finalCtx = targetCtx.withLayout join.target ∧
      code =
        artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
          artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
          [.code [], .brk] ∧
      ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
        {scope : List Name} {suffix : List Word}
        {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        code.length < targetFuel →
        sourceCtx.breakScope? = some scope →
        (∀ {name : Name}, name ∈ join.target → name ∈ scope) →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel .brk source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := code } target) := by
  rw [hLowered] at hCompile
  obtain ⟨joinCode, joinedCtx, brkCode, hJoinCompile, hBrkCompile,
      hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Join.compileArtifact join hSource
  have hJoinPair :=
    Option.some.inj (artifact.compileEq.symm.trans hJoinCompile)
  have hJoinCode :
      artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
          artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code =
        joinCode :=
    congrArg Prod.fst hJoinPair
  have hJoinedCtx : targetCtx.withLayout join.target = joinedCtx :=
    congrArg Prod.snd hJoinPair
  rw [← hJoinedCtx] at hBrkCompile
  have hStmtCompile :=
    Locals.Block.compileOpen_single_components hBrkCompile
  obtain ⟨depth, cleanup, hDepth, hCleanup, hBrkCode, hFinalCtx⟩ :=
    Locals.Stmt.compile_brk_components hStmtCompile
  have hDepthEq : depth = join.target.length := by
    have hDepth' :
        (targetCtx.withLayout join.target).breakDepth? =
          some join.target.length := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    rw [hDepth'] at hDepth
    exact (Option.some.inj hDepth).symm
  subst depth
  have hCleanupEq : cleanup = [] := by
    simp [Locals.Ctx.cleanupTo?, Locals.Ctx.withLayout] at hCleanup
    exact hCleanup
  subst cleanup
  have hCode :
      code =
        artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
          artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
          [.code [], .brk] := by
    rw [hWholeCode, ← hJoinCode, hBrkCode]
    simp [Locals.codeStmt, List.append_assoc]
  refine ⟨artifact, ?_, hCode, ?_⟩
  · exact hFinalCtx
  · intro sourceCtx sourceFuel targetFuel scope suffix returns source target
      hTargetFuel hScope hScopeCovers hInitial
    have hFuelEq :
        code.length + 1 =
          artifact.retainArtifact.promotionCodes.length + 1 +
            artifact.orderArtifact.promotionCodes.length + 3 := by
      rw [hCode]
      simp only [List.length_append, List.length_map,
        List.length_cons, List.length_nil]
    have hRun :=
      openRun_brk_join_generated sourceProgram targetProgram sourceCtx
        targetCtx sourceFuel targetFuel join artifact hScope
        hScopeCovers (by omega) hInitial
    rw [hFinalCtx]
    have hBlock :
        ({ stmts := code } : Expressions.Block) =
          { stmts :=
              artifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
                artifact.orderArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
                [.code [], .brk] } :=
      congrArg (fun stmts => ({ stmts } : Expressions.Block)) hCode
    rw [hBlock]
    exact hRun

theorem compiledBrkControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (join : AllocationLayout.Join)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hTarget : targets.brk? = some join.target)
    (hSource : targetCtx.layout = join.source)
    (hTargetDepth : targetCtx.breakDepth? = some join.target.length)
    (hLowered : lowered = join.statements ++ [.brk])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx finalCtx .brk code join.target := by
  obtain ⟨_artifact, hFinal, _hCode, hForward⟩ :=
    compiledBrkJoinPointOfEquations sourceProgram targetProgram targetCtx
      finalCtx join lowered code hSource hTargetDepth hLowered hCompile
  refine ⟨?_, ?_⟩
  · rw [hFinal]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  obtain ⟨scope, hScope, hScopeCovers⟩ :=
    (hCtx.breakTarget hTarget).sourceCovers
  have hRun :=
    hForward sourceCtx sourceFuel targetFuel
      (Expressions.TargetFuel.Covers.length_lt hFuel) hScope hScopeCovers
      hInitial
  rw [Functions.InteractionSemantics.Stmt.openRun_brk sourceProgram sourceCtx
    sourceFuel source hScope] at hRun
  obtain ⟨targetDone, hTargetDone, hDone⟩ :=
    Simulation.Interaction.Rel.done_left hRun
  rw [hTargetDone]
  rw [Functions.InteractionSemantics.Stmt.openRun_brk sourceProgram sourceCtx
    sourceFuel source hScope]
  apply Simulation.Interaction.ForwardRel.done
  cases hDone with
  | ok hResult =>
      apply Simulation.Interaction.ExceptRel.ok
      cases hResult with
      | brk hState =>
          exact .brk (by
            rw [hFinal]
            simpa [Locals.Ctx.withLayout] using hTarget) hState

theorem compiledContJoinPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (join : AllocationLayout.Join)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hSource : targetCtx.layout = join.source)
    (hTargetDepth : targetCtx.continueDepth? = some join.target.length)
    (hLowered : lowered = join.statements ++ [.cont])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ∃ artifact : StackTransitionCompilation.JoinArtifact targetCtx join,
      finalCtx = targetCtx.withLayout join.target ∧
      code =
        artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
          artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
          [.code [], .cont] ∧
      ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
        {scope : List Name} {suffix : List Word}
        {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        code.length < targetFuel →
        sourceCtx.continueScope? = some scope →
        (∀ {name : Name}, name ∈ join.target → name ∈ scope) →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel .cont source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := code } target) := by
  rw [hLowered] at hCompile
  obtain ⟨joinCode, joinedCtx, contCode, hJoinCompile, hContCompile,
      hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Join.compileArtifact join hSource
  have hJoinPair :=
    Option.some.inj (artifact.compileEq.symm.trans hJoinCompile)
  have hJoinCode :
      artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
          artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code =
        joinCode :=
    congrArg Prod.fst hJoinPair
  have hJoinedCtx : targetCtx.withLayout join.target = joinedCtx :=
    congrArg Prod.snd hJoinPair
  rw [← hJoinedCtx] at hContCompile
  have hStmtCompile :=
    Locals.Block.compileOpen_single_components hContCompile
  obtain ⟨depth, cleanup, hDepth, hCleanup, hContCode, hFinalCtx⟩ :=
    Locals.Stmt.compile_cont_components hStmtCompile
  have hDepthEq : depth = join.target.length := by
    have hDepth' :
        (targetCtx.withLayout join.target).continueDepth? =
          some join.target.length := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    rw [hDepth'] at hDepth
    exact (Option.some.inj hDepth).symm
  subst depth
  have hCleanupEq : cleanup = [] := by
    simp [Locals.Ctx.cleanupTo?, Locals.Ctx.withLayout] at hCleanup
    exact hCleanup
  subst cleanup
  have hCode :
      code =
        artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
          artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
          [.code [], .cont] := by
    rw [hWholeCode, ← hJoinCode, hContCode]
    simp [Locals.codeStmt, List.append_assoc]
  refine ⟨artifact, hFinalCtx, hCode, ?_⟩
  intro sourceCtx sourceFuel targetFuel scope suffix returns source target
    hTargetFuel hScope hScopeCovers hInitial
  have hFuelEq :
      code.length + 1 =
        artifact.retainArtifact.promotionCodes.length + 1 +
          artifact.orderArtifact.promotionCodes.length + 3 := by
    rw [hCode]
    simp only [List.length_append, List.length_map,
      List.length_cons, List.length_nil]
  have hRun :=
    openRun_cont_join_generated sourceProgram targetProgram sourceCtx
      targetCtx sourceFuel targetFuel join artifact hScope
      hScopeCovers (by omega) hInitial
  rw [hFinalCtx]
  have hBlock :
      ({ stmts := code } : Expressions.Block) =
        { stmts :=
            artifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
              artifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code ++
              [.code [], .cont] } :=
    congrArg (fun stmts => ({ stmts } : Expressions.Block)) hCode
  rw [hBlock]
  exact hRun

theorem compiledContControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (join : AllocationLayout.Join)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hTarget : targets.cont? = some join.target)
    (hSource : targetCtx.layout = join.source)
    (hTargetDepth : targetCtx.continueDepth? = some join.target.length)
    (hLowered : lowered = join.statements ++ [.cont])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx finalCtx .cont code join.target := by
  obtain ⟨_artifact, hFinal, _hCode, hForward⟩ :=
    compiledContJoinPointOfEquations sourceProgram targetProgram targetCtx
      finalCtx join lowered code hSource hTargetDepth hLowered hCompile
  refine ⟨?_, ?_⟩
  · rw [hFinal]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  obtain ⟨scope, hScope, hScopeCovers⟩ :=
    (hCtx.continueTarget hTarget).sourceCovers
  have hRun :=
    hForward sourceCtx sourceFuel targetFuel
      (Expressions.TargetFuel.Covers.length_lt hFuel) hScope hScopeCovers
      hInitial
  rw [Functions.InteractionSemantics.Stmt.openRun_cont sourceProgram sourceCtx
    sourceFuel source hScope] at hRun
  obtain ⟨targetDone, hTargetDone, hDone⟩ :=
    Simulation.Interaction.Rel.done_left hRun
  rw [hTargetDone]
  rw [Functions.InteractionSemantics.Stmt.openRun_cont sourceProgram sourceCtx
    sourceFuel source hScope]
  apply Simulation.Interaction.ForwardRel.done
  cases hDone with
  | ok hResult =>
      apply Simulation.Interaction.ExceptRel.ok
      cases hResult with
      | cont hState =>
          exact .cont (by
            rw [hFinal]
            simpa [Locals.Ctx.withLayout] using hTarget) hState

theorem openRun_terminal_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (kind : Assembly.HaltKind)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hArgCount : kind.argCount = 0)
    (hFuel : 2 < targetFuel)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.terminal kind) source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            Locals.codeStmt targetCtx.cleanupAll ++
              [Expressions.Stmt.terminal kind] }
        target) := by
  have hCleanup :
      targetCtx.cleanupTo? 0 = some targetCtx.cleanupAll := by
    simp [Locals.Ctx.cleanupTo?, Locals.Ctx.cleanupAll]
  obtain ⟨afterCleanup, hCleanupRun, hCleanupRel⟩ :=
    StackTransitionPreservation.Cleanup.openRun
      (ctx := targetCtx) (targetLayout := []) rfl (by simp)
      hCleanup hInitial
  have hLength : ([] : List Word).length = kind.argCount := by
    simpa [hArgCount]
  have hCleanupStack :
      afterCleanup.evm.stack = ([] : List Word).reverse ++ suffix := by
    simpa [StackRelation.values] using hCleanupRel.stack
  have hTerminal :=
    Locals.InteractionPreservation.Primitive.openTerminal_frame
      (source := source) hLength hCleanupRel.shared hCleanupStack
  have hWrapped :
      Simulation.Interaction.Rel
        (OpenOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.Primitive.openTerminal
            kind source [])
          (fun final =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.halt kind final,
                sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Terminal.openStep
            kind afterCleanup)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.halt kind final))) := by
    apply Simulation.Interaction.Rel.bind hTerminal
    intro sourceFinal targetFinal hTerminalResult
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact .halt hTerminalResult.1
      (hTerminalResult.2.trans hCleanupRel.returns)
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Functions.InteractionSemantics.primitiveSemantics
  let extra := targetFuel - 3
  have hTargetFuel : targetFuel = extra + 3 := by
    simp only [extra]
    omega
  rw [show
      Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
          { stmts :=
              Locals.codeStmt targetCtx.cleanupAll ++
                [Expressions.Stmt.terminal kind] }
          target =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            targetCtx.cleanupAll target)
          (fun afterCode =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Terminal.openStep
                kind afterCode)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.halt kind final))) by
      rw [hTargetFuel]
      simpa [Locals.codeStmt] using
        Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_terminal
          targetProgram extra targetCtx.cleanupAll kind target]
  rw [hCleanupRun]
  exact hWrapped

theorem compiledTerminalPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (kind : Assembly.HaltKind)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hArgCount : kind.argCount = 0)
    (hLowered : lowered = [.terminal kind])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    finalCtx = targetCtx ∧
      code =
        Locals.codeStmt targetCtx.cleanupAll ++
          [Expressions.Stmt.terminal kind] ∧
      ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        code.length < targetFuel →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.terminal kind) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := code } target) := by
  rw [hLowered] at hCompile
  have hStmtCompile :=
    Locals.Block.compileOpen_single_components hCompile
  obtain ⟨hCode, hFinal⟩ :=
    Locals.Stmt.compile_terminal_components hStmtCompile
  refine ⟨hFinal, hCode, ?_⟩
  intro sourceCtx sourceFuel targetFuel suffix returns source target
    hTargetFuel hInitial
  have hRun :=
    openRun_terminal_generated sourceProgram targetProgram sourceCtx
      targetCtx sourceFuel targetFuel kind hArgCount
      (by simpa [hCode, Locals.codeStmt] using hTargetFuel) hInitial
  rw [hFinal]
  have hBlock :
      ({ stmts := code } : Expressions.Block) =
        { stmts :=
            Locals.codeStmt targetCtx.cleanupAll ++
              [Expressions.Stmt.terminal kind] } :=
    congrArg (fun stmts => ({ stmts } : Expressions.Block)) hCode
  rw [hBlock]
  exact hRun

theorem compiledTerminalControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (kind : Assembly.HaltKind)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hArgCount : kind.argCount = 0)
    (hLowered : lowered = [.terminal kind])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.terminal kind) code targetCtx.layout := by
  obtain ⟨hFinal, _hCode, hForward⟩ :=
    compiledTerminalPointOfEquations sourceProgram targetProgram targetCtx
      finalCtx kind lowered code hArgCount hLowered hCompile
  refine ⟨?_, ?_⟩
  · rw [hFinal]
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    _hCtx hInitial
  have hRun :=
    hForward sourceCtx sourceFuel targetFuel
      (Expressions.TargetFuel.Covers.length_lt hFuel) hInitial
  apply openRelToControl hRun
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Functions.InteractionSemantics.primitiveSemantics
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial
      (Locals.InteractionSemantics.Primitive.openTerminal kind source []))
  · intro _error _hTrivial
    trivial
  · intro _result _hTrivial
    exact .done trivial

theorem openRun_terminalArgs_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (kind : Assembly.HaltKind)
    (args : Locals.ExprSeq kind.argCount)
    {argsCode : Structured.Code}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprSeqScoped targetCtx.layout args)
    (hSupported : Locals.InteractionSemantics.ExprSeq.OpenSupported args)
    (hCompile :
      Locals.ExprSeq.compileCode targetCtx 0 args = some argsCode)
    (hFuel : 2 < targetFuel)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
        sourceFuel (.terminalArgs kind args) source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            Locals.codeStmt argsCode ++
              [Expressions.Stmt.terminal kind] }
        target) := by
  have hArgs :=
    StackExpressionPreservation.openEvalSeq_compileCode args targetCtx
      hScoped hSupported hCompile hInitial
  have hCore :
      Simulation.Interaction.Rel
        (OpenOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.ExprSeq.openEval args source)
          (fun result =>
            Simulation.Interaction.bind
              (Locals.InteractionSemantics.Primitive.openTerminal
                kind result.1 result.2)
              (fun final =>
                Simulation.Interaction.pure
                  (Locals.Source.Effectful.Outcome.halt kind final,
                    sourceCtx))))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun argsCode target)
          (fun afterArgs =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Terminal.openStep
                kind afterArgs)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.halt kind final)))) := by
    apply Simulation.Interaction.Rel.bind hArgs
    intro sourceAfterArgs targetAfterArgs hArgsResult
    rcases sourceAfterArgs with ⟨sourceAfterArgs, values⟩
    have hTerminal :=
      Locals.InteractionPreservation.Primitive.openTerminal_frame
        hArgsResult.length hArgsResult.shared hArgsResult.stack
    apply Simulation.Interaction.Rel.bind hTerminal
    intro sourceFinal targetFinal hTerminalResult
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact .halt hTerminalResult.1
      (hTerminalResult.2.trans
        (hArgsResult.returns.trans hInitial.returns))
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Functions.InteractionSemantics.primitiveSemantics
  let extra := targetFuel - 3
  have hTargetFuel : targetFuel = extra + 3 := by
    simp only [extra]
    omega
  rw [show
      Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
          { stmts :=
              Locals.codeStmt argsCode ++
                [Expressions.Stmt.terminal kind] }
          target =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun argsCode target)
          (fun afterCode =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Terminal.openStep
                kind afterCode)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.halt kind final))) by
      rw [hTargetFuel]
      simpa [Locals.codeStmt] using
        Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_terminal
          targetProgram extra argsCode kind target]
  exact hCore

theorem compiledTerminalArgsPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (kind : Assembly.HaltKind) (args : Locals.ExprSeq kind.argCount)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprSeqScoped sourceEnv args)
    (hSupported : Locals.InteractionSemantics.ExprSeq.OpenSupported args)
    (hAccess : StackAccess.ExprSeq.check? targetCtx.layout 0 args = some ())
    (hLowered : lowered = [.terminalArgs kind args])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    finalCtx = targetCtx ∧
      ∃ argsCode,
        Locals.ExprSeq.compileCode targetCtx 0 args = some argsCode ∧
          code =
            Locals.codeStmt argsCode ++
              [Expressions.Stmt.terminal kind] ∧
          ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
            {suffix : List Word} {returns : List Structured.ReturnDest}
            {source : Locals.Source.State} {target : Structured.RunState},
            code.length < targetFuel →
            StateRel targetCtx.layout suffix returns source target →
            Simulation.Interaction.Rel
              (OpenOutcomeRel finalCtx suffix returns)
              (Functions.InteractionSemantics.Stmt.openRun
                sourceProgram sourceCtx sourceFuel
                  (.terminalArgs kind args) source)
              (Expressions.InteractionSemantics.Block.openRun targetProgram
                targetFuel { stmts := code } target) := by
  rw [hLowered] at hCompile
  have hStmtCompile :=
    Locals.Block.compileOpen_single_components hCompile
  obtain ⟨argsCode, hArgsCompile, hCode, hFinal⟩ :=
    Locals.Stmt.compile_terminalArgs_components hStmtCompile
  have hTargetScoped :=
    StackAccess.ExprSeq.scoped_of_check hAccess hScoped
  refine ⟨hFinal, argsCode, hArgsCompile, hCode, ?_⟩
  intro sourceCtx sourceFuel targetFuel suffix returns source target
    hTargetFuel hInitial
  have hRun :=
    openRun_terminalArgs_generated sourceProgram targetProgram sourceCtx
      targetCtx sourceFuel targetFuel kind args hTargetScoped hSupported
      hArgsCompile (by simpa [hCode, Locals.codeStmt] using hTargetFuel)
      hInitial
  rw [hFinal]
  have hBlock :
      ({ stmts := code } : Expressions.Block) =
        { stmts :=
            Locals.codeStmt argsCode ++
              [Expressions.Stmt.terminal kind] } :=
    congrArg (fun stmts => ({ stmts } : Expressions.Block)) hCode
  rw [hBlock]
  exact hRun

theorem compiledTerminalArgsControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (kind : Assembly.HaltKind) (args : Locals.ExprSeq kind.argCount)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprSeqScoped sourceEnv args)
    (hSupported : Locals.InteractionSemantics.ExprSeq.OpenSupported args)
    (hAccess : StackAccess.ExprSeq.check? targetCtx.layout 0 args = some ())
    (hLowered : lowered = [.terminalArgs kind args])
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.terminalArgs kind args) code targetCtx.layout := by
  obtain ⟨hFinal, _argsCode, _hArgsCompile, _hCode, hForward⟩ :=
    compiledTerminalArgsPointOfEquations sourceProgram targetProgram targetCtx
      finalCtx kind args lowered code hScoped hSupported hAccess hLowered
      hCompile
  refine ⟨?_, ?_⟩
  · rw [hFinal]
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    _hCtx hInitial
  have hRun :=
    hForward sourceCtx sourceFuel targetFuel
      (Expressions.TargetFuel.Covers.length_lt hFuel) hInitial
  apply openRelToControl hRun
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Functions.InteractionSemantics.primitiveSemantics
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial
      (Locals.InteractionSemantics.ExprSeq.openEval args source))
  · intro _error _hTrivial
    trivial
  · intro result _hTrivial
    apply Simulation.Interaction.AllDone.bind
      (Simulation.Interaction.AllDone.trivial
        (Locals.InteractionSemantics.Primitive.openTerminal
          kind result.1 result.2))
    · intro _error _hTerminal
      trivial
    · intro _final _hTerminal
      exact .done trivial

theorem openRun_transition_generated
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
      ∃ final,
        Locals.Block.compileOpen targetCtx
            { stmts := transition.schedule.statements } =
          some
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup],
             targetCtx.withLayout transition.schedule.target) ∧
        Structured.InteractionSemantics.Code.openRun
            (artifact.promotionCodes.flatten ++ artifact.cleanup) target =
          .done (.ok final) ∧
        RegularResultRel
          (targetCtx.withLayout transition.schedule.target)
          suffix returns
          (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
          (Structured.Outcome.regular final) := by
  obtain ⟨artifact, final, hCompile, hRun, hFinal⟩ :=
    StackTransitionCompilation.Transition.compiledOpenRun
      transition hSource hInitial
  exact
    ⟨artifact, final, hCompile, hRun,
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx.afterTransition transition hSource
        state := hFinal }⟩

theorem openRun_transition_block_generated
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
      ∃ final,
        Locals.Block.compileOpen targetCtx
            { stmts := transition.schedule.statements } =
          some
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup],
             targetCtx.withLayout transition.schedule.target) ∧
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (artifact.promotionCodes.length + 2)
            { stmts :=
                artifact.promotionCodes.map Expressions.Stmt.code ++
                  [Expressions.Stmt.code artifact.cleanup] }
            target =
          .done (.ok (Structured.Outcome.regular final)) ∧
        RegularResultRel
          (targetCtx.withLayout transition.schedule.target)
          suffix returns
          (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
          (Structured.Outcome.regular final) := by
  obtain ⟨artifact, final, hCompile, hRun, hFinal⟩ :=
    StackTransitionCompilation.Transition.compiledBlockOpenRun
      targetProgram transition hSource hInitial
  exact
    ⟨artifact, final, hCompile, hRun,
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx.afterTransition transition hSource
        state := hFinal }⟩

def RegularPointPreserves
    (targetProgram : Expressions.Program) (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    (sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
    (head : Expressions.Stmt)
    (targetFuel : Nat)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (target : Structured.RunState) : Prop :=
  ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
    Locals.Block.compileOpen targetCtx
        { stmts := transition.schedule.statements } =
      some
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup],
         targetCtx.withLayout transition.schedule.target) ∧
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout transition.schedule.target)
        suffix returns)
      sourceRun
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel
        { stmts :=
            head ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]) }
        target)

theorem regularThenTransition
    (targetProgram : Expressions.Program)
    (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    (sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
    (head : Expressions.Stmt)
    (targetFuel : Nat)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hHead : ∀ targetFuel,
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Stmt.openRun
          targetProgram targetFuel head target)) :
    RegularPointPreserves targetProgram targetCtx transition sourceRun
      head targetFuel suffix returns target := by
  unfold RegularPointPreserves
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact
      transition hSource
  have hCodeLength :
      artifact.promotionCodes.length =
        transition.schedule.promotions.length :=
    artifact.codes.code_length
  have hCodeFuel : artifact.promotionCodes.length + 2 < targetFuel := by
    rw [hCodeLength]
    exact hFuel
  refine ⟨artifact, artifact.compileEq, ?_⟩
  change
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout transition.schedule.target)
        suffix returns)
      sourceRun
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel
        { stmts := [head] ++
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]) }
        target)
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel head target (by omega)]
  rw [← Simulation.Interaction.bind_pure sourceRun]
  apply Simulation.Interaction.Rel.bind
    (hHead (targetFuel - 1))
  intro sourceResult targetResult hResult
  simp only [hResult.targetMode, List.length_cons, List.length_nil,
    Nat.add_zero]
  obtain ⟨final, hRun, hFinalRel⟩ :=
    artifact.blockOpenRun targetProgram (targetFuel - 1) (by omega)
      hResult.state
  rw [hRun]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    { sourceMode := hResult.sourceMode
      targetMode := rfl
      context := hResult.context.afterTransition transition hSource
      state := hFinalRel }

theorem openRun_expr_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Locals.Expr 0)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode targetCtx 0 expr = some code)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram targetFuel (.code code) target) := by
  have hExpr :=
    StackExpressionPreservation.openEvalZero_compileCode
      expr targetCtx hScoped hSupported hCompile hInitial
  have hWrapped :
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEval expr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular result.1,
               sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun code target)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final))) := by
    apply Simulation.Interaction.Rel.bind hExpr
    intro sourceFinal targetFinal hFinal
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx
        state := hFinal }
  unfold Locals.InteractionSemantics.Expr.openEval
    Structured.InteractionSemantics.Code.openRun at hWrapped
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Expressions.InteractionSemantics.Stmt.openRun
    Functions.InteractionSemantics.stateModel
  simp only [Expressions.EffectSemantics.Control.Stmt.run]
  exact hWrapped

theorem openRun_let_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
    {valueCode : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hValueScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hValueCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout (name :: targetCtx.layout)) suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram targetFuel
        (.code
          (valueCode ++ Locals.bindLocals 0 (name :: targetCtx.layout)))
        target) := by
  have hValue :=
    StackExpressionPreservation.openEvalOne_fresh_compileCode
      valueExpr targetCtx name hFresh hValueScoped hValueSupported
      hValueCompile hInitial
  have hCore :
      Simulation.Interaction.Rel
        (RegularOutcomeRel
          (targetCtx.withLayout (name :: targetCtx.layout)) suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEvalOne valueExpr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular
                (result.1.insert name result.2),
               { sourceCtx with scope := name :: sourceCtx.scope })))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun valueCode target)
          (fun targetAfterValue =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun
                (Locals.bindLocals 0 (name :: targetCtx.layout))
                targetAfterValue)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.regular final)))) := by
    apply Simulation.Interaction.Rel.bind hValue
    intro sourceAfterValue targetAfterValue hValueResult
    rcases sourceAfterValue with ⟨sourceFinal, value⟩
    rw [show Locals.bindLocals 0 (name :: targetCtx.layout) =
        [.bindLocals 0 (name :: targetCtx.layout)] by rfl,
      Locals.InteractionPreservation.Code.openRun_bindLocals]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx.prepend name
        state := hValueResult }
  unfold Locals.InteractionSemantics.Expr.openEvalOne
    Locals.InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel at hCore
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Expressions.InteractionSemantics.Stmt.openRun
    Functions.InteractionSemantics.stateModel
  simp only [Locals.Source.Effectful.StateModel.insert,
    Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout (name :: targetCtx.layout)) suffix returns)
      _
      (Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun
          (valueCode ++ Locals.bindLocals 0 (name :: targetCtx.layout))
          target)
        (fun final =>
          Simulation.Interaction.pure (Structured.Outcome.regular final)))
  rw [Structured.InteractionSemantics.Code.openRun_append]
  simpa [Simulation.Interaction.bind_assoc] using hCore

theorem openRun_assign_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
    {depth : Nat} {valueCode : Structured.Code}
    {swapOp : Structured.BasicOp} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hDepth :
      Locals.Layout.lookupDepth? name targetCtx.layout = some (depth + 1))
    (hValueScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hValueCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hSwap : Locals.StackOp.swap? (depth + 1) = some swapOp)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram targetFuel
        (.code
          (valueCode ++ [.op swapOp, .op .pop] ++
            Locals.bindLocals 0 targetCtx.layout))
        target) := by
  have hValue :=
    StackExpressionPreservation.openEvalOne_compileCode
      valueExpr targetCtx hValueScoped hValueSupported
      hValueCompile hInitial
  have hAt : targetCtx.layout[depth]? = some name :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  have hMem : name ∈ targetCtx.layout :=
    List.mem_of_getElem? hAt
  obtain ⟨old, hOld⟩ := hInitial.defined hMem
  have hContains : source.vars.contains name = true := by
    simp [Locals.Source.Store.contains, hOld]
  have hContains' :
      (Locals.InteractionSemantics.stateModel.source source).vars.contains
          name = true := by
    simpa [Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel] using hContains
  have hOldStack : target.evm.stack[depth]? = some old := by
    rw [hInitial.stack]
    have hValuesAt := values_getElem?_eq_some (source := source) hAt
    rw [hOld] at hValuesAt
    have hBound : depth < (values source targetCtx.layout).length :=
      List.getElem?_eq_some_iff.mp hValuesAt |>.1
    rw [List.getElem?_append_left hBound]
    exact hValuesAt
  have hCore :
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEvalOne valueExpr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular
                (result.1.insert name result.2), sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            (valueCode ++ [.op swapOp, .op .pop] ++
              Locals.bindLocals 0 targetCtx.layout)
            target)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final))) := by
    rw [List.append_assoc,
      Structured.InteractionSemantics.Code.openRun_append,
      Simulation.Interaction.bind_assoc]
    apply Simulation.Interaction.Rel.bind hValue
    intro sourceAfterValue targetAfterValue hValueResult
    rcases sourceAfterValue with ⟨sourceFinal, value⟩
    have hValueStack :
        targetAfterValue.evm.stack = value :: target.evm.stack := by
      simpa using hValueResult.stack
    obtain ⟨finalTarget, hSwapRun, hFinalStack,
        hFinalShared, hFinalReturns⟩ :=
      Locals.InteractionPreservation.Code.openRun_swap_pop
        hSwap hOldStack hValueStack
    rw [Structured.InteractionSemantics.Code.openRun_append,
      hSwapRun, Simulation.Interaction.bind_done_ok]
    rw [show Locals.bindLocals 0 targetCtx.layout =
        [.bindLocals 0 targetCtx.layout] by rfl,
      Locals.InteractionPreservation.Code.openRun_bindLocals,
      Simulation.Interaction.bind_done_ok]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx
        state := StateRel.ofExprResultOneAssign
          hNodup hDepth hInitial hValueResult
            hFinalShared hFinalReturns hFinalStack }
  unfold Locals.InteractionSemantics.Expr.openEvalOne
    Structured.InteractionSemantics.Code.openRun
    Locals.InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel at hCore
  simp only [Locals.Source.State.insert] at hCore
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Expressions.InteractionSemantics.Stmt.openRun
    Functions.InteractionSemantics.stateModel
  simp only [Locals.Source.Effectful.StateModel.vars,
    Expressions.EffectSemantics.Control.Stmt.run]
  rw [hContains']
  simp only [Locals.Source.Effectful.StateModel.withVars,
    if_true, Locals.Source.State.withVars]
  simpa [Simulation.Interaction.bind_assoc] using hCore

theorem exprThenTransition
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Functions.Expr 0)
    (transition : AllocationLayout.Transition)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode targetCtx 0 expr = some code)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    RegularPointPreserves targetProgram targetCtx transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (.code code) targetFuel suffix returns target := by
  apply regularThenTransition targetProgram targetCtx transition _ _
    targetFuel hSource hFuel
  intro leafFuel
  exact openRun_expr_generated sourceProgram targetProgram sourceCtx targetCtx
    sourceFuel leafFuel expr hCtx hScoped hSupported hCompile hInitial

theorem letThenTransition
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    {valueCode : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : name :: targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    RegularPointPreserves targetProgram
      (targetCtx.withLayout (name :: targetCtx.layout)) transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (.code (valueCode ++ Locals.bindLocals 0 (name :: targetCtx.layout)))
      targetFuel suffix returns target := by
  apply regularThenTransition targetProgram
    (targetCtx.withLayout (name :: targetCtx.layout)) transition _ _ targetFuel
      (by simpa [Locals.Ctx.withLayout] using hSource) hFuel
  intro leafFuel
  exact openRun_let_generated sourceProgram targetProgram sourceCtx targetCtx
    sourceFuel leafFuel valueExpr hCtx hFresh hScoped hSupported hCompile
    hInitial

theorem assignThenTransition
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    {depth : Nat} {valueCode : Structured.Code}
    {swapOp : Structured.BasicOp} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hDepth :
      Locals.Layout.lookupDepth? name targetCtx.layout = some (depth + 1))
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hSwap : Locals.StackOp.swap? (depth + 1) = some swapOp)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    RegularPointPreserves targetProgram targetCtx transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source)
      (.code
        (valueCode ++ [.op swapOp, .op .pop] ++
          Locals.bindLocals 0 targetCtx.layout))
      targetFuel suffix returns target := by
  apply regularThenTransition targetProgram targetCtx transition _ _
    targetFuel hSource hFuel
  intro leafFuel
  exact openRun_assign_generated sourceProgram targetProgram sourceCtx
    targetCtx sourceFuel leafFuel valueExpr hCtx hNodup hDepth hScoped
    hSupported hCompile hSwap hInitial

theorem RegularPointPreserves.compiledLowered
    (targetProgram : Expressions.Program)
    (beforeCtx pointCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    (sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
    (core : Locals.Stmt) (head : Expressions.Stmt)
    (lowered : List Locals.Stmt) (targetFuel : Nat)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (target : Structured.RunState)
    (hLowered :
      lowered = [core] ++ StackLowering.transitionStmts transition)
    (hCoreCompile :
      Locals.Stmt.compile beforeCtx core = some ([head], pointCtx))
    (hPreserves :
      RegularPointPreserves targetProgram pointCtx transition sourceRun
        head targetFuel suffix returns target) :
    ∃ artifact : StackTransitionCompilation.Artifact pointCtx transition,
      Locals.Block.compileOpen beforeCtx { stmts := lowered } =
          some
            (head ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             pointCtx.withLayout transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            (pointCtx.withLayout transition.schedule.target) suffix returns)
          sourceRun
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                head ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  obtain ⟨artifact, hTransitionCompile, hRun⟩ := hPreserves
  have hCoreBlock :
      Locals.Block.compileOpen beforeCtx { stmts := [core] } =
        some ([head], pointCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hWhole :=
    Locals.Block.compileOpen_append hCoreBlock hTransitionCompile
  refine ⟨artifact, ?_, hRun⟩
  simpa [hLowered] using hWhole

theorem compiledExprPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Functions.Expr 0)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt)
    {sourceEnv : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hScoped : Functions.Scope.ExprScoped sourceEnv expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 expr = some ())
    (hLowered :
      lowered = [.expr expr] ++ StackLowering.transitionStmts transition)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    ∃ code, ∃ artifact :
      StackTransitionCompilation.Artifact targetCtx transition,
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
          some
            ((.code code) ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             targetCtx.withLayout transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            (targetCtx.withLayout transition.schedule.target) suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.expr expr) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                (.code code) ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  have hTargetScoped :=
    StackAccess.Expr.scoped_of_check hAccess hScoped
  obtain ⟨code, hCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some ([.code code], targetCtx) := by
    simp [Locals.Stmt.compile, hCompile, Locals.codeStmt]
  have hPreserves :=
    exprThenTransition sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel expr transition hSource hFuel hCtx hTargetScoped
      hSupported hCompile hInitial
  obtain ⟨artifact, hWhole, hRun⟩ :=
    RegularPointPreserves.compiledLowered targetProgram targetCtx targetCtx
      transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (.expr expr) (.code code) lowered targetFuel suffix returns target
      hLowered hCoreCompile hPreserves
  exact ⟨code, artifact, hWhole, hRun⟩

theorem compiledLetPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (name : Name)
    (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt)
    {sourceEnv : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : name :: targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 value = some ())
    (hLowered :
      lowered = [.let_ name value] ++
        StackLowering.transitionStmts transition)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    ∃ code, ∃ artifact :
      StackTransitionCompilation.Artifact
        (targetCtx.withLayout (name :: targetCtx.layout)) transition,
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
          some
            ((.code
                (code ++
                  Locals.bindLocals 0 (name :: targetCtx.layout))) ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             (targetCtx.withLayout (name :: targetCtx.layout)).withLayout
               transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            ((targetCtx.withLayout (name :: targetCtx.layout)).withLayout
              transition.schedule.target) suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.let_ name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                (.code
                  (code ++
                    Locals.bindLocals 0 (name :: targetCtx.layout))) ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  have hTargetScoped :=
    StackAccess.Expr.scoped_of_check hAccess hScoped
  obtain ⟨code, hCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  let pointCtx := targetCtx.withLayout (name :: targetCtx.layout)
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.let_ name value) =
        some
          ([.code
              (code ++ Locals.bindLocals 0 (name :: targetCtx.layout))],
           pointCtx) := by
    simp [Locals.Stmt.compile, hCompile, Locals.codeStmt, pointCtx]
  have hPreserves :=
    letThenTransition sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel value transition hSource hFuel hCtx hFresh
      hTargetScoped hSupported hCompile hInitial
  obtain ⟨artifact, hWhole, hRun⟩ :=
    RegularPointPreserves.compiledLowered targetProgram targetCtx pointCtx
      transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name value) source)
      (.let_ name value)
      (.code (code ++ Locals.bindLocals 0 (name :: targetCtx.layout)))
      lowered targetFuel suffix returns target hLowered hCoreCompile hPreserves
  exact ⟨code, artifact, hWhole, hRun⟩

theorem compiledAssignPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (name : Name)
    (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt)
    {sourceEnv : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.assign? targetCtx.layout name value = some ())
    (hLowered :
      lowered = [.assign name value] ++
        StackLowering.transitionStmts transition)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    ∃ (valueCode : Structured.Code) (swap : Structured.BasicOp),
      ∃ artifact :
      StackTransitionCompilation.Artifact targetCtx transition,
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
          some
            ((.code
                (valueCode ++ [.op swap, .op .pop] ++
                  Locals.bindLocals 0 targetCtx.layout)) ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             targetCtx.withLayout transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            (targetCtx.withLayout transition.schedule.target) suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.assign name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                (.code
                  (valueCode ++ [.op swap, .op .pop] ++
                    Locals.bindLocals 0 targetCtx.layout)) ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  obtain ⟨depth, swap, hValueAccess, hDepth, hSwap⟩ :=
    StackAccess.assign_components hAccess
  have hTargetScoped :=
    StackAccess.Expr.scoped_of_check hValueAccess hScoped
  obtain ⟨valueCode, hValueCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check
      hValueAccess targetCtx rfl
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.assign name value) =
        some
          ([.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)],
           targetCtx) := by
    simp [Locals.Stmt.compile, hDepth, hValueCompile, hSwap,
      Locals.codeStmt]
  have hPreserves :=
    assignThenTransition sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel value transition hSource hFuel hCtx hNodup hDepth
      hTargetScoped hSupported hValueCompile hSwap hInitial
  obtain ⟨artifact, hWhole, hRun⟩ :=
    RegularPointPreserves.compiledLowered targetProgram targetCtx targetCtx
      transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name value) source)
      (.assign name value)
      (.code
        (valueCode ++ [.op swap, .op .pop] ++
          Locals.bindLocals 0 targetCtx.layout))
      lowered targetFuel suffix returns target hLowered hCoreCompile hPreserves
  exact ⟨valueCode, swap, artifact, hWhole, hRun⟩

theorem compiledExprPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx : Locals.Ctx)
    (expr : Functions.Expr 0)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : targetCtx.layout = transition.source)
    (hScoped : Functions.Scope.ExprScoped sourceEnv expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 expr = some ())
    (hLowered :
      lowered = [.expr expr] ++ StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    middleCtx = targetCtx.withLayout transition.schedule.target ∧
      headCode.length = transition.schedule.promotions.length + 2 ∧
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        transition.schedule.promotions.length + 2 < targetFuel →
        CtxCovers sourceCtx targetCtx →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (RegularOutcomeRel middleCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.expr expr) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := headCode } target) := by
  obtain ⟨exprCode, hExprCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition hSource
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some ([.code exprCode], targetCtx) := by
    simp [Locals.Stmt.compile, hExprCompile, Locals.codeStmt]
  have hCoreBlock :
      Locals.Block.compileOpen targetCtx { stmts := [.expr expr] } =
        some ([.code exprCode], targetCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hGenerated :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some
          ((.code exprCode) ::
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]),
           targetCtx.withLayout transition.schedule.target) := by
    rw [hLowered]
    simpa using
      Locals.Block.compileOpen_append hCoreBlock artifact.compileEq
  have hPair := Option.some.inj (hCompile.symm.trans hGenerated)
  have hCodeEq := congrArg Prod.fst hPair
  have hCtxEq := congrArg Prod.snd hPair
  change
    headCode =
      (.code exprCode) ::
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup]) at hCodeEq
  change
    middleCtx = targetCtx.withLayout transition.schedule.target at hCtxEq
  refine ⟨hCtxEq, ?_, ?_⟩
  · rw [hCodeEq]
    simp [artifact.codes.code_length]
  · intro sourceCtx sourceFuel targetFuel suffix returns source target
      hFuel hCtx hInitial
    obtain ⟨_runtimeCode, runtimeArtifact, hRuntimeCompile, hRun⟩ :=
      compiledExprPoint sourceProgram targetProgram sourceCtx targetCtx
        sourceFuel targetFuel expr transition lowered hSource hFuel hCtx
        hScoped hSupported hAccess hLowered hInitial
    have hRuntimePair :=
      Option.some.inj (hCompile.symm.trans hRuntimeCompile)
    have hRuntimeCodeEq := congrArg Prod.fst hRuntimePair
    have hRuntimeCtxEq := congrArg Prod.snd hRuntimePair
    change
      headCode =
        (.code _runtimeCode) ::
          (runtimeArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code runtimeArtifact.cleanup]) at hRuntimeCodeEq
    change middleCtx =
      targetCtx.withLayout transition.schedule.target at hRuntimeCtxEq
    simpa [hRuntimeCodeEq, hRuntimeCtxEq] using hRun

theorem compiledExprControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx middleCtx : Locals.Ctx)
    (expr : Functions.Expr 0)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : targetCtx.layout = transition.source)
    (hScoped : Functions.Scope.ExprScoped sourceEnv expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 expr = some ())
    (hLowered :
      lowered = [.expr expr] ++ StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx middleCtx (.expr expr) headCode transition.schedule.target := by
  obtain ⟨hMiddle, hLength, hForward⟩ :=
    compiledExprPointOfEquations sourceProgram targetProgram targetCtx middleCtx
      expr transition lowered headCode hSource hScoped hSupported hAccess
      hLowered hCompile
  refine ⟨?_, ?_⟩
  · rw [hMiddle]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hNumericFuel :
      transition.schedule.promotions.length + 2 < targetFuel := by
    rw [← hLength]
    exact hCodeLength
  have hRegular :=
    hForward sourceCtx sourceFuel targetFuel hNumericFuel hCtx.context hInitial
  apply regularRelToControl hRegular
  apply openRun_expr_controlCtx sourceProgram sourceCtx sourceFuel expr source
    targets middleCtx
  rw [hMiddle]
  exact hCtx.afterTransition transition hSource

theorem compiledLetPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx : Locals.Ctx)
    (name : Name) (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : name :: targetCtx.layout = transition.source)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 value = some ())
    (hLowered :
      lowered = [.let_ name value] ++
        StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    middleCtx =
        (targetCtx.withLayout (name :: targetCtx.layout)).withLayout
          transition.schedule.target ∧
      headCode.length = transition.schedule.promotions.length + 2 ∧
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        transition.schedule.promotions.length + 2 < targetFuel →
        CtxCovers sourceCtx targetCtx →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (RegularOutcomeRel middleCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.let_ name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := headCode } target) := by
  obtain ⟨valueCode, hValueCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  let pointCtx := targetCtx.withLayout (name :: targetCtx.layout)
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition
      (ctx := pointCtx) (by simpa [pointCtx, Locals.Ctx.withLayout] using hSource)
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.let_ name value) =
        some
          ([.code
              (valueCode ++
                Locals.bindLocals 0 (name :: targetCtx.layout))],
           pointCtx) := by
    simp [Locals.Stmt.compile, hValueCompile, Locals.codeStmt, pointCtx]
  have hCoreBlock :
      Locals.Block.compileOpen targetCtx { stmts := [.let_ name value] } =
        some
          ([.code
              (valueCode ++
                Locals.bindLocals 0 (name :: targetCtx.layout))],
           pointCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hGenerated :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some
          ((.code
              (valueCode ++
                Locals.bindLocals 0 (name :: targetCtx.layout))) ::
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]),
           pointCtx.withLayout transition.schedule.target) := by
    rw [hLowered]
    simpa using
      Locals.Block.compileOpen_append hCoreBlock artifact.compileEq
  have hPair := Option.some.inj (hCompile.symm.trans hGenerated)
  have hCodeEq := congrArg Prod.fst hPair
  have hCtxEq := congrArg Prod.snd hPair
  change
    headCode =
      (.code
          (valueCode ++
            Locals.bindLocals 0 (name :: targetCtx.layout))) ::
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup]) at hCodeEq
  change middleCtx =
    pointCtx.withLayout transition.schedule.target at hCtxEq
  refine ⟨by simpa [pointCtx] using hCtxEq, ?_, ?_⟩
  · rw [hCodeEq]
    simp [artifact.codes.code_length]
  · intro sourceCtx sourceFuel targetFuel suffix returns source target
      hFuel hCtx hInitial
    obtain ⟨_runtimeCode, runtimeArtifact, hRuntimeCompile, hRun⟩ :=
      compiledLetPoint sourceProgram targetProgram sourceCtx targetCtx
        sourceFuel targetFuel name value transition lowered hSource hFuel hCtx
        hFresh hScoped hSupported hAccess hLowered hInitial
    have hRuntimePair :=
      Option.some.inj (hCompile.symm.trans hRuntimeCompile)
    have hRuntimeCodeEq := congrArg Prod.fst hRuntimePair
    have hRuntimeCtxEq := congrArg Prod.snd hRuntimePair
    change
      headCode =
        (.code
            (_runtimeCode ++
              Locals.bindLocals 0 (name :: targetCtx.layout))) ::
          (runtimeArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code runtimeArtifact.cleanup]) at hRuntimeCodeEq
    change middleCtx =
      pointCtx.withLayout transition.schedule.target at hRuntimeCtxEq
    simpa [hRuntimeCodeEq, hRuntimeCtxEq, pointCtx] using hRun

theorem compiledLetControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx middleCtx : Locals.Ctx)
    (name : Name) (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : name :: targetCtx.layout = transition.source)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 value = some ())
    (hLowered :
      lowered = [.let_ name value] ++
        StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx middleCtx (.let_ name value) headCode
      transition.schedule.target := by
  obtain ⟨hMiddle, hLength, hForward⟩ :=
    compiledLetPointOfEquations sourceProgram targetProgram targetCtx middleCtx
      name value transition lowered headCode hSource hFresh hScoped hSupported
      hAccess hLowered hCompile
  refine ⟨?_, ?_⟩
  · rw [hMiddle]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hNumericFuel :
      transition.schedule.promotions.length + 2 < targetFuel := by
    rw [← hLength]
    exact hCodeLength
  have hRegular :=
    hForward sourceCtx sourceFuel targetFuel hNumericFuel hCtx.context hInitial
  apply regularRelToControl hRegular
  apply openRun_let_controlCtx sourceProgram sourceCtx sourceFuel name value
    source targets middleCtx
  rw [hMiddle]
  exact (hCtx.prepend name).afterTransition transition
    (by simpa [Locals.Ctx.withLayout] using hSource)

theorem compiledAssignPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx : Locals.Ctx)
    (name : Name) (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : targetCtx.layout = transition.source)
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.assign? targetCtx.layout name value = some ())
    (hLowered :
      lowered = [.assign name value] ++
        StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    middleCtx = targetCtx.withLayout transition.schedule.target ∧
      headCode.length = transition.schedule.promotions.length + 2 ∧
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        transition.schedule.promotions.length + 2 < targetFuel →
        CtxCovers sourceCtx targetCtx →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (RegularOutcomeRel middleCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.assign name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := headCode } target) := by
  obtain ⟨depth, swap, hValueAccess, hDepth, hSwap⟩ :=
    StackAccess.assign_components hAccess
  obtain ⟨valueCode, hValueCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check
      hValueAccess targetCtx rfl
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition hSource
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.assign name value) =
        some
          ([.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)],
           targetCtx) := by
    simp [Locals.Stmt.compile, hDepth, hValueCompile, hSwap,
      Locals.codeStmt]
  have hCoreBlock :
      Locals.Block.compileOpen targetCtx { stmts := [.assign name value] } =
        some
          ([.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)],
           targetCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hGenerated :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some
          ((.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)) ::
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]),
           targetCtx.withLayout transition.schedule.target) := by
    rw [hLowered]
    simpa using
      Locals.Block.compileOpen_append hCoreBlock artifact.compileEq
  have hPair := Option.some.inj (hCompile.symm.trans hGenerated)
  have hCodeEq := congrArg Prod.fst hPair
  have hCtxEq := congrArg Prod.snd hPair
  change
    headCode =
      (.code
          (valueCode ++ [.op swap, .op .pop] ++
            Locals.bindLocals 0 targetCtx.layout)) ::
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup]) at hCodeEq
  change middleCtx =
    targetCtx.withLayout transition.schedule.target at hCtxEq
  refine ⟨hCtxEq, ?_, ?_⟩
  · rw [hCodeEq]
    simp [artifact.codes.code_length]
  · intro sourceCtx sourceFuel targetFuel suffix returns source target
      hFuel hCtx hInitial
    obtain
        ⟨_runtimeValueCode, _runtimeSwap, runtimeArtifact,
          hRuntimeCompile, hRun⟩ :=
      compiledAssignPoint sourceProgram targetProgram sourceCtx targetCtx
        sourceFuel targetFuel name value transition lowered hSource hFuel hCtx
        hNodup hScoped hSupported hAccess hLowered hInitial
    have hRuntimePair :=
      Option.some.inj (hCompile.symm.trans hRuntimeCompile)
    have hRuntimeCodeEq := congrArg Prod.fst hRuntimePair
    have hRuntimeCtxEq := congrArg Prod.snd hRuntimePair
    change
      headCode =
        (.code
            (_runtimeValueCode ++ [.op _runtimeSwap, .op .pop] ++
              Locals.bindLocals 0 targetCtx.layout)) ::
          (runtimeArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code runtimeArtifact.cleanup]) at hRuntimeCodeEq
    change middleCtx =
      targetCtx.withLayout transition.schedule.target at hRuntimeCtxEq
    simpa [hRuntimeCodeEq, hRuntimeCtxEq] using hRun

theorem compiledAssignControlPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx middleCtx : Locals.Ctx)
    (name : Name) (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : targetCtx.layout = transition.source)
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.assign? targetCtx.layout name value = some ())
    (hLowered :
      lowered = [.assign name value] ++
        StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames
      targetCtx middleCtx (.assign name value) headCode
      transition.schedule.target := by
  obtain ⟨hMiddle, hLength, hForward⟩ :=
    compiledAssignPointOfEquations sourceProgram targetProgram targetCtx
      middleCtx name value transition lowered headCode hSource hNodup hScoped
      hSupported hAccess hLowered hCompile
  refine ⟨?_, ?_⟩
  · rw [hMiddle]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hNumericFuel :
      transition.schedule.promotions.length + 2 < targetFuel := by
    rw [← hLength]
    exact hCodeLength
  have hRegular :=
    hForward sourceCtx sourceFuel targetFuel hNumericFuel hCtx.context hInitial
  apply regularRelToControl hRegular
  apply openRun_assign_controlCtx sourceProgram sourceCtx sourceFuel name value
    source targets middleCtx
  rw [hMiddle]
  exact hCtx.afterTransition transition hSource

end StackStatementPreservation
end Functions
end EvmCompiler
