import EvmCompiler.Functions.AllocationObserverForward

namespace EvmCompiler
namespace Functions
namespace AllocationObserverDispatcher

open AllocationObserverRelation
open AllocationObserverForward

abbrev Trace := Assembly.ResourceTrace

namespace BodyCursor

/--
One fully dispatched source statement and its exact synchronized tail cursor.

Regular results retain the static transport and source-scope facts needed to
continue recursion. For abrupt results those fields are vacuous because the
tail is unreachable.
-/
structure HeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := stmt :: rest } lowerState localsCtx) where
  afterState : AllocationLowering.State
  afterLocals : Locals.Ctx
  headCode : List Expressions.Stmt
  tail :
    AllocationObserverForward.BodyCursor.Cursor prepared scope
      (Functions.Scope.Stmt.outEnv live stmt)
      { stmts := rest } afterState afterLocals
  compiled : cursor.compiled = headCode ++ tail.compiled
  tailPlan : tail.plan = cursor.plan
  tailFinalState : tail.finalState = cursor.finalState
  tailFinalLocals : tail.finalLocals = cursor.finalLocals
  runtime :
    ∃ targetOutcome,
      AllocationObserverOutcome.StmtRuntimeResult
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx afterState afterLocals cursor.plan fn.returns
        (Functions.Scope.Stmt.outEnv live stmt) frameBase mode program
        sourceCtx stmt source expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceOutcome targetOutcome finalCtx
  regularTransport :
    sourceOutcome.mode = .regular →
      AllocationObserverForward.BodyCursor.StepTransport
        lowerState afterState localsCtx afterLocals live stmt
  regularScope :
    sourceOutcome.mode = .regular →
      ∀ name,
        name ∈ finalCtx.scope ↔
          name ∈ Functions.Scope.Stmt.outEnv live stmt

namespace HeadResult

def regular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {headCode : List Expressions.Stmt}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope afterLive
        { stmts := rest } afterState afterLocals)
    (hAfterLive :
      afterLive = Functions.Scope.Stmt.outEnv live stmt)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hTailPlan : tail.plan = cursor.plan)
    (hTailFinalState : tail.finalState = cursor.finalState)
    (hTailFinalLocals : tail.finalLocals = cursor.finalLocals)
    (hForward :
      AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx afterState afterLocals cursor.plan afterLive
        frameBase beforeMode afterMode program sourceCtx stmt source
        expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceFinal targetFinal finalCtx)
    (hControl :
      AllocationObserverOutcome.SameControl sourceCtx finalCtx)
    (hStep :
      AllocationObserverForward.BodyCursor.StepTransport
        beforeState afterState beforeLocals afterLocals live stmt)
    (hScope :
      ∀ name, name ∈ finalCtx.scope ↔ name ∈ afterLive) :
    HeadResult cursor
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := beforeMode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := Functions.Source.Effectful.Outcome.regular
        sourceFinal) := by
  subst afterLive
  exact
    { afterState := afterState
      afterLocals := afterLocals
      headCode := headCode
      tail := tail
      compiled := hCompiled
      tailPlan := hTailPlan
      tailFinalState := hTailFinalState
      tailFinalLocals := hTailFinalLocals
      runtime :=
        ⟨Structured.EffectSemantics.Outcome.regular targetFinal,
          .regular hForward hControl⟩
      regularTransport := fun _ => hStep
      regularScope := fun _ => hScope }

def nonregular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode finalMode : ActivationMode}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    {headCode : List Expressions.Stmt}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope afterLive
        { stmts := rest } afterState afterLocals)
    (hAfterLive :
      afterLive = Functions.Scope.Stmt.outEnv live stmt)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hTailPlan : tail.plan = cursor.plan)
    (hTailFinalState : tail.finalState = cursor.finalState)
    (hTailFinalLocals : tail.finalLocals = cursor.finalLocals)
    (hForward :
      AllocationObserverOutcome.NonregularStmtRuntimeForward
        program.memoryContract config allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive
          fn.returns afterLive sourceCtx sourceOutcome.mode)
        frameBase beforeMode finalMode program sourceCtx stmt source
        expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceOutcome targetOutcome stmtCtx) :
    HeadResult cursor
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := beforeMode)
      (sourceCtx := sourceCtx) (finalCtx := stmtCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) := by
  have hMode : sourceOutcome.mode ≠ .regular := by
    rcases hForward with
      ⟨_sourceFuel, _targetFuel, _hSource, _hTarget,
        hMode, _hRel, _hSame, _hEffect⟩
    exact hMode
  subst afterLive
  exact
    { afterState := afterState
      afterLocals := afterLocals
      headCode := headCode
      tail := tail
      compiled := hCompiled
      tailPlan := hTailPlan
      tailFinalState := hTailFinalState
      tailFinalLocals := hTailFinalLocals
      runtime := ⟨targetOutcome, .nonregular hForward⟩
      regularTransport := fun hRegular => False.elim (hMode hRegular)
      regularScope := fun hRegular => False.elim (hMode hRegular) }

end HeadResult

/--
All semantic and static facts threaded by the canonical source-fuel
statement/block dispatcher.

The bundle contains source-facing context facts and the existing adjacent-pass
runtime invariant only. It does not contain generated code evidence, replay
data, or recursive preservation obligations.
-/
structure Boundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx) : Prop where
  sourceScope :
    ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live
  control :
    AllocationObserverOutcome.ControlScopesWithin
      fn.returns live sourceCtx
  destinations :
    AllocationObserverOutcome.ControlDestinations
      artifact.lowerCtx lowerState localsCtx cursor.plan live mode sourceCtx
  returnFrame :
    ∀ functionScope,
      sourceCtx.leaveScope? = some functionScope →
        target.source.returns ≠ []
  leaveTarget :
    ∀ functionScope,
      sourceCtx.leaveScope? = some functionScope →
        localsCtx.leaveDepth? = some 0 ∧
          localsCtx.leaveRetc = fn.returns.length
  budget : Frame.Budget config allocatorDepth
  invariant :
    AllocationObserverContext.ActivationRuntimeInvariant
      program.memoryContract config allocatorDepth artifact.lowerCtx
      lowerState localsCtx cursor.plan live frameBase mode source target

namespace Boundary

/--
Transport the dispatcher boundary across one regular statement.

The source and Locals control contexts, allocation state, live environment,
activation mode, return-frame availability, and allocator invariant all move
through their pass-owned relations.
-/
def afterRegular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {beforeLive afterLive : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase targetFuel : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {beforeCtx afterCtx : Functions.Source.Ctx}
    {beforeSource afterSource :
      Functions.ObserverSemantics.State transcript}
    {beforeTarget afterTarget :
      Structured.ObserverSemantics.State transcript}
    {headCode : List Structured.Stmt}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope beforeLive
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope afterLive
        { stmts := rest } afterState afterLocals)
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := beforeMode)
        (sourceCtx := beforeCtx) (source := beforeSource)
        (target := beforeTarget))
    (hAfterLive :
      afterLive = Functions.Scope.Stmt.outEnv beforeLive stmt)
    (hStep :
      AllocationObserverForward.BodyCursor.StepTransport
        beforeState afterState beforeLocals afterLocals beforeLive stmt)
    (hSourceControl :
      AllocationObserverOutcome.SameControl beforeCtx afterCtx)
    (hSameFrame : SameFrame beforeMode afterMode)
    (hSourceScope :
      ∀ name, name ∈ afterCtx.scope ↔ name ∈ afterLive)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured targetFuel { stmts := headCode } beforeTarget
          (Structured.EffectSemantics.Outcome.regular afterTarget))
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        afterState afterLocals tail.plan afterLive frameBase afterMode
        afterSource afterTarget) :
    Boundary tail (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := afterMode)
      (sourceCtx := afterCtx) (source := afterSource)
      (target := afterTarget) :=
  { sourceScope := hSourceScope
    control :=
      by
        rw [hAfterLive]
        exact
          hSourceControl.controlScopesWithin_outEnv hBoundary.control
    destinations :=
      AllocationObserverOutcome.ControlDestinations.transport
        hBoundary.destinations hSourceControl hStep.locals hStep.state
        (by
          intro name hName
          rw [hAfterLive]
          exact hStep.live name hName)
        hSameFrame
    returnFrame := by
      intro functionScope hLeave
      have hBeforeLeave :
          beforeCtx.leaveScope? = some functionScope :=
        hSourceControl.leaveScope.trans hLeave
      have hReturns :=
        Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
          hTarget
          (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
      simp only [Structured.ObserverSemantics.Outcome.regular_state] at hReturns
      rw [hReturns]
      exact hBoundary.returnFrame functionScope hBeforeLeave
    leaveTarget := by
      intro functionScope hLeave
      have hBeforeLeave :
          beforeCtx.leaveScope? = some functionScope :=
        hSourceControl.leaveScope.trans hLeave
      obtain ⟨hDepth, hRetc⟩ :=
        hBoundary.leaveTarget functionScope hBeforeLeave
      constructor
      · rw [← hStep.locals.leaveDepth]
        exact hDepth
      · rw [← hStep.locals.leaveRetc]
        exact hRetc
    budget := hBoundary.budget
    invariant := hInvariant }

/--
The empty synchronized cursor is the base case of the source-fuel dispatcher.
-/
theorem nilRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := [] } lowerState localsCtx)
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target))
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel { stmts := [] } source =
        .ok (sourceOutcome, finalCtx)) :
    ∃ targetOutcome,
      AllocationObserverOutcome.BlockRuntimeResult
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        fn.returns live frameBase mode program sourceCtx
        { stmts := [] } source expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceOutcome targetOutcome finalCtx := by
  cases sourceFuel with
  | zero =>
      simp [Functions.Source.Effectful.Block.runOpen,
        Functions.Source.invalid, Structured.invalid] at hSource
  | succ fuel =>
      have hEq :
          (Functions.Source.Effectful.Outcome.regular source, sourceCtx) =
            (sourceOutcome, finalCtx) := by
        simpa [Functions.Source.Effectful.Block.runOpen] using hSource
      cases hEq
      exact
        ⟨Structured.EffectSemantics.Outcome.regular target,
          cursor.nilRuntimeResult hBoundary.invariant⟩

/--
Compose one dispatched head with recursive preservation of its exact tail.

This is the sequence kernel of the source-fuel dispatcher. The only recursive
argument is the regular-tail callback; abrupt heads use the canonical
`runOpen` fact that the whole block returns the head outcome and original
context.
-/
theorem consRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx headCtx blockCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {headSourceOutcome blockSourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target))
    (head :
      HeadResult cursor
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := headCtx)
        (source := source) (target := target)
        (sourceOutcome := headSourceOutcome))
    (hTail :
      ∀ {sourceMid :
            Functions.ObserverSemantics.State transcript}
        {targetMid : Structured.ObserverSemantics.State transcript}
        {midMode : ActivationMode},
        AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
            program.memoryContract config allocatorDepth transcript
            artifact.lowerCtx head.afterState head.afterLocals cursor.plan
            (Functions.Scope.Stmt.outEnv live stmt) frameBase mode midMode
            program sourceCtx stmt source expressions.toStructured target
            (Expressions.StmtList.toStructured head.headCode)
            sourceMid targetMid headCtx →
        AllocationObserverOutcome.SameControl sourceCtx headCtx →
        Boundary head.tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := midMode)
            (sourceCtx := headCtx) (source := sourceMid)
            (target := targetMid) →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config allocatorDepth transcript
            artifact.lowerCtx head.tail.finalState head.tail.finalLocals
            head.tail.plan fn.returns
            (Functions.Scope.Block.outEnv
              (Functions.Scope.Stmt.outEnv live stmt)
              { stmts := rest })
            frameBase midMode program headCtx { stmts := rest } sourceMid
            expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured head.tail.compiled }
            targetMid blockSourceOutcome targetOutcome blockCtx)
    (hAbrupt :
      headSourceOutcome.mode ≠ .regular →
        blockSourceOutcome = headSourceOutcome ∧ blockCtx = sourceCtx) :
    ∃ targetOutcome,
      AllocationObserverOutcome.BlockRuntimeResult
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        fn.returns
        (Functions.Scope.Block.outEnv live { stmts := stmt :: rest })
        frameBase mode program sourceCtx { stmts := stmt :: rest } source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target blockSourceOutcome targetOutcome blockCtx := by
  obtain ⟨_headTargetOutcome, hRuntime⟩ := head.runtime
  cases hRuntime with
  | @regular sourceMid targetMid midMode _ hForward hControl =>
      have hForwardCopy := hForward
      rcases hForward with
        ⟨_sourceFuel, targetFuel, _hSource, hTarget,
          hInvariant, hSameFrame, _hEffect⟩
      have hTailInvariant :
          AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config allocatorDepth artifact.lowerCtx
            head.afterState head.afterLocals head.tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase midMode sourceMid targetMid := by
        rw [head.tailPlan]
        exact hInvariant
      have hTailBoundary :
          Boundary head.tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := midMode)
            (sourceCtx := headCtx) (source := sourceMid)
            (target := targetMid) :=
        hBoundary.afterRegular cursor head.tail rfl
          (head.regularTransport rfl) hControl hSameFrame
          (head.regularScope rfl) hTarget hTailInvariant
      obtain ⟨tailTargetOutcome, hTailResult⟩ :=
        hTail hForwardCopy hControl hTailBoundary
      exact
        ⟨tailTargetOutcome,
          cursor.consRegularRuntimeResult head.tail head.tailPlan
            head.tailFinalState head.tailFinalLocals head.compiled
            hForwardCopy hControl hTailResult⟩
  | @nonregular sourceAbrupt targetAbrupt finalMode _ hForward =>
      have hForwardCopy := hForward
      rcases hForward with
        ⟨_sourceFuel, _targetFuel, _hSource, _hTarget,
          hMode, _hRel, _hSame, _hEffect⟩
      obtain ⟨rfl, rfl⟩ := hAbrupt hMode
      have hForwardFinal :=
        AllocationObserverOutcome.NonregularStmtRuntimeForward.reindex_regularLive
          (afterLive :=
            Functions.Scope.Block.outEnv live { stmts := stmt :: rest })
          hForwardCopy
      exact
        ⟨_headTargetOutcome,
          cursor.consNonregularRuntimeResult head.compiled hForwardFinal⟩

end Boundary
end BodyCursor

end AllocationObserverDispatcher
end Functions
end EvmCompiler
