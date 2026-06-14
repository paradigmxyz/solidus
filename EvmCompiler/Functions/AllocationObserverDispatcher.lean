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
        { stmts := stmt :: rest } lowerState localsCtx)
    (afterState : AllocationLowering.State)
    (afterLocals : Locals.Ctx)
    (headCode : List Expressions.Stmt)
    (tail :
    AllocationObserverForward.BodyCursor.Cursor prepared scope
      (Functions.Scope.Stmt.outEnv live stmt)
      { stmts := rest } afterState afterLocals) : Prop where
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

/--
Package one pass-owned statement result together with the exact tail cursor
returned by the real lowering and Locals compiler.
-/
def ofRuntime
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
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
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
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    {headCode : List Expressions.Stmt}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hRuntime :
      AllocationObserverOutcome.StmtRuntimeResult
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx afterState afterLocals cursor.plan fn.returns
        (Functions.Scope.Stmt.outEnv live stmt) frameBase mode program
        sourceCtx stmt source expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceOutcome targetOutcome finalCtx)
    (hStep :
      AllocationObserverForward.BodyCursor.StepTransport
        beforeState afterState beforeLocals afterLocals live stmt)
    (hExact :
      AllocationObserverForward.BodyCursor.ExactTail cursor tail)
    (hScope :
      sourceOutcome.mode = .regular →
        ∀ name,
          name ∈ finalCtx.scope ↔
            name ∈ Functions.Scope.Stmt.outEnv live stmt) :
    HeadResult cursor afterState afterLocals headCode tail
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) :=
  { compiled := hCompiled
    tailPlan := hExact.plan
    tailFinalState := hExact.finalState
    tailFinalLocals := hExact.finalLocals
    runtime := ⟨targetOutcome, hRuntime⟩
    regularTransport := fun _ => hStep
    regularScope := hScope }

/--
Package an abrupt pass-owned statement result. No regular-step transport is
required because the source outcome proves that the tail is unreachable.
-/
def ofNonregular
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
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
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
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    {headCode : List Expressions.Stmt}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hRuntime :
      AllocationObserverOutcome.StmtRuntimeResult
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx afterState afterLocals cursor.plan fn.returns
        (Functions.Scope.Stmt.outEnv live stmt) frameBase mode program
        sourceCtx stmt source expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceOutcome targetOutcome finalCtx)
    (hExact :
      AllocationObserverForward.BodyCursor.ExactTail cursor tail)
    (hMode : sourceOutcome.mode ≠ .regular) :
    HeadResult cursor afterState afterLocals headCode tail
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) :=
  { compiled := hCompiled
    tailPlan := hExact.plan
    tailFinalState := hExact.finalState
    tailFinalLocals := hExact.finalLocals
    runtime := ⟨targetOutcome, hRuntime⟩
    regularTransport := fun hRegular => False.elim (hMode hRegular)
    regularScope := fun hRegular => False.elim (hMode hRegular) }

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
    HeadResult cursor afterState afterLocals headCode (by
      subst afterLive
      exact tail)
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := beforeMode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := Functions.Source.Effectful.Outcome.regular
        sourceFinal) := by
  subst afterLive
  exact
    { compiled := hCompiled
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
    HeadResult cursor afterState afterLocals headCode (by
      subst afterLive
      exact tail)
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
    { compiled := hCompiled
      tailPlan := hTailPlan
      tailFinalState := hTailFinalState
      tailFinalLocals := hTailFinalLocals
      runtime := ⟨targetOutcome, .nonregular hForward⟩
      regularTransport := fun hRegular => False.elim (hMode hRegular)
      regularScope := fun hRegular => False.elim (hMode hRegular) }

/--
Dispatch a zero-result expression statement from its successful canonical
source run.
-/
theorem exprOfSafeRun
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
    {expr : Functions.Expr 0}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := .expr expr :: rest } beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.expr expr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular sourceFinal) := by
  have hSourceCopy := hSource
  simp only [Functions.Source.Effectful.Stmt.run] at hSourceCopy
  cases hEval :
      Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        expr source with
  | error err =>
      simp [hEval] at hSourceCopy
  | ok result =>
      rcases result with ⟨evalFinal, values⟩
      simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
      have hEq :
          (Functions.Source.Effectful.Outcome.regular evalFinal, sourceCtx) =
            (Functions.Source.Effectful.Outcome.regular sourceFinal,
              sourceCtx) :=
        Except.ok.inj hSourceCopy
      cases hEq
      obtain
          ⟨afterState, afterLocals, headCode, tail, targetFinal,
            hCompiled, hRuntime, hStep, hExact⟩ :=
        cursor.exprRuntimeResult hConfig
          (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_eval hEval)
          hInvariant
      exact
        ⟨afterState, afterLocals, headCode, tail,
          ofRuntime cursor tail hCompiled hRuntime hStep hExact
            (by
              intro _ name
              simpa [Functions.Scope.Stmt.outEnv] using hSourceScope name)⟩

/--
Dispatch an assignment from its successful canonical source run.
-/
theorem assignOfSafeRun
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
    {name : Functions.Name}
    {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := .assign name valueExpr :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.assign name valueExpr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hSourceScope :
      ∀ localName, localName ∈ sourceCtx.scope ↔ localName ∈ live)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular sourceFinal) := by
  have hSourceCopy := hSource
  simp only [Functions.Source.Effectful.Stmt.run] at hSourceCopy
  cases hContains :
      (Functions.ObserverSemantics.stateModel transcript).vars source
        |>.contains name with
  | false =>
      simp [hContains, Functions.Source.invalid, Structured.invalid] at hSourceCopy
  | true =>
      simp only [hContains, ↓reduceIte] at hSourceCopy
      cases hEval :
          Functions.Source.Effectful.Expr.evalOne
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            valueExpr source with
      | error err =>
          simp [hEval] at hSourceCopy
      | ok result =>
          rcases result with ⟨evalFinal, value⟩
          simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
          have hEq :
              (Functions.Source.Effectful.Outcome.regular
                  ((Functions.ObserverSemantics.stateModel transcript).withVars
                    evalFinal
                    (Locals.Source.Store.insert
                      ((Functions.ObserverSemantics.stateModel transcript).vars
                        evalFinal)
                      name value)),
                sourceCtx) =
              (Functions.Source.Effectful.Outcome.regular sourceFinal,
                sourceCtx) :=
            Except.ok.inj hSourceCopy
          cases hEq
          obtain
              ⟨afterState, afterLocals, headCode, tail, targetFinal,
                hCompiled, hRuntime, hStep, hExact⟩ :=
            cursor.assignRuntimeResult hConfig
              (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
                hEval)
              hInvariant
          exact
            ⟨afterState, afterLocals, headCode, tail,
              ofRuntime cursor tail hCompiled hRuntime hStep hExact
                (by
                  intro _ localName
                  simpa [Functions.Scope.Stmt.outEnv] using
                    hSourceScope localName)⟩

/--
Dispatch a declaration from its successful canonical source run.
-/
theorem letOfSafeRun
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
    {name : Functions.Name}
    {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := .let_ name valueExpr :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.let_ name valueExpr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            finalCtx))
    (hSourceScope :
      ∀ localName, localName ∈ sourceCtx.scope ↔ localName ∈ live)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope
          (name :: live) { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular sourceFinal) := by
  have hSourceCopy := hSource
  simp only [Functions.Source.Effectful.Stmt.run] at hSourceCopy
  cases hEval :
      Functions.Source.Effectful.Expr.evalOne
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        valueExpr source with
  | error err =>
      simp [hEval] at hSourceCopy
  | ok result =>
      rcases result with ⟨evalFinal, value⟩
      simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
      have hEq :
          (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).insert
                evalFinal name value),
            { sourceCtx with scope := name :: sourceCtx.scope }) =
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            finalCtx) :=
        Except.ok.inj hSourceCopy
      cases hEq
      obtain
          ⟨afterState, afterLocals, headCode, tail, targetFinal,
            hCompiled, hRuntime, hStep, hExact⟩ :=
        cursor.letRuntimeResult hConfig
          (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne hEval)
          hInvariant
      exact
        ⟨afterState, afterLocals, headCode, tail,
          ofRuntime cursor tail hCompiled hRuntime hStep hExact
            (by
              intro _ localName
              simp only [Functions.Scope.Stmt.outEnv, List.mem_cons]
              exact or_congr Iff.rfl (hSourceScope localName))⟩

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
        sourceBlock lowerState localsCtx) where
  sourceScope :
    ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live
  control :
    AllocationObserverOutcome.ControlScopesWithin
      fn.returns live sourceCtx
  destinations :
    AllocationObserverOutcome.ControlDestinations
      artifact.lowerCtx lowerState localsCtx cursor.plan live mode sourceCtx
  returnFrame :
    AllocationObserverOutcome.ReturnFrameAvailable sourceCtx target
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

/--
Outcome-indexed exact loop-control evidence for one recursively dispatched
block.

The ordinary runtime theorem remains pass-owned. This relation adds only the
claim that `break` and `continue` finish at the canonical destination already
carried by the shared dispatcher boundary.
-/
structure ControlOutcomeForward
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
        sourceBlock lowerState localsCtx)
    (boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)) : Prop where
  brk :
    ∀ sourceFinal,
      sourceOutcome =
          Functions.Source.Effectful.Outcome.brk sourceFinal →
        ∃ targetFinal,
          targetOutcome =
              Structured.EffectSemantics.Outcome.brk targetFinal ∧
            AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant
              (contract := program.memoryContract) (config := config)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              boundary.destinations.brk sourceFinal targetFinal
  cont :
    ∀ sourceFinal,
      sourceOutcome =
          Functions.Source.Effectful.Outcome.cont sourceFinal →
        ∃ targetFinal,
          targetOutcome =
              Structured.EffectSemantics.Outcome.cont targetFinal ∧
            AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant
              (contract := program.memoryContract) (config := config)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              boundary.destinations.cont sourceFinal targetFinal

/--
One dispatched statement whose exact target outcome is shared by the ordinary
statement theorem and the dispatcher-only control-destination evidence.
-/
structure ControlledHeadResult
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
        { stmts := stmt :: rest } lowerState localsCtx)
    (boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (afterState : AllocationLowering.State)
    (afterLocals : Locals.Ctx)
    (headCode : List Expressions.Stmt)
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals) : Prop where
  head :
    HeadResult cursor afterState afterLocals headCode tail
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome)
  runtime :
    ∃ targetOutcome,
      AllocationObserverOutcome.StmtRuntimeResult
          program.memoryContract config allocatorDepth transcript
          artifact.lowerCtx afterState afterLocals cursor.plan fn.returns
          (Functions.Scope.Stmt.outEnv live stmt) frameBase mode program
          sourceCtx stmt source expressions.toStructured target
          (Expressions.StmtList.toStructured headCode)
          sourceOutcome targetOutcome finalCtx ∧
        ControlOutcomeForward cursor boundary sourceOutcome targetOutcome

/--
One recursively dispatched open block.

The runtime theorem remains the pass-owned `BlockRuntimeResult`. The only
dispatcher-specific addition is the outgoing source scope needed to enter
subsequent lexical loop components after a regular initializer.
-/
structure BlockResult
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
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx)
    (boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) : Prop where
  runtime :
    ∃ targetOutcome,
      AllocationObserverOutcome.BlockRuntimeResult
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        fn.returns (Functions.Scope.Block.outEnv live sourceBlock)
        frameBase mode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceOutcome targetOutcome finalCtx ∧
      ControlOutcomeForward cursor boundary sourceOutcome targetOutcome
  regularScope :
    sourceOutcome.mode = .regular →
      ∀ name,
        name ∈ finalCtx.scope ↔
          name ∈ Functions.Scope.Block.outEnv live sourceBlock

/--
The sole recursive interface used by structured statement adapters.

Every recursive call targets a real synchronized cursor, consumes a strictly
smaller source fuel, and receives only the shared source/control/allocation
boundary. Generated code and recursive proof evidence stay out of the public
boundary.
-/
def RecursiveBlockForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {config : Frame.Config}
    {allocatorDepth frameBase fuelBound : Nat}
    {transcript : Trace} : Prop :=
  ∀ {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceFuel : Nat}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx),
    sourceFuel < fuelBound →
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) →
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program sourceCtx sourceFuel sourceBlock source =
      .ok (sourceOutcome, finalCtx) →
    BlockResult cursor hBoundary (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome)

namespace BlockResult

theorem regular
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
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx)
    (boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (result :
      BlockResult cursor boundary (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome :=
          Functions.Source.Effectful.Outcome.regular sourceFinal)) :
    ∃ targetFinal finalMode,
      AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        (Functions.Scope.Block.outEnv live sourceBlock)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceFinal targetFinal finalCtx ∧
      AllocationObserverOutcome.SameControl sourceCtx finalCtx := by
  obtain ⟨targetOutcome, hRuntime, _hControlOutcome⟩ := result.runtime
  cases hRuntime with
  | regular hForward hControl =>
      exact ⟨_, _, hForward, hControl⟩
  | nonregular hMode _ =>
      exact False.elim (hMode rfl)

theorem nonregular
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
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx)
    (boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (result :
      BlockResult cursor boundary (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome := sourceOutcome))
    (hMode : sourceOutcome.mode ≠ .regular) :
    ∃ targetOutcome finalMode,
      AllocationObserverOutcome.BlockRuntimeForward
        program.memoryContract config allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive fn.returns
          (Functions.Scope.Block.outEnv live sourceBlock)
          sourceCtx sourceOutcome.mode)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceOutcome targetOutcome finalCtx := by
  obtain ⟨targetOutcome, hRuntime, _hControlOutcome⟩ := result.runtime
  cases hRuntime with
  | regular _ _ =>
      exact False.elim (hMode rfl)
  | nonregular _ hForward =>
      exact ⟨targetOutcome, _, hForward⟩

end BlockResult

namespace Boundary

/--
Invoke the recursive block interface at a regular open-block result.
-/
theorem recursiveRegular
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
    {allocatorDepth frameBase fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (prepared := prepared)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel sourceBlock source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            finalCtx)) :
    ∃ targetFinal finalMode,
      AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        (Functions.Scope.Block.outEnv live sourceBlock)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceFinal targetFinal finalCtx ∧
      AllocationObserverOutcome.SameControl sourceCtx finalCtx ∧
      (∀ name,
        name ∈ finalCtx.scope ↔
          name ∈ Functions.Scope.Block.outEnv live sourceBlock) := by
  have hResult :=
    hRecursive cursor hFuel hBoundary hSource
  obtain ⟨targetFinal, finalMode, hForward, hControl⟩ :=
    hResult.regular
  exact
    ⟨targetFinal, finalMode, hForward, hControl,
      hResult.regularScope rfl⟩

/--
Invoke the recursive block interface at an abrupt open-block result.
-/
theorem recursiveNonregular
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
    {allocatorDepth frameBase fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (prepared := prepared)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel sourceBlock source =
        .ok (sourceOutcome, finalCtx))
    (hMode : sourceOutcome.mode ≠ .regular) :
    ∃ targetOutcome finalMode,
      AllocationObserverOutcome.BlockRuntimeForward
        program.memoryContract config allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive fn.returns
          (Functions.Scope.Block.outEnv live sourceBlock)
          sourceCtx sourceOutcome.mode)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceOutcome targetOutcome finalCtx :=
  BlockResult.nonregular cursor
    hBoundary (hRecursive cursor hFuel hBoundary hSource) hMode

/--
Discharge one regular scoped block through recursive open-block preservation
and the statement-owned lexical cleanup theorem.
-/
theorem recursiveScopedRegular
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
    {allocatorDepth frameBase fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetBlock : Expressions.Block}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (prepared := prepared)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hSource :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceBlock sourceFuel source =
        .ok (Functions.Source.Effectful.Outcome.regular sourceFinal))
    (hAfterCompiler :
      AllocationObserverContext.ActivationExprContext
        artifact.lowerCtx lowerState localsCtx cursor.plan live mode)
    (hFinish :
      Locals.finishScoped localsCtx cursor.finalLocals cursor.compiled =
        some targetBlock) :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularScopedBlockRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx lowerState localsCtx cursor.plan live frameBase mode
        program sourceCtx sourceBlock source expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured targetBlock.stmts }
        target sourceFinal targetFinal := by
  rcases
      Functions.Source.Effectful.Block.runScoped_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hRegular | hNonregular
  · rcases hRegular with
      ⟨openFinal, finalCtx, hOpen, hOutcome⟩
    have hRestrict :
        (Functions.ObserverSemantics.stateModel transcript).restrictTo
            sourceCtx.scope openFinal =
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
            live openFinal :=
      Locals.Source.Effectful.StateModel.restrictTo_congr
        (Functions.ObserverSemantics.stateModel transcript)
        hBoundary.sourceScope
    have hFinal :
        sourceFinal =
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
            live openFinal := by
      have hState :=
        congrArg Locals.Source.Effectful.Outcome.state hOutcome
      rw [hRestrict] at hState
      simpa [Functions.Source.Effectful.Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] using hState
    obtain
        ⟨targetMid, finalMode, hForward, _hControl, _hScope⟩ :=
      recursiveRegular cursor hRecursive hFuel hBoundary hOpen
    obtain ⟨targetFinal, hScoped⟩ :=
      AllocationObserverStatement.Sequence.RegularScopedBlockRuntimeInvariantForward.finish_regular
        hForward hBoundary.sourceScope rfl hAfterCompiler cursor.planWF
        (fun _ hName => Functions.Scope.Block.mem_outEnv hName)
        cursor.sourceScoped cursor.lower hFinish
    rw [← hFinal] at hScoped
    exact ⟨targetFinal, hScoped⟩
  · rcases hNonregular with
      ⟨openOutcome, finalCtx, hOpen, hMode, hOutcome⟩
    have hImpossible :
        (Functions.Source.Effectful.Outcome.regular sourceFinal).mode ≠
          .regular := by
      rw [hOutcome]
      exact hMode
    exact False.elim (hImpossible rfl)

/--
Discharge one abrupt scoped block through recursive open-block preservation.
The compiler-emitted lexical cleanup is unreachable and is accounted for by
the statement-owned nonregular scoped theorem.
-/
theorem recursiveScopedNonregular
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
    {allocatorDepth frameBase fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetBlock : Expressions.Block}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (prepared := prepared)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hSource :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceBlock sourceFuel source =
        .ok sourceOutcome)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hFinish :
      Locals.finishScoped localsCtx cursor.finalLocals cursor.compiled =
        some targetBlock) :
    ∃ targetOutcome finalMode,
      AllocationObserverOutcome.ScopedBlockRuntimeForward
        program.memoryContract config allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive fn.returns
          (Functions.Scope.Block.outEnv live sourceBlock)
          sourceCtx sourceOutcome.mode)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured targetBlock.stmts }
        target sourceOutcome targetOutcome := by
  rcases
      Functions.Source.Effectful.Block.runScoped_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hRegular | hNonregular
  · rcases hRegular with
      ⟨openFinal, finalCtx, hOpen, hOutcome⟩
    have hImpossible :
        sourceOutcome.mode = .regular := by
      rw [hOutcome]
      rfl
    exact False.elim (hMode hImpossible)
  · rcases hNonregular with
      ⟨openOutcome, finalCtx, hOpen, hOpenMode, hOutcome⟩
    subst sourceOutcome
    obtain ⟨targetOutcome, finalMode, hForward⟩ :=
      recursiveNonregular cursor hRecursive hFuel hBoundary hOpen hOpenMode
    exact
      ⟨targetOutcome, finalMode,
        AllocationObserverStatement.Sequence.ScopedBlockRuntimeForward.finish_nonregular
          hForward hOpenMode hFinish⟩

/--
Enter a `for` initializer through its real lexical cursor.

The source and Locals contexts both disable loop control. The initializer plan
may include locations for declarations introduced later in the loop, so the
runtime invariant is transported only on the currently live outer bindings.
-/
def forInit
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {outerScope initScope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {outerBlock init : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.Cursor prepared outerScope live
        outerBlock lowerState localsCtx)
    (initCursor :
      AllocationObserverForward.BodyCursor.Cursor prepared initScope live
        init lowerState localsCtx.withoutLoopControl)
    (hBoundary :
      Boundary outer (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    Boundary initCursor (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
      (source := source) (target := target) := by
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        initCursor.plan outer.plan live :=
    initCursor.planAgreesOn outer rfl
  have hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        lowerState localsCtx.withoutLoopControl initCursor.plan live
        frameBase mode source target :=
    (hBoundary.invariant.transport_locals_layout
        (after := localsCtx.withoutLoopControl) rfl).transport_plan
      initCursor.planWF hPlanAgree.symm
  refine
    { sourceScope := ?_
      control :=
        AllocationObserverOutcome.ControlScopesWithin.withoutLoopControl
          hBoundary.control
      destinations :=
        AllocationObserverOutcome.ControlDestinations.withoutLoopControl
      returnFrame := ?_
      leaveTarget := ?_
      budget := hBoundary.budget
      invariant := hInvariant }
  · intro name
    simpa [Functions.Source.Ctx.withoutLoopControl] using
      hBoundary.sourceScope name
  · intro functionScope hLeave
    exact
      hBoundary.returnFrame functionScope
        (by
          simpa [Functions.Source.Ctx.withoutLoopControl] using hLeave)
  · intro functionScope hLeave
    obtain ⟨hDepth, hRetc⟩ :=
      hBoundary.leaveTarget functionScope
        (by
          simpa [Functions.Source.Ctx.withoutLoopControl] using hLeave)
    exact
      ⟨by
        simpa [Locals.Ctx.withoutLoopControl] using hDepth,
        by
          simpa [Locals.Ctx.withoutLoopControl] using hRetc⟩

/--
Recursively preserve a regular loop initializer through its exact lexical
cursor, retaining the control equivalence and outgoing loop scope needed by
both regular and activation-exit loop execution.
-/
theorem recursiveForInitRegular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {outerScope initScope : Locals.Allocation.ScopeId}
    {outerLive : List Functions.Name}
    {outerBlock init : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx initCtx : Functions.Source.Ctx}
    {source sourceAfterInit :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.Cursor prepared outerScope outerLive
        outerBlock lowerState localsCtx)
    (initCursor :
      AllocationObserverForward.BodyCursor.Cursor prepared initScope outerLive
        init lowerState localsCtx.withoutLoopControl)
    (hBoundary :
      Boundary outer (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      RecursiveBlockForward (prepared := prepared)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx.withoutLoopControl sourceFuel init source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceAfterInit,
            initCtx)) :
    ∃ targetAfterInit initMode,
      AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        artifact.lowerCtx initCursor.finalState initCursor.finalLocals
        initCursor.plan (Functions.Scope.Block.outEnv outerLive init)
        frameBase mode initMode program sourceCtx.withoutLoopControl init source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured initCursor.compiled }
        target sourceAfterInit targetAfterInit initCtx ∧
      AllocationObserverOutcome.SameControl
        sourceCtx.withoutLoopControl initCtx ∧
      (∀ name,
        name ∈ initCtx.scope ↔
          name ∈ Functions.Scope.Block.outEnv outerLive init) := by
  exact
    recursiveRegular initCursor hRecursive hFuel
      (forInit outer initCursor hBoundary) hSource

/--
Enter a loop post block after a regular body result.

Scoped post lowering starts from the loop-entry state with loop control
disabled. The recursive boundary is reconstructed from source control
equivalence, the real initializer compilation context, and the adjacent-pass
runtime invariant.
-/
def forPost
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {outerScope postScope : Locals.Allocation.ScopeId}
    {outerLive loopLive : List Functions.Name}
    {outerBlock post : Functions.Block}
    {initLowered : Locals.Block}
    {initCode : List Expressions.Stmt}
    {outerState loopState : AllocationLowering.State}
    {outerLocals initLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {outerCtx loopCtx : Functions.Source.Ctx}
    {outerSource postSource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget postTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.Cursor prepared outerScope outerLive
        outerBlock outerState outerLocals)
    (postCursor :
      AllocationObserverForward.BodyCursor.Cursor prepared postScope loopLive
        post loopState initLocals.withoutLoopControl)
    (hBoundary :
      Boundary outer (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := outerCtx) (source := outerSource)
        (target := outerTarget))
    (hInitCompile :
      Locals.Block.compileOpen outerLocals.withoutLoopControl
          initLowered =
        some (initCode, initLocals))
    (hLoopScope :
      ∀ name, name ∈ loopCtx.scope ↔ name ∈ loopLive)
    (hOuterSubset :
      ∀ name, name ∈ outerLive → name ∈ loopLive)
    (hInitControl :
      AllocationObserverOutcome.SameControl
        outerCtx.withoutLoopControl loopCtx)
    (hReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        loopCtx.withoutLoopControl postTarget)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        loopState initLocals.withoutLoopControl postCursor.plan loopLive
        frameBase mode postSource postTarget) :
    Boundary postCursor (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := loopCtx.withoutLoopControl)
      (source := postSource) (target := postTarget) := by
  have hLoopControl :
      AllocationObserverOutcome.ControlScopesWithin
        fn.returns loopLive loopCtx :=
    hInitControl.controlScopesWithin
      ((hBoundary.control.mono hOuterSubset).withoutLoopControl)
  have hLocalsControl :=
    Locals.Block.compileOpen_sameControl hInitCompile
  refine
    { sourceScope := by
        intro name
        simpa [Functions.Source.Ctx.withoutLoopControl] using
          hLoopScope name
      control := hLoopControl.withoutLoopControl
      destinations :=
        AllocationObserverOutcome.ControlDestinations.withoutLoopControl
      returnFrame := hReturnFrame
      leaveTarget := ?_
      budget := hBoundary.budget
      invariant := hInvariant }
  intro functionScope hLeave
  have hOuterLeave :
      outerCtx.leaveScope? = some functionScope := by
    calc
      outerCtx.leaveScope? =
          outerCtx.withoutLoopControl.leaveScope? := rfl
      _ = loopCtx.leaveScope? := hInitControl.leaveScope
      _ = loopCtx.withoutLoopControl.leaveScope? := rfl
      _ = some functionScope := hLeave
  obtain ⟨hDepth, hRetc⟩ :=
    hBoundary.leaveTarget functionScope hOuterLeave
  constructor
  · calc
      initLocals.withoutLoopControl.leaveDepth? =
          initLocals.leaveDepth? := rfl
      _ = outerLocals.withoutLoopControl.leaveDepth? :=
        hLocalsControl.leaveDepth.symm
      _ = outerLocals.leaveDepth? := rfl
      _ = some 0 := hDepth
  · calc
      initLocals.withoutLoopControl.leaveRetc =
          initLocals.leaveRetc := rfl
      _ = outerLocals.withoutLoopControl.leaveRetc :=
        hLocalsControl.leaveRetc.symm
      _ = outerLocals.leaveRetc := rfl
      _ = fn.returns.length := hRetc

/--
Enter a loop body at the state reached after scoped post lowering.

The destination cleanup still targets the loop-entry activation. The
source-side break and continue scopes are related extensionally to the compiler
live set, matching the shared source semantics.
-/
def forBody
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {outerScope bodyScope : Locals.Allocation.ScopeId}
    {outerLive loopLive : List Functions.Name}
    {outerBlock body : Functions.Block}
    {initLowered : Locals.Block}
    {initCode : List Expressions.Stmt}
    {outerState loopState bodyState : AllocationLowering.State}
    {outerLocals initLocals : Locals.Ctx}
    {loopPlan : Locals.Allocation.Plan}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {outerCtx loopCtx : Functions.Source.Ctx}
    {outerSource bodySource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget bodyTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.Cursor prepared outerScope outerLive
        outerBlock outerState outerLocals)
    (bodyCursor :
      AllocationObserverForward.BodyCursor.Cursor prepared bodyScope loopLive
        body bodyState
        (initLocals.withLoopControl initLocals.layout.length))
    (hBoundary :
      Boundary outer (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := outerCtx) (source := outerSource)
        (target := outerTarget))
    (hInitCompile :
      Locals.Block.compileOpen outerLocals.withoutLoopControl
          initLowered =
        some (initCode, initLocals))
    (hLoopScope :
      ∀ name, name ∈ loopCtx.scope ↔ name ∈ loopLive)
    (hOuterSubset :
      ∀ name, name ∈ outerLive → name ∈ loopLive)
    (hInitControl :
      AllocationObserverOutcome.SameControl
        outerCtx.withoutLoopControl loopCtx)
    (hLoopCompiler :
      AllocationObserverContext.ActivationExprContext
        artifact.lowerCtx loopState initLocals loopPlan loopLive mode)
    (hLoopPlanWF : loopPlan.WellFormed)
    (hState :
      AllocationLowering.StateExtends loopLive loopState bodyState)
    (hReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        (loopCtx.withLoopControl loopCtx.scope loopCtx.scope) bodyTarget)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        bodyState
        (initLocals.withLoopControl initLocals.layout.length)
        bodyCursor.plan loopLive frameBase mode bodySource bodyTarget) :
    Boundary bodyCursor (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode)
      (sourceCtx :=
        loopCtx.withLoopControl loopCtx.scope loopCtx.scope)
      (source := bodySource) (target := bodyTarget) := by
  have hLoopControl :
      AllocationObserverOutcome.ControlScopesWithin
        fn.returns loopLive loopCtx :=
    hInitControl.controlScopesWithin
      ((hBoundary.control.mono hOuterSubset).withoutLoopControl)
  have hLocalsControl :=
    Locals.Block.compileOpen_sameControl hInitCompile
  have hBaseDestinations :=
    AllocationObserverOutcome.ControlDestinations.loopBody
      hLoopCompiler hLoopPlanWF hState hLoopScope
  refine
    { sourceScope := by
        intro name
        simpa [Functions.Source.Ctx.withLoopControl] using
          hLoopScope name
      control := hLoopControl.withLoopControl hLoopScope
      destinations :=
        hBaseDestinations.transport
          (AllocationObserverOutcome.SameControl.refl _)
          (Locals.Ctx.SameControl.refl _)
          (AllocationLowering.StateExtends.of_shape rfl rfl)
          (fun _ hName => hName) (SameFrame.refl mode)
      returnFrame := hReturnFrame
      leaveTarget := ?_
      budget := hBoundary.budget
      invariant := hInvariant }
  intro functionScope hLeave
  have hOuterLeave :
      outerCtx.leaveScope? = some functionScope := by
    calc
      outerCtx.leaveScope? =
          outerCtx.withoutLoopControl.leaveScope? := rfl
      _ = loopCtx.leaveScope? := hInitControl.leaveScope
      _ = (loopCtx.withLoopControl
            loopCtx.scope loopCtx.scope).leaveScope? := rfl
      _ = some functionScope := hLeave
  obtain ⟨hDepth, hRetc⟩ :=
    hBoundary.leaveTarget functionScope hOuterLeave
  constructor
  · calc
      (initLocals.withLoopControl
          initLocals.layout.length).leaveDepth? =
          initLocals.leaveDepth? := rfl
      _ = outerLocals.withoutLoopControl.leaveDepth? :=
        hLocalsControl.leaveDepth.symm
      _ = outerLocals.leaveDepth? := rfl
      _ = some 0 := hDepth
  · calc
      (initLocals.withLoopControl
          initLocals.layout.length).leaveRetc =
          initLocals.leaveRetc := rfl
      _ = outerLocals.withoutLoopControl.leaveRetc :=
        hLocalsControl.leaveRetc.symm
      _ = outerLocals.leaveRetc := rfl
      _ = fn.returns.length := hRetc

/--
Rebase a recursive dispatcher boundary onto another pass-owned cursor in the
same source control context.

The caller supplies the actual lower-state extension, Locals control
preservation, return-frame fact, and runtime invariant produced by the adjacent
pass. No generated code or recursive preservation evidence is stored here.
-/
def rebase
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {outerScope nestedScope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {outerBlock nestedBlock : Functions.Block}
    {outerState nestedState : AllocationLowering.State}
    {outerLocals nestedLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {outerSource nestedSource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget nestedTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.Cursor prepared outerScope live
        outerBlock outerState outerLocals)
    (nested :
      AllocationObserverForward.BodyCursor.Cursor prepared nestedScope live
        nestedBlock nestedState nestedLocals)
    (hBoundary :
      Boundary outer (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := outerSource)
        (target := outerTarget))
    (hState :
      AllocationLowering.StateExtends live outerState nestedState)
    (hLocals : Locals.Ctx.SameControl outerLocals nestedLocals)
    (hReturnFrame :
      ∀ functionScope,
        sourceCtx.leaveScope? = some functionScope →
          nestedTarget.source.returns ≠ [])
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        nestedState nestedLocals nested.plan live frameBase mode
        nestedSource nestedTarget) :
    Boundary nested (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (source := nestedSource)
      (target := nestedTarget) :=
  { sourceScope := hBoundary.sourceScope
    control := hBoundary.control
    destinations :=
      hBoundary.destinations.transport
        (AllocationObserverOutcome.SameControl.refl sourceCtx)
        hLocals hState (fun _ hName => hName) (SameFrame.refl mode)
    returnFrame := hReturnFrame
    leaveTarget := by
      intro functionScope hLeave
      obtain ⟨hDepth, hRetc⟩ :=
        hBoundary.leaveTarget functionScope hLeave
      constructor
      · rw [← hLocals.leaveDepth]
        exact hDepth
      · rw [← hLocals.leaveRetc]
        exact hRetc
    budget := hBoundary.budget
    invariant := hInvariant }

/--
Dispatch the `for` branch whose initializer exits before condition evaluation.

The recursive call is confined to the exact initializer cursor. Since the
outcome leaves the activation or halts, the outcome-owned exit transport moves
the nested allocation index back to the outer statement plan before the
loop-owned statement theorem packages the unreachable condition, body, post,
and cleanup.
-/
theorem forInitExitHeadResult
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
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx initCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      RecursiveBlockForward (prepared := prepared)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := sourceFuel + 1)
        (transcript := transcript))
    (hInitSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx.withoutLoopControl sourceFuel init source =
        .ok (sourceOutcome, initCtx))
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState localsCtx,
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  obtain
      ⟨afterState, headLower, headCode, tail,
        loopState, afterPost, afterBody,
        initLocals, postLocals, bodyLocals,
        loweredCond, condCode, compiledPost, compiledBody, cleanup,
        initCursor, postCursor, bodyCursor,
        hCompiled, hLower, hCompile,
        hInitFinalState, hInitFinalLocals,
        hLowerCond, hCompileCond, hLowerPost, hFinishPost,
        hLowerBody, hFinishBody, hCleanup, hHeadCode, hAfterState,
        hCondScoped, hPostScoped, hBodyScoped, hStep, hExact⟩ :=
    cursor.forCursors
  have hInitBoundary :
      Boundary initCursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
        (source := source) (target := target) :=
    forInit cursor initCursor hBoundary
  obtain ⟨targetOutcome, finalMode, hForward⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.for_init_exit_of_components
      (outerPlan := cursor.plan) (exitPlan := cursor.plan)
      (outerLive := live)
      (resultLive :=
        AllocationObserverOutcome.outcomeLive fn.returns live sourceCtx
          sourceOutcome.mode)
      hBoundary.invariant
      (by
        intro loweredInit loopState' initCode initLocals'
          hLowerInit hCompileInit _hInvariant
        have hLowerPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit, loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit)
        cases hLowerPair
        have hCompilePair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode, initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit)
        cases hCompilePair
        obtain
            ⟨initTargetOutcome, initFinalMode, hInitForward⟩ :=
          recursiveNonregular initCursor hRecursive
            (Nat.lt_succ_self sourceFuel) hInitBoundary hInitSource
            (by
              intro hRegular
              rcases sourceOutcome with ⟨sourceFinal, sourceMode⟩
              cases sourceMode with
              | regular =>
                  simp [Functions.Source.Effectful.Outcome.IsExit,
                    Functions.Source.Effectful.Outcome.regular,
                    Locals.Source.Effectful.Outcome.regular] at hExit
              | brk =>
                  simp [Functions.Source.Effectful.Outcome.IsExit,
                    Functions.Source.Effectful.Outcome.brk,
                    Locals.Source.Effectful.Outcome.brk] at hExit
              | cont =>
                  simp [Functions.Source.Effectful.Outcome.IsExit,
                    Functions.Source.Effectful.Outcome.cont,
                    Locals.Source.Effectful.Outcome.cont] at hExit
              | leave =>
                  simp [Functions.Source.Effectful.Outcome.leave,
                    Locals.Source.Effectful.Outcome.leave] at hRegular
              | halt kind =>
                  simp [Functions.Source.Effectful.Outcome.halt,
                    Locals.Source.Effectful.Outcome.halt] at hRegular)
        refine
          ⟨initCtx, initTargetOutcome, initFinalMode,
            AllocationObserverOutcome.BlockRuntimeForward.transport_of_isExit
              hInitForward hExit ?_⟩
        intro hLeave
        simp [AllocationObserverOutcome.outcomeLive, hLeave])
      hExit hLower hCompile
  have hMode : sourceOutcome.mode ≠ .regular := by
    intro hRegular
    rcases sourceOutcome with ⟨sourceFinal, sourceMode⟩
    cases sourceMode with
    | regular =>
        simp [Functions.Source.Effectful.Outcome.IsExit,
          Functions.Source.Effectful.Outcome.regular,
          Locals.Source.Effectful.Outcome.regular] at hExit
    | brk =>
        simp [Functions.Source.Effectful.Outcome.IsExit,
          Functions.Source.Effectful.Outcome.brk,
          Locals.Source.Effectful.Outcome.brk] at hExit
    | cont =>
        simp [Functions.Source.Effectful.Outcome.IsExit,
          Functions.Source.Effectful.Outcome.cont,
          Locals.Source.Effectful.Outcome.cont] at hExit
    | leave =>
        simp [Functions.Source.Effectful.Outcome.leave,
          Locals.Source.Effectful.Outcome.leave] at hRegular
    | halt kind =>
        simp [Functions.Source.Effectful.Outcome.halt,
          Locals.Source.Effectful.Outcome.halt] at hRegular
  exact
    ⟨afterState, headCode, tail,
      HeadResult.ofNonregular cursor tail hCompiled
        (.nonregular hForward) hExact hMode⟩

/--
Dispatch an `if` head through the pass-owned conditional theorem. Recursive
work is limited to the exact lexical body cursor selected by the canonical
source run.
-/
theorem ifHeadResult
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
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1) (.if_ cond body) source =
        .ok (sourceOutcome, sourceCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target))
    (hBody :
      ∀ {sourceAfterCond :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        (bodyCursor :
          AllocationObserverForward.BodyCursor.Cursor prepared
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx),
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program sourceCtx sourceFuel body sourceAfterCond =
          .ok (bodyOutcome, bodyCtx) →
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth artifact.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              artifact.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan fn.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState localsCtx,
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  obtain
      ⟨afterState, headCode, tail, targetOutcome, hCompiled,
        hRuntime, hStep, hExact⟩ :=
    cursor.ifRuntimeResultOfSafeRun hConfig hSource hBoundary.sourceScope
      hBoundary.control hBoundary.invariant hBody
  exact
    ⟨afterState, headCode, tail,
      HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)⟩

/--
Dispatch a `switch` head through the pass-owned selected-body theorem.
-/
theorem switchHeadResult
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
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.Cursor prepared scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1)
            (.switch scrutinee cases defaultBody) source =
        .ok (sourceOutcome, sourceCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target))
    (hBody :
      ∀ {selected : Functions.Block}
        {sourceAfterScrutinee :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        {selectedStart : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        (bodyCursor :
          AllocationObserverForward.BodyCursor.Cursor prepared
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx),
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program sourceCtx sourceFuel selected sourceAfterScrutinee =
          .ok (bodyOutcome, bodyCtx) →
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth artifact.lowerCtx
              selectedStart localsCtx bodyCursor.plan live frameBase mode
              sourceAfterScrutinee targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              artifact.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan fn.returns
              (Functions.Scope.Block.outEnv live selected)
              frameBase mode program sourceCtx selected
              sourceAfterScrutinee expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState localsCtx,
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  obtain
      ⟨afterState, headCode, tail, targetOutcome, hCompiled,
        hRuntime, hStep, hExact⟩ :=
    cursor.switchRuntimeResultOfSafeRun hConfig hSource
      hBoundary.sourceScope hBoundary.control hBoundary.invariant hBody
  exact
    ⟨afterState, headCode, tail,
      HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)⟩

/--
Dispatch a lexical block by inverting its canonical scoped source run to the
exact open-block execution consumed by recursive preservation.
-/
theorem blockHeadResult
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
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .block body :: rest } lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.block body) source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target))
    (hBody :
      ∀ {bodyOutcome :
            Functions.ObserverSemantics.Outcome
              (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        (bodyCursor :
          AllocationObserverForward.BodyCursor.Cursor prepared
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx),
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program sourceCtx sourceFuel body source =
          .ok (bodyOutcome, bodyCtx) →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config allocatorDepth transcript
            artifact.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan fn.returns
            (Functions.Scope.Block.outEnv live body)
            frameBase mode program sourceCtx body source
            expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured bodyCursor.compiled }
            target bodyOutcome targetOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState localsCtx,
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  simp only [Functions.Source.Effectful.Stmt.run] at hSource
  cases hScoped :
      Functions.Source.Effectful.Block.runScoped
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program sourceCtx body sourceFuel source with
  | error err =>
      simp [hScoped] at hSource
  | ok scopedOutcome =>
      simp only [hScoped, Bind.bind, Except.bind] at hSource
      have hEq :
          (scopedOutcome, sourceCtx) = (sourceOutcome, finalCtx) :=
        Except.ok.inj hSource
      cases hEq
      rcases
          Functions.Source.Effectful.Block.runScoped_cases
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program hScoped with
        hRegular | hNonregular
      · rcases hRegular with
          ⟨bodyFinal, bodyCtx, hOpen, hScopedOutcome⟩
        subst sourceOutcome
        obtain
            ⟨afterState, headCode, tail, producedSourceOutcome,
              targetOutcome, hCompiled, hRuntime, hStep, hExact,
              hRegularOutcome, _hAbruptOutcome⟩ :=
          cursor.blockRuntimeResult hBoundary.sourceScope hBoundary.control
            hBoundary.invariant (fun bodyCursor => hBody bodyCursor hOpen)
        have hRestrict :
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
                sourceCtx.scope bodyFinal =
              (Functions.ObserverSemantics.stateModel transcript).restrictTo
                live bodyFinal :=
          Locals.Source.Effectful.StateModel.restrictTo_congr
            (Functions.ObserverSemantics.stateModel transcript)
            hBoundary.sourceScope
        rw [hRestrict]
        rw [hRegularOutcome rfl] at hRuntime
        exact
          ⟨afterState, headCode, tail,
            HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
              (by
                intro _ name
                simpa [Functions.Scope.Stmt.outEnv] using
                  hBoundary.sourceScope name)⟩
      · rcases hNonregular with
          ⟨openOutcome, bodyCtx, hOpen, hMode, hScopedOutcome⟩
        subst sourceOutcome
        obtain
            ⟨afterState, headCode, tail, producedSourceOutcome,
              targetOutcome, hCompiled, hRuntime, hStep, hExact,
              _hRegularOutcome, hAbruptOutcome⟩ :=
          cursor.blockRuntimeResult hBoundary.sourceScope hBoundary.control
            hBoundary.invariant (fun bodyCursor => hBody bodyCursor hOpen)
        rw [hAbruptOutcome hMode] at hRuntime
        exact
          ⟨afterState, headCode, tail,
            HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
              (by
                intro _ name
                simpa [Functions.Scope.Stmt.outEnv] using
                  hBoundary.sourceScope name)⟩

/--
Dispatch `break` using the loop destination already carried by the boundary.
-/
theorem brkControlledHeadResult
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
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .brk :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .brk source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        ControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  simp only [Functions.Source.Effectful.Stmt.run] at hSource
  cases hScope : sourceCtx.breakScope? with
  | none =>
      simp [hScope, Functions.Source.invalid, Structured.invalid] at hSource
  | some afterLive =>
      simp only [hScope] at hSource
      have hEq :
          (Functions.Source.Effectful.Outcome.brk
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source),
            sourceCtx) =
          (sourceOutcome, finalCtx) :=
        Except.ok.inj hSource
      cases hEq
      obtain
          ⟨controlArtifact, hOwned⟩ :=
        hBoundary.destinations.brk.transitionArtifact_of_source
          hBoundary.invariant.activation.compiler
          (by
            simpa [AllocationObserverOutcome.ControlKind.sourceScope?] using
              hScope)
      let hTransition :=
        controlArtifact.transition.reindex_after
          (fun name => (controlArtifact.sourceEquivalent name).symm)
      obtain
          ⟨afterState, afterLocals, headCode, tail, targetFinal,
            hCompiled, hRuntime, hFinalState, hFinalStack, hMachine,
            hExact⟩ :=
        cursor.brkRuntimeResultExact hScope
          (by
            simpa [hTransition,
              AllocationObserverOutcome.ControlKind.targetDepth?] using
              controlArtifact.target)
          hTransition hBoundary.invariant
      have hDestinationInvariant :=
        controlArtifact.runtimeInvariant hBoundary.invariant
          hFinalState hFinalStack hMachine
      have hControlInvariant :
          AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant
            (contract := program.memoryContract) (config := config)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            hBoundary.destinations.brk
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal :=
        AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_artifact
          controlArtifact hOwned hDestinationInvariant
      let hHead :
          HeadResult cursor afterState afterLocals headCode tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.brk
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  afterLive source)) :=
        HeadResult.ofNonregular cursor tail hCompiled hRuntime hExact
          (by
            simp [Functions.Source.Effectful.Outcome.brk,
              Locals.Source.Effectful.Outcome.brk])
      exact
        ⟨afterState, afterLocals, headCode, tail,
          { head := hHead
            runtime :=
              ⟨Structured.EffectSemantics.Outcome.brk targetFinal,
                hRuntime,
                { brk := by
                    intro sourceFinal hOutcome
                    cases hOutcome
                    exact ⟨targetFinal, rfl, hControlInvariant⟩
                  cont := by
                    intro sourceFinal hOutcome
                    have hMode :=
                      congrArg
                        (fun outcome =>
                          (outcome :
                            Functions.ObserverSemantics.Outcome
                              (Functions.ObserverSemantics.State transcript)).mode)
                        hOutcome
                    simp [Functions.Source.Effectful.Outcome.brk,
                      Functions.Source.Effectful.Outcome.cont,
                      Locals.Source.Effectful.Outcome.brk,
                      Locals.Source.Effectful.Outcome.cont] at hMode }⟩ }⟩

/--
Compatibility projection of `brkControlledHeadResult` for callers that need
only the ordinary statement result.
-/
theorem brkHeadResult
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
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .brk :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .brk source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  obtain ⟨afterState, afterLocals, headCode, tail, hControlled⟩ :=
    brkControlledHeadResult cursor hSource hBoundary
  exact ⟨afterState, afterLocals, headCode, tail, hControlled.head⟩

/--
Dispatch `continue` using the loop destination already carried by the boundary.
-/
theorem contControlledHeadResult
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
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .cont :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .cont source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        ControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  simp only [Functions.Source.Effectful.Stmt.run] at hSource
  cases hScope : sourceCtx.continueScope? with
  | none =>
      simp [hScope, Functions.Source.invalid, Structured.invalid] at hSource
  | some afterLive =>
      simp only [hScope] at hSource
      have hEq :
          (Functions.Source.Effectful.Outcome.cont
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source),
            sourceCtx) =
          (sourceOutcome, finalCtx) :=
        Except.ok.inj hSource
      cases hEq
      obtain
          ⟨controlArtifact, hOwned⟩ :=
        hBoundary.destinations.cont.transitionArtifact_of_source
          hBoundary.invariant.activation.compiler
          (by
            simpa [AllocationObserverOutcome.ControlKind.sourceScope?] using
              hScope)
      let hTransition :=
        controlArtifact.transition.reindex_after
          (fun name => (controlArtifact.sourceEquivalent name).symm)
      obtain
          ⟨afterState, afterLocals, headCode, tail, targetFinal,
            hCompiled, hRuntime, hFinalState, hFinalStack, hMachine,
            hExact⟩ :=
        cursor.contRuntimeResultExact hScope
          (by
            simpa [hTransition,
              AllocationObserverOutcome.ControlKind.targetDepth?] using
              controlArtifact.target)
          hTransition hBoundary.invariant
      have hDestinationInvariant :=
        controlArtifact.runtimeInvariant hBoundary.invariant
          hFinalState hFinalStack hMachine
      have hControlInvariant :
          AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant
            (contract := program.memoryContract) (config := config)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            hBoundary.destinations.cont
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal :=
        AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_artifact
          controlArtifact hOwned hDestinationInvariant
      let hHead :
          HeadResult cursor afterState afterLocals headCode tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.cont
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  afterLive source)) :=
        HeadResult.ofNonregular cursor tail hCompiled hRuntime hExact
          (by
            simp [Functions.Source.Effectful.Outcome.cont,
              Locals.Source.Effectful.Outcome.cont])
      exact
        ⟨afterState, afterLocals, headCode, tail,
          { head := hHead
            runtime :=
              ⟨Structured.EffectSemantics.Outcome.cont targetFinal,
                hRuntime,
                { brk := by
                    intro sourceFinal hOutcome
                    have hMode :=
                      congrArg
                        (fun outcome =>
                          (outcome :
                            Functions.ObserverSemantics.Outcome
                              (Functions.ObserverSemantics.State transcript)).mode)
                        hOutcome
                    simp [Functions.Source.Effectful.Outcome.brk,
                      Functions.Source.Effectful.Outcome.cont,
                      Locals.Source.Effectful.Outcome.brk,
                      Locals.Source.Effectful.Outcome.cont] at hMode
                  cont := by
                    intro sourceFinal hOutcome
                    cases hOutcome
                    exact ⟨targetFinal, rfl, hControlInvariant⟩ }⟩ }⟩

/--
Compatibility projection of `contControlledHeadResult` for callers that need
only the ordinary statement result.
-/
theorem contHeadResult
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
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .cont :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .cont source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  obtain ⟨afterState, afterLocals, headCode, tail, hControlled⟩ :=
    contControlledHeadResult cursor hSource hBoundary
  exact ⟨afterState, afterLocals, headCode, tail, hControlled.head⟩

/--
Dispatch `leave` using the function-return facts already carried by the
boundary.
-/
theorem leaveHeadResult
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
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .leave :: rest } beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .leave source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  simp only [Functions.Source.Effectful.Stmt.run] at hSource
  cases hScope : sourceCtx.leaveScope? with
  | none =>
      simp [hScope, Functions.Source.invalid, Structured.invalid] at hSource
  | some functionScope =>
      simp only [hScope] at hSource
      have hEq :
          (Functions.Source.Effectful.Outcome.leave
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                functionScope source),
            sourceCtx) =
          (sourceOutcome, finalCtx) :=
        Except.ok.inj hSource
      cases hEq
      obtain ⟨hTargetDepth, hRetc⟩ :=
        hBoundary.leaveTarget functionScope hScope
      obtain
          ⟨afterState, afterLocals, headCode, tail, targetFinal,
            hCompiled, hRuntime, hExact⟩ :=
        cursor.leaveRuntimeResult hConfig hScope hBoundary.control
          hTargetDepth hRetc (hBoundary.returnFrame functionScope hScope)
          hBoundary.invariant
      exact
        ⟨afterState, afterLocals, headCode, tail,
          HeadResult.ofNonregular cursor tail hCompiled hRuntime hExact
            (by
              simp [Functions.Source.Effectful.Outcome.leave,
                Locals.Source.Effectful.Outcome.leave])⟩

/--
Dispatch a plain terminal statement directly from its successful canonical
source run.
-/
theorem terminalHeadResult
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
    {kind : Assembly.HaltKind}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .terminal kind :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.terminal kind) source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  simp only [Functions.Source.Effectful.Stmt.run] at hSource
  cases hTerminalEval :
      (AllocationObserverSafety.SafeSemantics.primitiveSemantics
        program.memoryContract transcript).terminal kind source [] with
  | error err =>
      simp [hTerminalEval] at hSource
  | ok sourceFinal =>
      simp only [hTerminalEval] at hSource
      have hEq :
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            sourceCtx) =
          (sourceOutcome, finalCtx) :=
        Except.ok.inj hSource
      cases hEq
      obtain ⟨hMemory, hTerminal⟩ :=
        AllocationObserverSafety.SafeSemantics.terminal_parts hTerminalEval
      obtain
          ⟨afterState, afterLocals, headCode, tail, targetFinal,
            hCompiled, hRuntime, hExact⟩ :=
        cursor.terminalRuntimeResult hMemory hTerminal hBoundary.invariant
      exact
        ⟨afterState, afterLocals, headCode, tail,
          HeadResult.ofNonregular cursor tail hCompiled hRuntime hExact
            (by
              simp [Functions.Source.Effectful.Outcome.halt,
                Locals.Source.Effectful.Outcome.halt])⟩

/--
Dispatch a terminal-with-arguments statement directly from its successful
canonical source run.
-/
theorem terminalArgsHeadResult
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
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
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
        { stmts := .terminalArgs kind args :: rest } beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.terminalArgs kind args) source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.Cursor prepared scope live
          { stmts := rest } afterState afterLocals,
        HeadResult cursor afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  simp only [Functions.Source.Effectful.Stmt.run] at hSource
  cases hArgsEval :
      Locals.Source.Effectful.Expr.ExprSeq.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        args source with
  | error err =>
      simp [hArgsEval] at hSource
  | ok result =>
      rcases result with ⟨afterArgs, values⟩
      simp only [hArgsEval, Bind.bind, Except.bind] at hSource
      cases hTerminalEval :
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript).terminal
            kind afterArgs values with
      | error err =>
          simp [hTerminalEval] at hSource
      | ok sourceFinal =>
          simp only [hTerminalEval] at hSource
          have hEq :
              (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
                sourceCtx) =
              (sourceOutcome, finalCtx) :=
            Except.ok.inj hSource
          cases hEq
          obtain ⟨hMemory, hTerminal⟩ :=
            AllocationObserverSafety.SafeSemantics.terminal_parts
              hTerminalEval
          obtain
              ⟨afterState, afterLocals, headCode, tail, targetFinal,
                hCompiled, hRuntime, hExact⟩ :=
            cursor.terminalArgsRuntimeResult hConfig
              (AllocationObserverSafety.ExprSeq.MemorySafeEval.of_safe_eval
                hArgsEval)
              hMemory hTerminal hBoundary.invariant
          exact
            ⟨afterState, afterLocals, headCode, tail,
              HeadResult.ofNonregular cursor tail hCompiled hRuntime hExact
                (by
                  simp [Functions.Source.Effectful.Outcome.halt,
                    Locals.Source.Effectful.Outcome.halt])⟩

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
Transport exact abrupt-destination evidence from the tail boundary created by
one regular statement back to the enclosing block boundary.
-/
theorem ControlOutcomeForward.of_afterRegular
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
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome (transcript := transcript)}
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
        afterSource afterTarget)
    (hTail :
      ControlOutcomeForward tail
        (hBoundary.afterRegular cursor tail hAfterLive hStep hSourceControl
          hSameFrame hSourceScope hTarget hInvariant)
        sourceOutcome targetOutcome) :
    ControlOutcomeForward cursor hBoundary sourceOutcome targetOutcome := by
  constructor
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTargetOutcome, hDestination⟩ :=
      hTail.brk sourceFinal hOutcome
    refine ⟨targetFinal, hTargetOutcome, ?_⟩
    exact
      AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_transport
        hBoundary.destinations.brk hSourceControl hStep.locals hStep.state
        (by
          intro name hName
          rw [hAfterLive]
          exact hStep.live name hName)
        hSameFrame hDestination
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTargetOutcome, hDestination⟩ :=
      hTail.cont sourceFinal hOutcome
    refine ⟨targetFinal, hTargetOutcome, ?_⟩
    exact
      AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_transport
        hBoundary.destinations.cont hSourceControl hStep.locals hStep.state
        (by
          intro name hName
          rw [hAfterLive]
          exact hStep.live name hName)
        hSameFrame hDestination

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
The empty cursor satisfies the strengthened recursive block interface.
-/
theorem nilBlockResult
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
    BlockResult cursor hBoundary (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) := by
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
        { runtime :=
            ⟨Structured.EffectSemantics.Outcome.regular target,
              cursor.nilRuntimeResult hBoundary.invariant,
              { brk := by
                  intro sourceFinal hOutcome
                  cases hOutcome
                cont := by
                  intro sourceFinal hOutcome
                  cases hOutcome }⟩
          regularScope := by
            intro _ name
            simpa [Functions.Scope.Block.outEnv,
              Functions.Scope.StmtList.outEnv] using
              hBoundary.sourceScope name }

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
    {afterState : AllocationLowering.State}
    {afterLocals : Locals.Ctx}
    {headCode : List Expressions.Stmt}
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hHead :
      HeadResult cursor afterState afterLocals headCode tail
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
            artifact.lowerCtx afterState afterLocals cursor.plan
            (Functions.Scope.Stmt.outEnv live stmt) frameBase mode midMode
            program sourceCtx stmt source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceMid targetMid headCtx →
        AllocationObserverOutcome.SameControl sourceCtx headCtx →
        Boundary tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := midMode)
            (sourceCtx := headCtx) (source := sourceMid)
            (target := targetMid) →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config allocatorDepth transcript
            artifact.lowerCtx tail.finalState tail.finalLocals
            tail.plan fn.returns
            (Functions.Scope.Block.outEnv
              (Functions.Scope.Stmt.outEnv live stmt)
              { stmts := rest })
            frameBase midMode program headCtx { stmts := rest } sourceMid
            expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured tail.compiled }
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
  obtain ⟨_headTargetOutcome, hRuntime⟩ := hHead.runtime
  cases hRuntime with
  | @regular sourceMid targetMid midMode _ hForward hControl =>
      have hForwardCopy := hForward
      rcases hForward with
        ⟨_sourceFuel, targetFuel, _hSource, hTarget,
          hInvariant, hSameFrame, _hEffect⟩
      have hTailInvariant :
          AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config allocatorDepth artifact.lowerCtx
            afterState afterLocals tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase midMode sourceMid targetMid := by
        rw [hHead.tailPlan]
        exact hInvariant
      have hTailBoundary :
          Boundary tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := midMode)
            (sourceCtx := headCtx) (source := sourceMid)
            (target := targetMid) :=
        hBoundary.afterRegular cursor tail rfl
          (hHead.regularTransport rfl) hControl hSameFrame
          (hHead.regularScope rfl) hTarget hTailInvariant
      obtain ⟨tailTargetOutcome, hTailResult⟩ :=
        hTail hForwardCopy hControl hTailBoundary
      exact
        ⟨tailTargetOutcome,
          cursor.consRegularRuntimeResult tail hHead.tailPlan
            hHead.tailFinalState hHead.tailFinalLocals hHead.compiled
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
          cursor.consNonregularRuntimeResult hHead.compiled hForwardFinal⟩

/--
Compose one controlled head with the strengthened recursive result for its
tail. Exact `break` and `continue` destinations are preserved through regular
prefixes and are reused directly for abrupt heads.
-/
theorem consBlockResult
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
    {afterState : AllocationLowering.State}
    {afterLocals : Locals.Ctx}
    {headCode : List Expressions.Stmt}
    (tail :
      AllocationObserverForward.BodyCursor.Cursor prepared scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hHead :
      ControlledHeadResult cursor hBoundary afterState afterLocals headCode tail
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
            artifact.lowerCtx afterState afterLocals cursor.plan
            (Functions.Scope.Stmt.outEnv live stmt) frameBase mode midMode
            program sourceCtx stmt source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceMid targetMid headCtx →
        AllocationObserverOutcome.SameControl sourceCtx headCtx →
        ∀ hTailBoundary :
            Boundary tail
              (config := config) (allocatorDepth := allocatorDepth)
              (frameBase := frameBase) (mode := midMode)
              (sourceCtx := headCtx) (source := sourceMid)
              (target := targetMid),
          BlockResult tail hTailBoundary
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := midMode)
            (sourceCtx := headCtx) (finalCtx := blockCtx)
            (source := sourceMid) (target := targetMid)
            (sourceOutcome := blockSourceOutcome))
    (hAbrupt :
      headSourceOutcome.mode ≠ .regular →
        blockSourceOutcome = headSourceOutcome ∧ blockCtx = sourceCtx) :
    BlockResult cursor hBoundary
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := blockCtx)
      (source := source) (target := target)
      (sourceOutcome := blockSourceOutcome) := by
  obtain ⟨headTargetOutcome, hHeadRuntime, hHeadControl⟩ := hHead.runtime
  cases hHeadRuntime with
  | @regular sourceMid targetMid midMode _ hForward hControl =>
      have hForwardCopy := hForward
      rcases hForward with
        ⟨_sourceFuel, targetFuel, _hSource, hTarget,
          hInvariant, hSameFrame, _hEffect⟩
      have hTailInvariant :
          AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config allocatorDepth artifact.lowerCtx
            afterState afterLocals tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase midMode sourceMid targetMid := by
        rw [hHead.head.tailPlan]
        exact hInvariant
      let hTailBoundary :
          Boundary tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := midMode)
            (sourceCtx := headCtx) (source := sourceMid)
            (target := targetMid) :=
        hBoundary.afterRegular cursor tail rfl
          (hHead.head.regularTransport rfl) hControl hSameFrame
          (hHead.head.regularScope rfl) hTarget hTailInvariant
      have hTailResult :=
        hTail hForwardCopy hControl hTailBoundary
      obtain ⟨tailTargetOutcome, hTailRuntime, hTailControl⟩ :=
        hTailResult.runtime
      have hBlockControl :
          ControlOutcomeForward cursor hBoundary blockSourceOutcome
            tailTargetOutcome := by
        exact
          ControlOutcomeForward.of_afterRegular cursor tail hBoundary rfl
            (hHead.head.regularTransport rfl) hControl hSameFrame
            (hHead.head.regularScope rfl) hTarget hTailInvariant hTailControl
      exact
        { runtime :=
            ⟨tailTargetOutcome,
              cursor.consRegularRuntimeResult tail hHead.head.tailPlan
                hHead.head.tailFinalState hHead.head.tailFinalLocals
                hHead.head.compiled hForwardCopy hControl hTailRuntime,
              hBlockControl⟩
          regularScope := by
            intro hRegular name
            simpa [Functions.Scope.Block.outEnv,
              Functions.Scope.StmtList.outEnv] using
              hTailResult.regularScope hRegular name }
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
        { runtime :=
            ⟨headTargetOutcome,
              cursor.consNonregularRuntimeResult hHead.head.compiled
                hForwardFinal,
              hHeadControl⟩
          regularScope := fun hRegular =>
            False.elim (hMode hRegular) }

end Boundary
end BodyCursor

end AllocationObserverDispatcher
end Functions
end EvmCompiler
