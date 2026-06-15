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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (afterState : AllocationLowering.State)
    (afterLocals : Locals.Ctx)
    (headCode : List Expressions.Stmt)
    (tail :
    AllocationObserverForward.BodyCursor.CoreCursor root scope
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
        root.lowerCtx afterState afterLocals cursor.plan root.returns
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hRuntime :
      AllocationObserverOutcome.StmtRuntimeResult
        program.memoryContract config allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan root.returns
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hRuntime :
      AllocationObserverOutcome.StmtRuntimeResult
        program.memoryContract config allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan root.returns
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope afterLive
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
        root.lowerCtx afterState afterLocals cursor.plan afterLive
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope afterLive
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
          root.returns afterLive sourceCtx sourceOutcome.mode)
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .expr expr :: rest } beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .assign name valueExpr :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .let_ name valueExpr :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope
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
One fully dispatched statement under the compiler-selected resource mode.

This is the resource-indexed counterpart of `HeadResult`; it retains the same
exact compiler cursor and source-scope transport and changes only the
pass-owned semantic result.
-/
structure ResourceHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (afterState : AllocationLowering.State)
    (afterLocals : Locals.Ctx)
    (headCode : List Expressions.Stmt)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals) : Prop where
  compiled : cursor.compiled = headCode ++ tail.compiled
  tailPlan : tail.plan = cursor.plan
  tailFinalState : tail.finalState = cursor.finalState
  tailFinalLocals : tail.finalLocals = cursor.finalLocals
  runtime :
    ∃ targetOutcome,
      AllocationObserverOutcome.StmtResourceResult
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan root.returns
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

/-- Lift an existing scratch-backed head result into the resource API. -/
theorem toResource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState afterState : AllocationLowering.State}
    {localsCtx afterLocals : Locals.Ctx}
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
    {headCode : List Expressions.Stmt}
    {cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx}
    {tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals}
    (hHead :
      HeadResult cursor afterState afterLocals headCode tail
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome := sourceOutcome)) :
    ResourceHeadResult cursor afterState afterLocals headCode tail
      (resource := .scratch config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) := by
  obtain ⟨targetOutcome, hRuntime⟩ := hHead.runtime
  exact
    { compiled := hHead.compiled
      tailPlan := hHead.tailPlan
      tailFinalState := hHead.tailFinalState
      tailFinalLocals := hHead.tailFinalLocals
      runtime := ⟨targetOutcome, hRuntime.toResource⟩
      regularTransport := hHead.regularTransport
      regularScope := hHead.regularScope }

end HeadResult

namespace ResourceHeadResult

/--
Package one resource-indexed statement result together with the exact tail
cursor returned by the ordinary lowering and Locals compiler.
-/
def ofResource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hResource :
      AllocationObserverOutcome.StmtResourceResult
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan root.returns
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
    ResourceHeadResult cursor afterState afterLocals headCode tail
      (resource := resource) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) :=
  { compiled := hCompiled
    tailPlan := hExact.plan
    tailFinalState := hExact.finalState
    tailFinalLocals := hExact.finalLocals
    runtime := ⟨targetOutcome, hResource⟩
    regularTransport := fun _ => hStep
    regularScope := hScope }

/-- Package an abrupt resource-indexed statement result. -/
def ofNonregular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hResource :
      AllocationObserverOutcome.StmtResourceResult
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan root.returns
        (Functions.Scope.Stmt.outEnv live stmt) frameBase mode program
        sourceCtx stmt source expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceOutcome targetOutcome finalCtx)
    (hExact :
      AllocationObserverForward.BodyCursor.ExactTail cursor tail)
    (hMode : sourceOutcome.mode ≠ .regular) :
    ResourceHeadResult cursor afterState afterLocals headCode tail
      (resource := resource) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) :=
  { compiled := hCompiled
    tailPlan := hExact.plan
    tailFinalState := hExact.finalState
    tailFinalLocals := hExact.finalLocals
    runtime := ⟨targetOutcome, hResource⟩
    regularTransport := fun hRegular => False.elim (hMode hRegular)
    regularScope := fun hRegular => False.elim (hMode hRegular) }

/--
Dispatch a zero-result expression statement in a stack-only activation from
its successful canonical source run.
-/
theorem exprOfSafeRunStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {expr : Functions.Expr 0}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .expr expr :: rest } beforeState beforeLocals)
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
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ResourceHeadResult cursor afterState afterLocals headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
            hCompiled, hResource, hStep, hExact⟩ :=
        cursor.exprStackResourceResult
          (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_eval hEval)
          hInvariant
      exact
        ⟨afterState, afterLocals, headCode, tail,
          ofResource cursor tail hCompiled hResource hStep hExact
            (by
              intro _ name
              simpa [Functions.Scope.Stmt.outEnv] using
                hSourceScope name)⟩

/--
Dispatch an assignment in a stack-only activation from its successful source
run.
-/
theorem assignOfSafeRunStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name}
    {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .assign name valueExpr :: rest }
        beforeState beforeLocals)
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
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ResourceHeadResult cursor afterState afterLocals headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
      simp [hContains, Functions.Source.invalid, Structured.invalid]
        at hSourceCopy
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
                hCompiled, hResource, hStep, hExact⟩ :=
            cursor.assignStackResourceResult
              (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
                hEval)
              hInvariant
          exact
            ⟨afterState, afterLocals, headCode, tail,
              ofResource cursor tail hCompiled hResource hStep hExact
                (by
                  intro _ localName
                  simpa [Functions.Scope.Stmt.outEnv] using
                    hSourceScope localName)⟩

/--
Dispatch a declaration in a stack-only activation from its successful source
run.
-/
theorem letOfSafeRunStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name}
    {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .let_ name valueExpr :: rest }
        beforeState beforeLocals)
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
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope
          (name :: live) { stmts := rest } afterState afterLocals,
        ResourceHeadResult cursor afterState afterLocals headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
            hCompiled, hResource, hStep, hExact⟩ :=
        cursor.letStackResourceResult
          (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne hEval)
          hInvariant
      exact
        ⟨afterState, afterLocals, headCode, tail,
          ofResource cursor tail hCompiled hResource hStep hExact
            (by
              intro _ localName
              simp only [Functions.Scope.Stmt.outEnv, List.mem_cons]
              exact or_congr Iff.rfl (hSourceScope localName))⟩

end ResourceHeadResult

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx) where
  sourceScope :
    ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live
  control :
    AllocationObserverOutcome.ControlScopesWithin
      root.returns live sourceCtx
  destinations :
    AllocationObserverOutcome.ControlDestinations
      root.lowerCtx lowerState localsCtx cursor.plan live mode sourceCtx
  returnFrame :
    AllocationObserverOutcome.ReturnFrameAvailable sourceCtx target
  leaveTarget :
    ∀ functionScope,
      sourceCtx.leaveScope? = some functionScope →
        localsCtx.leaveDepth? = some 0 ∧
          localsCtx.leaveRetc = root.returns.length
  budget : Frame.Budget config allocatorDepth
  invariant :
    AllocationObserverContext.ActivationRuntimeInvariant
      program.memoryContract config allocatorDepth root.lowerCtx
      lowerState localsCtx cursor.plan live frameBase mode source target

/--
Statement-boundary contract indexed by the compiler-selected resource mode.

All source scope and control obligations are independent of scratch-frame
allocation. Only the budget and activation invariant vary by resource mode.
The existing `Boundary` is the `.scratch config` specialization.
-/
structure ResourceBoundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx) where
  sourceScope :
    ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live
  control :
    AllocationObserverOutcome.ControlScopesWithin
      root.returns live sourceCtx
  destinations :
    AllocationObserverOutcome.ControlDestinations
      root.lowerCtx lowerState localsCtx cursor.plan live mode sourceCtx
  returnFrame :
    AllocationObserverOutcome.ReturnFrameAvailable sourceCtx target
  leaveTarget :
    ∀ functionScope,
      sourceCtx.leaveScope? = some functionScope →
        localsCtx.leaveDepth? = some 0 ∧
          localsCtx.leaveRetc = root.returns.length
  budget : resource.Budget allocatorDepth
  invariant :
    AllocationObserverContext.ActivationResourceInvariant
      resource program.memoryContract allocatorDepth root.lowerCtx
      lowerState localsCtx cursor.plan live frameBase mode source target

namespace Boundary

def toResource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx}
    (boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    ResourceBoundary cursor (resource := .scratch config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := sourceCtx)
      (source := source) (target := target) :=
  { sourceScope := boundary.sourceScope
    control := boundary.control
    destinations := boundary.destinations
    returnFrame := boundary.returnFrame
    leaveTarget := boundary.leaveTarget
    budget := boundary.budget
    invariant :=
      AllocationObserverContext.ActivationResourceInvariant.scratch
        boundary.invariant }

end Boundary

namespace ResourceBoundary

def toScratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx}
    (boundary :
      ResourceBoundary cursor (resource := .scratch config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    Boundary cursor (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := sourceCtx)
      (source := source) (target := target) :=
  { sourceScope := boundary.sourceScope
    control := boundary.control
    destinations := boundary.destinations
    returnFrame := boundary.returnFrame
    leaveTarget := boundary.leaveTarget
    budget := boundary.budget
    invariant := boundary.invariant.toRuntime }

end ResourceBoundary

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
Resource-indexed exact loop-control evidence for one recursively dispatched
block.
-/
structure ResourceControlOutcomeForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (boundary :
      ResourceBoundary cursor (resource := resource)
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
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant
              (contract := program.memoryContract) (resource := resource)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              boundary.destinations.brk sourceFinal targetFinal
  cont :
    ∀ sourceFinal,
      sourceOutcome =
          Functions.Source.Effectful.Outcome.cont sourceFinal →
        ∃ targetFinal,
          targetOutcome =
              Structured.EffectSemantics.Outcome.cont targetFinal ∧
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant
              (contract := program.memoryContract) (resource := resource)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              boundary.destinations.cont sourceFinal targetFinal

namespace ControlOutcomeForward

/-- Lift the existing scratch-backed control result. -/
theorem toResource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    {cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx}
    {boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)}
    (hControl :
      ControlOutcomeForward cursor boundary sourceOutcome targetOutcome) :
    ResourceControlOutcomeForward cursor boundary.toResource sourceOutcome
      targetOutcome := by
  refine
    { brk := ?_
      cont := ?_ }
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTarget, hInvariant⟩ :=
      hControl.brk sourceFinal hOutcome
    exact ⟨targetFinal, hTarget, hInvariant.toResource⟩
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTarget, hInvariant⟩ :=
      hControl.cont sourceFinal hOutcome
    exact ⟨targetFinal, hTarget, hInvariant.toResource⟩

end ControlOutcomeForward

/--
One dispatched statement whose exact target outcome is shared by the ordinary
statement theorem and the dispatcher-only control-destination evidence.
-/
structure ControlledHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope
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
          root.lowerCtx afterState afterLocals cursor.plan root.returns
          (Functions.Scope.Stmt.outEnv live stmt) frameBase mode program
          sourceCtx stmt source expressions.toStructured target
          (Expressions.StmtList.toStructured headCode)
          sourceOutcome targetOutcome finalCtx ∧
        ControlOutcomeForward cursor boundary sourceOutcome targetOutcome

namespace ControlledHeadResult

/--
Lift an ordinary head result when its source outcome cannot be `break` or
`continue`.
-/
theorem of_no_control
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState afterState : AllocationLowering.State}
    {localsCtx afterLocals : Locals.Ctx}
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
    {headCode : List Expressions.Stmt}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (head :
      HeadResult cursor afterState afterLocals headCode tail
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome := sourceOutcome))
    (hBrk :
      ∀ sourceFinal,
        sourceOutcome ≠ Functions.Source.Effectful.Outcome.brk sourceFinal)
    (hCont :
      ∀ sourceFinal,
        sourceOutcome ≠ Functions.Source.Effectful.Outcome.cont sourceFinal) :
    ControlledHeadResult cursor boundary afterState afterLocals headCode tail
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) := by
  obtain ⟨targetOutcome, hRuntime⟩ := head.runtime
  exact
    { head := head
      runtime :=
        ⟨targetOutcome, hRuntime,
          { brk := by
              intro sourceFinal hOutcome
              exact False.elim (hBrk sourceFinal hOutcome)
            cont := by
              intro sourceFinal hOutcome
              exact False.elim (hCont sourceFinal hOutcome) }⟩ }

end ControlledHeadResult

/--
One resource-indexed dispatched statement whose exact target outcome is
shared by the statement theorem and canonical control-destination evidence.
-/
structure ResourceControlledHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (boundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (afterState : AllocationLowering.State)
    (afterLocals : Locals.Ctx)
    (headCode : List Expressions.Stmt)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals) : Prop where
  head :
    ResourceHeadResult cursor afterState afterLocals headCode tail
      (resource := resource) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome)
  runtime :
    ∃ targetOutcome,
      AllocationObserverOutcome.StmtResourceResult
          program.memoryContract resource allocatorDepth transcript
          root.lowerCtx afterState afterLocals cursor.plan root.returns
          (Functions.Scope.Stmt.outEnv live stmt) frameBase mode program
          sourceCtx stmt source expressions.toStructured target
          (Expressions.StmtList.toStructured headCode)
          sourceOutcome targetOutcome finalCtx ∧
        ResourceControlOutcomeForward cursor boundary sourceOutcome
          targetOutcome

namespace ControlledHeadResult

/-- Lift an existing scratch-backed controlled head into the resource API. -/
theorem toResource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState afterState : AllocationLowering.State}
    {localsCtx afterLocals : Locals.Ctx}
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
    {headCode : List Expressions.Stmt}
    {cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx}
    {boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)}
    {tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals}
    (hHead :
      ControlledHeadResult cursor boundary afterState afterLocals headCode tail
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome := sourceOutcome)) :
    ResourceControlledHeadResult cursor boundary.toResource afterState
      afterLocals headCode tail
      (resource := .scratch config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) := by
  obtain ⟨targetOutcome, hRuntime, hControl⟩ := hHead.runtime
  exact
    { head := hHead.head.toResource
      runtime :=
        ⟨targetOutcome, hRuntime.toResource, hControl.toResource⟩ }

end ControlledHeadResult

namespace ResourceControlledHeadResult

/--
Lift a resource-indexed head result when its source outcome cannot be
`break` or `continue`.
-/
theorem of_no_control
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState afterState : AllocationLowering.State}
    {localsCtx afterLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {headCode : List Expressions.Stmt}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (boundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (head :
      ResourceHeadResult cursor afterState afterLocals headCode tail
        (resource := resource) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome := sourceOutcome))
    (hBrk :
      ∀ sourceFinal,
        sourceOutcome ≠ Functions.Source.Effectful.Outcome.brk sourceFinal)
    (hCont :
      ∀ sourceFinal,
        sourceOutcome ≠ Functions.Source.Effectful.Outcome.cont sourceFinal) :
    ResourceControlledHeadResult cursor boundary afterState afterLocals
      headCode tail
      (resource := resource) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome) := by
  obtain ⟨targetOutcome, hRuntime⟩ := head.runtime
  exact
    { head := head
      runtime :=
        ⟨targetOutcome, hRuntime,
          { brk := by
              intro sourceFinal hOutcome
              exact False.elim (hBrk sourceFinal hOutcome)
            cont := by
              intro sourceFinal hOutcome
              exact False.elim (hCont sourceFinal hOutcome) }⟩ }

end ResourceControlledHeadResult

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        root.returns (Functions.Scope.Block.outEnv live sourceBlock)
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
One recursively dispatched open block under the compiler-selected resource
mode.
-/
structure ResourceBlockResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (boundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) : Prop where
  runtime :
    ∃ targetOutcome,
      AllocationObserverOutcome.BlockResourceResult
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        root.returns (Functions.Scope.Block.outEnv live sourceBlock)
        frameBase mode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceOutcome targetOutcome finalCtx ∧
      ResourceControlOutcomeForward cursor boundary sourceOutcome
        targetOutcome
  regularScope :
    sourceOutcome.mode = .regular →
      ∀ name,
        name ∈ finalCtx.scope ↔
          name ∈ Functions.Scope.Block.outEnv live sourceBlock

namespace BlockResult

/-- Lift the existing scratch-backed recursive block result. -/
theorem toResource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx}
    {boundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)}
    (hResult :
      BlockResult cursor boundary
        (sourceOutcome := sourceOutcome) (finalCtx := finalCtx)) :
    ResourceBlockResult cursor boundary.toResource
      (sourceOutcome := sourceOutcome) (finalCtx := finalCtx) := by
  obtain ⟨targetOutcome, hRuntime, hControl⟩ := hResult.runtime
  exact
    { runtime :=
        ⟨targetOutcome, hRuntime.toResource, hControl.toResource⟩
      regularScope := hResult.regularScope }

end BlockResult

/--
The compiler-selected recursive interface used by structured statement
adapters.

Every recursive call targets a real synchronized cursor, consumes a strictly
smaller source fuel, and receives only the shared source/control/allocation
boundary. Generated code and recursive proof evidence stay out of the public
boundary.
-/
def ResourceRecursiveBlockForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx),
    sourceFuel < fuelBound →
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) →
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program sourceCtx sourceFuel sourceBlock source =
      .ok (sourceOutcome, finalCtx) →
    ResourceBlockResult cursor hBoundary
      (resource := resource) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome)

/--
The existing scratch-backed recursive interface.
-/
def RecursiveBlockForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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

namespace RecursiveBlockForward

/-- Lift the complete existing scratch recursion into the resource API. -/
theorem toResource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {config : Frame.Config}
    {allocatorDepth frameBase fuelBound : Nat}
    {transcript : Trace}
    (hRecursive :
      RecursiveBlockForward (root := root) (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (fuelBound := fuelBound) (transcript := transcript)) :
    ResourceRecursiveBlockForward (root := root)
      (resource := .scratch config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (fuelBound := fuelBound) (transcript := transcript) := by
  intro scope live sourceBlock lowerState localsCtx mode sourceCtx finalCtx
    source target sourceFuel sourceOutcome cursor hFuel hBoundary hSource
  exact
    (hRecursive cursor hFuel hBoundary.toScratch hSource).toResource

end RecursiveBlockForward

namespace BlockResult

theorem regular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        (AllocationObserverOutcome.outcomeLive root.returns
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

namespace ResourceBlockResult

theorem regular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (boundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (result :
      ResourceBlockResult cursor boundary (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome :=
          Functions.Source.Effectful.Outcome.regular sourceFinal)) :
    ∃ targetFinal finalMode,
      AllocationObserverStatement.Sequence.RegularBlockResourceInvariantForward
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (boundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (result :
      ResourceBlockResult cursor boundary (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx) (finalCtx := finalCtx)
        (source := source) (target := target)
        (sourceOutcome := sourceOutcome))
    (hMode : sourceOutcome.mode ≠ .regular) :
    ∃ targetOutcome finalMode,
      AllocationObserverOutcome.BlockResourceForward
        program.memoryContract resource allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive root.returns
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

end ResourceBlockResult

namespace ResourceRecursiveBlockForward

/--
Invoke the compiler-selected recursive block interface at a regular open-block
result.
-/
theorem regular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := resource) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
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
      AllocationObserverStatement.Sequence.RegularBlockResourceInvariantForward
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
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
Invoke the compiler-selected recursive block interface at an abrupt open-block
result.
-/
theorem nonregular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := resource) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
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
      AllocationObserverOutcome.BlockResourceForward
        program.memoryContract resource allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive root.returns
          (Functions.Scope.Block.outEnv live sourceBlock)
          sourceCtx sourceOutcome.mode)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured cursor.compiled }
        target sourceOutcome targetOutcome finalCtx :=
  ResourceBlockResult.nonregular cursor
    hBoundary (hRecursive cursor hFuel hBoundary hSource) hMode

/--
Discharge one regular scoped block through compiler-selected recursive
open-block preservation and the statement-owned lexical cleanup theorem.

The loop pass only needs the ordinary scoped invariant. Resource bookkeeping
remains internal to the recursive open-block proof and is forgotten exactly at
this adjacent interface.
-/
theorem scopedRegularInvariant
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetBlock : Expressions.Block}
    {afterLocals : Locals.Ctx}
    {afterPlan : Locals.Allocation.Plan}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := resource) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
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
        root.lowerCtx lowerState afterLocals afterPlan live mode)
    (hAfterWF : afterPlan.WellFormed)
    (hAfterLayout : afterLocals.layout = localsCtx.layout)
    (hFinish :
      Locals.finishScoped afterLocals cursor.finalLocals cursor.compiled =
        some targetBlock) :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularScopedBlockInvariantForward
        program.memoryContract transcript root.lowerCtx lowerState afterLocals
        afterPlan live frameBase mode program sourceCtx sourceBlock source
        expressions.toStructured
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
      regular cursor hRecursive hFuel hBoundary hOpen
    obtain ⟨targetFinal, hScoped⟩ :=
      AllocationObserverStatement.Sequence.RegularScopedBlockInvariantForward.finish_regular
        hForward.toInvariant hBoundary.sourceScope
        (congrArg List.length hAfterLayout.symm)
        hAfterCompiler hAfterWF
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
Discharge one abrupt scoped block through compiler-selected recursive
open-block preservation. The ordinary scoped execution proof is separated from
the resource-indexed destination evidence retained by the recursive boundary.
-/
theorem scopedNonregularControlled
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := resource) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript))
    (hFuel : sourceFuel < fuelBound)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
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
      AllocationObserverStatement.Sequence.ScopedBlockForward
        program.memoryContract transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive root.returns
          (Functions.Scope.Block.outEnv live sourceBlock)
          sourceCtx sourceOutcome.mode)
        frameBase finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured targetBlock.stmts }
        target sourceOutcome targetOutcome ∧
      ResourceControlOutcomeForward cursor hBoundary sourceOutcome
        targetOutcome := by
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
    have hResult :=
      hRecursive cursor hFuel hBoundary hOpen
    obtain ⟨targetOutcome, hRuntime, hControl⟩ :=
      hResult.runtime
    cases hRuntime with
    | regular _ _ =>
        exact False.elim (hOpenMode rfl)
    | nonregular _ hForward =>
      exact
        ⟨targetOutcome, _,
          AllocationObserverStatement.Sequence.ScopedBlockForward.finish_nonregular
            (AllocationObserverStatement.Sequence.BlockForward.ofResource
              hForward)
            hOpenMode hFinish,
          hControl⟩

end ResourceRecursiveBlockForward

namespace Boundary

/--
Construct the canonical recursive boundary at a compiler-selected function
body. Selection and compilation remain owned by the call pass; this constructor
only aligns the source function scope with the allocation slot order and
records the control facts preserved by the generated parameter/return prelude.
-/
def functionBody
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hProgramScoped : program.Scoped)
    (hReturnFrame : target.source.returns ≠ [])
    (hBudget : Frame.Budget config allocatorDepth)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth artifact.lowerCtx
        artifact.bodyStart prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase
        (prepared.mode.atStackDepth
          (currentStackOrder prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)).length)
        source target) :
    Boundary
      (AllocationObserverForward.BodyCursor.RootArtifact.cursor
        (AllocationObserverForward.BodyCursor.RootArtifact.ofSelected
          artifact prepared (artifact.bodyScoped hProgramScoped)))
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase)
      (mode :=
        prepared.mode.atStackDepth
          (currentStackOrder prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)).length)
      (sourceCtx := Functions.Source.Effectful.FunDef.bodyCtx fn)
      (source := source) (target := target) := by
  have hParamControl :=
    Locals.Block.compileOpen_sameControl prepared.compileParams
  have hReturnControl :=
    Locals.Block.compileOpen_sameControl prepared.compileReturns
  have hPreludeControl :
      Locals.Ctx.SameControl artifact.entryCtx prepared.returnCtx :=
    hParamControl.trans hReturnControl
  refine
    { sourceScope := ?_
      control := ?_
      destinations := ?_
      returnFrame := ?_
      leaveTarget := ?_
      budget := hBudget
      invariant := hInvariant }
  · intro localName
    simp [AllocationObserverForward.BodyCursor.RootArtifact.ofSelected,
      Functions.Source.Effectful.FunDef.bodyCtx,
      Functions.Source.Ctx.initial,
      Functions.Source.Ctx.withLeaveScope,
      artifact.slotsMatch.2.1, artifact.slotsMatch.2.2]
  · simpa
      [AllocationObserverForward.BodyCursor.RootArtifact.ofSelected,
        artifact.slotsMatch.2.1, artifact.slotsMatch.2.2] using
      AllocationObserverOutcome.ControlScopesWithin.functionBody fn
  · refine
      { brk := .unavailable ?_ ?_
        cont := .unavailable ?_ ?_ }
    · simp [AllocationObserverOutcome.ControlKind.sourceScope?,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial,
        Functions.Source.Ctx.withLeaveScope]
    · change prepared.returnCtx.breakDepth? = none
      rw [← hPreludeControl.breakDepth]
      rfl
    · simp [AllocationObserverOutcome.ControlKind.sourceScope?,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial,
        Functions.Source.Ctx.withLeaveScope]
    · change prepared.returnCtx.continueDepth? = none
      rw [← hPreludeControl.continueDepth]
      rfl
  · intro _functionScope _hLeave
    exact hReturnFrame
  · intro _functionScope _hLeave
    constructor
    · change prepared.returnCtx.leaveDepth? = some 0
      rw [← hPreludeControl.leaveDepth]
      rfl
    · change prepared.returnCtx.leaveRetc = fn.returns.length
      rw [← hPreludeControl.leaveRetc]
      rfl

/--
Invoke the recursive block interface at a regular open-block result.
-/
theorem recursiveRegular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (root := root)
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
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (root := root)
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
        (AllocationObserverOutcome.outcomeLive root.returns
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {afterLocals : Locals.Ctx}
    {afterPlan : Locals.Allocation.Plan}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (root := root)
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
        root.lowerCtx lowerState afterLocals afterPlan live mode)
    (hAfterWF : afterPlan.WellFormed)
    (hAfterLayout : afterLocals.layout = localsCtx.layout)
    (hFinish :
      Locals.finishScoped afterLocals cursor.finalLocals cursor.compiled =
        some targetBlock) :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularScopedBlockRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        root.lowerCtx lowerState afterLocals afterPlan live frameBase mode
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
        hForward hBoundary.sourceScope
        (congrArg List.length hAfterLayout.symm)
        hAfterCompiler hAfterWF
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
the statement-owned nonregular scoped theorem. This strengthened form retains
the exact break/continue destination selected by the recursive boundary.
-/
theorem recursiveScopedNonregularControlled
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (root := root)
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
        (AllocationObserverOutcome.outcomeLive root.returns
          (Functions.Scope.Block.outEnv live sourceBlock)
          sourceCtx sourceOutcome.mode)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured targetBlock.stmts }
        target sourceOutcome targetOutcome ∧
      ControlOutcomeForward cursor hBoundary sourceOutcome targetOutcome := by
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
    have hResult :=
      hRecursive cursor hFuel hBoundary hOpen
    obtain ⟨targetOutcome, hRuntime, hControl⟩ :=
      hResult.runtime
    cases hRuntime with
    | regular _ _ =>
        exact False.elim (hOpenMode rfl)
    | nonregular _ hForward =>
      exact
        ⟨targetOutcome, _,
          AllocationObserverStatement.Sequence.ScopedBlockRuntimeForward.finish_nonregular
            hForward hOpenMode hFinish,
          hControl⟩

/--
Compatibility projection of `recursiveScopedNonregularControlled` for
adjacent pass theorems that do not inspect exact loop destinations.
-/
theorem recursiveScopedNonregular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        sourceBlock lowerState localsCtx)
    (hRecursive :
      RecursiveBlockForward (root := root)
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
        (AllocationObserverOutcome.outcomeLive root.returns
          (Functions.Scope.Block.outEnv live sourceBlock)
          sourceCtx sourceOutcome.mode)
        frameBase mode finalMode program sourceCtx sourceBlock source
        expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured targetBlock.stmts }
        target sourceOutcome targetOutcome := by
  obtain ⟨targetOutcome, finalMode, hForward, _hControl⟩ :=
    recursiveScopedNonregularControlled cursor hRecursive hFuel hBoundary
      hSource hMode hFinish
  exact
    ⟨targetOutcome, finalMode, hForward⟩

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope live
        outerBlock lowerState localsCtx)
    (initCursor :
      AllocationObserverForward.BodyCursor.CoreCursor root initScope live
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
        program.memoryContract config allocatorDepth root.lowerCtx
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope outerLive
        outerBlock lowerState localsCtx)
    (initCursor :
      AllocationObserverForward.BodyCursor.CoreCursor root initScope outerLive
        init lowerState localsCtx.withoutLoopControl)
    (hBoundary :
      Boundary outer (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      RecursiveBlockForward (root := root)
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
        root.lowerCtx initCursor.finalState initCursor.finalLocals
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {outerMode loopMode : ActivationMode}
    {outerCtx loopCtx : Functions.Source.Ctx}
    {outerSource postSource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget postTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope outerLive
        outerBlock outerState outerLocals)
    (postCursor :
      AllocationObserverForward.BodyCursor.CoreCursor root postScope loopLive
        post loopState initLocals.withoutLoopControl)
    (hBoundary :
      Boundary outer (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := outerMode)
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
        program.memoryContract config allocatorDepth root.lowerCtx
        loopState initLocals.withoutLoopControl postCursor.plan loopLive
        frameBase loopMode postSource postTarget) :
    Boundary postCursor (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := loopMode) (sourceCtx := loopCtx.withoutLoopControl)
      (source := postSource) (target := postTarget) := by
  have hLoopControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns loopLive loopCtx :=
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
      _ = root.returns.length := hRetc

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {outerMode loopMode : ActivationMode}
    {outerCtx loopCtx : Functions.Source.Ctx}
    {outerSource bodySource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget bodyTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope outerLive
        outerBlock outerState outerLocals)
    (bodyCursor :
      AllocationObserverForward.BodyCursor.CoreCursor root bodyScope loopLive
        body bodyState
        (initLocals.withLoopControl initLocals.layout.length))
    (hBoundary :
      Boundary outer (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := outerMode)
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
        root.lowerCtx loopState initLocals loopPlan loopLive loopMode)
    (hLoopPlanWF : loopPlan.WellFormed)
    (hState :
      AllocationLowering.StateExtends loopLive loopState bodyState)
    (hReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        (loopCtx.withLoopControl loopCtx.scope loopCtx.scope) bodyTarget)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        bodyState
        (initLocals.withLoopControl initLocals.layout.length)
        bodyCursor.plan loopLive frameBase loopMode bodySource bodyTarget) :
    Boundary bodyCursor (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := loopMode)
      (sourceCtx :=
        loopCtx.withLoopControl loopCtx.scope loopCtx.scope)
      (source := bodySource) (target := bodyTarget) := by
  have hLoopControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns loopLive loopCtx :=
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
          (fun _ hName => hName) (SameFrame.refl loopMode)
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
      _ = root.returns.length := hRetc

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope live
        outerBlock outerState outerLocals)
    (nested :
      AllocationObserverForward.BodyCursor.CoreCursor root nestedScope live
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
        program.memoryContract config allocatorDepth root.lowerCtx
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
Transport exact abrupt-destination evidence from a pass-owned nested cursor
back to the enclosing cursor boundary used to construct it.
-/
theorem ControlOutcomeForward.of_rebase
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome (transcript := transcript)}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope live
        outerBlock outerState outerLocals)
    (nested :
      AllocationObserverForward.BodyCursor.CoreCursor root nestedScope live
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
        program.memoryContract config allocatorDepth root.lowerCtx
        nestedState nestedLocals nested.plan live frameBase mode
        nestedSource nestedTarget)
    (hNested :
      ControlOutcomeForward nested
        (hBoundary.rebase outer nested hState hLocals hReturnFrame hInvariant)
        sourceOutcome targetOutcome) :
    ControlOutcomeForward outer hBoundary sourceOutcome targetOutcome := by
  constructor
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTargetOutcome, hDestination⟩ :=
      hNested.brk sourceFinal hOutcome
    refine ⟨targetFinal, hTargetOutcome, ?_⟩
    exact
      AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_transport
        hBoundary.destinations.brk
        (AllocationObserverOutcome.SameControl.refl sourceCtx)
        hLocals hState (fun _ hName => hName) (SameFrame.refl mode)
        hDestination
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTargetOutcome, hDestination⟩ :=
      hNested.cont sourceFinal hOutcome
    refine ⟨targetFinal, hTargetOutcome, ?_⟩
    exact
      AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_transport
        hBoundary.destinations.cont
        (AllocationObserverOutcome.SameControl.refl sourceCtx)
        hLocals hState (fun _ hName => hName) (SameFrame.refl mode)
        hDestination

end Boundary

namespace ResourceBoundary

/--
Rebase a resource-indexed dispatcher boundary onto another pass-owned cursor
in the same source control context.
-/
def rebase
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {outerScope nestedScope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {outerBlock nestedBlock : Functions.Block}
    {outerState nestedState : AllocationLowering.State}
    {outerLocals nestedLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {outerSource nestedSource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget nestedTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope live
        outerBlock outerState outerLocals)
    (nested :
      AllocationObserverForward.BodyCursor.CoreCursor root nestedScope live
        nestedBlock nestedState nestedLocals)
    (hBoundary :
      ResourceBoundary outer (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := outerSource) (target := outerTarget))
    (hState :
      AllocationLowering.StateExtends live outerState nestedState)
    (hLocals : Locals.Ctx.SameControl outerLocals nestedLocals)
    (hReturnFrame :
      ∀ functionScope,
        sourceCtx.leaveScope? = some functionScope →
          nestedTarget.source.returns ≠ [])
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
        nestedState nestedLocals nested.plan live frameBase mode
        nestedSource nestedTarget) :
    ResourceBoundary nested (resource := resource)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := sourceCtx)
      (source := nestedSource) (target := nestedTarget) :=
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
Enter a `for` initializer through its real lexical cursor under the
compiler-selected resource mode.
-/
def forInit
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {outerScope initScope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {outerBlock init : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope live
        outerBlock lowerState localsCtx)
    (initCursor :
      AllocationObserverForward.BodyCursor.CoreCursor root initScope live
        init lowerState localsCtx.withoutLoopControl)
    (hBoundary :
      ResourceBoundary outer (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    ResourceBoundary initCursor (resource := resource)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
      (source := source) (target := target) := by
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        initCursor.plan outer.plan live :=
    initCursor.planAgreesOn outer rfl
  have hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
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

/-- Enter a loop post block under the compiler-selected resource mode. -/
def forPost
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {outerScope postScope : Locals.Allocation.ScopeId}
    {outerLive loopLive : List Functions.Name}
    {outerBlock post : Functions.Block}
    {initLowered : Locals.Block}
    {initCode : List Expressions.Stmt}
    {outerState loopState : AllocationLowering.State}
    {outerLocals initLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {outerMode loopMode : ActivationMode}
    {outerCtx loopCtx : Functions.Source.Ctx}
    {outerSource postSource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget postTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope outerLive
        outerBlock outerState outerLocals)
    (postCursor :
      AllocationObserverForward.BodyCursor.CoreCursor root postScope loopLive
        post loopState initLocals.withoutLoopControl)
    (hBoundary :
      ResourceBoundary outer (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := outerMode) (sourceCtx := outerCtx)
        (source := outerSource) (target := outerTarget))
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
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
        loopState initLocals.withoutLoopControl postCursor.plan loopLive
        frameBase loopMode postSource postTarget) :
    ResourceBoundary postCursor (resource := resource)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := loopMode) (sourceCtx := loopCtx.withoutLoopControl)
      (source := postSource) (target := postTarget) := by
  have hLoopControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns loopLive loopCtx :=
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
      _ = root.returns.length := hRetc

/-- Enter a loop body under the compiler-selected resource mode. -/
def forBody
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {outerScope bodyScope : Locals.Allocation.ScopeId}
    {outerLive loopLive : List Functions.Name}
    {outerBlock body : Functions.Block}
    {initLowered : Locals.Block}
    {initCode : List Expressions.Stmt}
    {outerState loopState bodyState : AllocationLowering.State}
    {outerLocals initLocals : Locals.Ctx}
    {loopPlan : Locals.Allocation.Plan}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {outerMode loopMode : ActivationMode}
    {outerCtx loopCtx : Functions.Source.Ctx}
    {outerSource bodySource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget bodyTarget :
      Structured.ObserverSemantics.State transcript}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope outerLive
        outerBlock outerState outerLocals)
    (bodyCursor :
      AllocationObserverForward.BodyCursor.CoreCursor root bodyScope loopLive
        body bodyState
        (initLocals.withLoopControl initLocals.layout.length))
    (hBoundary :
      ResourceBoundary outer (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := outerMode) (sourceCtx := outerCtx)
        (source := outerSource) (target := outerTarget))
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
        root.lowerCtx loopState initLocals loopPlan loopLive loopMode)
    (hLoopPlanWF : loopPlan.WellFormed)
    (hState :
      AllocationLowering.StateExtends loopLive loopState bodyState)
    (hReturnFrame :
      AllocationObserverOutcome.ReturnFrameAvailable
        (loopCtx.withLoopControl loopCtx.scope loopCtx.scope) bodyTarget)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
        bodyState
        (initLocals.withLoopControl initLocals.layout.length)
        bodyCursor.plan loopLive frameBase loopMode bodySource bodyTarget) :
    ResourceBoundary bodyCursor (resource := resource)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := loopMode)
      (sourceCtx :=
        loopCtx.withLoopControl loopCtx.scope loopCtx.scope)
      (source := bodySource) (target := bodyTarget) := by
  have hLoopControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns loopLive loopCtx :=
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
          (fun _ hName => hName) (SameFrame.refl loopMode)
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
      _ = root.returns.length := hRetc

/--
Transport resource-indexed abrupt-destination evidence from a nested cursor
back to the enclosing cursor boundary.
-/
theorem ResourceControlOutcomeForward.of_rebase
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {outerScope nestedScope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {outerBlock nestedBlock : Functions.Block}
    {outerState nestedState : AllocationLowering.State}
    {outerLocals nestedLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {outerSource nestedSource :
      Functions.ObserverSemantics.State transcript}
    {outerTarget nestedTarget :
      Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome (transcript := transcript)}
    (outer :
      AllocationObserverForward.BodyCursor.CoreCursor root outerScope live
        outerBlock outerState outerLocals)
    (nested :
      AllocationObserverForward.BodyCursor.CoreCursor root nestedScope live
        nestedBlock nestedState nestedLocals)
    (hBoundary :
      ResourceBoundary outer (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := outerSource) (target := outerTarget))
    (hState :
      AllocationLowering.StateExtends live outerState nestedState)
    (hLocals : Locals.Ctx.SameControl outerLocals nestedLocals)
    (hReturnFrame :
      ∀ functionScope,
        sourceCtx.leaveScope? = some functionScope →
          nestedTarget.source.returns ≠ [])
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
        nestedState nestedLocals nested.plan live frameBase mode
        nestedSource nestedTarget)
    (hNested :
      ResourceControlOutcomeForward nested
        (hBoundary.rebase outer nested hState hLocals hReturnFrame hInvariant)
        sourceOutcome targetOutcome) :
    ResourceControlOutcomeForward outer hBoundary sourceOutcome
      targetOutcome := by
  constructor
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTargetOutcome, hDestination⟩ :=
      hNested.brk sourceFinal hOutcome
    refine ⟨targetFinal, hTargetOutcome, ?_⟩
    exact
      AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_transport
        hBoundary.destinations.brk
        (AllocationObserverOutcome.SameControl.refl sourceCtx)
        hLocals hState (fun _ hName => hName) (SameFrame.refl mode)
        hDestination
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTargetOutcome, hDestination⟩ :=
      hNested.cont sourceFinal hOutcome
    refine ⟨targetFinal, hTargetOutcome, ?_⟩
    exact
      AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_transport
        hBoundary.destinations.cont
        (AllocationObserverOutcome.SameControl.refl sourceCtx)
        hLocals hState (fun _ hName => hName) (SameFrame.refl mode)
        hDestination

end ResourceBoundary

namespace Boundary

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      RecursiveBlockForward (root := root)
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        AllocationObserverOutcome.outcomeLive root.returns live sourceCtx
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
Dispatch a `for` whose initializer and complete loop both finish regularly.

Recursive work is confined to the real initializer, body, and post cursors.
The initializer's empty final tail supplies the stable loop-entry plan used by
the loop-owned source-fuel theorem.
-/
theorem forRegularHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {source sourceAfterInit sourceLoopFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      RecursiveBlockForward (root := root)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := sourceFuel + 1)
        (transcript := transcript))
    (hInitSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx.withoutLoopControl sourceFuel init source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceAfterInit,
            initCtx))
    (hLoopSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program initCtx cond initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceLoopFinal)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                sourceCtx.scope sourceLoopFinal)) := by
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
  cases hInitFinalState
  cases hInitFinalLocals
  let initFinished := initCursor.finished
  have hInitBoundary :
      Boundary initCursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
        (source := source) (target := target) :=
    forInit cursor initCursor hBoundary
  obtain
      ⟨targetAfterInit, initMode, hInitForward,
        hInitControl, hInitScope⟩ :=
    recursiveRegular initCursor hRecursive
      (Nat.lt_succ_self sourceFuel) hInitBoundary hInitSource
  have hOuterSubset :
      ∀ name, name ∈ live →
        name ∈ Functions.Scope.Block.outEnv live init :=
    fun name hName => Functions.Scope.Block.mem_outEnv hName
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.for_regular_of_safe_source_run
      hConfig initCursor.sourceScoped hCondScoped hBoundary.sourceScope
      hInitScope hOuterSubset hBoundary.invariant hBoundary.returnFrame
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
        exact
          ⟨targetAfterInit, hInitForward, hInitControl⟩)
      (by
        intro loweredInit' loopState' afterPost' afterBody'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            Boundary bodyCursor (config := config)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          forBody cursor bodyCursor hBoundary initCursor.compile
            hInitScope hOuterSubset hInitControl
            hInvariant.activation.compiler
            initCursor.planWF hLoopStateExtends hReturnFrame hBodyInvariant
        have hAfterCompiler :
            AllocationObserverContext.ActivationExprContext
              root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              initCursor.plan (Functions.Scope.Block.outEnv live init)
              initMode :=
          (hInvariant.activation.compiler.transport_state
              hPostShape.1 hPostShape.2)
            |>.transport_locals_layout
              (after :=
                initCursor.finalLocals.withLoopControl
                  initCursor.finalLocals.layout.length) rfl
        exact
          by
            rw [hCompiledBodyShape]
            exact
              recursiveScopedRegular bodyCursor hRecursive
                (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
                hBodyBoundary hRun hAfterCompiler initCursor.planWF rfl
                hFinishBody)
      (by
        intro loweredInit' loopState' afterPost' afterBody'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            Boundary bodyCursor (config := config)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          forBody cursor bodyCursor hBoundary initCursor.compile
            hInitScope hOuterSubset hInitControl
            hInvariant.activation.compiler
            initCursor.planWF hLoopStateExtends hReturnFrame hBodyInvariant
        obtain
            ⟨targetOutcome, finalMode, hScoped, hControl⟩ :=
          recursiveScopedNonregularControlled bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun
            (by
              simp [Functions.Source.Effectful.Outcome.brk,
                Locals.Source.Effectful.Outcome.brk])
            hFinishBody
        obtain ⟨targetBodyFinal, hTargetOutcome, hDestination⟩ :=
          hControl.brk bodyFinal rfl
        subst targetOutcome
        rcases hScoped with
          ⟨bodySourceFuel, bodyTargetFuel, hBodySource,
            hBodyTarget, _hOutcomeRel, _hSameFrame, hBodyEffect⟩
        have hBaseDestination :
            AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant
              (contract := program.memoryContract) (config := config)
              (allocatorDepth := allocatorDepth)
              (frameBase := frameBase)
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.activation.compiler initCursor.planWF
                hLoopStateExtends
                hInitScope).brk bodyFinal targetBodyFinal := by
          apply
            AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_transport
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.activation.compiler initCursor.planWF
                hLoopStateExtends
                hInitScope).brk
              (AllocationObserverOutcome.SameControl.refl _)
              (Locals.Ctx.SameControl.refl _)
              (AllocationLowering.StateExtends.of_shape rfl rfl)
              (fun _ hName => hName) (SameFrame.refl initMode)
          simpa [hBodyBoundary, forBody] using hDestination
        have hLoopInvariant :=
          AllocationObserverOutcome.ControlDestinations.loopBody_break_destination
            hInvariant.activation.compiler initCursor.planWF
              hLoopStateExtends
              hInitScope hBaseDestination
        have hBodyActivationEffect :=
          Frame.OutcomeEffect.activation_of_not_halt hBodyEffect (by
            intro kind hMode
            cases hMode)
        rw [hCompiledBodyShape]
        exact
          ⟨targetBodyFinal, bodySourceFuel, bodyTargetFuel,
            hBodySource, hBodyTarget, hLoopInvariant,
            hBodyActivationEffect⟩)
      (by
        intro loweredInit' loopState' afterPost' afterBody'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            Boundary bodyCursor (config := config)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          forBody cursor bodyCursor hBoundary initCursor.compile
            hInitScope hOuterSubset hInitControl
            hInvariant.activation.compiler
            initCursor.planWF hLoopStateExtends hReturnFrame hBodyInvariant
        obtain
            ⟨targetOutcome, finalMode, hScoped, hControl⟩ :=
          recursiveScopedNonregularControlled bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun
            (by
              simp [Functions.Source.Effectful.Outcome.cont,
                Locals.Source.Effectful.Outcome.cont])
            hFinishBody
        obtain ⟨targetBodyFinal, hTargetOutcome, hDestination⟩ :=
          hControl.cont bodyFinal rfl
        subst targetOutcome
        rcases hScoped with
          ⟨bodySourceFuel, bodyTargetFuel, hBodySource,
            hBodyTarget, _hOutcomeRel, _hSameFrame, hBodyEffect⟩
        have hBaseDestination :
            AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant
              (contract := program.memoryContract) (config := config)
              (allocatorDepth := allocatorDepth)
              (frameBase := frameBase)
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.activation.compiler initCursor.planWF
                hLoopStateExtends
                hInitScope).cont bodyFinal targetBodyFinal := by
          apply
            AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_transport
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.activation.compiler initCursor.planWF
                hLoopStateExtends
                hInitScope).cont
              (AllocationObserverOutcome.SameControl.refl _)
              (Locals.Ctx.SameControl.refl _)
              (AllocationLowering.StateExtends.of_shape rfl rfl)
              (fun _ hName => hName) (SameFrame.refl initMode)
          simpa [hBodyBoundary, forBody] using hDestination
        have hLoopInvariant :=
          AllocationObserverOutcome.ControlDestinations.loopBody_continue_destination
            hInvariant.activation.compiler initCursor.planWF
              hLoopStateExtends
              hInitScope hBaseDestination
        have hContinueInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              initCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodyFinal targetBodyFinal :=
          (hLoopInvariant.transport_state hPostShape.1 hPostShape.2)
            |>.transport_locals_layout
              (after :=
                initCursor.finalLocals.withLoopControl
                  initCursor.finalLocals.layout.length) rfl
        have hBodyActivationEffect :=
          Frame.OutcomeEffect.activation_of_not_halt hBodyEffect (by
            intro kind hMode
            cases hMode)
        rw [hCompiledBodyShape]
        exact
          ⟨targetBodyFinal, bodySourceFuel, bodyTargetFuel,
            hBodySource, hBodyTarget, hContinueInvariant,
            hBodyActivationEffect⟩)
      (by
        intro loweredInit' loopState' afterPost' loweredPost initLocals'
          postLocals' initCode' postCode compiledPost' postFuel postSource
          postFinal postTarget hLowerInit' hCompileInit' hLowerPost'
          hCompilePost' hFinishPost' hInvariant
          hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hCompilePostPair :
            (postCursor.compiled, postCursor.finalLocals) =
              (postCode, postLocals') :=
          Option.some.inj (postCursor.compile.symm.trans hCompilePost')
        cases hCompilePostPair
        have hCompiledPost : compiledPost = compiledPost' :=
          Option.some.inj (hFinishPost.symm.trans hFinishPost')
        cases hCompiledPost
        have hCompiledPostShape :
            compiledPost.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledPost.stmts } := by
          cases compiledPost
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hPostPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan postCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (postCursor.planAgreesOn initFinished rfl).symm
        have hPostInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx initCursor.finalState
              initCursor.finalLocals.withoutLoopControl postCursor.plan
              (Functions.Scope.Block.outEnv live init)
              frameBase initMode postSource postTarget :=
          (((hInvariant.transport_state hPostShape.1.symm
                hPostShape.2.symm)
              |>.transport_locals_layout
                (after := initCursor.finalLocals.withoutLoopControl) rfl)
              |>.transport_plan postCursor.planWF hPostPlanAgree)
        have hPostBoundary :
            Boundary postCursor (config := config)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode) (sourceCtx := initCtx.withoutLoopControl)
              (source := postSource) (target := postTarget) :=
          forPost cursor postCursor hBoundary initCursor.compile
            hInitScope hOuterSubset hInitControl hReturnFrame hPostInvariant
        have hAfterCompiler :
            AllocationObserverContext.ActivationExprContext
              root.lowerCtx initCursor.finalState
              initCursor.finalLocals initCursor.plan
              (Functions.Scope.Block.outEnv live init) initMode :=
          (hInvariant.activation.compiler.transport_state hPostShape.1.symm
              hPostShape.2.symm)
            |>.transport_locals_layout
              (after := initCursor.finalLocals) rfl
        have hFinishPostAtLoop :
            Locals.finishScoped initCursor.finalLocals
                postCursor.finalLocals postCursor.compiled =
              some compiledPost := by
          simpa [Locals.finishScoped] using hFinishPost
        exact
          by
            rw [hCompiledPostShape]
            exact
              recursiveScopedRegular postCursor hRecursive
                (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
                hPostBoundary hRun hAfterCompiler initCursor.planWF
                rfl hFinishPostAtLoop)
      hLoopSource hLower hCompile
  have hRestrict :
      (Functions.ObserverSemantics.stateModel transcript).restrictTo
          sourceCtx.scope sourceLoopFinal =
        (Functions.ObserverSemantics.stateModel transcript).restrictTo
          live sourceLoopFinal :=
    Locals.Source.Effectful.StateModel.restrictTo_congr
      (Functions.ObserverSemantics.stateModel transcript)
      hBoundary.sourceScope
  rw [hRestrict]
  exact
    ⟨afterState, headCode, tail,
      HeadResult.ofRuntime cursor tail hCompiled
        (.regular
          (by
            simpa [Functions.Scope.Stmt.outEnv] using hForward)
          (AllocationObserverOutcome.SameControl.refl sourceCtx))
        hStep hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)⟩

/--
Dispatch a `for` whose initializer completes regularly and whose loop leaves
the activation or halts.

The dispatcher supplies the real lexical cursors and compiler artifacts. The
loop pass owns source-fuel recursion, while outcome-owned transport erases the
nested allocation index only after a genuine activation exit.
-/
theorem forExitHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
    {source sourceAfterInit :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceLoopOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      RecursiveBlockForward (root := root)
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := sourceFuel + 1)
        (transcript := transcript))
    (hInitSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx.withoutLoopControl sourceFuel init source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceAfterInit,
            initCtx))
    (hLoopSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program initCtx cond initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok sourceLoopOutcome)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceLoopOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceLoopOutcome) := by
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
  cases hInitFinalState
  cases hInitFinalLocals
  let initFinished := initCursor.finished
  have hInitBoundary :
      Boundary initCursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
        (source := source) (target := target) :=
    forInit cursor initCursor hBoundary
  obtain
      ⟨targetAfterInit, initMode, hInitForward,
        hInitControl, hInitScope⟩ :=
    recursiveRegular initCursor hRecursive
      (Nat.lt_succ_self sourceFuel) hInitBoundary hInitSource
  have hOuterSubset :
      ∀ name, name ∈ live →
        name ∈ Functions.Scope.Block.outEnv live init :=
    fun name hName => Functions.Scope.Block.mem_outEnv hName
  obtain ⟨targetOutcome, hForward⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.for_exit_of_components
      (outerPlan := cursor.plan) (loopPlan := initCursor.plan)
      (outerLive := live)
      (loopLive := Functions.Scope.Block.outEnv live init)
      (resultLive := root.returns)
      (outerMode := mode) (loopMode := initMode)
      hBoundary.invariant hBoundary.returnFrame
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
        exact
          ⟨targetAfterInit, hInitForward, hInitControl⟩)
      (by
        intro loweredInit' loopState' afterPost' afterBody'
          loweredCond' loweredPost loweredBody initLocals' postLocals'
          bodyLocals' initCode' condCode' postCode bodyCode compiledPost'
          compiledBody' targetAfterInit'
          hLowerInit' hCompileInit' hLowerCond' hLowerPost' hLowerBody'
          hCompileCond' hCompilePost' hFinishPost' hCompileBody'
          hFinishBody' hInvariant hLoopReturnFrame hPostReturnFrame
          hBodyReturnFrame
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerCondEq : loweredCond = loweredCond' :=
          Option.some.inj (hLowerCond.symm.trans hLowerCond')
        cases hLowerCondEq
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileCondEq : condCode = condCode' :=
          Option.some.inj (hCompileCond.symm.trans hCompileCond')
        cases hCompileCondEq
        have hCompilePostPair :
            (postCursor.compiled, postCursor.finalLocals) =
              (postCode, postLocals') :=
          Option.some.inj (postCursor.compile.symm.trans hCompilePost')
        cases hCompilePostPair
        have hCompiledPost : compiledPost = compiledPost' :=
          Option.some.inj (hFinishPost.symm.trans hFinishPost')
        cases hCompiledPost
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        cases targetAfterInit'
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hPostPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan postCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (postCursor.planAgreesOn initFinished rfl).symm
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hCompiledPostShape :
            compiledPost.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledPost.stmts } := by
          cases compiledPost
          rfl
        have hFinishPostAtLoop :
            Locals.finishScoped initCursor.finalLocals
                postCursor.finalLocals postCursor.compiled =
              some compiledPost := by
          simpa [Locals.finishScoped] using hFinishPost
        exact
          AllocationObserverStatement.ForLoop.NonregularRuntimeForward.of_safe_source_run
            hConfig hCondScoped hLowerCond hCompileCond
            hLoopReturnFrame hPostReturnFrame hBodyReturnFrame
            (by
              intro bodyFuel bodySource bodyFinal bodyTarget
                hBodyInvariant hReturnFrame hFuel hRun
              have hCursorInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx afterPost
                    (initCursor.finalLocals.withLoopControl
                      initCursor.finalLocals.layout.length)
                    bodyCursor.plan
                    (Functions.Scope.Block.outEnv live init)
                    frameBase initMode bodySource bodyTarget :=
                (((hBodyInvariant.transport_state
                      hPostShape.1 hPostShape.2)
                    |>.transport_locals_layout
                      (after :=
                        initCursor.finalLocals.withLoopControl
                          initCursor.finalLocals.layout.length) rfl)
                    |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
              let hBodyBoundary :
                  Boundary bodyCursor (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := initMode)
                    (sourceCtx :=
                      initCtx.withLoopControl initCtx.scope initCtx.scope)
                    (source := bodySource) (target := bodyTarget) :=
                forBody cursor bodyCursor hBoundary initCursor.compile
                  hInitScope hOuterSubset hInitControl
                  hBodyInvariant.activation.compiler
                  initCursor.planWF hLoopStateExtends hReturnFrame
                  hCursorInvariant
              have hAfterCompiler :
                  AllocationObserverContext.ActivationExprContext
                    root.lowerCtx afterPost
                    (initCursor.finalLocals.withLoopControl
                      initCursor.finalLocals.layout.length)
                    initCursor.plan
                    (Functions.Scope.Block.outEnv live init) initMode :=
                (hBodyInvariant.activation.compiler.transport_state
                    hPostShape.1 hPostShape.2)
                  |>.transport_locals_layout
                    (after :=
                      initCursor.finalLocals.withLoopControl
                        initCursor.finalLocals.layout.length) rfl
              rw [hCompiledBodyShape]
              exact
                recursiveScopedRegular bodyCursor hRecursive
                  (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
                  hBodyBoundary hRun hAfterCompiler initCursor.planWF rfl
                  hFinishBody)
            (by
              intro bodyFuel bodySource bodyFinal bodyTarget
                hBodyInvariant hReturnFrame hFuel hRun
              have hCursorInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx afterPost
                    (initCursor.finalLocals.withLoopControl
                      initCursor.finalLocals.layout.length)
                    bodyCursor.plan
                    (Functions.Scope.Block.outEnv live init)
                    frameBase initMode bodySource bodyTarget :=
                (((hBodyInvariant.transport_state
                      hPostShape.1 hPostShape.2)
                    |>.transport_locals_layout
                      (after :=
                        initCursor.finalLocals.withLoopControl
                          initCursor.finalLocals.layout.length) rfl)
                    |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
              let hBodyBoundary :
                  Boundary bodyCursor (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := initMode)
                    (sourceCtx :=
                      initCtx.withLoopControl initCtx.scope initCtx.scope)
                    (source := bodySource) (target := bodyTarget) :=
                forBody cursor bodyCursor hBoundary initCursor.compile
                  hInitScope hOuterSubset hInitControl
                  hBodyInvariant.activation.compiler
                  initCursor.planWF hLoopStateExtends hReturnFrame
                  hCursorInvariant
              obtain
                  ⟨targetBodyOutcome, bodyFinalMode,
                    hScoped, hControl⟩ :=
                recursiveScopedNonregularControlled bodyCursor hRecursive
                  (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
                  hBodyBoundary hRun
                  (by
                    simp [Functions.Source.Effectful.Outcome.cont,
                      Locals.Source.Effectful.Outcome.cont])
                  hFinishBody
              obtain
                  ⟨targetBodyFinal, hTargetOutcome, hDestination⟩ :=
                hControl.cont bodyFinal rfl
              subst targetBodyOutcome
              rcases hScoped with
                ⟨bodySourceFuel, bodyTargetFuel, hBodySource,
                  hBodyTarget, _hOutcomeRel, _hSameFrame, hBodyEffect⟩
              have hBaseDestination :
                  AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant
                    (contract := program.memoryContract)
                    (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase)
                    (AllocationObserverOutcome.ControlDestinations.loopBody
                      hBodyInvariant.activation.compiler
                      initCursor.planWF hLoopStateExtends
                      hInitScope).cont bodyFinal targetBodyFinal := by
                apply
                  AllocationObserverOutcome.ControlBinding.DestinationRuntimeInvariant.of_transport
                    (AllocationObserverOutcome.ControlDestinations.loopBody
                      hBodyInvariant.activation.compiler
                      initCursor.planWF hLoopStateExtends
                      hInitScope).cont
                    (AllocationObserverOutcome.SameControl.refl _)
                    (Locals.Ctx.SameControl.refl _)
                    (AllocationLowering.StateExtends.of_shape rfl rfl)
                    (fun _ hName => hName) (SameFrame.refl initMode)
                simpa [hBodyBoundary, forBody] using hDestination
              have hLoopInvariant :=
                AllocationObserverOutcome.ControlDestinations.loopBody_continue_destination
                  hBodyInvariant.activation.compiler
                  initCursor.planWF hLoopStateExtends
                  hInitScope hBaseDestination
              have hContinueInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx afterPost
                    (initCursor.finalLocals.withLoopControl
                      initCursor.finalLocals.layout.length)
                    initCursor.plan
                    (Functions.Scope.Block.outEnv live init)
                    frameBase initMode bodyFinal targetBodyFinal :=
                (hLoopInvariant.transport_state
                    hPostShape.1 hPostShape.2)
                  |>.transport_locals_layout
                    (after :=
                      initCursor.finalLocals.withLoopControl
                        initCursor.finalLocals.layout.length) rfl
              have hBodyActivationEffect :=
                Frame.OutcomeEffect.activation_of_not_halt hBodyEffect (by
                  intro kind hMode
                  cases hMode)
              rw [hCompiledBodyShape]
              exact
                ⟨targetBodyFinal, bodySourceFuel, bodyTargetFuel,
                  hBodySource, hBodyTarget, hContinueInvariant,
                  hBodyActivationEffect⟩)
            (by
              intro bodyFuel bodySource bodyOutcome bodyTarget
                hBodyExit hBodyInvariant hReturnFrame hFuel hRun
              have hCursorInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx afterPost
                    (initCursor.finalLocals.withLoopControl
                      initCursor.finalLocals.layout.length)
                    bodyCursor.plan
                    (Functions.Scope.Block.outEnv live init)
                    frameBase initMode bodySource bodyTarget :=
                (((hBodyInvariant.transport_state
                      hPostShape.1 hPostShape.2)
                    |>.transport_locals_layout
                      (after :=
                        initCursor.finalLocals.withLoopControl
                          initCursor.finalLocals.layout.length) rfl)
                    |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
              have hBodyBoundary :
                  Boundary bodyCursor (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := initMode)
                    (sourceCtx :=
                      initCtx.withLoopControl initCtx.scope initCtx.scope)
                    (source := bodySource) (target := bodyTarget) :=
                forBody cursor bodyCursor hBoundary initCursor.compile
                  hInitScope hOuterSubset hInitControl
                  hBodyInvariant.activation.compiler
                  initCursor.planWF hLoopStateExtends hReturnFrame
                  hCursorInvariant
              obtain
                  ⟨targetBodyOutcome, bodyFinalMode, hScoped⟩ :=
                recursiveScopedNonregular bodyCursor hRecursive
                  (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
                  hBodyBoundary hRun hBodyExit.not_regular hFinishBody
              rw [← hCompiledBodyShape] at hScoped
              refine
                ⟨targetBodyOutcome, bodyFinalMode,
                  AllocationObserverOutcome.ScopedBlockRuntimeForward.transport_of_isExit
                    hScoped hBodyExit ?_⟩
              intro hLeave
              simp [AllocationObserverOutcome.outcomeLive, hLeave])
            (by
              intro postFuel postSource postFinal postTarget
                hPostInvariant hReturnFrame hFuel hRun
              have hCursorInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx initCursor.finalState
                    initCursor.finalLocals.withoutLoopControl
                    postCursor.plan
                    (Functions.Scope.Block.outEnv live init)
                    frameBase initMode postSource postTarget :=
                (((hPostInvariant.transport_state
                      hPostShape.1.symm hPostShape.2.symm)
                    |>.transport_locals_layout
                      (after :=
                        initCursor.finalLocals.withoutLoopControl) rfl)
                    |>.transport_plan postCursor.planWF hPostPlanAgree)
              have hPostBoundary :
                  Boundary postCursor (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := initMode)
                    (sourceCtx := initCtx.withoutLoopControl)
                    (source := postSource) (target := postTarget) :=
                forPost cursor postCursor hBoundary initCursor.compile
                  hInitScope hOuterSubset hInitControl hReturnFrame
                  hCursorInvariant
              have hAfterCompiler :
                  AllocationObserverContext.ActivationExprContext
                    root.lowerCtx initCursor.finalState
                    initCursor.finalLocals initCursor.plan
                    (Functions.Scope.Block.outEnv live init) initMode :=
                (hPostInvariant.activation.compiler.transport_state
                    hPostShape.1.symm hPostShape.2.symm)
                  |>.transport_locals_layout
                    (after := initCursor.finalLocals) rfl
              rw [hCompiledPostShape]
              exact
                recursiveScopedRegular postCursor hRecursive
                  (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
                  hPostBoundary hRun hAfterCompiler initCursor.planWF
                  rfl hFinishPostAtLoop)
            (by
              intro postFuel postSource postOutcome postTarget
                hPostExit hPostInvariant hReturnFrame hFuel hRun
              have hCursorInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx initCursor.finalState
                    initCursor.finalLocals.withoutLoopControl
                    postCursor.plan
                    (Functions.Scope.Block.outEnv live init)
                    frameBase initMode postSource postTarget :=
                (((hPostInvariant.transport_state
                      hPostShape.1.symm hPostShape.2.symm)
                    |>.transport_locals_layout
                      (after :=
                        initCursor.finalLocals.withoutLoopControl) rfl)
                    |>.transport_plan postCursor.planWF hPostPlanAgree)
              have hPostBoundary :
                  Boundary postCursor (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := initMode)
                    (sourceCtx := initCtx.withoutLoopControl)
                    (source := postSource) (target := postTarget) :=
                forPost cursor postCursor hBoundary initCursor.compile
                  hInitScope hOuterSubset hInitControl hReturnFrame
                  hCursorInvariant
              obtain
                  ⟨targetPostOutcome, postFinalMode, hScoped⟩ :=
                recursiveScopedNonregular postCursor hRecursive
                  (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
                  hPostBoundary hRun hPostExit.not_regular hFinishPost
              rw [← hCompiledPostShape] at hScoped
              refine
                ⟨targetPostOutcome, postFinalMode,
                  AllocationObserverOutcome.ScopedBlockRuntimeForward.transport_of_isExit
                    hScoped hPostExit ?_⟩
              intro hLeave
              simp [AllocationObserverOutcome.outcomeLive, hLeave])
            hExit hLoopSource hInvariant)
      hExit hLower hCompile
  have hForwardOuter :
      AllocationObserverOutcome.NonregularStmtRuntimeForward
        program.memoryContract config allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive root.returns live sourceCtx
          sourceLoopOutcome.mode)
        frameBase mode initMode program sourceCtx
        (.for_ init cond post body) source expressions.toStructured target
        (Expressions.StmtList.toStructured headCode) sourceLoopOutcome
        targetOutcome sourceCtx :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.transport_of_isExit
      hForward hExit
        (by
          intro hLeave
          simp [AllocationObserverOutcome.outcomeLive, hLeave])
  exact
    ⟨afterState, headCode, tail,
      HeadResult.ofNonregular cursor tail hCompiled
        (.nonregular hForwardOuter) hExact hExit.not_regular⟩

/--
Dispatch an `if` head through the pass-owned conditional theorem. Recursive
work is limited to the exact lexical body cursor selected by the canonical
source run.
-/
theorem ifHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
          AllocationObserverForward.BodyCursor.CoreCursor root
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
              program.memoryContract config allocatorDepth root.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
Dispatch an `if` head while retaining exact `break` or `continue`
destinations produced by recursive preservation of its selected lexical body.
-/
theorem ifControlledHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
          AllocationObserverForward.BodyCursor.CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx)
        (hOpen :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                program.memoryContract transcript)
              program sourceCtx sourceFuel body sourceAfterCond =
            .ok (bodyOutcome, bodyCtx))
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript}
        (bodyBoundary :
          Boundary bodyCursor (config := config)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (mode := mode) (sourceCtx := sourceCtx)
            (source := sourceAfterCond) (target := targetBodyStart)),
        BlockResult bodyCursor bodyBoundary
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := bodyCtx)
          (source := sourceAfterCond) (target := targetBodyStart)
          (sourceOutcome := bodyOutcome)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ControlledHeadResult cursor hBoundary afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  rcases
      Functions.Source.Effectful.Stmt.run_if_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hFalse | hTrue
  · rcases hFalse with
      ⟨sourceAfterCond, hCond, hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    have hZero : value = EvmYul.UInt256.ofNat 0 := by
      by_contra hNe
      have hNonzero :
          (value != EvmYul.UInt256.ofNat 0) = true :=
        TypedCfg.Preservation.uint256_bne_zero_of_ne value hNe
      rw [hNonzero] at hValue
      contradiction
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hRuntime, hStep, hExact⟩ :=
      cursor.ifFalseRuntimeResult
        (sourceCtx := sourceCtx) hConfig hSafe hZero hBoundary.invariant
    have hHead :
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular sourceAfterCond) :=
      HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)
    exact
      ⟨afterState, headCode, tail,
        ControlledHeadResult.of_no_control cursor hBoundary tail hHead
          (by
            intro sourceFinal hEq
            cases hEq)
          (by
            intro sourceFinal hEq
            cases hEq)⟩
  · rcases hTrue with
      ⟨sourceAfterCond, bodyOutcome, hCond, hScoped,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hBoundary.sourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hRuntime, hStep, hExact⟩ :=
        cursor.ifTrueRegularRuntimeResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hConfig hSafe hValue hBoundary.sourceScope hBoundary.invariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant hReturns
            have hPlanAgree :
                AllocationObserverRelation.PlanAgreesOn
                  bodyCursor.plan cursor.plan live :=
              bodyCursor.planAgreesOn cursor rfl
            let bodyBoundary :
                Boundary bodyCursor (config := config)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx) (source := sourceAfterCond)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor
                (AllocationLowering.StateExtends.of_shape rfl rfl)
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            have bodyResult :=
              hBody bodyCursor hBodyRun bodyBoundary
            obtain ⟨bodyTargetOutcome, hBodyRuntime, _hBodyControl⟩ :=
              bodyResult.runtime
            cases hBodyRuntime with
            | @regular _ _ finalMode _ hBodyForward _hControl =>
                exact ⟨_, .regular hBodyForward _hControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      have hHead :
          HeadResult cursor afterState localsCtx headCode tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.regular
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  live sourceBodyFinal)) :=
        HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
          (by
            intro _ name
            simpa [Functions.Scope.Stmt.outEnv] using
              hBoundary.sourceScope name)
      exact
        ⟨afterState, headCode, tail,
          ControlledHeadResult.of_no_control cursor hBoundary tail hHead
            (by
              intro sourceFinal hEq
              cases hEq)
            (by
              intro sourceFinal hEq
              cases hEq)⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hRuntime, hStep, hExact, hControlOutcome⟩ :=
        cursor.ifTrueNonregularRuntimeResult
          (P := fun targetOutcome =>
            ControlOutcomeForward cursor hBoundary openOutcome targetOutcome)
          hConfig hSafe hValue hMode hBoundary.control hBoundary.invariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant hReturns
            have hPlanAgree :
                AllocationObserverRelation.PlanAgreesOn
                  bodyCursor.plan cursor.plan live :=
              bodyCursor.planAgreesOn cursor rfl
            let bodyBoundary :
                Boundary bodyCursor (config := config)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx) (source := sourceAfterCond)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor
                (AllocationLowering.StateExtends.of_shape rfl rfl)
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            have bodyResult :=
              hBody bodyCursor hBodyRun bodyBoundary
            obtain ⟨bodyTargetOutcome, hBodyRuntime, hBodyControl⟩ :=
              bodyResult.runtime
            exact
              ⟨bodyTargetOutcome, bodyCtx, hBodyRuntime,
                ControlOutcomeForward.of_rebase cursor bodyCursor hBoundary
                  (AllocationLowering.StateExtends.of_shape rfl rfl)
                  (Locals.Ctx.SameControl.refl localsCtx)
                  (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                    hBoundary.returnFrame hReturns)
                  hBodyInvariant hBodyControl⟩)
      have hHead :
          HeadResult cursor afterState localsCtx headCode tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome := openOutcome) :=
        HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
          (by
            intro _ name
            simpa [Functions.Scope.Stmt.outEnv] using
              hBoundary.sourceScope name)
      exact
        ⟨afterState, headCode, tail,
          { head := hHead
            runtime := ⟨targetOutcome, hRuntime, hControlOutcome⟩ }⟩

/--
Dispatch a `switch` head through the pass-owned selected-body theorem.
-/
theorem switchHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
          AllocationObserverForward.BodyCursor.CoreCursor root
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
              program.memoryContract config allocatorDepth root.lowerCtx
              selectedStart localsCtx bodyCursor.plan live frameBase mode
              sourceAfterScrutinee targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live selected)
              frameBase mode program sourceCtx selected
              sourceAfterScrutinee expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
Dispatch a `switch` head while retaining exact `break` or `continue`
destinations produced by recursive preservation of its selected lexical body.
-/
theorem switchControlledHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
          AllocationObserverForward.BodyCursor.CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx)
        (hState :
          AllocationLowering.StateExtends
            live lowerState selectedStart)
        (hOpen :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                program.memoryContract transcript)
              program sourceCtx sourceFuel selected sourceAfterScrutinee =
            .ok (bodyOutcome, bodyCtx))
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript}
        (bodyBoundary :
          Boundary bodyCursor (config := config)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (mode := mode) (sourceCtx := sourceCtx)
            (source := sourceAfterScrutinee) (target := targetBodyStart)),
        BlockResult bodyCursor bodyBoundary
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := bodyCtx)
          (source := sourceAfterScrutinee) (target := targetBodyStart)
          (sourceOutcome := bodyOutcome)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ControlledHeadResult cursor hBoundary afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  rcases
      Functions.Source.Effectful.Stmt.run_switch_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hNone | hSome
  · rcases hNone with
      ⟨sourceAfterScrutinee, value, hScrutinee, hSelect,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hRuntime, hStep, hExact⟩ :=
      cursor.switchNoneRuntimeResult
        (sourceCtx := sourceCtx) hConfig
        (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
          hScrutinee)
        hSelect hBoundary.invariant
    have hHead :
        HeadResult cursor afterState localsCtx headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular
              sourceAfterScrutinee) :=
      HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)
    exact
      ⟨afterState, headCode, tail,
        ControlledHeadResult.of_no_control cursor hBoundary tail hHead
          (by
            intro sourceFinal hEq
            cases hEq)
          (by
            intro sourceFinal hEq
            cases hEq)⟩
  · rcases hSome with
      ⟨sourceAfterScrutinee, value, selected, bodyOutcome,
        hScrutinee, hSelect, hScoped, hOutcome, _hCtx⟩
    subst sourceOutcome
    have hSafe :
        AllocationObserverSafety.Expr.MemorySafeEval
          program.memoryContract transcript scrutinee source
          sourceAfterScrutinee [value] :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
        hScrutinee
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hBoundary.sourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hRuntime, hStep, hExact⟩ :=
        cursor.switchSomeRegularRuntimeResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hConfig hSafe hSelect hBoundary.sourceScope hBoundary.invariant
          (by
            intro selectedStart selectedPlanning bodyCursor
              targetBodyStart hSelectedExtends hBodyInvariant hReturns
            let bodyBoundary :
                Boundary bodyCursor (config := config)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx)
                  (source := sourceAfterScrutinee)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor hSelectedExtends
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            have bodyResult :=
              hBody bodyCursor hSelectedExtends hBodyRun bodyBoundary
            obtain ⟨bodyTargetOutcome, hBodyRuntime, _hBodyControl⟩ :=
              bodyResult.runtime
            cases hBodyRuntime with
            | @regular _ _ finalMode _ hBodyForward hBodyControl =>
                exact ⟨_, .regular hBodyForward hBodyControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      have hHead :
          HeadResult cursor afterState localsCtx headCode tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.regular
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  live sourceBodyFinal)) :=
        HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
          (by
            intro _ name
            simpa [Functions.Scope.Stmt.outEnv] using
              hBoundary.sourceScope name)
      exact
        ⟨afterState, headCode, tail,
          ControlledHeadResult.of_no_control cursor hBoundary tail hHead
            (by
              intro sourceFinal hEq
              cases hEq)
            (by
              intro sourceFinal hEq
              cases hEq)⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hRuntime, hStep, hExact, hControlOutcome⟩ :=
        cursor.switchSomeNonregularRuntimeResult
          (P := fun targetOutcome =>
            ControlOutcomeForward cursor hBoundary openOutcome targetOutcome)
          hConfig hSafe hSelect hMode hBoundary.control hBoundary.invariant
          (by
            intro selectedStart selectedPlanning bodyCursor targetBodyStart
              hSelectedExtends hBodyInvariant hReturns
            let bodyBoundary :
                Boundary bodyCursor (config := config)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx)
                  (source := sourceAfterScrutinee)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor hSelectedExtends
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            have bodyResult :=
              hBody bodyCursor hSelectedExtends hBodyRun bodyBoundary
            obtain ⟨bodyTargetOutcome, hBodyRuntime, hBodyControl⟩ :=
              bodyResult.runtime
            exact
              ⟨bodyTargetOutcome, bodyCtx, hBodyRuntime,
                ControlOutcomeForward.of_rebase cursor bodyCursor hBoundary
                  hSelectedExtends
                  (Locals.Ctx.SameControl.refl localsCtx)
                  (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                    hBoundary.returnFrame hReturns)
                  hBodyInvariant hBodyControl⟩)
      have hHead :
          HeadResult cursor afterState localsCtx headCode tail
            (config := config) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome := openOutcome) :=
        HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
          (by
            intro _ name
            simpa [Functions.Scope.Stmt.outEnv] using
              hBoundary.sourceScope name)
      exact
        ⟨afterState, headCode, tail,
          { head := hHead
            runtime := ⟨targetOutcome, hRuntime, hControlOutcome⟩ }⟩

/--
Dispatch a lexical block by inverting its canonical scoped source run to the
exact open-block execution consumed by recursive preservation.
-/
theorem blockHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
          AllocationObserverForward.BodyCursor.CoreCursor root
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
            root.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan root.returns
            (Functions.Scope.Block.outEnv live body)
            frameBase mode program sourceCtx body source
            expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured bodyCursor.compiled }
            target bodyOutcome targetOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
              hRegularOutcome, _hAbruptOutcome, _hDecoration⟩ :=
          cursor.blockRuntimeResult (P := fun _ => True)
            hBoundary.sourceScope hBoundary.control hBoundary.invariant
            (fun bodyCursor => by
              obtain ⟨targetOutcome, hRuntime⟩ := hBody bodyCursor hOpen
              exact ⟨targetOutcome, hRuntime, trivial⟩)
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
              _hRegularOutcome, hAbruptOutcome, _hDecoration⟩ :=
          cursor.blockRuntimeResult (P := fun _ => True)
            hBoundary.sourceScope hBoundary.control hBoundary.invariant
            (fun bodyCursor => by
              obtain ⟨targetOutcome, hRuntime⟩ := hBody bodyCursor hOpen
              exact ⟨targetOutcome, hRuntime, trivial⟩)
        rw [hAbruptOutcome hMode] at hRuntime
        exact
          ⟨afterState, headCode, tail,
            HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
              (by
                intro _ name
                simpa [Functions.Scope.Stmt.outEnv] using
                  hBoundary.sourceScope name)⟩

/--
Dispatch a lexical block while retaining the exact `break` or `continue`
destination produced by recursive preservation of its open body.
-/
theorem blockControlledHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
          AllocationObserverForward.BodyCursor.CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx)
        (hOpen :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                program.memoryContract transcript)
              program sourceCtx sourceFuel body source =
            .ok (bodyOutcome, bodyCtx))
        (bodyBoundary :
          Boundary bodyCursor (config := config)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (mode := mode) (sourceCtx := sourceCtx)
            (source := source) (target := target)),
        BlockResult bodyCursor bodyBoundary
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := bodyCtx)
          (source := source) (target := target)
          (sourceOutcome := bodyOutcome)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ControlledHeadResult cursor hBoundary afterState localsCtx headCode tail
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
              hRegularOutcome, _hAbruptOutcome, _hDecoration⟩ :=
          cursor.blockRuntimeResult (P := fun _ => True)
            hBoundary.sourceScope hBoundary.control hBoundary.invariant
            (by
              intro bodyCursor
              have hPlanAgree :
                  AllocationObserverRelation.PlanAgreesOn
                    bodyCursor.plan cursor.plan live :=
                bodyCursor.planAgreesOn cursor rfl
              have hBodyInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx lowerState localsCtx bodyCursor.plan live
                    frameBase mode source target :=
                hBoundary.invariant.transport_plan
                  bodyCursor.planWF hPlanAgree.symm
              let bodyBoundary :
                  Boundary bodyCursor (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := mode)
                    (sourceCtx := sourceCtx) (source := source)
                    (target := target) :=
                hBoundary.rebase cursor bodyCursor
                  (AllocationLowering.StateExtends.of_shape rfl rfl)
                  (Locals.Ctx.SameControl.refl localsCtx)
                  hBoundary.returnFrame hBodyInvariant
              obtain ⟨targetOutcome, hRuntime, _hControl⟩ :=
                (hBody bodyCursor hOpen bodyBoundary).runtime
              exact ⟨targetOutcome, hRuntime, trivial⟩)
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
        have hHead :
            HeadResult cursor afterState localsCtx headCode tail
              (config := config) (allocatorDepth := allocatorDepth)
              (frameBase := frameBase) (mode := mode)
              (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
              (source := source) (target := target)
              (sourceOutcome :=
                Functions.Source.Effectful.Outcome.regular
                  ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                    live bodyFinal)) :=
          HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
            (by
              intro _ name
              simpa [Functions.Scope.Stmt.outEnv] using
                hBoundary.sourceScope name)
        exact
          ⟨afterState, headCode, tail,
            ControlledHeadResult.of_no_control cursor hBoundary tail hHead
              (by
                intro sourceFinal hOutcome
                cases hOutcome)
              (by
                intro sourceFinal hOutcome
                cases hOutcome)⟩
      · rcases hNonregular with
          ⟨openOutcome, bodyCtx, hOpen, hMode, hScopedOutcome⟩
        subst sourceOutcome
        obtain
            ⟨afterState, headCode, tail, producedSourceOutcome,
              targetOutcome, hCompiled, hRuntime, hStep, hExact,
              _hRegularOutcome, hAbruptOutcome, hControlOutcome⟩ :=
          cursor.blockRuntimeResult
            (P := fun targetOutcome =>
              ControlOutcomeForward cursor hBoundary openOutcome targetOutcome)
            hBoundary.sourceScope hBoundary.control hBoundary.invariant
            (by
              intro bodyCursor
              have hPlanAgree :
                  AllocationObserverRelation.PlanAgreesOn
                    bodyCursor.plan cursor.plan live :=
                bodyCursor.planAgreesOn cursor rfl
              have hBodyInvariant :
                  AllocationObserverContext.ActivationRuntimeInvariant
                    program.memoryContract config allocatorDepth
                    root.lowerCtx lowerState localsCtx bodyCursor.plan live
                    frameBase mode source target :=
                hBoundary.invariant.transport_plan
                  bodyCursor.planWF hPlanAgree.symm
              let bodyBoundary :
                  Boundary bodyCursor (config := config)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := mode)
                    (sourceCtx := sourceCtx) (source := source)
                    (target := target) :=
                hBoundary.rebase cursor bodyCursor
                  (AllocationLowering.StateExtends.of_shape rfl rfl)
                  (Locals.Ctx.SameControl.refl localsCtx)
                  hBoundary.returnFrame hBodyInvariant
              have bodyResult := hBody bodyCursor hOpen bodyBoundary
              obtain ⟨bodyTargetOutcome, hBodyRuntime, hBodyControl⟩ :=
                bodyResult.runtime
              exact
                ⟨bodyTargetOutcome, hBodyRuntime,
                  ControlOutcomeForward.of_rebase cursor bodyCursor hBoundary
                    (AllocationLowering.StateExtends.of_shape rfl rfl)
                    (Locals.Ctx.SameControl.refl localsCtx)
                    hBoundary.returnFrame hBodyInvariant hBodyControl⟩)
        rw [hAbruptOutcome hMode] at hRuntime hControlOutcome
        have hHead :
            HeadResult cursor afterState localsCtx headCode tail
              (config := config) (allocatorDepth := allocatorDepth)
              (frameBase := frameBase) (mode := mode)
              (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
              (source := source) (target := target)
              (sourceOutcome := openOutcome) :=
          HeadResult.ofRuntime cursor tail hCompiled hRuntime hStep hExact
            (by
              intro _ name
              simpa [Functions.Scope.Stmt.outEnv] using
                hBoundary.sourceScope name)
        exact
          ⟨afterState, headCode, tail,
            { head := hHead
              runtime :=
                ⟨targetOutcome, hRuntime, hControlOutcome hMode⟩ }⟩

/--
Dispatch `break` using the loop destination already carried by the boundary.
-/
theorem brkControlledHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .leave :: rest } beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest } beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
Dispatch a regular internal function call through the compiler-selected callee.

The body callback is the strictly fuel-smaller recursive use that the mutual
Functions theorem will discharge. It is consumed immediately by the call pass
and is not retained in the returned head result.
-/
theorem callRegularHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {targets : List Functions.Name}
    {name : Functions.Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .call targets name args :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 2)
          (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hBody :
      ∀ {selectedFn : Functions.FunDef}
        {selected :
          AllocationObserverCall.SelectedCallee.Artifact
            allocation program expressions name selectedFn}
        (selectedPrepared :
          AllocationObserverCall.SelectedCallee.Prepared selected)
        {sourceBodyStart :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx' : Functions.Source.Ctx}
        {targetBodyStart : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program (Functions.Source.Effectful.FunDef.bodyCtx selectedFn)
            sourceFuel selectedFn.body sourceBodyStart =
          .ok (bodyOutcome, bodyCtx') →
        calleeDepth ≤ allocatorDepth + 1 →
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth selected.lowerCtx
            selected.bodyStart selectedPrepared.returnCtx selectedPrepared.plan
            ((selected.slots.returns.map Prod.fst).reverse ++
              (selected.slots.params.map Prod.fst).reverse)
            calleeFrameBase
            (selectedPrepared.mode.atStackDepth
              (currentStackOrder selectedPrepared.plan
                ((selected.slots.returns.map Prod.fst).reverse ++
                  (selected.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config calleeDepth transcript
            selected.lowerCtx selectedPrepared.bodyFinal
            selectedPrepared.bodyCtx selectedPrepared.plan
            selectedFn.returns
            (Functions.Scope.Block.outEnv
              ((selected.slots.returns.map Prod.fst).reverse ++
                (selected.slots.params.map Prod.fst).reverse)
              selectedFn.body)
            calleeFrameBase
            (selectedPrepared.mode.atStackDepth
              (currentStackOrder selectedPrepared.plan
                ((selected.slots.returns.map Prod.fst).reverse ++
                  (selected.slots.params.map Prod.fst).reverse)).length)
            program (Functions.Source.Effectful.FunDef.bodyCtx selectedFn)
            selectedFn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured selectedPrepared.bodyCode }
            targetBodyStart bodyOutcome targetOutcome bodyCtx') :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular sourceFinal) := by
  obtain
      ⟨afterState, afterLocals, lowered, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals,
        hLower, hCompile, _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverForward.Call.regular_of_safe_source
      compilation hConfig
      root.lowerCtxShared
      hSource hScoped hBoundary.invariant hBoundary.budget
      hLower hCompile hBody
  have hStep :
      AllocationObserverForward.BodyCursor.StepTransport
        lowerState afterState localsCtx afterLocals live
        (.call targets name args) :=
    AllocationObserverForward.BodyCursor.StepTransport.of_compilers
      hScoped hLower hCompile
  have hHead :
      HeadResult cursor afterState afterLocals headCode tail
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
        (source := source) (target := target)
        (sourceOutcome :=
          Functions.Source.Effectful.Outcome.regular sourceFinal) :=
    HeadResult.regular cursor tail rfl hCompiled hPlan hFinalState
      hFinalLocals hForward
      (AllocationObserverOutcome.SameControl.refl sourceCtx)
      hStep
      (by
        intro localName
        simpa [Functions.Scope.Stmt.outEnv] using
          hBoundary.sourceScope localName)
  exact
    ⟨afterState, afterLocals, headCode, tail,
      ControlledHeadResult.of_no_control cursor hBoundary tail hHead
        (by
          intro sourceFinal hEq
          have hMode :=
            congrArg Locals.Source.Effectful.Outcome.mode hEq
          change
            (Locals.Source.Mode.regular : Locals.Source.Mode) =
              Locals.Source.Mode.brk at hMode
          contradiction)
        (by
          intro sourceFinal hEq
          have hMode :=
            congrArg Locals.Source.Effectful.Outcome.mode hEq
          change
            (Locals.Source.Mode.regular : Locals.Source.Mode) =
              Locals.Source.Mode.cont at hMode
          contradiction)⟩

/--
Dispatch a terminal internal function call through the compiler-selected
callee. The recursive callback is consumed by the call-owned theorem, and the
generated caller tail is proved unreachable.
-/
theorem callHaltHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {targets : List Functions.Name}
    {name : Functions.Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .call targets name args :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 2)
          (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            sourceCtx))
    (hBoundary :
      Boundary cursor (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hBody :
      ∀ {selectedFn : Functions.FunDef}
        {selected :
          AllocationObserverCall.SelectedCallee.Artifact
            allocation program expressions name selectedFn}
        (selectedPrepared :
          AllocationObserverCall.SelectedCallee.Prepared selected)
        {sourceBodyStart :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx' : Functions.Source.Ctx}
        {targetBodyStart : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program (Functions.Source.Effectful.FunDef.bodyCtx selectedFn)
            sourceFuel selectedFn.body sourceBodyStart =
          .ok (bodyOutcome, bodyCtx') →
        calleeDepth ≤ allocatorDepth + 1 →
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth selected.lowerCtx
            selected.bodyStart selectedPrepared.returnCtx selectedPrepared.plan
            ((selected.slots.returns.map Prod.fst).reverse ++
              (selected.slots.params.map Prod.fst).reverse)
            calleeFrameBase
            (selectedPrepared.mode.atStackDepth
              (currentStackOrder selectedPrepared.plan
                ((selected.slots.returns.map Prod.fst).reverse ++
                  (selected.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config calleeDepth transcript
            selected.lowerCtx selectedPrepared.bodyFinal
            selectedPrepared.bodyCtx selectedPrepared.plan
            selectedFn.returns
            (Functions.Scope.Block.outEnv
              ((selected.slots.returns.map Prod.fst).reverse ++
                (selected.slots.params.map Prod.fst).reverse)
              selectedFn.body)
            calleeFrameBase
            (selectedPrepared.mode.atStackDepth
              (currentStackOrder selectedPrepared.plan
                ((selected.slots.returns.map Prod.fst).reverse ++
                  (selected.slots.params.map Prod.fst).reverse)).length)
            program (Functions.Source.Effectful.FunDef.bodyCtx selectedFn)
            selectedFn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured selectedPrepared.bodyCode }
            targetBodyStart bodyOutcome targetOutcome bodyCtx') :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.halt kind sourceFinal) := by
  obtain
      ⟨afterState, afterLocals, lowered, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals,
        hLower, hCompile, _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverForward.Call.halt_of_safe_source
      compilation hConfig
      root.lowerCtxShared
      hSource hScoped hBoundary.invariant hBoundary.budget
      hLower hCompile
      (fun {fn} {artifact} prepared
          {sourceBodyStart} {bodyCtx'} {targetBodyStart}
          {calleeDepth} {calleeFrameBase}
          hRun hInvariant hReturnFrame =>
        hBody (selectedFn := fn) (selected := artifact) prepared
          hRun hInvariant hReturnFrame)
  have hRuntime :
      AllocationObserverOutcome.StmtRuntimeResult
        program.memoryContract config allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan root.returns
        live frameBase mode program sourceCtx
        (.call targets name args) source expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx :=
    .nonregular hForward
  have hExact :
      AllocationObserverForward.BodyCursor.ExactTail cursor tail :=
    ⟨hPlan, hFinalState, hFinalLocals⟩
  have hHead :
      HeadResult cursor afterState afterLocals headCode tail
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
        (source := source) (target := target)
        (sourceOutcome :=
          Functions.Source.Effectful.Outcome.halt kind sourceFinal) :=
    HeadResult.ofNonregular cursor tail hCompiled hRuntime hExact (by
      intro hMode
      change Locals.Source.Mode.halt kind = .regular at hMode
      contradiction)
  exact
    ⟨afterState, afterLocals, headCode, tail,
      ControlledHeadResult.of_no_control cursor hBoundary tail hHead
        (by
          intro sourceFinal' hEq
          have hMode :=
            congrArg Locals.Source.Effectful.Outcome.mode hEq
          change
            Locals.Source.Mode.halt kind = Locals.Source.Mode.brk at hMode
          contradiction)
        (by
          intro sourceFinal' hEq
          have hMode :=
            congrArg Locals.Source.Effectful.Outcome.mode hEq
          change
            Locals.Source.Mode.halt kind = Locals.Source.Mode.cont at hMode
          contradiction)⟩

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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope beforeLive
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope afterLive
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
        program.memoryContract config allocatorDepth root.lowerCtx
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope beforeLive
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope afterLive
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
        program.memoryContract config allocatorDepth root.lowerCtx
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        root.returns live frameBase mode program sourceCtx
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target))
    {afterState : AllocationLowering.State}
    {afterLocals : Locals.Ctx}
    {headCode : List Expressions.Stmt}
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
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
            root.lowerCtx afterState afterLocals cursor.plan
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
            root.lowerCtx tail.finalState tail.finalLocals
            tail.plan root.returns
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
        root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
        root.returns
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
            program.memoryContract config allocatorDepth root.lowerCtx
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (hBoundary :
      Boundary cursor (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target))
    {afterState : AllocationLowering.State}
    {afterLocals : Locals.Ctx}
    {headCode : List Expressions.Stmt}
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
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
            root.lowerCtx afterState afterLocals cursor.plan
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
            program.memoryContract config allocatorDepth root.lowerCtx
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

namespace ResourceBoundary

/--
Dispatch the stack-only `for` branch whose initializer exits before condition
evaluation.
-/
theorem forInitExitHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ResourceHeadResult cursor afterState localsCtx headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
      ResourceBoundary initCursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
        (source := source) (target := target) :=
    ResourceBoundary.forInit cursor initCursor hBoundary
  have hInitResult :=
    hRecursive initCursor (Nat.lt_succ_self sourceFuel)
      hInitBoundary hInitSource
  obtain ⟨initTargetOutcome, hInitResource, _hInitControl⟩ :=
    hInitResult.runtime
  have hMode : sourceOutcome.mode ≠ .regular :=
    hExit.not_regular
  cases hInitResource with
  | regular _hInitForward _hControl =>
      exact False.elim (hMode rfl)
  | @nonregular _ _ finalMode _ _ hInitForward =>
      have hInitForwardCopy := hInitForward
      rcases hInitForward with
        ⟨_sourceFuel, _targetFuel, _hSourceRun, _hTargetRun,
          _hOutcomeRel, hSame, _hEffect⟩
      have hFinalStack : finalMode = .stack :=
        hSame.right_eq_stack_of_left_eq_stack hBoundary.invariant.owned
      have hInitForwardOuter :=
        AllocationObserverOutcome.BlockResourceForward.transport_of_isExit
          (afterPlan := cursor.plan)
          (afterLive :=
            AllocationObserverOutcome.outcomeLive
              root.returns live sourceCtx sourceOutcome.mode)
          hInitForwardCopy hExit
          (by
            intro hLeave
            simp [AllocationObserverOutcome.outcomeLive, hLeave])
      obtain ⟨targetOutcome, hForward⟩ :=
        AllocationObserverStatement.Sequence.NonregularStmtForward.for_init_exit_of_components
          (outerPlan := cursor.plan) (exitPlan := cursor.plan)
          (outerLive := live)
          (resultLive :=
            AllocationObserverOutcome.outcomeLive root.returns live
              sourceCtx sourceOutcome.mode)
          (exitMode := finalMode)
          hBoundary.invariant.activation
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
            exact
              ⟨initCtx, initTargetOutcome,
                AllocationObserverStatement.Sequence.BlockForward.ofResource
                  hInitForwardOuter⟩)
          hExit hLower hCompile
      have hResource :=
        hForward.toStackResource
          (allocatorDepth := allocatorDepth)
          hBoundary.invariant.owned hFinalStack
      exact
        ⟨afterState, headCode, tail,
          ResourceHeadResult.ofNonregular cursor tail hCompiled
            (.nonregular hResource) hExact hMode⟩

/--
Dispatch a stack-only `for` whose initializer and complete loop both finish
regularly.

The loop-owned guarded source-fuel theorem handles iteration. Recursive work
is confined to the exact initializer, body, and post cursors, while
break/continue destinations remain owned by the shared resource boundary.
-/
theorem forRegularHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx initCtx : Functions.Source.Ctx}
    {source sourceAfterInit sourceLoopFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := .stackOnly) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := sourceFuel + 1)
        (transcript := transcript))
    (hInitSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx.withoutLoopControl sourceFuel init source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceAfterInit,
            initCtx))
    (hLoopSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program initCtx cond initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceLoopFinal)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ResourceHeadResult cursor afterState localsCtx headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                sourceCtx.scope sourceLoopFinal)) := by
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
  cases hInitFinalState
  cases hInitFinalLocals
  let initFinished := initCursor.finished
  have hInitBoundary :
      ResourceBoundary initCursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
        (source := source) (target := target) :=
    ResourceBoundary.forInit cursor initCursor hBoundary
  obtain
      ⟨targetAfterInit, initMode, hInitForward,
        hInitControl, hInitScope⟩ :=
    ResourceRecursiveBlockForward.regular initCursor hRecursive
      (Nat.lt_succ_self sourceFuel) hInitBoundary hInitSource
  have hInitModeStack : initMode = .stack := by
    rcases hInitForward with
      ⟨_sourceFuel, _targetFuel, _hSource, _hTarget,
        _hInvariant, hSame, _hEffect⟩
    exact
      hSame.right_eq_stack_of_left_eq_stack hBoundary.invariant.owned
  have hOuterSubset :
      ∀ name, name ∈ live →
        name ∈ Functions.Scope.Block.outEnv live init :=
    fun name hName => Functions.Scope.Block.mem_outEnv hName
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.for_regular_of_safe_source_run
      initCursor.sourceScoped hCondScoped hBoundary.sourceScope
      hInitScope hOuterSubset hBoundary.invariant.activation
      hBoundary.returnFrame
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
        exact
          ⟨targetAfterInit, hInitForward.toInvariant, hInitControl⟩)
      (by
        intro loopState' afterPost' afterBody' loweredInit'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            ResourceBoundary bodyCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          ResourceBoundary.forBody cursor bodyCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hInvariant.compiler initCursor.planWF hLoopStateExtends
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant hInitModeStack)
        have hAfterCompiler :
            AllocationObserverContext.ActivationExprContext
              root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              initCursor.plan (Functions.Scope.Block.outEnv live init)
              initMode :=
          (hInvariant.compiler.transport_state
              hPostShape.1 hPostShape.2)
            |>.transport_locals_layout
              (after :=
                initCursor.finalLocals.withLoopControl
                  initCursor.finalLocals.layout.length) rfl
        rw [hCompiledBodyShape]
        exact
          ResourceRecursiveBlockForward.scopedRegularInvariant
            bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun hAfterCompiler initCursor.planWF rfl
            hFinishBody)
      (by
        intro loopState' afterPost' afterBody' loweredInit'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            ResourceBoundary bodyCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          ResourceBoundary.forBody cursor bodyCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hInvariant.compiler initCursor.planWF hLoopStateExtends
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant hInitModeStack)
        obtain
            ⟨targetOutcome, finalMode, hScoped, hControl⟩ :=
          ResourceRecursiveBlockForward.scopedNonregularControlled
            bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun
            (by
              simp [Functions.Source.Effectful.Outcome.brk,
                Locals.Source.Effectful.Outcome.brk])
            hFinishBody
        obtain ⟨targetBodyFinal, hTargetOutcome, hDestination⟩ :=
          hControl.brk bodyFinal rfl
        subst targetOutcome
        rcases hScoped with
          ⟨bodySourceFuel, bodyTargetFuel, hBodySource,
            hBodyTarget, _hOutcomeRel⟩
        have hBaseDestination :
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant
              (contract := program.memoryContract)
              (resource := .stackOnly)
              (allocatorDepth := allocatorDepth)
              (frameBase := frameBase)
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.compiler initCursor.planWF
                hLoopStateExtends hInitScope).brk
              bodyFinal targetBodyFinal := by
          apply
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_transport
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.compiler initCursor.planWF
                hLoopStateExtends hInitScope).brk
              (AllocationObserverOutcome.SameControl.refl _)
              (Locals.Ctx.SameControl.refl _)
              (AllocationLowering.StateExtends.of_shape rfl rfl)
              (fun _ hName => hName) (SameFrame.refl initMode)
          simpa [hBodyBoundary, ResourceBoundary.forBody] using
            hDestination
        have hLoopInvariant :=
          AllocationObserverOutcome.ControlDestinations.loopBody_break_resource_destination
            hInvariant.compiler initCursor.planWF hLoopStateExtends
              hInitScope hBaseDestination
        rw [hCompiledBodyShape]
        exact
          ⟨targetBodyFinal, bodySourceFuel, bodyTargetFuel,
            hBodySource, hBodyTarget, hLoopInvariant.activation⟩)
      (by
        intro loopState' afterPost' afterBody' loweredInit'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            ResourceBoundary bodyCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          ResourceBoundary.forBody cursor bodyCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hInvariant.compiler initCursor.planWF hLoopStateExtends
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant hInitModeStack)
        obtain
            ⟨targetOutcome, finalMode, hScoped, hControl⟩ :=
          ResourceRecursiveBlockForward.scopedNonregularControlled
            bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun
            (by
              simp [Functions.Source.Effectful.Outcome.cont,
                Locals.Source.Effectful.Outcome.cont])
            hFinishBody
        obtain ⟨targetBodyFinal, hTargetOutcome, hDestination⟩ :=
          hControl.cont bodyFinal rfl
        subst targetOutcome
        rcases hScoped with
          ⟨bodySourceFuel, bodyTargetFuel, hBodySource,
            hBodyTarget, _hOutcomeRel⟩
        have hBaseDestination :
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant
              (contract := program.memoryContract)
              (resource := .stackOnly)
              (allocatorDepth := allocatorDepth)
              (frameBase := frameBase)
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.compiler initCursor.planWF
                hLoopStateExtends hInitScope).cont
              bodyFinal targetBodyFinal := by
          apply
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_transport
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.compiler initCursor.planWF
                hLoopStateExtends hInitScope).cont
              (AllocationObserverOutcome.SameControl.refl _)
              (Locals.Ctx.SameControl.refl _)
              (AllocationLowering.StateExtends.of_shape rfl rfl)
              (fun _ hName => hName) (SameFrame.refl initMode)
          simpa [hBodyBoundary, ResourceBoundary.forBody] using
            hDestination
        have hLoopInvariant :=
          AllocationObserverOutcome.ControlDestinations.loopBody_continue_resource_destination
            hInvariant.compiler initCursor.planWF hLoopStateExtends
              hInitScope hBaseDestination
        have hContinueInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              initCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodyFinal targetBodyFinal :=
          (hLoopInvariant.activation.transport_state
              hPostShape.1 hPostShape.2)
            |>.transport_locals_layout
              (after :=
                initCursor.finalLocals.withLoopControl
                  initCursor.finalLocals.layout.length) rfl
        rw [hCompiledBodyShape]
        exact
          ⟨targetBodyFinal, bodySourceFuel, bodyTargetFuel,
            hBodySource, hBodyTarget, hContinueInvariant⟩)
      (by
        intro loopState' afterPost' loweredInit' loweredPost initLocals'
          postLocals' initCode' postCode compiledPost' postFuel postSource
          postFinal postTarget hLowerInit' hCompileInit' hLowerPost'
          hCompilePost' hFinishPost' hInvariant
          hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hCompilePostPair :
            (postCursor.compiled, postCursor.finalLocals) =
              (postCode, postLocals') :=
          Option.some.inj (postCursor.compile.symm.trans hCompilePost')
        cases hCompilePostPair
        have hCompiledPost : compiledPost = compiledPost' :=
          Option.some.inj (hFinishPost.symm.trans hFinishPost')
        cases hCompiledPost
        have hCompiledPostShape :
            compiledPost.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledPost.stmts } := by
          cases compiledPost
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hPostPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan postCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (postCursor.planAgreesOn initFinished rfl).symm
        have hPostInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx initCursor.finalState
              initCursor.finalLocals.withoutLoopControl postCursor.plan
              (Functions.Scope.Block.outEnv live init)
              frameBase initMode postSource postTarget :=
          (((hInvariant.transport_state hPostShape.1.symm
                hPostShape.2.symm)
              |>.transport_locals_layout
                (after := initCursor.finalLocals.withoutLoopControl) rfl)
              |>.transport_plan postCursor.planWF hPostPlanAgree)
        have hPostBoundary :
            ResourceBoundary postCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode) (sourceCtx := initCtx.withoutLoopControl)
              (source := postSource) (target := postTarget) :=
          ResourceBoundary.forPost cursor postCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hPostInvariant hInitModeStack)
        have hAfterCompiler :
            AllocationObserverContext.ActivationExprContext
              root.lowerCtx initCursor.finalState
              initCursor.finalLocals initCursor.plan
              (Functions.Scope.Block.outEnv live init) initMode :=
          (hInvariant.compiler.transport_state hPostShape.1.symm
              hPostShape.2.symm)
            |>.transport_locals_layout
              (after := initCursor.finalLocals) rfl
        have hFinishPostAtLoop :
            Locals.finishScoped initCursor.finalLocals
                postCursor.finalLocals postCursor.compiled =
              some compiledPost := by
          simpa [Locals.finishScoped] using hFinishPost
        rw [hCompiledPostShape]
        exact
          ResourceRecursiveBlockForward.scopedRegularInvariant
            postCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hPostBoundary hRun hAfterCompiler initCursor.planWF
            rfl hFinishPostAtLoop)
      hLoopSource hLower hCompile
  have hRestrict :
      (Functions.ObserverSemantics.stateModel transcript).restrictTo
          sourceCtx.scope sourceLoopFinal =
        (Functions.ObserverSemantics.stateModel transcript).restrictTo
          live sourceLoopFinal :=
    Locals.Source.Effectful.StateModel.restrictTo_congr
      (Functions.ObserverSemantics.stateModel transcript)
      hBoundary.sourceScope
  rw [hRestrict]
  have hResource :=
    hForward.toStackResource
      (allocatorDepth := allocatorDepth)
      hBoundary.invariant.owned
  exact
    ⟨afterState, headCode, tail,
      ResourceHeadResult.ofResource cursor tail hCompiled
        (.regular
          (by
            simpa [Functions.Scope.Stmt.outEnv] using hResource)
          (AllocationObserverOutcome.SameControl.refl sourceCtx))
        hStep hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)⟩

/--
Dispatch a stack-only `for` whose initializer completes regularly and whose
loop leaves the activation or halts.

The loop pass owns source-fuel recursion. This dispatcher theorem supplies
only adjacent lowering, Locals compilation, recursive resource results, and
the final stack-only lift at the enclosing statement boundary.
-/
theorem forExitHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx initCtx : Functions.Source.Ctx}
    {source sourceAfterInit :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceLoopOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := .stackOnly) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := sourceFuel + 1)
        (transcript := transcript))
    (hInitSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx.withoutLoopControl sourceFuel init source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceAfterInit,
            initCtx))
    (hLoopSource :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program initCtx cond initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok sourceLoopOutcome)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceLoopOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ResourceHeadResult cursor afterState localsCtx headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceLoopOutcome) := by
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
  cases hInitFinalState
  cases hInitFinalLocals
  let initFinished := initCursor.finished
  have hInitBoundary :
      ResourceBoundary initCursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx.withoutLoopControl)
        (source := source) (target := target) :=
    ResourceBoundary.forInit cursor initCursor hBoundary
  obtain
      ⟨targetAfterInit, initMode, hInitForward,
        hInitControl, hInitScope⟩ :=
    ResourceRecursiveBlockForward.regular initCursor hRecursive
      (Nat.lt_succ_self sourceFuel) hInitBoundary hInitSource
  have hInitModeStack : initMode = .stack := by
    rcases hInitForward with
      ⟨_sourceFuel, _targetFuel, _hSource, _hTarget,
        _hInvariant, hSame, _hEffect⟩
    exact
      hSame.right_eq_stack_of_left_eq_stack hBoundary.invariant.owned
  have hOuterSubset :
      ∀ name, name ∈ live →
        name ∈ Functions.Scope.Block.outEnv live init :=
    fun name hName => Functions.Scope.Block.mem_outEnv hName
  obtain ⟨targetOutcome, hForward⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.for_exit_of_safe_source_run
      (outerPlan := cursor.plan) (loopPlan := initCursor.plan)
      (outerLive := live)
      (loopLive := Functions.Scope.Block.outEnv live init)
      (resultLive := root.returns)
      (outerMode := mode) (loopMode := initMode)
      hCondScoped hInitScope hBoundary.invariant.activation
      hBoundary.returnFrame
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
        exact
          ⟨targetAfterInit, hInitForward.toInvariant, hInitControl⟩)
      (by
        intro loopState' afterPost' afterBody' loweredInit'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            ResourceBoundary bodyCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          ResourceBoundary.forBody cursor bodyCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hInvariant.compiler initCursor.planWF hLoopStateExtends
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant hInitModeStack)
        have hAfterCompiler :
            AllocationObserverContext.ActivationExprContext
              root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              initCursor.plan (Functions.Scope.Block.outEnv live init)
              initMode :=
          (hInvariant.compiler.transport_state
              hPostShape.1 hPostShape.2)
            |>.transport_locals_layout
              (after :=
                initCursor.finalLocals.withLoopControl
                  initCursor.finalLocals.layout.length) rfl
        rw [hCompiledBodyShape]
        exact
          ResourceRecursiveBlockForward.scopedRegularInvariant
            bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun hAfterCompiler initCursor.planWF rfl
            hFinishBody)
      (by
        intro loopState' afterPost' afterBody' loweredInit'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyFinal bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody'
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            ResourceBoundary bodyCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          ResourceBoundary.forBody cursor bodyCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hInvariant.compiler initCursor.planWF hLoopStateExtends
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant hInitModeStack)
        obtain
            ⟨targetBodyOutcome, _bodyFinalMode,
              hScoped, hControl⟩ :=
          ResourceRecursiveBlockForward.scopedNonregularControlled
            bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun
            (by
              simp [Functions.Source.Effectful.Outcome.cont,
                Locals.Source.Effectful.Outcome.cont])
            hFinishBody
        obtain ⟨targetBodyFinal, hTargetOutcome, hDestination⟩ :=
          hControl.cont bodyFinal rfl
        subst targetBodyOutcome
        rw [← hCompiledBodyShape] at hScoped
        rcases hScoped with
          ⟨bodySourceFuel, bodyTargetFuel, hBodySource,
            hBodyTarget, _hOutcomeRel⟩
        have hBaseDestination :
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant
              (contract := program.memoryContract)
              (resource := .stackOnly)
              (allocatorDepth := allocatorDepth)
              (frameBase := frameBase)
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.compiler initCursor.planWF
                hLoopStateExtends hInitScope).cont
              bodyFinal targetBodyFinal := by
          apply
            AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_transport
              (AllocationObserverOutcome.ControlDestinations.loopBody
                hInvariant.compiler initCursor.planWF
                hLoopStateExtends hInitScope).cont
              (AllocationObserverOutcome.SameControl.refl _)
              (Locals.Ctx.SameControl.refl _)
              (AllocationLowering.StateExtends.of_shape rfl rfl)
              (fun _ hName => hName) (SameFrame.refl initMode)
          simpa [hBodyBoundary, ResourceBoundary.forBody] using
            hDestination
        have hLoopInvariant :=
          AllocationObserverOutcome.ControlDestinations.loopBody_continue_resource_destination
            hInvariant.compiler initCursor.planWF hLoopStateExtends
              hInitScope hBaseDestination
        have hContinueInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              initCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodyFinal targetBodyFinal :=
          (hLoopInvariant.activation.transport_state
              hPostShape.1 hPostShape.2)
            |>.transport_locals_layout
              (after :=
                initCursor.finalLocals.withLoopControl
                  initCursor.finalLocals.layout.length) rfl
        exact
          ⟨targetBodyFinal, bodySourceFuel, bodyTargetFuel,
            hBodySource, hBodyTarget, hContinueInvariant⟩)
      (by
        intro loopState' afterPost' afterBody' loweredInit'
          loweredPost loweredBody initLocals' bodyLocals' initCode'
          bodyCode compiledBody' bodyFuel bodySource bodyOutcome bodyTarget
          hLowerInit' hCompileInit' hLowerPost' hLowerBody'
          hCompileBody' hFinishBody' hBodyExit
          hInvariant hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hLowerBodyPair :
            (bodyCursor.lowered, afterBody) =
              (loweredBody, afterBody') :=
          Option.some.inj (hLowerBody.symm.trans hLowerBody')
        cases hLowerBodyPair
        have hCompileBodyPair :
            (bodyCursor.compiled, bodyCursor.finalLocals) =
              (bodyCode, bodyLocals') :=
          Option.some.inj (bodyCursor.compile.symm.trans hCompileBody')
        cases hCompileBodyPair
        have hCompiledBody : compiledBody = compiledBody' :=
          Option.some.inj (hFinishBody.symm.trans hFinishBody')
        cases hCompiledBody
        have hCompiledBodyShape :
            compiledBody.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledBody.stmts } := by
          cases compiledBody
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hBodyPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan bodyCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (bodyCursor.planAgreesOn initFinished hPostShape.1).symm
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx afterPost
              (initCursor.finalLocals.withLoopControl
                initCursor.finalLocals.layout.length)
              bodyCursor.plan (Functions.Scope.Block.outEnv live init)
              frameBase initMode bodySource bodyTarget :=
          (((hInvariant.transport_state hPostShape.1 hPostShape.2)
              |>.transport_locals_layout
                (after :=
                  initCursor.finalLocals.withLoopControl
                    initCursor.finalLocals.layout.length) rfl)
              |>.transport_plan bodyCursor.planWF hBodyPlanAgree)
        have hLoopStateExtends :
            AllocationLowering.StateExtends
              (Functions.Scope.Block.outEnv live init)
              initCursor.finalState afterPost :=
          AllocationLowering.StateExtends.of_shape
            hPostShape.2 hPostShape.1
        let hBodyBoundary :
            ResourceBoundary bodyCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode)
              (sourceCtx :=
                initCtx.withLoopControl initCtx.scope initCtx.scope)
              (source := bodySource) (target := bodyTarget) :=
          ResourceBoundary.forBody cursor bodyCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hInvariant.compiler initCursor.planWF hLoopStateExtends
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant hInitModeStack)
        obtain
            ⟨targetBodyOutcome, _bodyFinalMode,
              hScoped, _hControl⟩ :=
          ResourceRecursiveBlockForward.scopedNonregularControlled
            bodyCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hBodyBoundary hRun hBodyExit.not_regular hFinishBody
        rw [← hCompiledBodyShape] at hScoped
        exact
          ⟨targetBodyOutcome,
            AllocationObserverStatement.Sequence.ScopedBlockForward.transport_of_isExit
              (afterPlan := initCursor.plan)
              (afterLive := root.returns)
              (afterMode := initMode)
              hScoped hBodyExit
              (by
                intro hLeave
                simp [AllocationObserverOutcome.outcomeLive, hLeave])⟩)
      (by
        intro loopState' afterPost' loweredInit' loweredPost initLocals'
          postLocals' initCode' postCode compiledPost' postFuel postSource
          postFinal postTarget hLowerInit' hCompileInit' hLowerPost'
          hCompilePost' hFinishPost' hInvariant
          hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hCompilePostPair :
            (postCursor.compiled, postCursor.finalLocals) =
              (postCode, postLocals') :=
          Option.some.inj (postCursor.compile.symm.trans hCompilePost')
        cases hCompilePostPair
        have hCompiledPost : compiledPost = compiledPost' :=
          Option.some.inj (hFinishPost.symm.trans hFinishPost')
        cases hCompiledPost
        have hCompiledPostShape :
            compiledPost.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledPost.stmts } := by
          cases compiledPost
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hPostPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan postCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (postCursor.planAgreesOn initFinished rfl).symm
        have hPostInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx initCursor.finalState
              initCursor.finalLocals.withoutLoopControl postCursor.plan
              (Functions.Scope.Block.outEnv live init)
              frameBase initMode postSource postTarget :=
          (((hInvariant.transport_state hPostShape.1.symm
                hPostShape.2.symm)
              |>.transport_locals_layout
                (after := initCursor.finalLocals.withoutLoopControl) rfl)
              |>.transport_plan postCursor.planWF hPostPlanAgree)
        have hPostBoundary :
            ResourceBoundary postCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode) (sourceCtx := initCtx.withoutLoopControl)
              (source := postSource) (target := postTarget) :=
          ResourceBoundary.forPost cursor postCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hPostInvariant hInitModeStack)
        have hAfterCompiler :
            AllocationObserverContext.ActivationExprContext
              root.lowerCtx initCursor.finalState
              initCursor.finalLocals initCursor.plan
              (Functions.Scope.Block.outEnv live init) initMode :=
          (hInvariant.compiler.transport_state hPostShape.1.symm
              hPostShape.2.symm)
            |>.transport_locals_layout
              (after := initCursor.finalLocals) rfl
        have hFinishPostAtLoop :
            Locals.finishScoped initCursor.finalLocals
                postCursor.finalLocals postCursor.compiled =
              some compiledPost := by
          simpa [Locals.finishScoped] using hFinishPost
        rw [hCompiledPostShape]
        exact
          ResourceRecursiveBlockForward.scopedRegularInvariant
            postCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hPostBoundary hRun hAfterCompiler initCursor.planWF
            rfl hFinishPostAtLoop)
      (by
        intro loopState' afterPost' loweredInit' loweredPost initLocals'
          postLocals' initCode' postCode compiledPost' postFuel postSource
          postOutcome postTarget hLowerInit' hCompileInit' hLowerPost'
          hCompilePost' hFinishPost' hPostExit hInvariant
          hReturnFrame hFuel hRun
        have hLowerInitPair :
            (initCursor.lowered, initCursor.finalState) =
              (loweredInit', loopState') :=
          Option.some.inj (initCursor.lower.symm.trans hLowerInit')
        cases hLowerInitPair
        have hCompileInitPair :
            (initCursor.compiled, initCursor.finalLocals) =
              (initCode', initLocals') :=
          Option.some.inj (initCursor.compile.symm.trans hCompileInit')
        cases hCompileInitPair
        have hLowerPostPair :
            (postCursor.lowered, afterPost) =
              (loweredPost, afterPost') :=
          Option.some.inj (hLowerPost.symm.trans hLowerPost')
        cases hLowerPostPair
        have hCompilePostPair :
            (postCursor.compiled, postCursor.finalLocals) =
              (postCode, postLocals') :=
          Option.some.inj (postCursor.compile.symm.trans hCompilePost')
        cases hCompilePostPair
        have hCompiledPost : compiledPost = compiledPost' :=
          Option.some.inj (hFinishPost.symm.trans hFinishPost')
        cases hCompiledPost
        have hCompiledPostShape :
            compiledPost.toStructured =
              { stmts :=
                  Expressions.StmtList.toStructured compiledPost.stmts } := by
          cases compiledPost
          rfl
        have hPostShape :=
          AllocationLowering.lowerBlockScoped_state_shape hLowerPost
        have hPostPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              initCursor.plan postCursor.plan
                (Functions.Scope.Block.outEnv live init) :=
          (postCursor.planAgreesOn initFinished rfl).symm
        have hPostInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx initCursor.finalState
              initCursor.finalLocals.withoutLoopControl postCursor.plan
              (Functions.Scope.Block.outEnv live init)
              frameBase initMode postSource postTarget :=
          (((hInvariant.transport_state hPostShape.1.symm
                hPostShape.2.symm)
              |>.transport_locals_layout
                (after := initCursor.finalLocals.withoutLoopControl) rfl)
              |>.transport_plan postCursor.planWF hPostPlanAgree)
        have hPostBoundary :
            ResourceBoundary postCursor (resource := .stackOnly)
              (allocatorDepth := allocatorDepth) (frameBase := frameBase)
              (mode := initMode) (sourceCtx := initCtx.withoutLoopControl)
              (source := postSource) (target := postTarget) :=
          ResourceBoundary.forPost cursor postCursor hBoundary
            initCursor.compile hInitScope hOuterSubset hInitControl
            hReturnFrame
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hPostInvariant hInitModeStack)
        obtain
            ⟨targetPostOutcome, _postFinalMode,
              hScoped, _hControl⟩ :=
          ResourceRecursiveBlockForward.scopedNonregularControlled
            postCursor hRecursive
            (Nat.lt_trans hFuel (Nat.lt_succ_self sourceFuel))
            hPostBoundary hRun hPostExit.not_regular hFinishPost
        rw [← hCompiledPostShape] at hScoped
        exact
          ⟨targetPostOutcome,
            AllocationObserverStatement.Sequence.ScopedBlockForward.transport_of_isExit
              (afterPlan := initCursor.plan)
              (afterLive := root.returns)
              (afterMode := initMode)
              hScoped hPostExit
              (by
                intro hLeave
                simp [AllocationObserverOutcome.outcomeLive, hLeave])⟩)
      hExit hLoopSource hLower hCompile
  have hForwardOuter :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.transport_of_isExit
      (afterPlan := cursor.plan)
      (afterLive :=
        AllocationObserverOutcome.outcomeLive
          root.returns live sourceCtx sourceLoopOutcome.mode)
      hForward hExit
      (by
        intro hLeave
        simp [AllocationObserverOutcome.outcomeLive, hLeave])
  have hResource :=
    hForwardOuter.toStackResource
      (allocatorDepth := allocatorDepth)
      hBoundary.invariant.owned hInitModeStack
  exact
    ⟨afterState, headCode, tail,
      ResourceHeadResult.ofNonregular cursor tail hCompiled
        (.nonregular hResource) hExact hExit.not_regular⟩

/--
Dispatch every successful stack-only `for` run through the three adjacent
loop-head theorems.

This wrapper owns only the canonical source-run case split. Initializer exit,
regular completion, and post-initializer activation exit remain proved by
their dedicated pass-owned theorems above.
-/
theorem forControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1)
          (.for_ init cond post body) source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hRecursive :
      ResourceRecursiveBlockForward (root := root)
        (resource := .stackOnly) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (fuelBound := sourceFuel + 1)
        (transcript := transcript)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ResourceControlledHeadResult cursor hBoundary afterState localsCtx
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  rcases
      Functions.Source.Effectful.Stmt.run_for_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with hRegular | hExit
  · rcases hRegular with
      ⟨sourceAfterInit, initCtx, sourceLoopFinal, hInit, hLoop,
        hOutcome, hFinal⟩
    subst sourceOutcome
    subst finalCtx
    obtain ⟨afterState, headCode, tail, hHead⟩ :=
      forRegularHeadResultStack cursor hBoundary hRecursive hInit hLoop
    exact
      ⟨afterState, headCode, tail,
        ResourceControlledHeadResult.of_no_control
          cursor hBoundary tail hHead
          (by
            intro sourceFinal hAbrupt
            have hMode :=
              congrArg Locals.Source.Effectful.Outcome.mode hAbrupt
            contradiction)
          (by
            intro sourceFinal hAbrupt
            have hMode :=
              congrArg Locals.Source.Effectful.Outcome.mode hAbrupt
            contradiction)⟩
  · rcases hExit with hLoopExit | hInitExit
    · rcases hLoopExit with
        ⟨sourceAfterInit, initCtx, hInit, hLoop, hIsExit, hFinal⟩
      subst finalCtx
      obtain ⟨afterState, headCode, tail, hHead⟩ :=
        forExitHeadResultStack cursor hBoundary hRecursive
          hInit hLoop hIsExit
      exact
        ⟨afterState, headCode, tail,
          ResourceControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hAbrupt
              exact hIsExit.ne_brk sourceFinal hAbrupt)
            (by
              intro sourceFinal hAbrupt
              exact hIsExit.ne_cont sourceFinal hAbrupt)⟩
    · rcases hInitExit with ⟨initCtx, hInit, hIsExit, hFinal⟩
      subst finalCtx
      obtain ⟨afterState, headCode, tail, hHead⟩ :=
        forInitExitHeadResultStack cursor hBoundary hRecursive
          hInit hIsExit
      exact
        ⟨afterState, headCode, tail,
          ResourceControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hAbrupt
              exact hIsExit.ne_brk sourceFinal hAbrupt)
            (by
              intro sourceFinal hAbrupt
              exact hIsExit.ne_cont sourceFinal hAbrupt)⟩

/--
Dispatch a lexical block in a compiler-selected stack-only activation while
retaining exact recursive control destinations.
-/
theorem blockControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .block body :: rest } lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.block body) source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hBody :
      ∀ {bodyOutcome :
            Functions.ObserverSemantics.Outcome
              (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        (bodyCursor :
          AllocationObserverForward.BodyCursor.CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx)
        (hOpen :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                program.memoryContract transcript)
              program sourceCtx sourceFuel body source =
            .ok (bodyOutcome, bodyCtx))
        (bodyBoundary :
          ResourceBoundary bodyCursor (resource := .stackOnly)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (mode := mode) (sourceCtx := sourceCtx)
            (source := source) (target := target)),
        ResourceBlockResult bodyCursor bodyBoundary
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := bodyCtx)
          (source := source) (target := target)
          (sourceOutcome := bodyOutcome)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ResourceControlledHeadResult cursor hBoundary afterState localsCtx
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
              targetOutcome, hCompiled, hResource, hStep, hExact,
              hRegularOutcome, _hAbruptOutcome, _hDecoration⟩ :=
          cursor.blockStackResourceResult (P := fun _ => True)
            hBoundary.sourceScope hBoundary.control hBoundary.invariant
            (by
              intro bodyCursor
              have hPlanAgree :
                  AllocationObserverRelation.PlanAgreesOn
                    bodyCursor.plan cursor.plan live :=
                bodyCursor.planAgreesOn cursor rfl
              have hBodyInvariant :
                  AllocationObserverContext.ActivationResourceInvariant
                    .stackOnly program.memoryContract allocatorDepth
                    root.lowerCtx lowerState localsCtx bodyCursor.plan live
                    frameBase mode source target :=
                hBoundary.invariant.transport_plan
                  bodyCursor.planWF hPlanAgree.symm
              let bodyBoundary :
                  ResourceBoundary bodyCursor (resource := .stackOnly)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := mode)
                    (sourceCtx := sourceCtx) (source := source)
                    (target := target) :=
                hBoundary.rebase cursor bodyCursor
                  (AllocationLowering.StateExtends.of_shape rfl rfl)
                  (Locals.Ctx.SameControl.refl localsCtx)
                  hBoundary.returnFrame hBodyInvariant
              obtain ⟨targetOutcome, hRuntime, _hControl⟩ :=
                (hBody bodyCursor hOpen bodyBoundary).runtime
              exact ⟨targetOutcome, hRuntime, trivial⟩)
        have hRestrict :
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
                sourceCtx.scope bodyFinal =
              (Functions.ObserverSemantics.stateModel transcript).restrictTo
                live bodyFinal :=
          Locals.Source.Effectful.StateModel.restrictTo_congr
            (Functions.ObserverSemantics.stateModel transcript)
            hBoundary.sourceScope
        rw [hRestrict]
        rw [hRegularOutcome rfl] at hResource
        have hHead :
            ResourceHeadResult cursor afterState localsCtx headCode tail
              (resource := .stackOnly) (allocatorDepth := allocatorDepth)
              (frameBase := frameBase) (mode := mode)
              (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
              (source := source) (target := target)
              (sourceOutcome :=
                Functions.Source.Effectful.Outcome.regular
                  ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                    live bodyFinal)) :=
          ResourceHeadResult.ofResource cursor tail hCompiled hResource hStep
            hExact
            (by
              intro _ name
              simpa [Functions.Scope.Stmt.outEnv] using
                hBoundary.sourceScope name)
        exact
          ⟨afterState, headCode, tail,
            ResourceControlledHeadResult.of_no_control
              cursor hBoundary tail hHead
              (by
                intro sourceFinal hOutcome
                cases hOutcome)
              (by
                intro sourceFinal hOutcome
                cases hOutcome)⟩
      · rcases hNonregular with
          ⟨openOutcome, bodyCtx, hOpen, hMode, hScopedOutcome⟩
        subst sourceOutcome
        obtain
            ⟨afterState, headCode, tail, producedSourceOutcome,
              targetOutcome, hCompiled, hResource, hStep, hExact,
              _hRegularOutcome, hAbruptOutcome, hControlOutcome⟩ :=
          cursor.blockStackResourceResult
            (P := fun targetOutcome =>
              ResourceControlOutcomeForward cursor hBoundary openOutcome
                targetOutcome)
            hBoundary.sourceScope hBoundary.control hBoundary.invariant
            (by
              intro bodyCursor
              have hPlanAgree :
                  AllocationObserverRelation.PlanAgreesOn
                    bodyCursor.plan cursor.plan live :=
                bodyCursor.planAgreesOn cursor rfl
              have hBodyInvariant :
                  AllocationObserverContext.ActivationResourceInvariant
                    .stackOnly program.memoryContract allocatorDepth
                    root.lowerCtx lowerState localsCtx bodyCursor.plan live
                    frameBase mode source target :=
                hBoundary.invariant.transport_plan
                  bodyCursor.planWF hPlanAgree.symm
              let bodyBoundary :
                  ResourceBoundary bodyCursor (resource := .stackOnly)
                    (allocatorDepth := allocatorDepth)
                    (frameBase := frameBase) (mode := mode)
                    (sourceCtx := sourceCtx) (source := source)
                    (target := target) :=
                hBoundary.rebase cursor bodyCursor
                  (AllocationLowering.StateExtends.of_shape rfl rfl)
                  (Locals.Ctx.SameControl.refl localsCtx)
                  hBoundary.returnFrame hBodyInvariant
              have bodyResult := hBody bodyCursor hOpen bodyBoundary
              obtain ⟨bodyTargetOutcome, hBodyRuntime, hBodyControl⟩ :=
                bodyResult.runtime
              exact
                ⟨bodyTargetOutcome, hBodyRuntime,
                  ResourceControlOutcomeForward.of_rebase
                    cursor bodyCursor hBoundary
                    (AllocationLowering.StateExtends.of_shape rfl rfl)
                    (Locals.Ctx.SameControl.refl localsCtx)
                    hBoundary.returnFrame hBodyInvariant hBodyControl⟩)
        rw [hAbruptOutcome hMode] at hResource hControlOutcome
        have hHead :
            ResourceHeadResult cursor afterState localsCtx headCode tail
              (resource := .stackOnly) (allocatorDepth := allocatorDepth)
              (frameBase := frameBase) (mode := mode)
              (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
              (source := source) (target := target)
              (sourceOutcome := openOutcome) :=
          ResourceHeadResult.ofNonregular cursor tail hCompiled hResource
            hExact hMode
        exact
          ⟨afterState, headCode, tail,
            { head := hHead
              runtime :=
                ⟨targetOutcome, hResource, hControlOutcome hMode⟩ }⟩

/--
Dispatch an `if` in a compiler-selected stack-only activation while retaining
exact `break` and `continue` destinations from its selected lexical body.
-/
theorem ifControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1) (.if_ cond body) source =
        .ok (sourceOutcome, sourceCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hBody :
      ∀ {sourceAfterCond :
            Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        (bodyCursor :
          AllocationObserverForward.BodyCursor.CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx)
        (hOpen :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                program.memoryContract transcript)
              program sourceCtx sourceFuel body sourceAfterCond =
            .ok (bodyOutcome, bodyCtx))
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript}
        (bodyBoundary :
          ResourceBoundary bodyCursor (resource := .stackOnly)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (mode := mode) (sourceCtx := sourceCtx)
            (source := sourceAfterCond) (target := targetBodyStart)),
        ResourceBlockResult bodyCursor bodyBoundary
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := bodyCtx)
          (source := sourceAfterCond) (target := targetBodyStart)
          (sourceOutcome := bodyOutcome)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ResourceControlledHeadResult cursor hBoundary afterState localsCtx
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  rcases
      Functions.Source.Effectful.Stmt.run_if_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hFalse | hTrue
  · rcases hFalse with
      ⟨sourceAfterCond, hCond, hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    have hZero : value = EvmYul.UInt256.ofNat 0 := by
      by_contra hNe
      have hNonzero :
          (value != EvmYul.UInt256.ofNat 0) = true :=
        TypedCfg.Preservation.uint256_bne_zero_of_ne value hNe
      rw [hNonzero] at hValue
      contradiction
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hResource, hStep, hExact⟩ :=
      cursor.ifFalseStackResourceResult
        (sourceCtx := sourceCtx) hSafe hZero hBoundary.invariant
    have hHead :
        ResourceHeadResult cursor afterState localsCtx headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular sourceAfterCond) :=
      ResourceHeadResult.ofResource cursor tail hCompiled hResource hStep
        hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)
    exact
      ⟨afterState, headCode, tail,
        ResourceControlledHeadResult.of_no_control
          cursor hBoundary tail hHead
          (by
            intro sourceFinal hEq
            cases hEq)
          (by
            intro sourceFinal hEq
            cases hEq)⟩
  · rcases hTrue with
      ⟨sourceAfterCond, bodyOutcome, hCond, hScoped,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hBoundary.sourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hResource, hStep, hExact⟩ :=
        cursor.ifTrueRegularStackResourceResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hSafe hValue hBoundary.sourceScope hBoundary.invariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant hReturns
            let bodyBoundary :
                ResourceBoundary bodyCursor (resource := .stackOnly)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx) (source := sourceAfterCond)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor
                (AllocationLowering.StateExtends.of_shape rfl rfl)
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            obtain ⟨bodyTargetOutcome, hBodyResource, _hBodyControl⟩ :=
              (hBody bodyCursor hBodyRun bodyBoundary).runtime
            cases hBodyResource with
            | regular hBodyForward hBodyControl =>
                exact ⟨_, .regular hBodyForward hBodyControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      have hHead :
          ResourceHeadResult cursor afterState localsCtx headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.regular
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  live sourceBodyFinal)) :=
        ResourceHeadResult.ofResource cursor tail hCompiled hResource hStep
          hExact
          (by
            intro _ name
            simpa [Functions.Scope.Stmt.outEnv] using
              hBoundary.sourceScope name)
      exact
        ⟨afterState, headCode, tail,
          ResourceControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hEq
              cases hEq)
            (by
              intro sourceFinal hEq
              cases hEq)⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hResource, _hStep, hExact, hControlOutcome⟩ :=
        cursor.ifTrueNonregularStackResourceResult
          (P := fun targetOutcome =>
            ResourceControlOutcomeForward cursor hBoundary openOutcome
              targetOutcome)
          hSafe hValue hMode hBoundary.control hBoundary.invariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant hReturns
            let bodyBoundary :
                ResourceBoundary bodyCursor (resource := .stackOnly)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx) (source := sourceAfterCond)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor
                (AllocationLowering.StateExtends.of_shape rfl rfl)
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            obtain ⟨bodyTargetOutcome, hBodyResource, hBodyControl⟩ :=
              (hBody bodyCursor hBodyRun bodyBoundary).runtime
            exact
              ⟨bodyTargetOutcome, bodyCtx, hBodyResource,
                ResourceControlOutcomeForward.of_rebase
                  cursor bodyCursor hBoundary
                  (AllocationLowering.StateExtends.of_shape rfl rfl)
                  (Locals.Ctx.SameControl.refl localsCtx)
                  (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                    hBoundary.returnFrame hReturns)
                  hBodyInvariant hBodyControl⟩)
      have hHead :
          ResourceHeadResult cursor afterState localsCtx headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome := openOutcome) :=
        ResourceHeadResult.ofNonregular cursor tail hCompiled hResource
          hExact hMode
      exact
        ⟨afterState, headCode, tail,
          { head := hHead
            runtime := ⟨targetOutcome, hResource, hControlOutcome⟩ }⟩

/--
Dispatch a `switch` in a compiler-selected stack-only activation while
retaining exact `break` and `continue` destinations from its selected body.
-/
theorem switchControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok (sourceOutcome, sourceCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
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
          AllocationObserverForward.BodyCursor.CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx)
        (hState :
          AllocationLowering.StateExtends
            live lowerState selectedStart)
        (hOpen :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                program.memoryContract transcript)
              program sourceCtx sourceFuel selected sourceAfterScrutinee =
            .ok (bodyOutcome, bodyCtx))
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript}
        (bodyBoundary :
          ResourceBoundary bodyCursor (resource := .stackOnly)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (mode := mode) (sourceCtx := sourceCtx)
            (source := sourceAfterScrutinee) (target := targetBodyStart)),
        ResourceBlockResult bodyCursor bodyBoundary
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := bodyCtx)
          (source := sourceAfterScrutinee) (target := targetBodyStart)
          (sourceOutcome := bodyOutcome)) :
    ∃ afterState headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        ResourceControlledHeadResult cursor hBoundary afterState localsCtx
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  rcases
      Functions.Source.Effectful.Stmt.run_switch_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hNone | hSome
  · rcases hNone with
      ⟨sourceAfterScrutinee, value, hScrutinee, hSelect,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hResource, hStep, hExact⟩ :=
      cursor.switchNoneStackResourceResult
        (sourceCtx := sourceCtx)
        (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
          hScrutinee)
        hSelect hBoundary.invariant
    have hHead :
        ResourceHeadResult cursor afterState localsCtx headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
          (source := source) (target := target)
          (sourceOutcome :=
            Functions.Source.Effectful.Outcome.regular
              sourceAfterScrutinee) :=
      ResourceHeadResult.ofResource cursor tail hCompiled hResource hStep
        hExact
        (by
          intro _ name
          simpa [Functions.Scope.Stmt.outEnv] using
            hBoundary.sourceScope name)
    exact
      ⟨afterState, headCode, tail,
        ResourceControlledHeadResult.of_no_control
          cursor hBoundary tail hHead
          (by
            intro sourceFinal hEq
            cases hEq)
          (by
            intro sourceFinal hEq
            cases hEq)⟩
  · rcases hSome with
      ⟨sourceAfterScrutinee, value, selected, bodyOutcome,
        hScrutinee, hSelect, hScoped, hOutcome, _hCtx⟩
    subst sourceOutcome
    have hSafe :
        AllocationObserverSafety.Expr.MemorySafeEval
          program.memoryContract transcript scrutinee source
          sourceAfterScrutinee [value] :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
        hScrutinee
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hBoundary.sourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hResource, hStep, hExact⟩ :=
        cursor.switchSomeRegularStackResourceResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hSafe hSelect hBoundary.sourceScope hBoundary.invariant
          (by
            intro selectedStart selectedPlanning bodyCursor
              targetBodyStart hSelectedExtends hBodyInvariant hReturns
            let bodyBoundary :
                ResourceBoundary bodyCursor (resource := .stackOnly)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx)
                  (source := sourceAfterScrutinee)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor hSelectedExtends
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            obtain ⟨bodyTargetOutcome, hBodyResource, _hBodyControl⟩ :=
              (hBody bodyCursor hSelectedExtends hBodyRun
                bodyBoundary).runtime
            cases hBodyResource with
            | @regular _ _ finalMode _ hBodyForward hBodyControl =>
                exact ⟨_, .regular hBodyForward hBodyControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      have hHead :
          ResourceHeadResult cursor afterState localsCtx headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.regular
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  live sourceBodyFinal)) :=
        ResourceHeadResult.ofResource cursor tail hCompiled hResource hStep
          hExact
          (by
            intro _ name
            simpa [Functions.Scope.Stmt.outEnv] using
              hBoundary.sourceScope name)
      exact
        ⟨afterState, headCode, tail,
          ResourceControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hEq
              cases hEq)
            (by
              intro sourceFinal hEq
              cases hEq)⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hResource, _hStep, hExact, hControlOutcome⟩ :=
        cursor.switchSomeNonregularStackResourceResult
          (P := fun targetOutcome =>
            ResourceControlOutcomeForward cursor hBoundary openOutcome
              targetOutcome)
          hSafe hSelect hMode hBoundary.control hBoundary.invariant
          (by
            intro selectedStart selectedPlanning bodyCursor targetBodyStart
              hSelectedExtends hBodyInvariant hReturns
            let bodyBoundary :
                ResourceBoundary bodyCursor (resource := .stackOnly)
                  (allocatorDepth := allocatorDepth)
                  (frameBase := frameBase) (mode := mode)
                  (sourceCtx := sourceCtx)
                  (source := sourceAfterScrutinee)
                  (target := targetBodyStart) :=
              hBoundary.rebase cursor bodyCursor hSelectedExtends
                (Locals.Ctx.SameControl.refl localsCtx)
                (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                  hBoundary.returnFrame hReturns)
                hBodyInvariant
            obtain ⟨bodyTargetOutcome, hBodyResource, hBodyControl⟩ :=
              (hBody bodyCursor hSelectedExtends hBodyRun
                bodyBoundary).runtime
            exact
              ⟨bodyTargetOutcome, bodyCtx, hBodyResource,
                ResourceControlOutcomeForward.of_rebase
                  cursor bodyCursor hBoundary hSelectedExtends
                  (Locals.Ctx.SameControl.refl localsCtx)
                  (AllocationObserverOutcome.ReturnFrameAvailable.transport_target
                    hBoundary.returnFrame hReturns)
                  hBodyInvariant hBodyControl⟩)
      have hHead :
          ResourceHeadResult cursor afterState localsCtx headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome := openOutcome) :=
        ResourceHeadResult.ofNonregular cursor tail hCompiled hResource
          hExact hMode
      exact
        ⟨afterState, headCode, tail,
          { head := hHead
            runtime := ⟨targetOutcome, hResource, hControlOutcome⟩ }⟩

/--
Dispatch `break` in a compiler-selected stack-only activation using the
canonical loop destination already carried by the shared boundary.
-/
theorem brkControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .brk :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .brk source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ResourceControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
        cursor.brkStackResourceResultExact hScope
          (by
            simpa [hTransition,
              AllocationObserverOutcome.ControlKind.targetDepth?] using
              controlArtifact.target)
          hTransition hBoundary.invariant
      have hDestinationInvariant :=
        controlArtifact.resourceInvariant hBoundary.invariant
          hFinalState hFinalStack hMachine
      have hControlInvariant :
          AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant
            (contract := program.memoryContract) (resource := .stackOnly)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            hBoundary.destinations.brk
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal :=
        AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_artifact
          controlArtifact hOwned hDestinationInvariant
      let hHead :
          ResourceHeadResult cursor afterState afterLocals headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.brk
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  afterLive source)) :=
        ResourceHeadResult.ofNonregular cursor tail hCompiled hRuntime hExact
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
Dispatch `continue` in a compiler-selected stack-only activation using the
canonical loop destination already carried by the shared boundary.
-/
theorem contControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .cont :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .cont source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ResourceControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
        cursor.contStackResourceResultExact hScope
          (by
            simpa [hTransition,
              AllocationObserverOutcome.ControlKind.targetDepth?] using
              controlArtifact.target)
          hTransition hBoundary.invariant
      have hDestinationInvariant :=
        controlArtifact.resourceInvariant hBoundary.invariant
          hFinalState hFinalStack hMachine
      have hControlInvariant :
          AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant
            (contract := program.memoryContract) (resource := .stackOnly)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            hBoundary.destinations.cont
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal :=
        AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_artifact
          controlArtifact hOwned hDestinationInvariant
      let hHead :
          ResourceHeadResult cursor afterState afterLocals headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.cont
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  afterLive source)) :=
        ResourceHeadResult.ofNonregular cursor tail hCompiled hRuntime hExact
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
Dispatch `leave` in a compiler-selected stack-only activation using the
function-return facts carried by the shared boundary.
-/
theorem leaveControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .leave :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel .leave source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ResourceControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
            hCompiled, hResource, hExact⟩ :=
        cursor.leaveStackResourceResult hScope hBoundary.control
          hTargetDepth hRetc (hBoundary.returnFrame functionScope hScope)
          hBoundary.invariant
      let hHead :
          ResourceHeadResult cursor afterState afterLocals headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.leave
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  functionScope source)) :=
        ResourceHeadResult.ofNonregular cursor tail hCompiled hResource hExact
          (by
            simp [Functions.Source.Effectful.Outcome.leave,
              Locals.Source.Effectful.Outcome.leave])
      exact
        ⟨afterState, afterLocals, headCode, tail,
          ResourceControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hOutcome
              cases hOutcome)
            (by
              intro sourceFinal hOutcome
              cases hOutcome)⟩

/--
Dispatch a plain terminal statement in a compiler-selected stack-only
activation.
-/
theorem terminalControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .terminal kind :: rest } beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.terminal kind) source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ResourceControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
            hCompiled, hResource, hExact⟩ :=
        cursor.terminalStackResourceResult hMemory hTerminal
          hBoundary.invariant
      let hHead :
          ResourceHeadResult cursor afterState afterLocals headCode tail
            (resource := .stackOnly) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := mode)
            (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
            (source := source) (target := target)
            (sourceOutcome :=
              Functions.Source.Effectful.Outcome.halt kind sourceFinal) :=
        ResourceHeadResult.ofNonregular cursor tail hCompiled hResource hExact
          (by
            simp [Functions.Source.Effectful.Outcome.halt,
              Locals.Source.Effectful.Outcome.halt])
      exact
        ⟨afterState, afterLocals, headCode, tail,
          ResourceControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hOutcome
              cases hOutcome)
            (by
              intro sourceFinal hOutcome
              cases hOutcome)⟩

/--
Dispatch a terminal-with-arguments statement in a compiler-selected
stack-only activation.
-/
theorem terminalArgsControlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest }
        beforeState beforeLocals)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.terminalArgs kind args) source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      ResourceBoundary cursor (resource := .stackOnly)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
        ResourceControlledHeadResult cursor hBoundary afterState afterLocals
          headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
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
                hCompiled, hResource, hExact⟩ :=
            cursor.terminalArgsStackResourceResult
              (AllocationObserverSafety.ExprSeq.MemorySafeEval.of_safe_eval
                hArgsEval)
              hMemory hTerminal hBoundary.invariant
          let hHead :
              ResourceHeadResult cursor afterState afterLocals headCode tail
                (resource := .stackOnly) (allocatorDepth := allocatorDepth)
                (frameBase := frameBase) (mode := mode)
                (sourceCtx := sourceCtx) (finalCtx := sourceCtx)
                (source := source) (target := target)
                (sourceOutcome :=
                  Functions.Source.Effectful.Outcome.halt
                    kind sourceFinal) :=
            ResourceHeadResult.ofNonregular cursor tail hCompiled hResource
              hExact
              (by
                simp [Functions.Source.Effectful.Outcome.halt,
                  Locals.Source.Effectful.Outcome.halt])
          exact
            ⟨afterState, afterLocals, headCode, tail,
              ResourceControlledHeadResult.of_no_control
                cursor hBoundary tail hHead
                (by
                  intro abruptFinal hOutcome
                  cases hOutcome)
                (by
                  intro abruptFinal hOutcome
                  cases hOutcome)⟩

/--
Transport a resource-indexed dispatcher boundary across one regular
statement.
-/
def afterRegular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {beforeLive afterLive : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope beforeLive
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope afterLive
        { stmts := rest } afterState afterLocals)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := beforeMode) (sourceCtx := beforeCtx)
        (source := beforeSource) (target := beforeTarget))
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
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
        afterState afterLocals tail.plan afterLive frameBase afterMode
        afterSource afterTarget) :
    ResourceBoundary tail (resource := resource)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := afterMode) (sourceCtx := afterCtx)
      (source := afterSource) (target := afterTarget) :=
  { sourceScope := hSourceScope
    control := by
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
Transport resource-indexed abrupt-destination evidence through one regular
statement prefix.
-/
theorem ResourceControlOutcomeForward.of_afterRegular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {beforeLive afterLive : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope beforeLive
        { stmts := stmt :: rest } beforeState beforeLocals)
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope afterLive
        { stmts := rest } afterState afterLocals)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := beforeMode) (sourceCtx := beforeCtx)
        (source := beforeSource) (target := beforeTarget))
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
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
        afterState afterLocals tail.plan afterLive frameBase afterMode
        afterSource afterTarget)
    (hTail :
      ResourceControlOutcomeForward tail
        (hBoundary.afterRegular cursor tail hAfterLive hStep hSourceControl
          hSameFrame hSourceScope hTarget hInvariant)
        sourceOutcome targetOutcome) :
    ResourceControlOutcomeForward cursor hBoundary sourceOutcome
      targetOutcome := by
  constructor
  · intro sourceFinal hOutcome
    obtain ⟨targetFinal, hTargetOutcome, hDestination⟩ :=
      hTail.brk sourceFinal hOutcome
    refine ⟨targetFinal, hTargetOutcome, ?_⟩
    exact
      AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_transport
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
      AllocationObserverOutcome.ControlBinding.DestinationResourceInvariant.of_transport
        hBoundary.destinations.cont hSourceControl hStep.locals hStep.state
        (by
          intro name hName
          rw [hAfterLive]
          exact hStep.live name hName)
        hSameFrame hDestination

/-- The empty synchronized cursor satisfies the resource recursive result. -/
theorem nilBlockResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := [] } lowerState localsCtx)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel { stmts := [] } source =
        .ok (sourceOutcome, finalCtx)) :
    ResourceBlockResult cursor hBoundary
      (resource := resource) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := sourceCtx) (finalCtx := finalCtx)
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
              cursor.nilResourceResult hBoundary.invariant,
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
Compose one resource-indexed controlled head with recursive preservation of
its exact tail.
-/
theorem consBlockResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : Frame.ResourceMode}
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
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (hBoundary :
      ResourceBoundary cursor (resource := resource)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (mode := mode) (sourceCtx := sourceCtx)
        (source := source) (target := target))
    {afterState : AllocationLowering.State}
    {afterLocals : Locals.Ctx}
    {headCode : List Expressions.Stmt}
    (tail :
      AllocationObserverForward.BodyCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hHead :
      ResourceControlledHeadResult cursor hBoundary afterState afterLocals
        headCode tail
        (resource := resource) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (finalCtx := headCtx)
        (source := source) (target := target)
        (sourceOutcome := headSourceOutcome))
    (hTail :
      ∀ {sourceMid :
            Functions.ObserverSemantics.State transcript}
        {targetMid : Structured.ObserverSemantics.State transcript}
        {midMode : ActivationMode},
        AllocationObserverStatement.Sequence.RegularStmtResourceInvariantForward
            program.memoryContract resource allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            (Functions.Scope.Stmt.outEnv live stmt) frameBase mode midMode
            program sourceCtx stmt source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceMid targetMid headCtx →
        AllocationObserverOutcome.SameControl sourceCtx headCtx →
        ∀ hTailBoundary :
            ResourceBoundary tail
              (resource := resource) (allocatorDepth := allocatorDepth)
              (frameBase := frameBase) (mode := midMode)
              (sourceCtx := headCtx) (source := sourceMid)
              (target := targetMid),
          ResourceBlockResult tail hTailBoundary
            (resource := resource) (allocatorDepth := allocatorDepth)
            (frameBase := frameBase) (mode := midMode)
            (sourceCtx := headCtx) (finalCtx := blockCtx)
            (source := sourceMid) (target := targetMid)
            (sourceOutcome := blockSourceOutcome))
    (hAbrupt :
      headSourceOutcome.mode ≠ .regular →
        blockSourceOutcome = headSourceOutcome ∧ blockCtx = sourceCtx) :
    ResourceBlockResult cursor hBoundary
      (resource := resource) (allocatorDepth := allocatorDepth)
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
          AllocationObserverContext.ActivationResourceInvariant
            resource program.memoryContract allocatorDepth root.lowerCtx
            afterState afterLocals tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase midMode sourceMid targetMid := by
        rw [hHead.head.tailPlan]
        exact hInvariant
      let hTailBoundary :
          ResourceBoundary tail
            (resource := resource) (allocatorDepth := allocatorDepth)
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
          ResourceControlOutcomeForward cursor hBoundary blockSourceOutcome
            tailTargetOutcome := by
        exact
          ResourceControlOutcomeForward.of_afterRegular cursor tail hBoundary
            rfl (hHead.head.regularTransport rfl) hControl hSameFrame
            (hHead.head.regularScope rfl) hTarget hTailInvariant hTailControl
      exact
        { runtime :=
            ⟨tailTargetOutcome,
              cursor.consRegularResourceResult tail hHead.head.tailPlan
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
        AllocationObserverOutcome.NonregularStmtResourceForward.reindex_regularLive
          (afterLive :=
            Functions.Scope.Block.outEnv live { stmts := stmt :: rest })
          hForwardCopy
      exact
        { runtime :=
            ⟨headTargetOutcome,
              cursor.consNonregularResourceResult hHead.head.compiled
                hForwardFinal,
              hHeadControl⟩
          regularScope := fun hRegular =>
            False.elim (hMode hRegular) }

end ResourceBoundary
end BodyCursor

end AllocationObserverDispatcher
end Functions
end EvmCompiler
