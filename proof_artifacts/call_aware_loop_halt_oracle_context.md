# Oracle Context: bounded switch-aware spill `for` loop halt helper

Repository: `/Users/dan/Projects/evm-compiler`
File: `EvmCompiler/Functions/CallAwareSpill.lean`

We are completing a verified spill-aware stack-too-deep fallback for imported Yul/Solidity. The runtime/main compiler path is smoke-green for Aave/Permit2; current remaining work is proof-spine completion in `Functions.CallAwareSpill`.

## Current proof state

Already committed:

- `SwitchFallbackStmtHaltSoundBelow` exists.
- Bounded halt block/list consumers exist:
  - `compileBlockOpenWithSwitchFallback?_halt_sound_meta_of_stmt_sound_below`
  - `compileBlockStmtWithSwitchFallback?_halt_sound_meta_of_stmt_sound_below`
- Bounded direct `for` halt branches exist and typecheck:
  - `compileForFallbackWithSwitchFallback?_halt_sound_meta_of_body_halt_stmt_sound_below`
  - `compileStmtWithSwitchFallback?_for_halt_sound_meta_of_source_body_halt_stmt_sound_below`
  - `compileForFallbackWithSwitchFallback?_halt_sound_meta_of_body_regular_post_halt_stmt_sound_below`
  - `compileStmtWithSwitchFallback?_for_halt_sound_meta_of_source_body_regular_post_halt_stmt_sound_below`
  - `compileForFallbackWithSwitchFallback?_halt_sound_meta_of_body_cont_post_halt_stmt_sound_below`
  - `compileStmtWithSwitchFallback?_for_halt_sound_meta_of_source_body_cont_post_halt_stmt_sound_below`

Focused Lean and module builds pass after these commits.

## Missing bottleneck

Need the recursive loop halt case: source `for` executes one iteration with body/post regular, then the recursive `Source.Stmt.runForLoop ... loopFuel sourceAfterPost` halts.

The existing regular recursive helper is:

```lean
theorem compileForFallbackWithSwitchFallback?_loop_regular_sound_meta_exact_of_stmt_sound_below
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {maxFuel : Nat}
    {range : ScratchRange} {program : Program}
    {handlers : FallbackHandlers} {returns : List Name}
    {cond : Expr 1} {post body : Block}
    {exprProgram : Expressions.Program} {initCtx : Source.Ctx}
    {initPlan : Plan} {condCode : Structured.Code}
    {postRaw postPlan bodyRaw bodyPlan : Plan}
    (hCondSafe : SourceNoMemoryTouch.expr? cond = true)
    (hCondCode :
      SpillExpr.compileCode? range 0 initPlan.layout cond = some condCode)
    (hPostCompile :
      compileBlockStmtWithSwitchFallback? range program
          handlers.withoutLoopControl returns initPlan.sourceScope []
          initPlan.layout post =
        some postRaw)
    (hPostNorm : normalizePlanStack? range postRaw = some postPlan)
    (hPostOk :
      postPlan.sourceScope = initPlan.sourceScope ∧
        postPlan.stackLayout = [] ∧ postPlan.layout = initPlan.layout)
    (hBodyCompile :
      compileBlockStmtWithSwitchFallback? range program
          (handlers.withLoopControl initPlan.sourceScope) returns
          initPlan.sourceScope [] initPlan.layout body =
        some bodyRaw)
    (hBodyNorm : normalizePlanStack? range bodyRaw = some bodyPlan)
    (hBodyOk :
      bodyPlan.sourceScope = initPlan.sourceScope ∧
        bodyPlan.stackLayout = [] ∧ bodyPlan.layout = initPlan.layout)
    (hInitCtxScope : initCtx.scope = initPlan.sourceScope) :
    ∀ {loopFuel : Nat} {source sourceAfterLoop : Source.State}
      {loopTarget : Expressions.RunState},
      Source.Stmt.runForLoop Locals.Source.PrimitiveSemantics.structured
          program initCtx cond initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope) body loopFuel
          source =
        .ok (Source.Outcome.regular sourceAfterLoop) →
      loopFuel ≤ maxFuel →
      SpillStateRel range initPlan.sourceScope [] initPlan.layout source
        loopTarget.evm →
      SpillLayout.StoreDefined source.vars initPlan.layout →
      loopTarget.evm.stack.length = ([] : List Name).length →
      SwitchFallbackStmtRegularSoundBelow maxFuel range program
        handlers.withoutLoopControl returns exprProgram →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtRegularSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtRegularReferenceSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtBrkReferenceSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtContReferenceSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      ∃ finalRunState exprFuel,
        Expressions.Stmt.runForLoop exprProgram exprFuel (.code condCode)
            postPlan.block bodyPlan.block loopTarget =
          .ok (Expressions.Outcome.regular finalRunState) ∧
        SpillStateRel range initPlan.sourceScope [] initPlan.layout
          sourceAfterLoop finalRunState.evm ∧
        SpillLayout.StoreDefined sourceAfterLoop.vars initPlan.layout ∧
        finalRunState.evm.stack.length = ([] : List Name).length
```

The proof is by recursion on `loopFuel`. In true branches it handles:

- body regular, post regular, recursive loop regular
- body cont, post regular, recursive loop regular
- body brk exits regular
- impossible modes by `simp`

It uses target composition lemmas:

```lean
theorem expressionsRunForLoop_true_bodyRegular_postRegular_loop_exists
    ... {outcome : Expressions.Outcome} ...
    (hLoop :
      Expressions.Stmt.runForLoop exprProgram loopFuel cond post body
          postState =
        .ok outcome) :
    ∃ forFuel,
      Expressions.Stmt.runForLoop exprProgram forFuel cond post body state =
        .ok outcome

theorem expressionsRunForLoop_true_bodyCont_postRegular_loop_exists
    ... {outcome : Expressions.Outcome} ...
```

These are outcome-polymorphic, so they can compose a recursive halt run too.

## Desired new theorem shape

We likely need:

```lean
theorem compileForFallbackWithSwitchFallback?_loop_halt_sound_meta_of_stmt_sound_below
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {maxFuel : Nat}
    ...same compile/normalization params as loop_regular...
    (hInitCtxScope : initCtx.scope = initPlan.sourceScope) :
    ∀ {loopFuel : Nat} {source sourceAfterLoop : Source.State}
      {loopTarget : Expressions.RunState} {kind : Assembly.HaltKind},
      Source.Stmt.runForLoop Locals.Source.PrimitiveSemantics.structured
          program initCtx cond initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope) body loopFuel
          source =
        .ok (Source.Outcome.halt kind sourceAfterLoop) →
      loopFuel ≤ maxFuel →
      SpillStateRel range initPlan.sourceScope [] initPlan.layout source
        loopTarget.evm →
      SpillLayout.StoreDefined source.vars initPlan.layout →
      loopTarget.evm.stack.length = ([] : List Name).length →
      SwitchFallbackStmtRegularSoundBelow maxFuel range program
        handlers.withoutLoopControl returns exprProgram →
      SwitchFallbackStmtHaltSoundBelow maxFuel range program
        handlers.withoutLoopControl returns exprProgram →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtRegularSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtHaltSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtRegularReferenceSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      (∀ {bodyHandlerScope : List Name},
        SwitchFallbackStmtContReferenceSoundBelow maxFuel range program
          (handlers.withLoopControl bodyHandlerScope) returns exprProgram) →
      ∃ haltTarget exprFuel,
        Expressions.Stmt.runForLoop exprProgram exprFuel (.code condCode)
            postPlan.block bodyPlan.block loopTarget =
          .ok (Expressions.Outcome.halt kind haltTarget) ∧
        SharedStateEqOutsideScratch range sourceAfterLoop.shared
          haltTarget.evm.toSharedState
```

Question: is this the right theorem boundary? In particular:

1. Should the helper take `bodyBrkReference` too, even though body break cannot produce source halt? Keeping it symmetric with `SwitchFallbackLoopStmtSoundBelow` may simplify package plumbing.
2. Should we instead generalize the existing regular helper to an outcome-indexed loop helper to avoid duplicating the induction? What would the relation/index look like in Lean so regular returns layout relation and halt returns shared-state equality without becoming too abstract?
3. For direct body-halt and post-halt branches inside this helper, should we call the existing block halt consumers directly, then use small target `simp`/composition, or route through the already-added outer `for` direct halt theorems?
4. What is the smallest proof/statement sequence that will let us thread `halt` into `SwitchFallbackStmtPackagesBelow` honestly?

Constraints:

- No `sorry`, no axioms.
- Prefer local proof bricks matching existing style.
- Main goal is proof honesty, not reducing code size at all costs.
- The final public-ish route should not expose generated dispatcher packages or call replay/bootstrap as raw assumptions forever; this helper is one step toward deriving them checked.
