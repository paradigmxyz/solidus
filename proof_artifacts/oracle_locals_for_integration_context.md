# Oracle Context: Locals `for` Integration Boundary

We are building a Lean verified compiler tower in `/Users/dan/Projects/evm-compiler`.
The current active repair is the locals abstraction boundary:

`Locals.Source` is a stack-free named-environment interpreter. `Locals.Direct`
is the lower stack/layout backend. `EvmCompiler/Locals/SourceLowering.lean`
owns the relation and proofs between them.

The immediate goal is to integrate `Stmt.for_` into the recursive structural
locals theorem:

```lean
EvmCompiler.Locals.SourceLowering.Structural.stmtRunBridgeAt_of_source_run
```

The currently checked standalone loop theorem is:

```lean
theorem runForLoopBridgeAt_of_source_run
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceLoopCtx : Source.Ctx}
    {targetLoopCtx : Ctx} {cond : Expr 1} {post body : Block}
    {fuel : Nat} {source sourceAfter : Source.State}
    {target : RunState} {sourceOutcome : Source.Outcome}
    (hCondScoped : Scope.ExprScoped sourceLoopCtx.scope cond)
    (hCondAccess : Access.ExprBound sourceLoopCtx.scope 0 cond)
    (hPostLower : BlockLowerable sourceLoopCtx.scope post)
    (hBodyLower : BlockLowerable sourceLoopCtx.scope body)
    (hEntryLeave : entryCtx.leaveScope? = sourceLoopCtx.leaveScope?)
    (hCtx : CtxRel sourceLoopCtx targetLoopCtx)
    (hHandlers : CtxHandlersRel sourceLoopCtx targetLoopCtx)
    (hNoDup : sourceLoopCtx.scope.Nodup)
    (hRel : StateRel sourceLoopCtx.scope source target)
    (hSourceRun :
      Source.Stmt.runForLoop prim program sourceLoopCtx cond
          sourceLoopCtx.withoutLoopControl post
          (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
            sourceLoopCtx.scope)
          body fuel source =
        .ok sourceOutcome) :
    ∃ targetOutcome : Outcome,
      Direct.Stmt.runForLoop program targetLoopCtx cond
          targetLoopCtx.withoutLoopControl post
          (targetLoopCtx.withLoopControl targetLoopCtx.layout.length) body
          fuel target =
        .ok targetOutcome ∧
      ScopedOutcomeRelAt entryCtx sourceLoopCtx.scope sourceOutcome
        targetOutcome
```

This theorem is green. It uses only leave-scope agreement between `entryCtx`
and `sourceLoopCtx`, not full break/continue/leave equality, because loop init
runs under `withoutLoopControl`.

The recursive theorem family currently looks like:

```lean
mutual
  theorem blockOpenRunBridgeAt_of_source_run ...
  theorem stmtListOpenRunBridgeAt_of_source_run ...
  theorem stmtRunBridgeAt_of_source_run ...
end
```

and `StmtLowerable` currently keeps `for` out:

```lean
def StmtLowerable (env : List Name) : Stmt → Prop
  ...
  | .for_ _init _cond _post _body => False
```

The intended `for` lowerability shape is:

```lean
| .for_ init cond post body =>
    BlockLowerable env init ∧
      let loopEnv := Scope.Block.outEnv env init
      Scope.ExprScoped loopEnv cond ∧
        Access.ExprBound loopEnv 0 cond ∧
          BlockLowerable loopEnv post ∧ BlockLowerable loopEnv body
```

The intended proof outline for the `for` statement case is:

1. Run `init` under `sourceCtx.withoutLoopControl` and
   `targetCtx.withoutLoopControl`.
2. If init is regular, use `Source.Block.runOpen_regular_scope` to identify
   `sourceLoopCtx.scope = Scope.Block.outEnv sourceCtx.scope init`.
3. Use `blockLowerable_regular_handlerScopesEq` to show init regular preserves
   leave scope, then combine with `hEntryHandlers` to get
   `entryCtx.leaveScope? = sourceLoopCtx.leaveScope?`.
4. Apply the checked `runForLoopBridgeAt_of_source_run`.
5. For regular loop outcome, clean the direct target from the init/loop layout
   back to `sourceCtx.scope` using `StateRel.cleanupTo_scope_exists`.
6. For loop leave/halt, return the same abrupt outcome at the outer context.
7. Init break/continue are invalid because init runs under `withoutLoopControl`.
   Init leave/halt pass through to the outer context.

What failed:

1. If I move `runForLoopBridgeAt_of_source_run` into the mutual family so the
   statement theorem can call it, Lean reports mutual termination trouble. The
   intuitive measure is fuel-first, then syntax size, but I did not yet install
   a robust `termination_by`/`decreasing_by` for the four-theorem family.

2. If I keep the loop theorem outside the mutual family and parameterize it by
   a generic block-bridge argument, then instantiate that argument inside the
   statement theorem with a lambda calling `blockOpenRunBridgeAt_of_source_run`,
   Lean's termination checker sees a recursive call hidden inside a generic
   lambda and cannot prove the fuel decrease.

Constraints:

- No `sorry`, no new axioms, no public replay/certificate assumption.
- We want a compositional theorem boundary, not a fused special case.
- The source locals semantics must stay stack-free. Stack cleanup belongs only
  in `SourceLowering.lean`.
- It is acceptable to introduce a small auxiliary relation/theorem interface if
  it avoids hiding recursive calls from Lean.

Question:

What is the cleanest Lean architecture for integrating the `for` case into the
recursive structural theorem? In particular, should we:

1. Add `runForLoopBridgeAt_of_source_run` as a fourth theorem in the mutual
   family with explicit fuel/syntax `termination_by`, and if so what exact
   measure shape is likely to work?
2. Keep the loop theorem outside the mutual family, but replace the generic
   block-bridge lambda with a fuel-indexed bridge interface that Lean can accept?
3. Split the recursive theorem family by fuel first, or define a single
   fuel-indexed structural theorem over an explicit syntax sum to make the
   decrease obvious?

Useful failure would be a clear rejection of one route and a smaller theorem
interface that avoids both Lean blowup and hidden recursive calls.
