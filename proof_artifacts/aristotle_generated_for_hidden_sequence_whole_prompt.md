We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: prove the whole generated `for` inside hidden-sequence bridge in
`EvmCompiler/Yul/RecursiveBridgeSupport.lean`, without weakening statements and
without adding axioms/sorry/admit.

Namespace:

```
EvmCompiler.Yul.Reference.SourceBridgeFacts
```

The current module builds with:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

The immediate missing public theorem is the reservation-aware hidden-context
sequence constructor for a source `for :: rest`.  Please add and prove it, plus
any small private/compositional helper lemmas needed:

```
theorem checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_programAcceptedLoop_reserved
    {cfg : StateRelConfig} {reserved layout outcomeLayout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {yulProgram : Program} {program : Functions.Program}
    {context : ProgramBridgeContext yulProgram program} {bound tailFuel : Nat}
    {ctx : Functions.Source.Ctx}
    {cond : AstExpr} {post body rest : List AstStmt}
    {allowed : Except Exception State → Prop}
    {canBreak canContinue canLeave : Bool}
    (hRecursive :
      ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames cfg
        terminalRel revertRel prim yulProgram program context bound)
    (hFuel : tailFuel ≤ bound)
    (hSafeFor : Safe.stmt (.For cond post body))
    (hScopedFor :
      ControlFlow.ScopedStmt canBreak canContinue canLeave
        (.For cond post body))
    (hStmtOkFor :
      UserCallArity.StmtOk yulProgram.contract (.For cond post body))
    (hSourceScopedFor :
      SourceLexical.StmtScoped layout (.For cond post body))
    (hReservedFor :
      SourceNamesReserved reserved (Stmt.names (.For cond post body)))
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hCompat :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultOutcomeLayoutCompatible ctx layout outcomeLayout
          sourceResult)
    (hScopeContains : ∀ name : Name, name ∈ layout → name ∈ ctx.scope)
    (hPrimSound :
      ∀ {fuel : Nat} {yulPrim : EvmYul.Operation .Yul}
        {op : Structured.BasicOp},
        fuel < bound.succ →
        Safe.primitive yulPrim →
        Prim.toBasicOp? yulPrim = some op →
        Expressions.Structured.BasicOp.outputs op = 1 →
        PrimitiveStackSoundAt cfg layout prim fuel yulPrim op)
    (hResultOk :
      ∀ {fuel : Nat} {expr : AstExpr},
        fuel < bound.succ →
        Safe.expr expr →
        SourceExprScoped layout expr →
        UserCallArity.ExprOk yulProgram.contract expr →
        ExprEvalResultOkAt cfg layout fuel expr
          (some yulProgram.contract))
    (hTail :
      ∀ {compileFuel : Nat} {ctxMid : Functions.Source.Ctx},
        CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx cfg
          reserved layout outcomeLayout terminalRel revertRel prim program
          ctxMid tailFuel compileFuel rest (some yulProgram.contract)
          allowed) :
    ∀ {compileFuel : Nat},
      CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx cfg
        reserved layout outcomeLayout terminalRel revertRel prim program ctx
        tailFuel.succ compileFuel (.For cond post body :: rest)
        (some yulProgram.contract) allowed
```

If the exact theorem needs a small fuel-index adjustment to match the existing
hidden sequence constructors, keep the same public intent: source-visible
`layout` unchanged across the `for` head, tail at the same visible `layout`,
hidden target contexts allowed, and no exact-scope premise such as
`ctx.scope = layout`.

Current useful definitions and theorems already in the file:

- `GeneratedForBodyModeSound`
- `GeneratedForPostModeSound`
- `GeneratedForBodyModeSound.regularBlockSound`
- `GeneratedForBodyModeSound.breakBlockSound`
- `GeneratedForBodyModeSound.continueBlockSound`
- `GeneratedForBodyModeSound.leaveBlockSound`
- `GeneratedForBodyModeSound.haltBlockSound`
- `GeneratedForPostModeSound.regularBlockSound`
- `GeneratedForPostModeSound.leaveBlockSound`
- `GeneratedForPostModeSound.haltBlockSound`
- `GeneratedForLoopBranchContracts`
- `generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_loop`
- `generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`
- `generatedForLoopBranchContracts_of_nonrecursive_and_postRegular`
- `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches`
- `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_if_of_programAcceptedCondition_reserved`
- `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_switch_of_programAcceptedScrutinee_reserved`

Important background:

- The old exact-scope `for` wrappers require `ctx.scope = layout`.  Do NOT use
  that route for the hidden sequence theorem.
- In hidden sequence proofs, source-visible state is related at `layout`, while
  the target context may have a larger hidden scope.  Use
  `hScopeContains : ∀ name, name ∈ layout → name ∈ ctx.scope`.
- Generated loop bodies run with hidden loop handlers at `ctx.scope`.
  Therefore internal body `break` and `continue` should project only to the
  visible `layout`; they should not be forced through
  `SourceResultOutcomeLayoutCompatible`.
- `leave`, terminal halts, and errors still use the outer outcome relation.
- The mode-facing structures above were introduced exactly to express this
  boundary compositionally.

Suggested proof architecture / PROVIDED SOLUTION:

1. Follow the structure of the existing hidden sequence constructors for
   `if :: rest` and `switch :: rest`.

   - Case split on `tailFuel`.
   - The zero tail case should use
     `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_one`.
   - The productive case should use
     `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular`.
   - The tail-cover proof should be
     `freshCoversLayout_toFunctionsListFuel?_of_some`, because `for` adds no
     source-visible locals.

2. Decompose the lowered head with:

```
BridgeFacts.toFunctionsListFuel?_for_components
```

   and package the decomposition as:

```
let pieces : GeneratedForCompiled reserved layout cond post body := ...
```

3. Derive the usual structural facts from the accepted source statement:

```
hSafeCond      : Safe.expr cond
hSafePost      : Safe.stmts post
hSafeBody      : Safe.stmts body
hScopedPost    : ControlFlow.ScopedStmts false false canLeave post
hScopedBody    : ControlFlow.ScopedStmts true true canLeave body
hCondOk        : UserCallArity.ExprOk yulProgram.contract cond
hPostOk        : UserCallArity.StmtsOk yulProgram.contract post
hBodyOk        : UserCallArity.StmtsOk yulProgram.contract body
hCondScoped    : SourceExprScoped layout cond
hSourcePostScoped : SourceLexical.StmtsScoped layout post
hSourceBodyScoped : SourceLexical.StmtsScoped layout body
```

4. Derive condition facts as in the existing source-facing `for` wrappers and
   hidden `if`/`switch` constructors:

```
sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_of_argRegularAllCheckedAt
lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt
eval_ok_domain_exact_of_safe_primitiveFamilies
hRecursive.args
hPrimSound
hResultOk
```

   The fuel offsets should mirror the existing singleton generated-for theorem
   and the old exact-scope wrapper.  It is better to introduce a tiny local
   helper for the fuel arithmetic than to duplicate a brittle proof many times.

5. Build body/post mode contracts from `hRecursive.hiddenBlock`, not from
   exact-scope wrappers.  For the body, use the generated hidden loop context:

```
ctx.withoutLoopControl.withLoopControl ctx.scope ctx.scope
```

   together with a `SourceCtxHandlersEq` fact for the actual context produced
   after compiling the prelude.  For the post block, use `ctx.withoutLoopControl`.

6. Convert those mode contracts into the branch callbacks needed by
   `GeneratedForLoopBranchContracts`:

   - body error: existing hidden body halt theorem plus
     `GeneratedForBodyModeSound.haltBlockSound`
   - body break: existing hidden body break theorem plus
     `GeneratedForBodyModeSound.breakBlockSound`
   - body leave: existing hidden body leave theorem plus
     `GeneratedForBodyModeSound.leaveBlockSound`
   - post error: existing regular/continue post halt theorem plus
     `GeneratedForPostModeSound.haltBlockSound`
   - post leave: existing regular/continue post leave theorem plus
     `GeneratedForPostModeSound.leaveBlockSound`
   - post regular recursion: use
     `generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`
     with body regular/continue and post regular mode facts, and recursive
     loop evidence from the hidden singleton theorem.

7. Feed the resulting `GeneratedForLoopBranchContracts` into the singleton
   generated-for dispatcher, then fold the head result into the tail with
   `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular`.

Constraints:

- Keep theorem statements unchanged unless a tiny fuel-index correction is
  required by existing definitions.
- Do not introduce axioms.
- Do not leave `sorry` or `admit`.
- Do not add a premise `ctx.scope = layout` or any equivalent exact-scope
  assumption.
- Do not expose generated callback obligations as public assumptions in this
  theorem.
- Prefer small compositional helper lemmas over one giant brittle term.
- Return a patch or complete replacement proof and explain the key dependencies.

Validation command:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

After integrating any proof, we will run `#print axioms`/grep checks and reject
any dependency on `sorryAx` or unexpected axioms.
