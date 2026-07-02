We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: finish the generated `for` inside hidden-context sequence proof in
`EvmCompiler/Yul/RecursiveBridgeSupport.lean`, without weakening statements and
without adding axioms/sorry/admit.

Namespace:

```
EvmCompiler.Yul.Reference.SourceBridgeFacts
```

Validation command:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

Current state:

The module builds locally.  The hidden generated-`for` proof has most branch
contracts, mode-facing adapters, and the lowering/list plumbing theorem.  The
current semantic blocker is the post-regular recursive-loop branch when the
`for` statement is the head of a larger hidden sequence.

Important semantic issue:

`GeneratedForLoopPostRegularBranchContract` currently requires
`allowedInner loopResult`.  That is fine for singleton generated-`for`, but it
is too strong for a sequence `(.For cond post body) :: rest`.

If the recursive loop result is regular:

```
EvmYul.Yul.exec sourceFuel (.For cond post body) codeOverride
  (.Ok sharedAfterPost storeAfterPost) =
    .ok (.Ok sharedLoop storeLoop)
```

then that regular loop state is only an intermediate state.  The surrounding
sequence's `allowed` predicate applies to the result after running `rest`, not
to this intermediate loop result.  So the regular recursive-loop case must
prove a regular head without requiring outer `allowed` or
`SourceResultOutcomeLayoutCompatible`.

If the recursive loop result is nonregular, the tail is skipped and the final
sequence result is exactly the loop result, so the existing outer `allowed` /
compatibility path is still appropriate.

Already added definition:

```
def GeneratedForLoopPostRegularOkBranchContract
    (cfg : StateRelConfig) (layout : List Name)
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (sourceFuel : Nat) (cond : AstExpr) (post body : List AstStmt)
    (codeOverride : Option AstContract) (reserved : List Name)
    (pieces : GeneratedForCompiled reserved layout cond post body) : Prop := ...
```

This is the regular-only sibling of
`GeneratedForLoopPostRegularBranchContract`; it has no `allowedInner` argument.

Please add and prove compositional helper theorems around this definition.
Suggested theorem names:

```
generatedForLoopPostRegularOkBranchContract_of_hiddenCtx_callbacks_and_loop
generatedForLoopPostRegularOkBranchContract_of_hiddenCtx_callbacks_and_hidden_loop
generatedForLoopPostRegularOkBranchContract_of_hiddenCtx_modeSound_and_hidden_loop
```

They should mirror the regular branches of the existing theorems:

```
generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_loop
generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop
generatedForLoopPostRegularBranchContract_of_hiddenCtx_modeSound_and_hidden_loop
```

The first theorem should take essentially these inputs:

- `hScopeContains`
- `hPrim`
- `hCondSound`
- `hEvalDomain`
- `hBodyDomainOk`
- `hBodyDomainContinue`
- `hPostDomainOk`
- `hBodyRegular`
- `hBodyContinue`
- `hPostRegular`
- `hLoopRegular`

and no `allowedInner`/compat premises.  Its proof should case split on
`bodyWasContinue` and use:

```
sourceRegularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero_hidden_scope
sourceRegularStmtRunHiddenExact_for_generated_body_continue_post_regular_of_eval_domain_nonzero_hidden_scope
```

The hidden-loop wrapper should copy only the regular-loop half of
`generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`:

- define `allowedLoop` as equality to the restricted regular loop state;
- prove relatable/compatible at `layout`;
- obtain the singleton hidden block theorem from `hLoopBlock`;
- use `sourceRegularStmtRunHiddenExact_for_of_singleton_hiddenBlockSound_ok`;
- finish with `sourceRegularGeneratedForLoopStmtRun_of_hiddenExact_singleton`.

Next target:

Prove a semantic head theorem for a hidden sequence head
`(.For cond post body) :: rest` that consumes:

- existing nonrecursive generated-loop branch contracts,
- existing `GeneratedForLoopPostRegularBranchContract` for nonregular
  recursive-loop results,
- new `GeneratedForLoopPostRegularOkBranchContract` for regular recursive-loop
  results.

Suggested theorem shape:

```
theorem sourceResultSeqSoundWhenAtExactHiddenCtx_cons_for_head_of_split_branch_contracts
    ... :
    SourceStateExactRel cfg layout source compiler ->
    allowed sourceResult ->
    EvmYul.Yul.execSeq sourceFuel.succ
      (.For cond post body :: rest) codeOverride source = sourceResult ->
    SourceRegularStmtRunHiddenExact cfg layout layout prim program ctx
      sourceFuel (.For cond post body) codeOverride source compiler
      (generatedForLowerBlock pieces.preCond pieces.lowerCond
        pieces.lowerPost pieces.lowerBody) ∨
    SourceNonregularStmtRunHiddenExact cfg layout outcomeLayout terminalRel
      revertRel prim program ctx sourceFuel (.For cond post body)
      codeOverride source compiler
      (generatedForLowerBlock pieces.preCond pieces.lowerCond
        pieces.lowerPost pieces.lowerBody)
```

The exact theorem name/parameters can be adjusted to fit the file, but the key
proof split must be:

- regular recursive loop result: use
  `GeneratedForLoopPostRegularOkBranchContract`, no `allowed`/compat for the
  intermediate loop result;
- nonregular recursive loop result: use
  `GeneratedForLoopPostRegularBranchContract`, with the outer final sequence
  `allowed`/compat.

Then plug the semantic head theorem into the already-proved lowering/list
plumbing theorem:

```
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_generated_head_reserved
```

and finally add/prove the public reservation-aware hidden sequence constructor:

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

If an exact fuel index needs a tiny adjustment to match existing constructors,
preserve the public intent: source-visible `layout` unchanged across the `for`
head, tail at the same visible `layout`, hidden target contexts allowed, and no
exact-scope premise such as `ctx.scope = layout`.

Existing useful theorems in the file:

- `GeneratedForBodyModeSound`
- `GeneratedForPostModeSound`
- `GeneratedForLoopNonrecursiveBranchContracts`
- `GeneratedForLoopBranchContracts`
- `generatedForLoopNonrecursiveBranchContracts_of_hiddenCtx_modeSound`
- `generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_loop`
- `generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`
- `generatedForLoopPostRegularBranchContract_of_hiddenCtx_modeSound_and_hidden_loop`
- `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches`
- `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_branch_contracts`
- `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_generated_head_reserved`
- hidden `if :: rest` and `switch :: rest` constructors, which are good models
  for the final public `for :: rest` constructor.

Constraints:

- Do not introduce `ctx.scope = layout` or any equivalent exact-scope premise.
- Do not introduce axioms, `sorry`, or `admit`.
- Do not weaken theorem statements.
- Prefer small compositional helper lemmas over one giant proof term.
- Do not solve the regular recursive-loop case by asking the outer `allowed`
  predicate to accept the intermediate loop state.
- Any Aristotle output must still pass local Lean and axiom audit here.
