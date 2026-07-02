We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: finish the generated `for` inside hidden-sequence proof in
`EvmCompiler/Yul/RecursiveBridgeSupport.lean`.

Please add and prove the missing reserved hidden-context sequence constructor
for a source `for :: tail`:

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

If the exact statement needs a small adjustment to fuel indexing so it composes
with the existing hidden-sequence frontier, keep the same public intent:
reservation-aware, hidden target context, source-visible layout unchanged,
tail receives the same visible `layout`, and all assumptions are acceptedness /
recursive-bridge assumptions rather than generated-loop callback assumptions.

Current status:

- The project currently builds with:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

- The immediate proof frontier is not an isolated source singleton statement.
  It is the nonempty hidden-context sequence case:

```
(.For cond post body) :: rest
```

  The generic sequence facade already exists:

```
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular
```

  It should be used the same way the existing hidden sequence constructors use
  it, especially:

```
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_if_of_programAcceptedCondition_reserved
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_switch_of_programAcceptedScrutinee_reserved
```

Important hidden generated-loop helpers already proved nearby:

```
GeneratedForLoopPostRegularBranchContract
generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_loop
generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop
sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches
sourceRegularGeneratedForLoopStmtRun_of_hiddenExact_singleton
sourceNonregularGeneratedForLoopStmtRun_of_hiddenExact_singleton
sourceRegularStmtRunHiddenExact_for_of_singleton_hiddenBlockSound_ok
sourceNonregularStmtRunHiddenExact_for_of_singleton_hiddenBlockSound
checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition_frontier
```

The new hidden-context theorem
`generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`
was added specifically to avoid the exact-scope bottleneck.  In this proof,
do not require `ctx.scope = layout`; use the premise:

```
hScopeContains : ∀ name, name ∈ layout → name ∈ ctx.scope
```

Key semantic shape:

- Source-visible state is related at `layout`.
- The compiled generated loop body may run under hidden break/continue handlers
  at the full `ctx.scope`.
- The recursive loop tail is the source `.For cond post body`, but the compiled
  loop is the generated lowered block:

```
generatedForLowerBlock pieces.preCond pieces.lowerCond
  pieces.lowerPost pieces.lowerBody
```

- `leave` remains a nonregular source result; terminal EVM/Yul builtins are
  represented through `terminalRel`/`revertRel`.
- Out-of-fuel source results are not relatable and should be eliminated using
  the existing `SourceResultRelatable` lemmas, not added as assumptions.

Likely proof strategy / PROVIDED SOLUTION:

1. Follow the structure of the existing `if :: tail` and `switch :: tail`
   constructors:
   - case split on `tailFuel`;
   - the zero case uses
     `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_one`;
   - the productive case invokes
     `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular`.

2. In `hTailCovers`, use:

```
freshCoversLayout_toFunctionsListFuel?_of_some
```

   because `for` does not add source-visible locals to the tail layout.

3. In `hHead`, decompose the compiler output with:

```
BridgeFacts.toFunctionsListFuel?_for_components
```

   then build the generated pieces:

```
let pieces : GeneratedForCompiled reserved layout cond post body := ...
```

4. Derive accepted facts exactly as in the source-facing for wrapper:

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

5. Derive condition terminal/soundness/result-domain facts from:

```
sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_of_argRegularAllCheckedAt
lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt
eval_ok_domain_exact_of_safe_primitiveFamilies
hRecursive.args
hPrimSound
hResultOk
```

   Be careful with fuel: mirror the offsets used by
   `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition`
   and the singleton sequence theorem
   `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches`.

6. Body and post block evidence should come from `hRecursive.hiddenBlock`.
   For body, compile/run under a context with hidden loop handlers:

```
ctxAfterPre
SourceCtxHandlersEq
  (ctx.withoutLoopControl.withLoopControl ctx.scope ctx.scope)
  ctxAfterPre
```

   For post, use `ctx.withoutLoopControl`.

7. The recursive loop callback for the post-regular branch should be discharged
   through:

```
generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop
```

   using a hidden singleton block proof from `hRecursive.hiddenBlock` for
   `[.For cond post body]` with the lowered generated block.

8. Finally feed the resulting head proof into
   `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular`
   and pass the tail unchanged:

```
fun {compileFuel ctxMid} =>
  hTail (compileFuel := compileFuel) (ctxMid := ctxMid)
```

Constraints:

- Do not introduce axioms.
- Do not use `sorry`, `admit`, or `unsafe`.
- Do not weaken public theorem statements.
- Avoid broad unfolding/simp that causes blowup; prefer the existing branch
  contracts and small local lemmas.
- Do not touch unrelated layers.
- If you add `#print axioms`, they should show only standard Lean axioms
  (`propext`, `Classical.choice`, `Quot.sound`) for the new theorem.

Validation command:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

If you export through `LayerAudit`, also validate:

```
/Users/dan/.elan/bin/lake build EvmCompiler.LayerAudit
```
