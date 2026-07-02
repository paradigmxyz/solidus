We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: finish the whole generated `for` inside hidden-context sequence proof in
`EvmCompiler/Yul/RecursiveBridgeSupport.lean`, without weakening statements and
without adding axioms/sorry/admit.

Namespace:

```
EvmCompiler.Yul.Reference.SourceBridgeFacts
```

The current module should build with:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

Main public theorem to add/prove:

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

Keep the same public intent if an exact existing name/fuel index needs a tiny
adjustment: source-visible `layout` unchanged across the `for` head, tail at
the same visible `layout`, hidden target contexts allowed, and no exact-scope
premise such as `ctx.scope = layout`.

Current proof boundary:

- Exact-scope generated-for wrappers are the wrong route because they require
  `ctx.scope = layout`.
- Hidden sequence uses `hScopeContains : ∀ name, name ∈ layout → name ∈ ctx.scope`.
- Generated loop body handlers run at `ctx.scope`, not `layout`.
- Internal body `break` and `continue` project only to the visible `layout`.
- `leave`, terminal halts, and errors still use the outer outcome relation.
- Do not expose generated loop branch obligations as public assumptions.

Already available compositional interfaces:

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
- `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches`
- `generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`
- `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_if_of_programAcceptedCondition_reserved`
- `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_switch_of_programAcceptedScrutinee_reserved`

New helpers already added and audited:

- `sourceForGeneratedBodyHaltStmtRunExists_of_eval_domain_nonzero_hidden_scope`
- `sourceNonregularStmtRunHiddenExact_for_generated_body_halt_exists_of_eval_domain_nonzero_hidden_scope`
- `sourceNonregularStmtRunHiddenExact_for_generated_body_halt_of_modeSound_hidden_scope`

Important current gap:

The post-halt branches still have fixed-`haltKind` hidden-scope lemmas:

- `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_eval_domain_nonzero_hidden_scope`
- `sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_halt_of_eval_domain_nonzero_hidden_scope`

Please first add existential variants and mode-facing wrappers analogous to the
body-halt helper, because `GeneratedForPostModeSound.halt` chooses
`∃ haltKind` from the actual post proof:

Suggested helper names:

```
sourceForGeneratedBodyRegularPostHaltStmtRunExists_of_eval_domain_nonzero_hidden_scope
sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_exists_of_eval_domain_nonzero_hidden_scope
sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_modeSound_hidden_scope

sourceForGeneratedBodyContinuePostHaltStmtRunExists_of_eval_domain_nonzero_hidden_scope
sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_halt_exists_of_eval_domain_nonzero_hidden_scope
sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_halt_of_modeSound_hidden_scope
```

The existential helpers should be straightforward copies of the existing
fixed-`haltKind` hidden-scope post-halt lemmas, with `haltKind` moved under the
post callback existential. Keep them private/nonpublic if convenient, but audit
the final public theorem.

After those helpers, build:

1. A hidden-context branch-contract theorem from mode contracts, e.g.

```
generatedForLoopNonrecursiveBranchContracts_of_hiddenCtx_modeSound
```

or directly a `GeneratedForLoopBranchContracts` value for the generated `for`.
It should fill:

- `bodyError` with `sourceNonregularStmtRunHiddenExact_for_generated_body_halt_of_modeSound_hidden_scope`
- `bodyBreak` with the existing hidden body-break lemma plus `hBodyMode.brk`
- `bodyLeave` with the existing hidden body-leave lemma plus `hBodyMode.leave`
- `postError` with the new post-halt existential mode wrappers for body-regular
  and body-continue
- `postLeave` with the existing post-leave hidden lemmas and
  `GeneratedForPostModeSound.leaveBlockSound`
- `postRegular` with
  `generatedForLoopPostRegularBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`
  and body regular/continue plus post regular mode facts.

2. Then prove the public hidden-sequence constructor by mirroring the existing
`if :: rest` and `switch :: rest` constructors:

- split on `tailFuel`;
- zero case uses
  `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_one`;
- productive case uses
  `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular`;
- decompose the lowered head with
  `BridgeFacts.toFunctionsListFuel?_for_components`;
- package `pieces : GeneratedForCompiled reserved layout cond post body`;
- derive accepted facts from `hSafeFor`, `hScopedFor`, `hStmtOkFor`,
  `hSourceScopedFor`;
- derive condition terminal/sound/domain facts using the same machinery as the
  existing switch/if hidden constructors and old generated-for wrappers:
  `sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_of_argRegularAllCheckedAt`,
  `lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt`,
  `eval_ok_domain_exact_of_safe_primitiveFamilies`, `hRecursive.args`,
  `hPrimSound`, and `hResultOk`;
- build body/post mode contracts from `hRecursive.hiddenBlock` under the
  generated contexts, not through exact-scope wrappers;
- feed branch contracts into
  `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches`;
- fold the head into the tail using the generic hidden-sequence cons theorem.

Constraints:

- Do not introduce `ctx.scope = layout` or any equivalent exact-scope premise.
- Do not introduce axioms, `sorry`, or `admit`.
- Do not weaken theorem statements.
- Prefer small compositional helper lemmas over one giant proof term.
- Any Aristotle output must still pass local Lean and axiom audit here.

Validation command:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```
