# Oracle request: reserved-name recursive bridge architecture

Project: `/Users/dan/Projects/evm-compiler`

Validation command for the current checkpoint:

```bash
lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

Current build status: green before this request.

## Goal

We are proving an end-to-end verified compiler bridge from Nethermind-style Yul
source semantics to our compiler tower and ultimately to gas-aware EVM.  The
current blocker is the recursive successor theorem for the Yul bridge.  We need
to finish the source-fuel induction without a caller-supplied recursive/callee
oracle.

The immediate proof target is the accepted-program recursive bridge successor.
The hard frontier is the statement-list dispatcher over `execSeq`, especially
because declarations/fresh names require a `reserved` source-name invariant.

Please do a top-down architectural critique and propose the proof structure.
The question is not just "which Lean tactic"; it is whether the recursive bridge
and dispatcher-facing wrapper APIs should be reservation-aware everywhere, or
whether this should be split differently.

## Important definitions

In `EvmCompiler/Yul/RecursiveBridgeSupport.lean`:

```lean
def SourceNamesReserved (reserved names : List Name) : Prop :=
  ∀ name, name ∈ names → name ∈ reserved
```

There are two accepted recursive bridge structures:

```lean
structure ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames
  ... (bound : Nat) : Prop where
  stmt :
    ∀ {reserved layout outcomeLayout : List Name} ... {sourceStmt : AstStmt} ...,
      Safe.stmt sourceStmt →
      ControlFlow.ScopedStmt canBreak canContinue canLeave sourceStmt →
      UserCallArity.StmtOk yulProgram.contract sourceStmt →
      SourceLexical.StmtScoped layout sourceStmt →
      (∀ {sourceResult}, allowed sourceResult → SourceResultRelatable sourceResult) →
      (∀ {sourceResult}, allowed sourceResult →
        SourceResultOutcomeLayoutCompatible ctx layout outcomeLayout sourceResult) →
      sourceFuel ≤ bound →
      ctx.scope = layout →
      CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact cfg reserved layout ...

  block / hiddenBlock / hiddenModeBlock / args : ...
```

and the newer reservation-aware variant:

```lean
structure ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
  ... (bound : Nat) : Prop where
  stmt :
    ∀ {reserved layout outcomeLayout : List Name} ... {sourceStmt : AstStmt} ...,
      Safe.stmt sourceStmt →
      ControlFlow.ScopedStmt canBreak canContinue canLeave sourceStmt →
      UserCallArity.StmtOk yulProgram.contract sourceStmt →
      SourceLexical.StmtScoped layout sourceStmt →
      SourceNamesReserved reserved (Stmt.names sourceStmt) →
      (∀ {sourceResult}, allowed sourceResult → SourceResultRelatable sourceResult) →
      (∀ {sourceResult}, allowed sourceResult →
        SourceResultOutcomeLayoutCompatible ctx layout outcomeLayout sourceResult) →
      sourceFuel ≤ bound →
      ctx.scope = layout →
      CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact cfg reserved layout ...

  block / hiddenBlock / hiddenModeBlock also take
      SourceNamesReserved reserved (Stmt.List.names sourceStmts)

  args :
    ∀ {reserved layout : List Name} {sourceFuel : Nat},
      sourceFuel ≤ bound →
      SourceArgListPreludeRegularAllCheckedAt cfg layout prim program
        yulProgram.contract (reserved ++ layout) sourceFuel
```

There is a one-way embedding:

```lean
theorem ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.of_unreserved :
  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames ... bound →
  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved ... bound
```

There is intentionally no general projection from reserved to unreserved,
because the unreserved bridge must work for arbitrary `reserved`, while the
reserved bridge only works when `SourceNamesReserved reserved ...` is supplied.

## Current successor handoff

The exact theorem we want to feed is:

```lean
theorem ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
    .succ_of_hiddenCtxSeq_frontier_fields_supported
    (hRecursive :
      ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved ...
        bound)
    (hStmt :
      ∀ ... sourceStmt ...,
        Safe.stmt sourceStmt →
        ControlFlow.ScopedStmt ... sourceStmt →
        UserCallArity.StmtOk yulProgram.contract sourceStmt →
        SourceLexical.StmtScoped layout sourceStmt →
        SourceNamesReserved reserved (Stmt.names sourceStmt) →
        ... →
        CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact ... bound.succ ...)
    (hSeq :
      ∀ ... sourceStmts ...,
        Safe.stmts sourceStmts →
        ControlFlow.ScopedStmts ... sourceStmts →
        UserCallArity.StmtsOk yulProgram.contract sourceStmts →
        SourceLexical.StmtsScoped layout sourceStmts →
        SourceNamesReserved reserved (Stmt.List.names sourceStmts) →
        ... SourceResultOutcomeLayoutSupported ... →
        CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx
          ... bound compileFuel sourceStmts ...)
    (hHiddenModeBlock : ...)
    (hArgs : ...)
  : ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved ...
      bound.succ
```

So the main missing ingredient is an `hSeq` dispatcher by induction/cases on
`sourceStmts`, at source fuel `bound`, using the previous recursive bridge
`hRecursive` for subcalls.

## Work already build-checked

Many head cases are proved:

- simple heads: break/continue/leave, assignment literal/variable,
  generated let none/literal/variable;
- arbitrary uninitialized declaration list heads (`let x, y`);
- primitive expression/assignment/generated-let heads, including low-fuel
  out-of-fuel branches;
- structured block/if/switch/for head wrappers;
- user-call expression/assignment/generated-let hidden-head theorems migrated
  internally to the reserved recursive bridge;
- callee-body lookup/freshness and return/halt reconstruction on the reserved
  bridge.

However, several dispatcher-facing wrappers are still named
`..._reserved_supported` while their `hRecursive` argument is the older
non-reserved bridge:

```text
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_programAcceptedLoop_reserved_supported
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_block_of_programAcceptedBody_reserved_supported
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_user_call_of_programAccepted_reserved_supported
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_user_call_of_programAccepted_reserved_supported
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_user_call_of_programAccepted_reserved_supported
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_if_of_programAcceptedCondition_reserved_supported
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_switch_of_programAcceptedScrutinee_reserved_supported
```

The core user-call hidden-head theorem signatures now take
`ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved`, but
their outer supported sequence wrappers still often take the older bridge.

## Failed attempt

I tried a broad signature flip: change all the dispatcher-facing
`...reserved_supported` wrappers to take the reserved bridge.  This produced
many Lean type mismatches because lower helper APIs still expected the older
non-reserved bridge, including:

- `sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_of_argRegularAllCheckedAt`
- `lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt`
- `generatedForLoopBranchContracts_of_programAccepted_hiddenMode`
- `generatedForLoopPostRegularOkBranchContract_of_programAccepted_hiddenMode`
- `sourceArgListPreludeTerminalAt_of_programAccepted_checkedArgs`
- and some old wrappers that explicitly call `.of_unreserved hRecursive`.

This showed that simply "make everything reserved" is not a local edit unless
we also migrate or split many lower helper APIs.

## Architectural question

What is the right top-down architecture?

Options I see:

1. Make the whole accepted recursive bridge reservation-aware and migrate all
   helper APIs that consume recursive bridge evidence to the reserved variant.
   This seems semantically clean but risks a large proof churn.

2. Keep the old non-reserved bridge as the induction hypothesis and embed it
   into reserved via `of_unreserved` when needed.  This seems too strong or
   possibly unprovable for declarations, because the final public theorem is
   specifically trying to avoid requiring arbitrary fresh-name reservations.

3. Keep both, but create a small reserved-compatible dispatcher facade: each
   head wrapper takes the reserved bridge plus only the local
   `SourceNamesReserved` facts it needs, while legacy lower helper APIs stay
   non-reserved until truly needed.  This was my current intended path, but I
   want critique before continuing.

4. Refactor the bridge invariant: instead of two structures, make one bridge
   parameterized by a "reservation policy" or by local `SourceNamesReserved`
   predicates.  This might be cleaner but could be too disruptive.

Please answer:

- Which option is architecturally right for a verified compiler proof?
- Should `SourceNamesReserved` live in the recursive bridge fields, in the
  lowering soundness theorem, in the statement-list dispatcher only, or in a
  bundled compile context?
- Is it valid to try to prove the final recursive successor from an unreserved
  bridge and then embed into reserved, or does that smuggle in the wrong
  invariant?
- What precise theorem/interface should the statement-list dispatcher expose?
- What is the smallest sequence of Lean proof moves likely to finish this
  successor theorem without another broad failing rewrite?
- Are there signs that the abstraction boundary is wrong and should move
  lower/higher in the compiler tower?

Constraints:

- No `sorry`, `admit`, new axioms, or weakened public theorem.
- Public theorem must not take a caller-supplied recursive/callee oracle.
- Compiler-generated evidence must be discharged, not exposed as assumptions.
- Keep source semantics independent; do not turn the source layer into
  "compile then run lower layer."
- Prefer compositional helpers over one-off giant case proofs.

