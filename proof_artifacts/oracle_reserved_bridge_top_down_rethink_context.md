# Top-down architecture question: reserved-name bridge for recursive Yul compiler proof

We are in the Lean project:

`/Users/dan/Projects/evm-compiler`

Main file:

`/Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean`

Validation command:

```bash
lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

The last focused build was green. The current bottleneck is not a syntax error; it is whether the remaining recursive successor proof is using the right invariant.

## Project goal

We are building a formally verified compiler tower:

Nethermind-style Yul semantics
  -> our stack-free Yul-ish source semantics
  -> objects/functions/locals/expressions/structured control
  -> typed/labeled assembly
  -> gas-aware EVM theorem

The immediate proof target is the recursive bridge from imported Yul runs to our source semantics for accepted programs. The recursive source feature is internal Yul/user functions: a source run of a call may execute a callee body, so the bridge is proved by induction on source fuel.

The public theorem must not take a caller-supplied “all callees preserve” oracle. We need to finish the successor step and then fuel induction.

## Current architecture

We have an older accepted recursive bridge:

```lean
structure ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames
    (cfg : StateRelConfig)
    (terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop)
    (revertRel : State -> Objects.Source.State -> Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (yulProgram : Program) (program : Functions.Program)
    (context : ProgramBridgeContext yulProgram program)
    (bound : Nat) : Prop
```

Its fields are `stmt`, `block`, `hiddenBlock`, `hiddenModeBlock`, and `args`.
Each statement/block field assumes accepted-source facts:

- `Safe`
- `ControlFlow.Scoped`
- `UserCallArity`
- `SourceLexical`
- source-result relatability/compatible outcome layout
- source fuel below `bound`

But the old bridge does not require source names to be in the compiler fresh-name reserved set.

We also added:

```lean
def SourceNamesReserved (reserved names : List Name) : Prop :=
  forall name, name ∈ names -> name ∈ reserved
```

Interpretation: all source names collected from a syntax fragment have been reserved in the fresh generator's hidden prefix, so generated temporaries cannot collide with future source declarations before those declarations are reached. This is intended as a compiler-hygiene invariant, not a source-semantics invariant.

Then we added a reservation-aware bridge:

```lean
structure ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
    ... (bound : Nat) : Prop where
  stmt :
    ... ->
    SourceNamesReserved reserved (Stmt.names sourceStmt) ->
    ... ->
    CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact ...
  block :
    ... ->
    SourceNamesReserved reserved (Stmt.List.names sourceStmts) ->
    ... ->
    CheckedBlockLoweringSoundWhenFreshNamesAtExact ...
  hiddenBlock :
    ... ->
    SourceNamesReserved reserved (Stmt.List.names sourceStmts) ->
    ... ->
    CheckedBlockLoweringSoundWhenFreshNamesAtCompileFuelHiddenScope ...
  hiddenModeBlock :
    ... ->
    SourceNamesReserved reserved (Stmt.List.names sourceStmts) ->
    ... ->
    CheckedHiddenBlockModeSoundWhenFreshNamesAtCompileFuelHiddenScope ...
  args :
    forall {reserved layout sourceFuel},
      sourceFuel <= bound ->
      SourceArgListPreludeRegularAllCheckedAt cfg layout prim program
        yulProgram.contract (reserved ++ layout) sourceFuel
```

The `args` field intentionally does not take `SourceNamesReserved`; expressions/argument lists do not declare source names. They still use `(reserved ++ layout)` as the compiler fresh-name prefix.

There is a coercion:

```lean
theorem ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.of_unreserved :
  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames ... bound ->
  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved ... bound
```

This works because the unreserved bridge is stronger. The reverse direction is not expected.

We also added a narrow capability view:

```lean
structure ProgramAcceptedRecursiveSourceBridgeCapabilitiesReserved ... where
  block : ...
  hiddenBlock : ...
  hiddenModeBlock : ...
  args : ...
```

and:

```lean
theorem ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.toCapabilities :
  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved ... bound ->
  ProgramAcceptedRecursiveSourceBridgeCapabilitiesReserved ... bound
```

The intent is that lower helpers should consume small capabilities, not always the whole bridge.

## Current successor handoff

The reservation-aware successor theorem already exists and is green:

```lean
theorem ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
  .succ_of_hiddenCtxSeq_frontier_fields_supported
    (hRecursive :
      ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
        ... bound)
    (hStmt : ... SourceNamesReserved reserved (Stmt.names sourceStmt) -> ...)
    (hSeq :
      forall {reserved layout outcomeLayout ctx compileFuel sourceStmts allowed
              canBreak canContinue canLeave},
        Safe.stmts sourceStmts ->
        ControlFlow.ScopedStmts canBreak canContinue canLeave sourceStmts ->
        UserCallArity.StmtsOk yulProgram.contract sourceStmts ->
        SourceLexical.StmtsScoped layout sourceStmts ->
        SourceNamesReserved reserved (Stmt.List.names sourceStmts) ->
        (forall {sourceResult}, allowed sourceResult ->
          SourceResultRelatable sourceResult) ->
        (forall {sourceResult}, allowed sourceResult ->
          SourceResultOutcomeLayoutSupported ctx layout outcomeLayout sourceResult) ->
        (forall name, name ∈ layout -> name ∈ ctx.scope) ->
        CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx
          cfg reserved layout outcomeLayout terminalRel revertRel prim program ctx
          bound compileFuel sourceStmts (some yulProgram.contract) allowed)
    (hHiddenModeBlock : ... SourceNamesReserved reserved (Stmt.List.names sourceStmts) -> ...)
    (hArgs : forall {reserved layout}, SourceArgListPreludeRegularAllCheckedAt
      cfg layout prim program yulProgram.contract (reserved ++ layout) bound.succ) :
    ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
      ... bound.succ
```

So the last big missing proof is the statement-list frontier `hSeq`, plus the `hStmt`, `hHiddenModeBlock`, and `hArgs` frontier fields around it.

## What has already happened

An earlier oracle answer recommended:

- make the reserved bridge the canonical recursive induction invariant;
- do not prove successor from the old unreserved bridge;
- do not mutate every old theorem in place;
- add reserved-native sibling wrappers and keep old theorem names as compatibility aliases via `of_unreserved`;
- split helper APIs by capability (`args`, `hiddenModeBlock`, etc.) rather than passing the whole bridge everywhere.

We followed part of that:

- added `SourceNamesReserved` split/mono/weakening lemmas;
- added reserved capability view;
- moved expression terminal and checked expression-terminal dispatcher helpers onto reserved bridge;
- added `sourceArgListPreludeTerminalAt_of_programAccepted_reserved_checkedArgs`;
- added a reserved sibling for expression-statement user-call sequence heads:

```lean
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_user_call_of_programAccepted_reservedBridge_supported
```

and kept:

```lean
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_user_call_of_programAccepted_reserved_supported
```

as an old-bridge compatibility alias using `of_unreserved`.

Remaining analogous user-call head wrappers for assignment and generated-let still have old-bridge variants and some internal `of_unreserved` adaptation.

## Current worry

We have spent many hours around the final dispatcher. The proof is progressing, but it may still be too bottom-up. The user asked for a big top-down architectural rethink:

> Do we want all these to be reserved or what?

Please answer from first principles. We want to avoid a local patch that typechecks but leaves the compiler tower with a bad public proof interface.

## Questions

1. Should the final recursive source-fuel induction invariant be the reserved bridge? If yes, should all statement/block/hidden-mode theorem surfaces in the recursive bridge path be reserved-native, with old unreserved names only as compatibility aliases?

2. Is `SourceNamesReserved reserved (Stmt.List.names sourceStmts)` the right property and direction? Should `reserved` contain all source names, or should this be represented as a stronger freshness/context object bundled with `FreshCoversLayout`, `FreshCoversDispatcherNames`, or `ProgramBridgeContext`?

3. Should expression/argument helpers remain mostly unreserved and consume only `args` capabilities, or should they also be reservation-aware for uniformity?

4. What should be the clean theorem API for the final `hSeq` dispatcher? In particular, should the dispatcher take:
   - the full `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved`, or
   - a smaller capability record, or
   - separate field hypotheses?

5. Should we continue the sibling-wrapper migration pattern, or should we do a more global refactor now?

6. What exact remaining proof steps would you recommend to finish the successor theorem without another 24-hour loop?

7. Are there any signs that `SourceNamesReserved` is compensating for a deeper abstraction leak in the compiler tower? If so, where should the invariant really live?

Please be concrete. A useful answer can include Lean theorem-shape sketches, but the most important part is the architecture: which invariants belong at the public successor theorem boundary, which belong in helper wrappers, and which should be hidden behind capability records.

Constraints:

- No `sorry`, `admit`, new axioms, or weakened theorem statements.
- Do not assume the unreserved bridge can be recovered from the reserved bridge.
- The final public compiler theorem may assume source acceptedness, fuel/resource bounds, initial state relation, and gas bounds, but must not take compiler-generated proof artifacts or callee-preservation oracles.
- Keep source semantics stack-free and do not leak lower compiler machinery upward.
