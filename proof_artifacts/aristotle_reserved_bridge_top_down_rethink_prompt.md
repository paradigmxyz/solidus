We are in the Lean project at:

/Users/dan/Projects/evm-compiler

Task: solve or sharply reduce the architecture/proof bottleneck for the recursive accepted Yul source bridge successor theorem. The key question is whether the remaining recursive bridge path should be reservation-aware everywhere.

Primary file:

/Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Validation command:

lake build EvmCompiler.Yul.RecursiveBridgeSupport

Current state:

- The module currently builds.
- The final public bridge must be proved by source-fuel induction, not by a caller-supplied callee-preservation oracle.
- We have an old bridge:

  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames

  whose statement/block fields do not require source names to be present in the compiler reserved-name set.

- We have a newer bridge:

  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved

  whose statement/block/hiddenBlock/hiddenModeBlock fields additionally require:

  SourceNamesReserved reserved (Stmt.names sourceStmt)
  SourceNamesReserved reserved (Stmt.List.names sourceStmts)

- `SourceNamesReserved` is defined near the top of the file:

  def SourceNamesReserved (reserved names : List Name) : Prop :=
    forall name, name ∈ names -> name ∈ reserved

  It is intended as compiler hygiene: source names are pre-reserved so generated temporaries cannot collide with future source declarations.

- There is a theorem:

  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.of_unreserved

  from the old bridge to the reserved bridge. The reverse direction is not expected.

- The successor handoff we want to feed is:

  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.succ_of_hiddenCtxSeq_frontier_fields_supported

  It expects:
  1. `hRecursive`, a reserved bridge up to `bound`;
  2. `hStmt`, a reserved-aware statement frontier;
  3. `hSeq`, a reserved-aware statement-list/hidden-context sequence frontier;
  4. `hHiddenModeBlock`, a reserved-aware hidden-mode block frontier;
  5. `hArgs`, an argument frontier.

- The exact `hSeq` shape expected by that theorem is the one in the file at the theorem `succ_of_hiddenCtxSeq_frontier_fields_supported`.

- We have already added and build-checked a reserved-native expression-statement user-call head theorem:

  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_user_call_of_programAccepted_reservedBridge_supported

  The old theorem:

  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_user_call_of_programAccepted_reserved_supported

  is kept as a compatibility alias by applying `of_unreserved` to its old bridge hypothesis.

Problem:

We are spending too long around the final dispatcher. Please solve the architectural proof question and, if feasible, provide a patch:

1. Decide whether the final recursive successor proof should use the reserved bridge as the canonical invariant. If yes, explain and implement the next clean step toward that.

2. Prefer a compositional proof. Do not globally mutate old theorem names unless necessary. The known promising pattern is: add reserved-native sibling theorem(s), then preserve old theorem names as compatibility aliases through `of_unreserved`.

3. The next likely Lean step is to add analogous reserved-native siblings for:

   checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_user_call_of_programAccepted_reserved_supported

   and/or

   checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_user_call_of_programAccepted_reserved_supported

   so the final `hSeq` dispatcher can use a reserved recursive bridge directly.

4. If you can prove one or both sibling theorems, return the patch. If the whole dispatcher is feasible, prove it. If not, return the exact theorem-shape recommendation and the next few helper lemmas needed.

Constraints:

- Keep theorem statements semantically strong; do not weaken the public theorem.
- Do not introduce axioms, `sorry`, or `admit`.
- Do not depend on `sorryAx` or hidden generated axioms.
- Do not assume a reserved bridge implies an unreserved bridge.
- Do not push `SourceNamesReserved` into source semantics; it is a compiler hygiene invariant.
- Keep expression/argument helpers capability-based where possible rather than passing the full bridge everywhere.
- The final theorem must not take a caller-supplied callee-preservation oracle or compiler-generated evidence.

Useful known validation:

The current file builds with:

lake build EvmCompiler.Yul.RecursiveBridgeSupport

Please return either a Lean patch or a precise proof architecture that would let us complete the reserved successor theorem without another loop.
