We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: solve or substantially reduce the reserved-name recursive dispatcher
successor proof in:

  /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

The project currently builds:

  lake build EvmCompiler.Yul.RecursiveBridgeSupport

The final goal is a verified compiler bridge from Nethermind-style Yul to our
compiler tower.  The current local blocker is the recursive successor theorem
for the accepted-program Yul source bridge.

Relevant existing theorem:

  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
    .succ_of_hiddenCtxSeq_frontier_fields_supported

It takes:

  hRecursive :
    ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
      cfg terminalRel revertRel prim yulProgram program context bound

and needs an `hSeq` frontier:

  ∀ {reserved layout outcomeLayout : List Name}
    {ctx : Functions.Source.Ctx}
    {compileFuel : Nat} {sourceStmts : List AstStmt}
    {allowed : Except Exception State → Prop}
    {canBreak canContinue canLeave : Bool},
    Safe.stmts sourceStmts →
    ControlFlow.ScopedStmts canBreak canContinue canLeave sourceStmts →
    UserCallArity.StmtsOk yulProgram.contract sourceStmts →
    SourceLexical.StmtsScoped layout sourceStmts →
    SourceNamesReserved reserved (Stmt.List.names sourceStmts) →
    (∀ {sourceResult}, allowed sourceResult →
      SourceResultRelatable sourceResult) →
    (∀ {sourceResult}, allowed sourceResult →
      SourceResultOutcomeLayoutSupported ctx layout outcomeLayout
        sourceResult) →
    (∀ name : Name, name ∈ layout → name ∈ ctx.scope) →
    CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx cfg
      reserved layout outcomeLayout terminalRel revertRel prim program ctx
      bound compileFuel sourceStmts (some yulProgram.contract) allowed

Definitions:

  def SourceNamesReserved (reserved names : List Name) : Prop :=
    ∀ name, name ∈ names → name ∈ reserved

There are two recursive bridge structures:

1. ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames
   has stmt/block/hiddenBlock/hiddenModeBlock fields that do NOT require
   SourceNamesReserved.

2. ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
   has the same fields but stmt requires
     SourceNamesReserved reserved (Stmt.names sourceStmt)
   and block/hiddenBlock/hiddenModeBlock require
     SourceNamesReserved reserved (Stmt.List.names sourceStmts).

There is only:

  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.of_unreserved :
    ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames ... bound →
    ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved ... bound

There is no projection reserved -> unreserved, and that projection would be
invalid in general.

Current dispatcher-facing wrappers already proved/building include:

  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_simple_head_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_none_of_sourceScoped_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_programAcceptedLoop_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_block_of_programAcceptedBody_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_user_call_of_programAccepted_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_user_call_of_programAccepted_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_user_call_of_programAccepted_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_if_of_programAcceptedCondition_reserved_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_switch_of_programAcceptedScrutinee_reserved_supported

But several of those `...reserved_supported` wrappers still take the older
non-reserved bridge as their `hRecursive`.  A broad attempt to flip all of them
to the reserved bridge failed with many type mismatches because lower helper
APIs still expected the old bridge, especially:

  sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_of_argRegularAllCheckedAt
  lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt
  generatedForLoopBranchContracts_of_programAccepted_hiddenMode
  generatedForLoopPostRegularOkBranchContract_of_programAccepted_hiddenMode
  sourceArgListPreludeTerminalAt_of_programAccepted_checkedArgs

What I want from Aristotle:

1. If feasible, produce a patch that adds a reserved-compatible hSeq
   statement-list dispatcher and then uses
   ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
     .succ_of_hiddenCtxSeq_frontier_fields_supported
   to prove the accepted-program successor.

2. If a direct patch is too large, identify the smallest missing helper theorem
   whose statement should be added first.  Prefer a theorem that makes the
   reserved/non-reserved boundary clean instead of pushing the mismatch into a
   giant dispatcher proof.

3. Critique the architecture: should the recursive bridge be reservation-aware
   everywhere, should the dispatcher use a facade, or should the invariant be
   refactored?

Constraints:

- Keep theorem statements semantically strong; do not weaken the public theorem.
- Do not introduce axioms, sorry, admit, or trust-generated certificates.
- Do not add a fake reserved -> unreserved projection.
- Prefer compositional helper lemmas.
- Validation command: lake build EvmCompiler.Yul.RecursiveBridgeSupport

Useful search terms inside the file:

  SourceNamesReserved
  ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved
  succ_of_hiddenCtxSeq_frontier_fields_supported
  checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_*_reserved_supported

