We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: solve the remaining generated `for` frontier item in
`EvmCompiler/Yul/RecursiveBridgeSupport.lean`, or reduce it by adding the
right compositional helper theorem(s) that Lean verifies.

Current checkpoint:
The recursive Nethermind-Yul bridge is stuck on the source `.For` exact-fuel
successor frontier.  The current roadmap item is:

  Construct `ForOkDomainExactContracts` at the exact-fuel successor site from
  `Safe`, scoped post facts, condition result/domain facts, and recursive
  hidden-scope body/post block-domain facts.

Important existing definitions/theorems in namespace
`EvmCompiler.Yul.Reference.SourceBridgeFacts`:

1. `ExprOkDomainExactContract`

```
structure ExprOkDomainExactContract
    (layout : List Name) (expr : AstExpr)
    (codeOverride : Option AstContract) : Prop where
  evalOk :
    ∀ {fuel : Nat} {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore} {stateAfter : State}
      {value : Word},
      StoreDomainExact layout store →
      EvmYul.Yul.eval fuel expr codeOverride (.Ok shared store) =
        .ok (stateAfter, value) →
      ∃ sharedAfter storeAfter,
        stateAfter = .Ok sharedAfter storeAfter ∧
        StoreDomainExact layout storeAfter
```

2. `BlockDomainExactContract`

```
structure BlockDomainExactContract
    (layout : List Name) (stmts : List AstStmt)
    (codeOverride : Option AstContract) : Prop where
  ok :
    ∀ {fuel : Nat}
      {shared sharedAfter : EvmYul.SharedState .Yul}
      {store storeAfter : EvmYul.Yul.VarStore},
      StoreDomainExact layout store →
      EvmYul.Yul.exec fuel (.Block stmts) codeOverride
        (.Ok shared store) =
          .ok (.Ok sharedAfter storeAfter) →
      StoreDomainExact layout storeAfter
  brk :
    ∀ {fuel : Nat}
      {shared sharedAfter : EvmYul.SharedState .Yul}
      {store storeAfter : EvmYul.Yul.VarStore},
      StoreDomainExact layout store →
      EvmYul.Yul.exec fuel (.Block stmts) codeOverride
        (.Ok shared store) =
          .ok (.Checkpoint (.Break sharedAfter storeAfter)) →
      StoreDomainExact layout storeAfter
  cont :
    ∀ {fuel : Nat}
      {shared sharedAfter : EvmYul.SharedState .Yul}
      {store storeAfter : EvmYul.Yul.VarStore},
      StoreDomainExact layout store →
      EvmYul.Yul.exec fuel (.Block stmts) codeOverride
        (.Ok shared store) =
          .ok (.Checkpoint (.Continue sharedAfter storeAfter)) →
      StoreDomainExact layout storeAfter
  leave :
    ∀ {fuel : Nat}
      {shared sharedAfter : EvmYul.SharedState .Yul}
      {store storeAfter : EvmYul.Yul.VarStore},
      StoreDomainExact layout store →
      EvmYul.Yul.exec fuel (.Block stmts) codeOverride
        (.Ok shared store) =
          .ok (.Checkpoint (.Leave sharedAfter storeAfter)) →
      StoreDomainExact layout storeAfter
```

3. Already-proved block facade:

```
theorem BlockDomainExactContract.of_execSeq_contains
    {layout : List Name} {stmts : List AstStmt}
    {codeOverride : Option AstContract}
    (hSeq :
      ∀ {fuel : Nat} {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore},
        StoreDomainExact layout store →
        SourceResultStoreContains layout
          (EvmYul.Yul.execSeq fuel stmts codeOverride (.Ok shared store))) :
    BlockDomainExactContract layout stmts codeOverride
```

4. `ForOkDomainExactContracts.of_contracts`

```
theorem ForOkDomainExactContracts.of_contracts
    {layout : List Name} {cond : AstExpr} {post body : List AstStmt}
    {codeOverride : Option AstContract}
    (hCond :
      ExprOkDomainExactContract layout cond codeOverride)
    (hBody :
      BlockDomainExactContract layout body codeOverride)
    (hPost :
      BlockDomainExactContract layout post codeOverride)
    (hPostBreakFalse :
      ∀ {fuel : Nat}
        {sharedAfterBody sharedAfterPost : EvmYul.SharedState .Yul}
        {storeAfterBody storeAfterPost : EvmYul.Yul.VarStore},
        EvmYul.Yul.exec fuel (.Block post) codeOverride
          (.Ok sharedAfterBody storeAfterBody) =
            .ok (.Checkpoint (.Break sharedAfterPost storeAfterPost)) →
        False)
    (hPostContinueFalse :
      ∀ {fuel : Nat}
        {sharedAfterBody sharedAfterPost : EvmYul.SharedState .Yul}
        {storeAfterBody storeAfterPost : EvmYul.Yul.VarStore},
        EvmYul.Yul.exec fuel (.Block post) codeOverride
          (.Ok sharedAfterBody storeAfterBody) =
            .ok (.Checkpoint (.Continue sharedAfterPost storeAfterPost)) →
        False) :
    ForOkDomainExactContracts layout cond post body codeOverride
```

5. The checked `for` wrapper now consumes:

```
(hLoopDomain :
  ForOkDomainExactContracts layout cond post body
    (some yulProgram.contract))
```

in theorem:

```
checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_programAcceptedLoop
```

Current known difficulty:
Do not prove a broad arbitrary-state store-containment theorem.  That route is
false because imported block cleanup observes `State.store`, which is `default`
outside `.Ok`.  Stay specialized to successful `.Ok` entries/results and block
boundaries.

Likely useful existing theorem family:

- `SourceResultStoreContains.execSeq_cons_succ`
- `SourceResultStoreContains.exec_block_succ_of_execSeq`
- `SourceResultStoreContains.loop_succ_succ_of_ok_parts`
- `SourceResultStoreContains.exec_for_of_loop_input`
- `eval_state_domain_exact_of_safe_primitiveFamilies`
- `ExprEvalResultOkAt`
- `post_break_false_of_checkpointAllowed_false_false_true`
- `post_continue_false_of_checkpointAllowed_false_false_true`
- `SourceResultBlockSoundWhenAtExactHiddenScope` and hidden-scope mode
  extractors, if needed.

What I want:

Prefer a patch that adds one or both of these reusable helper layers:

1. A theorem that constructs `ForOkDomainExactContracts` from:
   - an `ExprOkDomainExactContract` for the condition;
   - all-fuel `SourceResultStoreContains` facts for `body` and `post`
     `execSeq` from exact `.Ok` stores;
   - scoped-post `break`/`continue` impossibility facts.

2. If possible, a successor-frontier theorem or helper that obtains those
   `SourceResultStoreContains` facts from the accepted recursive bridge /
   source acceptedness facts already present around the exact-fuel `.For`
   case.

If the current all-fuel `ExprOkDomainExactContract` is too strong to construct
from the exact-fuel frontier facts, please say so explicitly and return the
minimal checked patch that changes the contract shape to the right fuel-bounded
or resource-parametric form, then updates uses without weakening the public
recursive bridge theorem.

Constraints:
- Keep public theorem statements as strong as possible; do not silently replace
  the goal with an accepted fragment.
- Do not introduce axioms.
- Do not use `sorry`, `admit`, or `unsafe`.
- Do not depend on `sorryAx`.
- Do not add broad `simp`/unfold proof terms that cause major blowup if a
  small compositional helper can express the invariant.
- Avoid changing unrelated layers or documentation.

Validation command:

```
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

If you add exported public helpers, also validate:

```
/Users/dan/.elan/bin/lake build EvmCompiler.LayerAudit
```
