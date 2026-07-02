We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: finish the current generated `for` inside hidden-context sequence proof in
`EvmCompiler/Yul/RecursiveBridgeSupport.lean`, without weakening public theorem
intent and without using `sorry`, `admit`, or new axioms.

Namespace:

```lean
EvmCompiler.Yul.Reference.SourceBridgeFacts
```

Validation command:

```bash
/Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

The current file has two intended proof boundaries:

1. `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_for_head_of_branch_contracts`
   is already present and should remain the semantic dispatcher from generated
   loop branch contracts to a hidden-context `for :: rest` head proof.

2. The remaining checked/lowering-side theorem should be the whole proof for
   a generated `for` head inside a hidden sequence:

```lean
theorem checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_branch_contracts_reserved
    {cfg : StateRelConfig} {reserved layout outcomeLayout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {cond : AstExpr} {post body rest : List AstStmt}
    {codeOverride : Option AstContract}
    {allowed : Except Exception State → Prop}
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hCompat :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultOutcomeLayoutCompatible ctx layout outcomeLayout
          sourceResult)
    (hScopeContains : ∀ name : Name, name ∈ layout → name ∈ ctx.scope)
    (hPrim :
      PrimitiveStackSoundAt cfg layout prim sourceFuel.succ
        (.CompBit .ISZERO : EvmYul.Operation .Yul) .iszero)
    (hCondTerminal :
      ∀ (pieces : GeneratedForCompiled reserved layout cond post body),
        SourceExprPreludeTerminalAt cfg layout outcomeLayout terminalRel
          revertRel prim program
          (ctx.withoutLoopControl.withLoopControl ctx.scope ctx.scope)
          sourceFuel cond codeOverride pieces.preCond)
    (hCondSound :
      ∀ (pieces : GeneratedForCompiled reserved layout cond post body),
        ExprEvalPreludeSound cfg layout prim program
          (ctx.withoutLoopControl.withLoopControl ctx.scope ctx.scope)
          sourceFuel cond codeOverride pieces.preCond pieces.lowerCond)
    (hResultOk :
      ExprEvalResultOkAt cfg layout sourceFuel cond codeOverride)
    (hEvalDomain :
      ∀ {shared store sharedAfter storeAfter value},
        StoreDomainExact layout store →
        EvmYul.Yul.eval sourceFuel cond codeOverride (.Ok shared store) =
          .ok (.Ok sharedAfter storeAfter, value) →
        StoreDomainExact layout storeAfter)
    (hPostBreakFalse :
      ∀ {sharedAfterBody sharedAfterPost : EvmYul.SharedState .Yul}
        {storeAfterBody storeAfterPost : EvmYul.Yul.VarStore},
        EvmYul.Yul.exec sourceFuel (.Block post) codeOverride
          (.Ok sharedAfterBody storeAfterBody) =
            .ok (.Checkpoint (.Break sharedAfterPost storeAfterPost)) →
        False)
    (hPostContinueFalse :
      ∀ {sharedAfterBody sharedAfterPost : EvmYul.SharedState .Yul}
        {storeAfterBody storeAfterPost : EvmYul.Yul.VarStore},
        EvmYul.Yul.exec sourceFuel (.Block post) codeOverride
          (.Ok sharedAfterBody storeAfterBody) =
            .ok (.Checkpoint (.Continue sharedAfterPost storeAfterPost)) →
        False)
    (hBranches :
      ∀ (pieces : GeneratedForCompiled reserved layout cond post body),
        GeneratedForLoopBranchContracts cfg layout outcomeLayout terminalRel
          revertRel prim program ctx sourceFuel cond post body codeOverride
          reserved pieces allowed)
    (hPostRegularOk :
      ∀ (pieces : GeneratedForCompiled reserved layout cond post body),
        GeneratedForLoopPostRegularOkBranchContract cfg layout prim program
          ctx sourceFuel cond post body codeOverride reserved pieces)
    (hTail :
      ∀ {compileFuel : Nat} {ctxMid : Functions.Source.Ctx},
        CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx cfg
          reserved layout outcomeLayout terminalRel revertRel prim program
          ctxMid sourceFuel.succ.succ.succ compileFuel rest codeOverride
          allowed) :
    ∀ {compileFuel : Nat},
      CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx cfg
        reserved layout outcomeLayout terminalRel revertRel prim program ctx
        sourceFuel.succ.succ.succ.succ compileFuel
        (.For cond post body :: rest) codeOverride allowed
```

Current local build failure:

```text
error: EvmCompiler/Yul/RecursiveBridgeSupport.lean:102403:20: unknown identifier 'hFuelEq'
error: EvmCompiler/Yul/RecursiveBridgeSupport.lean:102401:15: unsolved goals
...
⊢ Stmt.toFunctionsListFuel? (Stmt.fuel (Ast.Stmt.For cond post body)) freshState
      (Ast.Stmt.For cond post body) =
    some ([Functions.Stmt.for_ ... lowerPost ...], stateHead)

error: EvmCompiler/Yul/RecursiveBridgeSupport.lean:102526:8: type mismatch
  sourceResultSeqSoundWhenAtExactHiddenCtx_cons_for_head_of_branch_contracts ...
has type ... generatedForLowerBlock pieces.preCond pieces.lowerCond pieces.lowerPost pieces.lowerBody
but is expected to have type the explicit block
  { stmts := [Functions.Stmt.for_ ... lowerPost ...] }
```

Important diagnosis:

- `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_generated_head_reserved`
  decomposes an arbitrary successful `Stmt.toFunctionsListFuel? lowerFuel`
  for the generated `for` head. It does not currently have a local `hFuelEq`;
  that was copied from exact-fuel singleton wrappers and is invalid here.
- `GeneratedForCompiled` currently contains `stmtLower`, an exact
  `Stmt.toFunctionsList?` proof. That proof may need to be derived using
  `LoweringFuel.stmt_toFunctionsListFuel?_stable_pair` plus any necessary
  fuel-bound helper, or the checked theorem should be refactored to avoid
  demanding exact-fuel `stmtLower` when the semantic branch theorem only needs
  the decomposed generated pieces.
- If refactoring is cleaner, prefer adding a smaller bundle or a theorem over
  explicit generated pieces for this checked-sequence path, rather than forcing
  an unjustified exact-fuel witness.
- The explicit-block mismatch should be solved by a local `simpa
  [generatedForLowerBlock, List.append_assoc]` or by making the wrapper return
  exactly the explicit block expected by
  `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_generated_head_reserved`.

Relevant existing helpers/theorems:

```lean
GeneratedForCompiled
generatedForLowerBlock
GeneratedForLoopBranchContracts
GeneratedForLoopPostRegularOkBranchContract
sourceResultSeqSoundWhenAtExactHiddenCtx_cons_for_head_of_branch_contracts
checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular
LoweringFuel.stmt_toFunctionsListFuel?_stable_pair
LoweringFuel.list_toBlockFuel?_stable_pair
BridgeFacts.toFunctionsListFuel?_for_components
freshCoversLayout_toFunctionsListFuel?_of_some
```

Architectural constraints:

- Do not add `ctx.scope = layout`; this theorem is deliberately hidden-context.
- Do not expose raw compiler-generated evidence as a new public assumption.
- Keep the proof compositional: semantic generated-loop cases should flow
  through `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_for_head_of_branch_contracts`;
  lowering/list plumbing should stay in the checked-sequence constructor.
- It is fine to add a private/helper theorem or a smaller generated-piece
  record if it makes the exact-fuel boundary honest.
- Do not introduce axioms, `sorry`, `admit`, or weaken definitions.

Please return a patch or complete replacement proof that makes
`lake build EvmCompiler.Yul.RecursiveBridgeSupport` pass.
