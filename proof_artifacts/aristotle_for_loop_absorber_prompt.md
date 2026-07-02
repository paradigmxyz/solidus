We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: solve the narrow remaining generated `for` frontier item by proving the
resource absorber lemma(s) needed for loop-domain preservation.

File:
  /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Namespace:
  EvmCompiler.Yul.Reference.SourceBridgeFacts

Current state:
The recursive Nethermind-Yul bridge has a successful-loop exact-domain contract:

  ForOkDomainExactContracts layout cond post body codeOverride

and an all-fuel theorem:

  exec_for_ok_domain_exact_of_all_fuel_parts

This currently needs the condition contract:

  ExprOkDomainExactContract layout cond codeOverride

which says every successful condition eval from an exact `.Ok` store returns an
ordinary `.Ok` state with exact-domain store.

We have already proved a weaker and more realistic condition theorem:

  eval_ok_or_outOfFuel_domain_exact_of_safe_primitiveFamilies

and wrapped it as:

  ExprOkOrOutOfFuelDomainExactContract
  ExprOkOrOutOfFuelDomainExactContract.of_safe_primitiveFamilies

That theorem says safe expression evaluation from an exact `.Ok` store returns
either:

  * `.OutOfFuel`, or
  * ordinary `.Ok sharedAfter storeAfter` with exact-domain store.

The failed local refactor exposed the exact missing premise: if a `for`
condition eval succeeds to `State.OutOfFuel`, the imported loop must not later
produce a final ordinary `.Ok` result.  Please prove this as a narrow helper and
wire it into the loop-domain contract path if possible.

Desired theorem shape:
Add one or more checked helpers, with names adjusted if needed, along these
lines:

  theorem exec_for_ok_false_of_condition_outOfFuel
      {cond : AstExpr} {post body : List AstStmt}
      {codeOverride : Option AstContract}
      (hSafeBody : Safe.stmts body)
      (hSafePost : Safe.stmts post)
      (hEval :
        EvmYul.Yul.eval fuel cond codeOverride (.Ok shared store) =
          .ok (.OutOfFuel, value))
      (hExec :
        EvmYul.Yul.exec fuel.succ.succ.succ (.For cond post body)
          codeOverride (.Ok shared store) =
            .ok (.Ok sharedAfter storeAfter)) :
      False

The exact fuel arithmetic can be changed to match the local imported `loop`
unfolding.  It is also fine to prove a stronger, compositional absorber first:

  safe eval/exec/execSeq from `.OutOfFuel` cannot produce an ordinary `.Ok`
  final state, and successful safe primitive/user calls on `.OutOfFuel` preserve
  `.OutOfFuel`.

Likely useful existing theorem family:

  primCall_safe_nonOk_state_eq_of_ok
  eval_ok_or_outOfFuel_domain_exact_of_safe_primitiveFamilies
  SourceResultStoreContains.loop_succ_succ_of_ok_parts
  exec_for_ok_domain_exact_of_all_fuel_parts
  ExprOkOrOutOfFuelDomainExactContract.of_safe_primitiveFamilies
  post_break_false_of_checkpointAllowed_false_false_true
  post_continue_false_of_checkpointAllowed_false_false_true

Target integration if feasible:
Change `ForOkDomainExactContracts` so the condition premise can be the
`Ok`-or-`OutOfFuel` contract plus the absorber lemma, then update:

  ForOkDomainExactContracts.of_contracts
  ForOkDomainExactContracts.of_execSeq_contains
  ForOkDomainExactContracts.exec_for_ok
  checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_programAcceptedLoop

If that full wiring is too large, return the minimal checked patch adding the
absorber theorem(s) and a short explanation of exactly where to use them.

Important constraints:
- Do not prove a broad arbitrary-state store-containment theorem.  That route
  is false here because imported block cleanup observes `State.store`, which is
  `default` outside ordinary `.Ok`.
- Keep theorem statements strong; do not silently narrow source semantics.
- Do not introduce axioms.
- Do not use `sorry`, `admit`, or `unsafe`.
- Do not depend on `sorryAx`.
- Prefer small compositional helpers over huge `simp`/unfold proofs that cause
  blowup.
- Avoid unrelated layer or documentation changes.

Validation commands:

  /Users/dan/.elan/bin/lake build EvmCompiler.Yul.RecursiveBridgeSupport

If exported through LayerAudit:

  /Users/dan/.elan/bin/lake build EvmCompiler.LayerAudit
