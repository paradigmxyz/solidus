We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: add and prove the bounded switch-preservation family in
`EvmCompiler/Structured/Preservation.lean`, without weakening existing
theorems and without using `sorry`, `admit`, `axiom`, `unsafe`, or `partial`.

Background:

The file already has the unbounded switch proof family:

- `SwitchCasesPreservesInProgramLayout`
- `SwitchDefaultPreservesInProgramLayout`
- `switchCasesPreservesInProgramLayout_head`
- `switchCasesPreservesInProgramLayout_tail`
- `switchDefaultPreservesInProgramLayout_some`
- `switchCasesPreservesInProgramLayout_of_all`
- `labeled_body_tail_result_ctx_in_programLayout`
- `head_case_from_tests_result_ctx_in_programLayout`
- `default_selected_tail_result_ctx_in_programLayout`
- `selected_cases_result_ctx_in_programLayout`
- `preserves_switch_in_programLayout`

The file now also has checked bounded interfaces:

- `StmtPreservesInProgramLayoutUpTo`
- `BlockPreservesInProgramLayoutUpTo`
- `CallObligationUpTo`
- `CallObligationForAllFuel`
- `preserves_cons_in_programLayout_upTo`
- `preserves_if_in_programLayout_upTo`

Goal:

Add the switch analogues needed by the future source-fuel induction:

- `SwitchCasesPreservesInProgramLayoutUpTo`
- `SwitchDefaultPreservesInProgramLayoutUpTo`
- head/tail/some accessors for those predicates
- `switchCasesPreservesInProgramLayoutUpTo_of_all`
- bounded versions of the selected/default switch runner helpers as needed
- final theorem:

```lean
theorem preserves_switch_in_programLayout_upTo {program : Program}
    {layout : ProgramLayout program} {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply}
    {scrutinee : Code} {cases : List (Word × Block)}
    {defaultBody : Option Block}
    (hScrutineeSafe : Code.RunnerSafe scrutinee)
    (hScrutineeFrame : Code.FrameSafe scrutinee)
    (hCases :
      SwitchCasesPreservesInProgramLayoutUpTo layout maxFuel ctx
        (LabelSupply.label supply 0) supply (LabelSupply.next supply) 0
        cases)
    (hDefault :
      SwitchDefaultPreservesInProgramLayoutUpTo layout maxFuel ctx
        (SwitchCases.compileFromCtx cases ctx (LabelSupply.label supply 0)
          supply (LabelSupply.next supply) 0).next defaultBody) :
    StmtPreservesInProgramLayoutUpTo layout maxFuel ctx supply
      (.switch scrutinee cases defaultBody)
```

PROVIDED SOLUTION:

Use the existing unbounded switch family as the template, but do not assume an
unbounded body-preservation theorem. Whenever a source switch selects a body,
the outer `Stmt.Eval` constructor has fuel `fuel + 1`, so from the bounded
theorem's premise `fuel + 1 < maxFuel` derive the selected body fuel proof
`fuel < maxFuel` by `omega`, and pass that proof to
`BlockPreservesInProgramLayoutUpTo`.

For helper theorems that run a selected body directly, add an explicit premise
such as `(hFuel : fuel < maxFuel)` and thread it to the selected body
preservation call. For recursive traversal over the case list, keep the same
`hFuel` when recursing, because the selected body fuel does not change while
walking the tests.

Constraints:

- Keep all existing theorem statements unchanged.
- Add new theorem names rather than replacing the unbounded family.
- Do not introduce axioms, sorries, admits, unsafe, partial, or weakened
  definitions.
- Prefer local helper lemmas over fused special cases.
- The proof should be generic over all switch cases/defaults, not a special
  case.

Validation command:

```zsh
/Users/dan/.elan/bin/lake build EvmCompiler.Structured.Preservation
```
