# Oracle request: next sound theorem for the Yul reference bridge

We are in `/Users/dan/Projects/evm-compiler`, a Lean project building a verified compiler tower:

```text
Imported Nethermind EvmYul.Yul semantics
  -> EvmCompiler.Yul lowering
  -> Objects -> Functions -> Locals -> Expressions -> Structured
  -> labeled assembly -> bytecode/gas-aware EVMYulLean
```

Current status:

- All internal layers through Objects have independent interpreters and checked adjacent preservation theorems.
- `Yul.Program.run` is now the independent imported source boundary:
  `EvmYul.Yul.callDispatcher fuel (some program.contract) (Program.installContract program state)`.
- The old compiler-facing path is quarantined as `Yul.Lowered.run`, defined by `program.toObjects? >>= Objects.Program.run`.
- The public Yul-to-bytecode theorem still crosses the imported/source gap through:

```lean
structure SourceBridge (stateRel : StateRel) (outcomeRel : OutcomeRel)
    (program : Program) (referenceFuel : Nat)
    (referenceInitial : State) (referenceResult : Result) where
  accepted : Accepted program
  sourceFuel : Nat
  compilerInitial : EVMState
  outcome : Outcome
  referenceRun :
    runResult referenceFuel program referenceInitial = .ok referenceResult
  initialRel : stateRel (installContract program referenceInitial)
    compilerInitial
  sourceRun :
    Lowered.run sourceFuel program compilerInitial = .ok outcome
  outcomeRel : outcomeRel referenceResult outcome
```

Goal: replace `SourceBridge.sourceRun` with checked per-construct bridge lemmas/theorems, without making a replay validator or hiding compiler-generated evidence as public assumptions.

Important current code:

- `EvmCompiler/Yul/Reference.lean`
  - `Reference.Safe.primitive` rejects code-image/external-call/create/revert/selfdestruct blockers:
    `CODESIZE`, `CODECOPY`, `EXTCODESIZE`, `EXTCODECOPY`, `EXTCODEHASH`, `CREATE`, `CALL`, `CALLCODE`, `DELEGATECALL`, `CREATE2`, `STATICCALL`, `REVERT`, `SELFDESTRUCT`.
  - `Reference.Safe.stmt` admits switches only when `defaultBody = []` because imported Nethermind `exec Switch` evaluates default before case selection.
  - `Reference.StateRelConfig`, `CompilerStateRel`, `ExecutionEnvRel`, etc. are defined to relate Yul/EVM states parametrically.
  - I added checked imported interpreter reduction lemmas:
    `eval_lit_succ`, `eval_var_succ`, `evalArgs_zero`, `evalArgs_nil_succ`,
    `evalArgs_cons_succ`, `evalTail_error`, `evalTail_ok_zero`,
    `eval_prim_call_succ`, `eval_user_call_succ`,
    `exec_block_nil_succ`, `exec_block_cons_succ`,
    `exec_let_none_succ`, `exec_let_lit_succ`, `exec_let_var_succ`,
    `exec_let_prim_call_succ`, `exec_let_user_call_succ`,
    `exec_if_succ`, `exec_expr_prim_call_succ`,
    `exec_expr_user_call_succ`, `exec_for_succ`,
    `exec_continue_succ`, `exec_break_succ`, `exec_leave_succ`.

- `EvmCompiler/Yul/Compiler.lean`
  - `Expr.List.lower1?` recurses over the tail before the head so generated prelude statements execute in Yul's last-to-first argument evaluation order:
    ```lean
    | expr :: rest => do
        let (preRest, lowerRest, state') ← List.lower1? state rest
        let (preHead, lowerHead, state'') ← lower? 1 state' expr
        some (preRest ++ preHead, lowerHead :: lowerRest, state'')
    ```
  - `Stmt.toFunctionsListFuel?` lowers imported AST statements into `Functions.Stmt`, including lets, calls, terminal primitive calls, switch, for, if, break/continue/leave.

The imported Nethermind interpreter quirks we know:

1. Function/primitive arguments are evaluated by `args.reverse` and `reverse'`.
2. `Switch` evaluates every case from the same post-scrutinee state, and evaluates default before selecting a case. Successful selected-case runs can still be related if nonselected branches/default are harmless, but default errors/fuel failures can kill a run even when a case matches.
3. `SELFDESTRUCT` in imported Yul primitive semantics is TODO/not halting like EVM selfdestruct.
4. Code-image/account-code primitives need a separate relation because `.Yul.code` is a `YulContract` and `.EVM.code` is `ByteArray`.

Question:

What is the smallest **sound next theorem** to implement in Lean that actually reduces the `SourceBridge` assumption and fits a future full bridge?

Please be concrete about:

1. The theorem statement shape: source big-step/fuel-indexed theorem? expression bridge first? statement bridge first? top-level dispatcher bridge?
2. The relation shape between imported `EvmYul.Yul.State.Ok shared varstore` and compiler `EVMState`: should it use the existing `CompilerStateRel cfg layout`, or do we need a richer relation including function frames/return variables?
3. How to handle `Yul.Lowered.run`: should the bridge target it directly, or target `Objects/Functions` interpreters after `toObjects? = some lower`?
4. How to structure induction to match imported fuel and compiler fuel, given both interpreters consume fuel differently.
5. Which constructs should be proved first to avoid proof-search blowup but not become a one-off special case.

Constraints:

- No `sorry`, `admit`, new `axiom`, unsafe, or public replay/certificate assumption.
- Accepted restrictions may reject known semantic blockers, but should not reject proof-inconvenient constructs.
- We need a route that can eventually compose into:
  `Yul.Program.compile_whole_program_result_sound_of_source_bridge_with_result_rel`
  without a user-supplied `SourceBridge.sourceRun`.
