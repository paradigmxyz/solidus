We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: add a fuel-bounded call preservation lemma for the Structured procedure-control compiler, without weakening theorem statements and without using sorry, admit, unsafe, partial, or axioms.

File: /Users/dan/Projects/evm-compiler/EvmCompiler/Structured/Preservation.lean

Current context:
- The module builds with `lake build EvmCompiler.Structured.Preservation`.
- Namespace: `EvmCompiler.Structured.Preservation.ProcedurePreservation`.
- Existing unbounded call route:
  * `call_stmt_of_programLayout_eval`
  * `preserves_call_in_programLayout`
  These currently require a semantic `hProcPreserves` premise.
- Existing bounded interfaces:
  * `StmtPreservesInProgramLayoutUpTo layout maxFuel ...`
  * `BlockPreservesInProgramLayoutUpTo layout maxFuel ...`
  * `CallObligationUpTo layout maxFuel`
  * `CallObligationForAllFuel layout`

Goal:
Add a theorem equivalent to this shape:

```
theorem preserves_call_in_programLayout_upTo {program : Program}
    (layout : ProgramLayout program) {maxFuel : Nat}
    (hProcPreservesUpTo :
      ∀ {name : Name} {proc : Proc}
        (hLookup : ProcList.lookup? name program.procs = some proc),
        BlockPreservesInProgramLayoutUpTo layout maxFuel
          (bodyCtx program proc)
          (layout.procLayout hLookup).bodySupply proc.body)
    {ctx : CompileContext} {supply : LabelSupply} {name : Name} :
    StmtPreservesInProgramLayoutUpTo layout (maxFuel + 1) ctx supply
      (.call name) := by
  ...
```

It is acceptable to use `maxFuel.succ` instead of `maxFuel + 1` if that works better with `omega`/simp, but keep the theorem strong enough for the induction step of `CallObligationForAllFuel`.

Informal proof / guidance:
PROVIDED SOLUTION:
Follow the structure of `call_stmt_of_programLayout_eval` and `call_stmt_segments`. Case on the source `Stmt.Eval` call constructors. In each call constructor, the callee body evaluation uses fuel `evalFuel`, while the source call statement has fuel `evalFuel + 1`. From the bounded call theorem premise `fuel < maxFuel + 1` derive `evalFuel < maxFuel` using `omega`, then use `hProcPreservesUpTo hLookup` for the callee body.

If existing helper lemmas such as `call_regular_segments`, `call_leave_segments`, or `call_halt_segments` block because they expect unbounded `BlockPreserves`, add bounded variants of the smallest needed helper(s). Prefer factoring a helper that takes the already-produced body `ARunResult` at the procedure entry rather than copying the entire dispatch proof three times. Preserve the existing unbounded lemmas.

Constraints:
- Do not weaken any existing theorem/definition.
- Do not add axiom/sorry/admit/unsafe/partial.
- Do not hide call preservation inside `Program.Accepted`, `ProgramLayout`, or `CompilationCertificate`.
- Use source-fuel inequalities explicitly; `omega` is acceptable.
- Return a patch or complete code and mention any helper lemmas added.

Validation command:
lake build EvmCompiler.Structured.Preservation
