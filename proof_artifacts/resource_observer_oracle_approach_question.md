# Oracle request: dry-run observer oracle proof route for gas()/msize()

## Repository / file

Repo: `/Users/dan/Projects/evm-compiler`

Main file: `EvmCompiler/Yul/ObserverOracle.lean`

Request mode: critique / theorem-boundary audit / proof strategy advice.

Constraints: no new axioms, no `sorry`; keep theorem boundary honest. This is an end-to-end verified compiler project in Lean. We want advice about whether the current dry-run observer-oracle approach is sound and whether the current proof decomposition is the right route.

## User-level goal

We want to support Yul programs using `gas()` and `msize()`. Previously they compiled, but the source/target proof did not cover them because they observe EVM-specific resources that can differ after compilation.

Proposed route:

1. Run the unchecked compiled EVM target once as a dry run.
2. Record the dynamic sequence of resource observations:
   - `gas` observations
   - `msize` observations
3. Feed those observations as an oracle trace to the source/Yul replay semantics.
4. Prove a conditional theorem: if source replay consumes exactly the dry-run observations and reaches the same result, then source assembly oracle execution, compiled assembly oracle execution, and target oracle execution all agree with the dry-run target result.

The intended trust boundary is not "gas/msize are source-deterministic". It is: the dry-run target trace is an explicit input/oracle, and the proof shows equivalence under that trace.

## Current checked status

Focused check currently passes:

```bash
lake env lean EvmCompiler/Yul/ObserverOracle.lean -DmaxErrors=20
```

There are many existing unused-simp warnings, but no errors.

Already checked:

1. Assembly target observer/dry-run semantics exists.
2. `TargetDryRun.sourceOracle_run_matches_targetOracle_of_compile` exists and checks.
3. Expression/source replay to structured-code oracle replay exists for code-shaped expression blocks.
4. `OracleFrameSafe` and `OracleStepPC` exist for emitted expression code, including singleton `gas`/`msize`.
5. New in-progress route: `OracleRelSafe`, relating source-oracle structured-code replay to target/source assembly oracle execution from a same-data target state.

## Key definitions/theorems

Basic instruction oracle step:

```lean
namespace StructuredReplay.BasicInstr

def stepWithOracle (program : Assembly.Program) (pc : Nat)
    (instr : Structured.BasicInstr) (state : EVMState) (trace : Trace) :
    Except EVMException (EVMState × Trace) :=
  match
      Assembly.Source.stepAtResultWithOracle program pc instr.toAssembly state
        trace with
  | .error err => .error err
  | .ok (.running state', trace') => .ok (state', trace')
  | .ok (.halted _halt, _trace') => .error .InvalidInstruction

def OracleRelSafe (instr : Structured.BasicInstr) : Prop :=
  ∀ {program : Assembly.Program} {pc : Nat}
    {source target source' : EVMState} {trace trace' : Trace},
    Structured.Preservation.SameData target source →
      stepWithOracle program pc instr source trace = .ok (source', trace') →
        ∃ target',
          Assembly.Source.stepAtResultWithOracle program pc
              instr.toAssembly target trace =
            .ok (.running target', trace') ∧
          Structured.Preservation.SameData target' source' ∧
          target'.pc =
            target.pc + EvmYul.UInt256.ofNat instr.toAssembly.byteSize
```

For ordinary non-observer instructions:

```lean
theorem oracleRelSafe_of_runnerSafe_nonObserver
    {instr : Structured.BasicInstr}
    (hSafe : Structured.Preservation.BasicInstr.RunnerSafe instr)
    (hObserver : Assembly.ResourceObserver.ofInstr? instr.toAssembly = none) :
    OracleRelSafe instr

theorem oracleRelSafe_push (value : Word) :
    OracleRelSafe (Structured.BasicInstr.push value)
```

For singleton `gas`/`msize`, checked facts:

```lean
theorem oracleRelSafe_gas :
    BasicInstr.OracleRelSafe (Structured.BasicInstr.op .gas)

theorem oracleRelSafe_msize :
    BasicInstr.OracleRelSafe (Structured.BasicInstr.op .msize)
```

Shape of these proofs:

- run raw target `GAS`/`MSIZE`;
- oracle overwrites the top stack word with the supplied trace value;
- prove final `SameData` with the source replay state, ignoring gas via `eraseControl`/`eraseGas`;
- prove PC advances by byte size.

Code-level relation:

```lean
namespace StructuredReplay.Code

def OracleRelSafe : Structured.Code → Prop
  | [] => True
  | instr :: rest =>
      BasicInstr.OracleRelSafe instr ∧ OracleRelSafe rest

theorem runWithOracle_source_runNResultWithOracle_rel_segment :
    ∀ {pre post : Assembly.Program} {code : Structured.Code}
      {source target source' : EVMState} {trace trace' : Trace},
      OracleRelSafe code →
      Structured.Preservation.Code.PCFitsFrom pre code →
      target.pc = Assembly.Program.pcAfter pre →
      Structured.Preservation.SameData target source →
      runWithOracle (pre ++ code.toAssembly ++ post)
          (Assembly.Program.byteLength pre) code source trace =
        .ok (source', trace') →
      ∃ target',
        Assembly.Source.runNResultWithOracle
            (pre ++ code.toAssembly ++ post) code.length target trace =
          .ok (.running target', trace') ∧
        Structured.Preservation.SameData target' source' ∧
        target'.pc = Assembly.Program.pcAfter (pre ++ code.toAssembly)
```

This theorem also checks.

Relation-aware `Locals.codeStmt` wrappers now check:

```lean
theorem ExpressionsReplay.StmtList.runCodeWithOracle_codeStmt_source_runNResultWithOracle_rel_segment
    ... :
  ∃ target',
    Assembly.Source.runNResultWithOracle
      (pre ++ code.toAssembly ++ post) code.length target trace =
      .ok (.running target', trace') ∧
    Structured.Preservation.SameData target' evm' ∧
    target'.pc = Assembly.Program.pcAfter (pre ++ code.toAssembly)

theorem ExpressionsReplay.Block.runWithOracle_codeStmt_source_runNResultWithOracle_rel_segment
    ... :
  ∃ target',
    Assembly.Source.runNResultWithOracle
      (pre ++ code.toAssembly ++ post) code.length target trace =
      .ok (.running target', trace') ∧
    Structured.Preservation.SameData target' state'.evm ∧
    target'.pc = Assembly.Program.pcAfter (pre ++ code.toAssembly) ∧
    state' = state.withEVM state'.evm
```

Target dry-run boundary:

```lean
namespace TargetDryRun

theorem sourceOracle_run_matches_targetOracle_of_compile
    {asm : Assembly.Program} (dryRun : TargetDryRun) (rest : Trace)
    (hCompile : Assembly.compile? asm = some dryRun.target)
    (hSource :
      Assembly.Source.runNResultWithOracle asm dryRun.fuel
          dryRun.initial (dryRun.trace ++ rest) =
        .ok (dryRun.result, rest)) :
    Assembly.Accepted asm ∧
      Assembly.Preservation.BlockTraceResultWithOracle asm dryRun.target
        dryRun.fuel dryRun.initial (dryRun.trace ++ rest) rest
        dryRun.result ∧
      Assembly.Compiled.runNResultWithOracle asm dryRun.fuel
        dryRun.initial (dryRun.trace ++ rest) =
          .ok (dryRun.result, rest) ∧
      Assembly.Target.runNResultWithOracle dryRun.target dryRun.fuel
        dryRun.initial (dryRun.trace ++ rest) =
          .ok (dryRun.result, rest)
```

This checks and uses the checked assembly compiler preservation theorem plus the target observer run replay theorem.

## Current intended next steps

We are trying to discharge `StructuredReplay.Code.OracleRelSafe code` for actual emitted source-owned expression code, in the same style as already-checked `OracleFrameSafe`/`OracleStepPC` facts:

```lean
theorem SourceReplay.Expr.oracleFrameSafe_compileCode_of_eval_sourceOwned :
  Locals.Source.Expr.SourceOwned expr →
  Locals.Expr.compileCode ctx offset expr = some code →
  Expr.eval expr state = .ok (state', values) →
  StructuredReplay.Code.OracleFrameSafe code

theorem SourceReplay.Expr.oracleStepPC_compileCode_of_eval_sourceOwned :
  Locals.Source.Expr.SourceOwned expr →
  Locals.Expr.compileCode ctx offset expr = some code →
  Expr.eval expr state = .ok (state', values) →
  StructuredReplay.Code.OracleStepPC code
```

Planned analogous theorem:

```lean
theorem oracleRelSafe_compileCode_of_eval_sourceOwned :
  Locals.Source.Expr.SourceOwned expr →
  Locals.Expr.compileCode ctx offset expr = some code →
  Expr.eval expr state = .ok (state', values) →
  StructuredReplay.Code.OracleRelSafe code
```

For `.lit`, use `oracleRelSafe_push`.

For `.var`, compiled code is `[op]` where `Locals.StackOp.dup? (offset + depth) = some op`; use existing stack-op runner-safe facts plus non-observer facts.

For `.prim op args`, compile emits `argsCode ++ [Structured.BasicInstr.op op]`; recurse on args, then:

- if replay op is non-observer ordinary op, use existing runner-safe/non-observer route;
- if op is `gas`, use `oracleRelSafe_gas`;
- if op is `msize`, use `oracleRelSafe_msize`;
- if replay succeeds, cases where source primitive semantics rejects the op are impossible.

## Concerns / questions for the oracle

1. Is the high-level dry-run observer-oracle theorem boundary sound for `gas()` and `msize()`?

   In particular, are we correctly proving a conditional theorem over an explicit target-observed oracle trace, rather than accidentally claiming source-level determinism for gas/msize?

2. Is `OracleRelSafe` the right relation to bridge source replay to target/source assembly oracle execution?

   It uses `Structured.Preservation.SameData target source`, where `SameData` erases control PC and gas via `eraseControl`/`eraseGas`, and then carries target PC separately.

3. Is the singleton `msize` treatment sound?

   We run raw `MSIZE` on the target/source EVM state, then overwrite the top stack value from the oracle trace. Since `MSIZE` should have no memory side effects, `SameData` should survive even if raw `msize` values differ because scratch/prelude code changed active words. Is there any hidden side effect or semantic issue here?

4. Is there a possible circularity/dynamic-path problem?

   Target dry run records observations along the target path. Source replay consumes the same ordered observations. If the observations make the source path diverge, source replay will fail or consume a different trace, so the theorem premise will not hold. Is this acceptable as a conditional theorem, or do we need an additional uniqueness/path theorem?

5. Is the planned next theorem `oracleRelSafe_compileCode_of_eval_sourceOwned` the right next proof step, or should the proof be decomposed differently?

6. What theorem-boundary red flags remain before claiming the dry-run route covers Yul programs with `gas()`/`msize()`?

Please be direct if this route is unsound or if a premise makes the final theorem too weak to be useful.
