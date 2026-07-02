# Oracle Context: Completing the Yul-to-EVM Verified Compiler Boundary

## Project

Lean 4 project in `/Users/dan/Projects/evm-compiler`.  It builds a verified
compiler tower over Nethermind's EVMYulLean:

```text
Nethermind Yul reference semantics
  -> EvmCompiler.Yul source semantics
  -> Objects -> Functions -> Locals -> Expressions -> Structured control
  -> labeled Assembly -> resolved EVM assembly -> bytecode
  -> EVMYulLean gas-aware EVM.X
```

Current verified lower tower builds with no `sorry`/`admit`/`axiom`.

## Current Hard Boundary

The user wants a source-complete compiler theorem from Nethermind Yul reference
semantics (`EvmYul.Yul.exec/eval/call/primCall`) to gas-aware EVMYulLean `X`,
modulo explicit assumptions for gas, PC if exposed, outside world if needed,
jumpdest scanning, and possible out-of-gas.

The lower tower currently has checked theorems for an accepted Yul fragment.
Missing source-complete pieces:

- Yul `gas()` / EVM `GAS`.
- Yul/EVM call/create family: `CREATE`, `CALL`, `CALLCODE`,
  `DELEGATECALL`, `CREATE2`, `STATICCALL`.
- True Yul `leave`.
- Nested user-call expressions and multi-return expression plumbing.
- Object data pseudo-builtins `datasize`, `dataoffset`, `datacopy`.
- A real bridge from `EvmYul.Yul.exec` over `EvmYul.Yul.State` to the
  compiler source semantics over `EvmYul.EVM.State`.

## Important Local Facts

`EvmCompiler.Assembly.PrimOp` currently contains all EVM ops except `GAS` and
raw jumps.  Assembly theorem signatures currently produce
`target.GasOpcodeAbsent`.  Adding `GAS` naively breaks that public theorem.

`EvmCompiler.Structured.BasicOp` is the continuing primitive subset used by
structured/expression layers.  It excludes `GAS`, `PC`, terminal ops, and
call/create.  Preservation for ordinary primitives depends on:

```lean
Assembly.PrimOp.continuingStep? : PrimOp -> Option PrimStep
```

and projection lemmas over `PrimStep.run`.

Nethermind imported semantics split:

- Generic `EvmYul.step` implements shared primitive semantics and Yul `GAS`,
  terminal ops, `SELFDESTRUCT`, etc.
- Generic `EvmYul.step` does **not** implement `CALL`/`CREATE` for EVM; it
  falls through to default for `.EVM, _`.
- Real EVM `CALL`/`CREATE` semantics live in:

```lean
EvmYul.EVM.step (fuel : Nat) (gasCost : Nat)
```

and `EvmYul.EVM.X`.

Yul reference call/create semantics live in `EvmYul.Yul.primCall`, and are not
syntactically the same as EVM `X` because they are Yul-level/gasless-ish and use
Yul contracts/accounts.

## Current Reference Wrapper

We have just added this explicit bridge obligation in
`EvmCompiler/Yul/Reference.lean`:

```lean
structure SourceBridge (program : Program) (fuel : Nat)
    (referenceInitial referenceFinal : State)
    (compilerInitial : EVMState) (outcome : Outcome)
    (obsRel : State -> Outcome -> Prop) : Prop where
  referenceRun :
    execDispatcher fuel program referenceInitial = .ok referenceFinal
  compilerRun :
    Program.Eval fuel program compilerInitial outcome
  observationsAgree :
    obsRel referenceFinal outcome
```

and a checked theorem:

```lean
theorem compile_whole_program_X_bridge_of_source_bridge
  (hBridge : SourceBridge ...)
  (hToExpressions : program.toExpressions? = some exprs)
  (hAccepted : program.Accepted)
  (hEntryPc : compilerInitial.pc = Assembly.Program.pcAfter [])
  (hFits : Structured.AssemblyProgram.PCFitsFrom [] exprs.compile)
  (hCompile : Assembly.compile? exprs.compile = some target)
  (hRuntime : Assembly.RuntimeAssumptions exprs.compile target compilerInitial)
  (hPreconditions :
    forall assemblyFuel assemblyFinal,
      Assembly.Source.runN exprs.compile assemblyFuel compilerInitial =
        .ok assemblyFinal ->
      Structured.eraseControl assemblyFinal =
        Structured.eraseControl outcome.state.evm ->
      Assembly.GasAware.XPreconditionAssumptions target compilerInitial
        assemblyFinal) :
  obsRel referenceFinal outcome /\
    exists assemblyFuel assemblyFinal,
      Assembly.GasAware.XBridgeCertificate exprs.compile target
        assemblyFuel compilerInitial assemblyFinal /\
      Structured.eraseControl assemblyFinal =
        Structured.eraseControl outcome.state.evm
```

This is only a bridge-obligation theorem, not the desired completed theorem.

## Ask

Please critique the correct architecture for completing the compiler theorem
without Lean blowup and without proving the wrong thing.

Specific questions:

1. Should `GAS` be added to the lower assembly syntax and force a second
   gas-aware theorem route that does not claim `GasOpcodeAbsent`, or should
   `gas()` remain an explicit oracle at higher layers compiled some other way?
   What theorem shape is honest?

2. How should `CALL`/`CREATE` be represented in the gasless/source layers?
   Since generic `EvmYul.step` lacks EVM call/create semantics, should the
   source layer delegate to `EvmYul.EVM.step fuel 0`, use a bespoke gas-erased
   wrapper around `EvmYul.EVM.step`, or carry an external-interaction agreement
   assumption between Yul `primCall` and target `X`?

3. For `leave`, is the right implementation a function-level abrupt outcome
   through the functions layer, lowered by continuation/exit labels directly to
   assembly or by adding a lower `leave` mode to locals/structured?

4. What is the smallest next Lean theorem that would strictly reduce the trust
   boundary from `SourceBridge` toward a real Nethermind Yul bridge?

Constraints:

- No `sorry`, `admit`, new `axiom`, `unsafe`, or `partial` in our code.
- Avoid huge opcode-dispatcher unfolding; prefer semantic-family classifiers
  or theorem interfaces.
- Public theorem must be source-complete or explicitly name assumptions; no
  "accepted fragment" pretending to be full Yul.
