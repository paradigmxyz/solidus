# Oracle Context: Locals-to-Expressions Preservation Theorem Shape

Repository: `/Users/dan/Projects/evm-compiler`

Lean version/package: `lake build` is green. The new locals layer currently
builds through expression-level preservation:

- `EvmCompiler/Locals/Syntax.lean`
- `EvmCompiler/Locals/Semantics.lean`
- `EvmCompiler/Locals/Compiler.lean`
- `EvmCompiler/Locals/Preservation.lean`

## Goal

We are building a verified compiler tower:

`Locals -> Expressions -> Structured -> labeled assembly -> gas-aware EVMYulLean`

The current bottleneck is the theorem shape for `Locals -> Expressions`.
I want a proof-friendly public theorem, not a replay-certificate boundary, that
can compose into the existing `Expressions.Program.compile_whole_program_*`
theorems.

## Current Locals Design

The source locals layer is a Yul-shaped stack-local layer:

- lexical `Block`s/scopes,
- `let`, assignment, identifier reads,
- `if`, `switch`, `for`, `break`, `continue`, and terminal EVM outcomes,
- primitives are inherited from the lower structured/expression layer.

Important: to avoid proving every EVM opcode commutes past a hidden source
environment, the source locals semantics itself carries the same stack layout as
the target. The source environment is ghost scope/layout data, not a separate
value store.

Relevant definitions:

```lean
abbrev Frame := List Name
abbrev Env := List Frame
abbrev Layout := List Name

namespace Env
def toLayout : Env → Layout
def lookupDepth? (name : Name) (env : Env) : Option Nat :=
  Layout.lookupDepth? name (toLayout env)
def depth : Env → Nat
end Env

structure RunState where
  evm : EVMState
  env : Env

structure RunCtx where
  breakDepth? : Option Nat
  continueDepth? : Option Nat
```

Expression source semantics is offset-aware, so variables under expression
temporaries compile to `DUP(offset + depth)`:

```lean
mutual
  def Expr.runAtOffset {results : Nat} (expr : Expr results)
      (env : Env) (offset : Nat) (state : EVMState) :
      Except EVMException EVMState

  def ExprSeq.runAtOffset {results : Nat} (exprs : ExprSeq results)
      (env : Env) (offset : Nat) (state : EVMState) :
      Except EVMException EVMState
end
```

The compiler has a matching context:

```lean
structure Ctx where
  layout : Layout
  breakDepth? : Option Nat
  continueDepth? : Option Nat
```

and the checked relation is:

```lean
structure Ctx.Matches (runCtx : RunCtx) (env : Env) (ctx : Ctx) : Prop where
  layout : ctx.layout = Env.toLayout env
  breakDepth : ctx.breakDepth? = runCtx.breakDepth?
  continueDepth : ctx.continueDepth? = runCtx.continueDepth?
```

Currently proved in `EvmCompiler/Locals/Preservation.lean`:

```lean
theorem Expr.runAtOffset_compileCode ...
theorem ExprSeq.runAtOffset_compileCode ...
theorem Expr.run_compile ...
theorem Expr.runCondition_compile ...
```

These build without `sorry`.

## Compiler Shape

`Stmt.compile` returns a list of expression-layer statements because cleanup is
explicit:

```lean
def Stmt.compile (ctx : Ctx) :
    Stmt → Option (List Expressions.Stmt × Ctx)
```

Examples:

- `let x := e`: compile `e` as code and leave the value on the target stack;
  extend `ctx.layout`.
- `assign x := e`: compile `e`, then `SWAP depth; POP`.
- `break`: emit cleanup pops to `ctx.breakDepth?`, then lower `.brk`.
- `continue`: emit cleanup pops to `ctx.continueDepth?`, then lower `.cont`.
- `terminal`: emit cleanup pops for all locals, then terminal.
- scoped blocks append regular-path cleanup pops.
- `for` compiles init so its locals remain across condition/body/post, then
  appends regular-path cleanup after the lower loop.

This is semantically nice, but it creates the bottleneck below.

## Bottleneck

The lower `Expressions.Block.run` decrements fuel per lower statement. A single
source locals statement can compile to multiple lower statements, for example
cleanup code plus `brk`, or a `for` statement plus post-loop cleanup.

So a theorem with the same numeric fuel is false or at least unnatural:

```lean
Expressions.Program.run fuel lower initial = Locals.Program.run fuel source initial
```

The existing downstream theorem only needs some successful lower run, because
`Expressions.Program.compile_whole_program_sound_of_run` accepts any fuel:

```lean
(hRun : Expressions.Program.run fuel lower initial = .ok outcome) -> ...
```

So the locals public theorem could reasonably expose an existential lower fuel:

```lean
theorem Locals.Program.compile_preserves_of_run
    (hCompile : Program.toExpressions? program = some lower)
    (hRun : Program.run sourceFuel program initial = .ok sourceOutcome) :
    ∃ lowerFuel lowerOutcome,
      Expressions.Program.run lowerFuel lower initial = .ok lowerOutcome ∧
      Structured.eraseControl lowerOutcome.state =
        Structured.eraseControl sourceOutcome.state ∧
      lowerOutcome.mode = sourceOutcome.mode
```

But I need a Lean-manageable route to prove it, especially through loops.

## Questions

1. What theorem shape is best here?
   - Existential target fuel?
   - Monotonic/sufficient-fuel theorem?
   - Add relational big-step semantics for Locals and Expressions and prove
     executable adequacy later?
   - Refactor lower `Expressions`/`Structured` with cleanup-aware single
     statements to preserve same fuel?

2. If existential target fuel is best, what induction/interface should I use so
   loops do not become painful?

3. Should the public theorem expose exact target outcome equality or only
   `Structured.eraseControl` equality? Variable reads use `DUPn` while source
   can be defined to use the same `DUPn`, so exact state equality is plausible
   except for any future source-level abstraction that ignores PC.

Constraints:

- No `sorry`, no new axioms.
- Avoid brittle fused lemmas.
- The proof should be the model for later layers.
- Prefer structural layer-adjacent theorem boundaries.
- Lean performance matters; avoid giant unfold/simp over full EVM dispatchers.

Useful local fact: expression preservation already avoids opcode blowup by
compiling variables and expressions to structured code and proving code-run
equality directly. The remaining issue is statement/control/fuel accounting.
