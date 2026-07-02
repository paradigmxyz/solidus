# Oracle Request: Procedure Control Layer Placement In Lean Verified Compiler

## Mode

Critique / architecture recommendation. Please be hostile to attractive but brittle layer boundaries.

## Project Context

We are building a Lean verified compiler tower over Nethermind's `EVMYulLean`.
Current lower tower:

```text
Yul reference bridge boundary
Yul AST lowering
Objects
Functions
Locals/scopes
Expressions/literals
Structured control
Labeled assembly
Resolved/encoded EVM
Gas-aware EVMYulLean X bridge
```

The current `Structured` layer has no source-level jumps. Its source syntax is
structured control over straight-line stack code:

```lean
inductive Stmt where
  | code (code : Code)
  | if_ (cond : Code) (body : Block)
  | switch (scrutinee : Code) (cases : List (Word × Block))
      (defaultBody : Option Block)
  | for_ (init : Block) (cond : Code) (post : Block) (body : Block)
  | brk
  | cont
  | leave
  | leaveScope (body : Block)
  | terminal (kind : Assembly.HaltKind)
```

`Structured` compiles directly to labeled assembly, which has labels and
labeled `jump`/`jumpi`. Preservation is already proved for `if`, `switch`,
`for`, `break`, `continue`, terminal outcomes, and the current local
`leaveScope` delimiter.

Current `Functions` is call-capable only by bounded inlining into `Locals`.
This is known to be the wrong long-term semantics for user functions. We want
real procedures/calls.

User's current design direction:

- Extend the control stack with `proc`, `call`, and `leave`.
- Remove `leaveScope`.
- At and above the resulting layer, no source language should have `jump`,
  `jumpi`, raw labels, or dynamic jumps.
- Compile procedure returns using static continuation-token dispatch: each call
  site has a compiler-generated token and return label; callee epilogue switches
  on the token and uses only labeled jumps to static return labels.
- Higher layers pass procedure constructs through:
  - Expressions evaluates args then calls.
  - Locals binds/assigns returns.
  - Functions lowers Yul functions into procs/calls/leaves.

## The Three Options

1. Add a separate Procedure layer **below** Structured and make Structured lower
   into it, possibly passing through a `JUMP`-like construct.

2. Add a separate Procedure layer **above** Structured and make it lower into
   Structured, again probably requiring Structured to pass through a `JUMP`-like
   construct.

3. Merge procedures into Structured itself: `Structured.Program` gets a procedure
   table, `Stmt` gets `call`, `leave` becomes procedure-local abrupt control,
   `leaveScope` disappears, and the Structured-to-Assembly compiler owns
   continuation tokens/epilogue dispatch.

## Current Concern

Options 1 and 2 seem to reintroduce raw jump-like control into an intermediate
source layer, undermining the clean boundary that only labeled assembly has
jumps. Option 3 risks making the `Structured` layer larger and disturbing a
large existing proof, but conceptually procedure calls are the same kind of
control abstraction as `if`/`switch`/`for`.

## Questions

1. Which option is architecturally best for a Lean verified compiler tower?
2. Is it better to merge procedure control into the existing structured control
   layer, or create a new `Control`/`StructuredV2` layer that subsumes the old
   one and later retarget upper layers?
3. Should `leaveScope` be deleted entirely, or kept internally/private as proof
   machinery?
4. What exact source semantics should the procedure layer have? In particular:
   - Is `leave` caught only by procedure boundaries?
   - Does falling off the end of a proc body return normally?
   - How should top-level `leave` be rejected?
   - Should `call` be statement-level stack-shaped at this layer?
5. What theorem shape and invariants should we use for static continuation-token
   dispatch, so the proof works for arbitrary programs?
6. What order do verified compilers / conventional compilers usually use for
   procedures relative to structured control and low-level jumps?

## Constraints

- No new axioms or `sorry`.
- Avoid source-level raw jumps above labeled assembly if possible.
- Public theorem should quantify over arbitrary accepted programs, not per-program
  hand witnesses.
- Keep the adjacent theorem clean: procedure/control layer should preserve source
  semantics to labeled assembly, then existing assembly-to-EVM bridge composes.
- We are proof-engineering constrained: huge opcode or generated-label proofs can
  blow up Lean if not bundled.

## Useful Existing Names

- `EvmCompiler.Structured.Stmt`
- `EvmCompiler.Structured.Program`
- `EvmCompiler.Structured.Program.compile_whole_program_X_bridge_of_run`
- `EvmCompiler.Assembly.Program`
- `EvmCompiler.Functions.Inline.Program`
- `EvmCompiler.Locals.Stmt.leaveScope`

