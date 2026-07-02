# Oracle Request: Correct Design for Yul `leave` in a Verified Compiler Tower

## Mode

Design critique / architecture advice. Please be hostile to hacks. I want the right semantic layer and proof interface, not a quick encoding.

## Project Context

We are building a Lean verified compiler tower over Nethermind's `EVMYulLean`.

Current tower:

```text
Nethermind Yul reference semantics
  -> Yul AST bridge
  -> objects/data
  -> functions
  -> locals/scopes
  -> expressions/literals
  -> structured control
  -> labeled assembly
  -> resolved EVM assembly / bytecode
  -> gas-aware EVMYulLean target
```

The low layers share EVM state and primitive opcode semantics. Source layers abstract away gas and concrete PCs. The gas-aware bridge carries explicit assumptions about gas, out-of-gas, external interaction agreement, and jumpdest scanning.

Important current design:

- `Structured.Mode` has `.regular`, `.brk`, `.cont`, `.leave`, `.halt kind`.
- `Structured.Outcome` and lower executable semantics can propagate `.leave`.
- Structured and Expressions do **not** have public `leave` syntax, so preservation currently proves no existing source run can produce `.leave`.
- Locals has Yul-style variables/scopes/blocks/loops, but no `leave` syntax. Locals executable semantics now pattern-matches `.leave` exhaustively, but the public relational semantics has no way to produce it.
- Functions syntax has `Stmt.leave` and statement-level `Stmt.call targets functionName args`.
- Functions accepted theorem currently rejects `leave` with `Program.NoLeave`.
- Calls are currently lowered by bounded inlining into the locals layer:
  - bind params as locals;
  - initialize return variables;
  - inline function body;
  - assign return variables back to caller targets.
- Functions semantics is currently an elaboration semantics through `Inline.Program.toLocals?` and then Locals semantics. This means calls are "semantics by inlining" for now.

Relevant snippets:

```lean
-- EvmCompiler/Structured/Syntax.lean
inductive Mode where
  | regular
  | brk
  | cont
  | leave
  | halt (kind : Assembly.HaltKind)
```

```lean
-- EvmCompiler/Functions/Syntax.lean
inductive Stmt where
  | expr (expr : Expr 0)
  | let_ (name : Name) (value : Expr 1)
  | assign (name : Name) (value : Expr 1)
  | block (body : Block)
  | if_ (cond : Expr 1) (body : Block)
  | switch (scrutinee : Expr 1) (cases : List (Word × Block))
      (defaultBody : Option Block)
  | for_ (init : Block) (cond : Expr 1) (post : Block) (body : Block)
  | brk
  | cont
  | leave
  | call (targets : List Name) (functionName : Name)
      (args : List (Expr 1))
  | terminal (kind : Assembly.HaltKind)
  | terminalArgs (kind : Assembly.HaltKind)
      (args : Locals.ExprSeq kind.argCount)

inductive Stmt.WF : Bool → Bool → Bool → Stmt → Prop where
  ...
  | leave {canBreak canContinue inFunction : Bool}
      (hAllowed : inFunction = true) :
      Stmt.WF canBreak canContinue inFunction .leave
```

```lean
-- EvmCompiler/Functions/Compiler.lean
-- non-inline function-free lowering still rejects calls and leave:
| .leave => none
| .call _targets _functionName _args => none

-- bounded inline lowering currently rejects leave:
| .leave => none
| .call targets functionName args =>
    match fuel with
    | 0 => none
    | fuel' + 1 => do
        let fn ← FunList.find? functionName functions
        let paramCode ← bindParams fn.params args
        let body ← Block.toLocals? fuel' functions fn.body
        let returnCode := initReturns fn.returns
        let assignCode ← assignReturns targets fn.returns
        some (.block
          { stmts := paramCode ++ returnCode ++ body.stmts ++ assignCode })

def Accepted (program : Program) : Prop :=
  program.WF ∧ program.NoLeave ∧
    ∃ lower : Expressions.Program, toExpressions? program = some lower
```

```lean
-- EvmCompiler/Functions/Semantics.lean
-- This is currently elaboration semantics, not an independent function-call semantics.
inductive Inline.Program.Eval :
    Nat → Functions.Program → EVMState → Outcome → Prop where
  | ofLocals {fuel : Nat} {program : Functions.Program}
      {initial : EVMState} {outcome : Outcome} {lower : Locals.Program}
      (hToLocals : Inline.Program.toLocals? program = some lower)
      (hEval :
        Locals.Stmt.ScopedEval Locals.RunCtx.initial fuel lower.body
          (Locals.Program.initialState initial) outcome) :
      Eval fuel program initial outcome
```

## Design Problem

In Yul, `leave` exits the current function. It is similar to abrupt control effects like `break` and `continue`, but the delimiter is a function boundary, not a loop:

- `break`: exits nearest loop.
- `continue`: exits current loop body and still runs the loop post block.
- `leave`: exits nearest function and should skip all remaining statements in the function body, including loop post blocks.

I briefly tried a compiler hack:

- introduce a private local `__evmcompiler.leave` flag in each inlined function call;
- compile `leave` to setting the flag;
- wrap rest-of-sequence in `if iszero(flag)`;
- rewrite loops so the flag prevents further iterations/post blocks.

This smelled bad: it encodes control flow through mutable source locals, risks name collisions, requires systematic guarded lowering everywhere, and obscures the semantic proof. The user asked us to stop and think through the right design.

## Questions

1. Which layer should own `leave`?
   - Should `leave` be added to Locals syntax/semantics because locals/scopes are where Yul blocks/functions are already close?
   - Should it remain only in Functions syntax/semantics as a function-delimited effect?
   - Should Structured/Expressions/Locals all expose `leave` as syntax, or merely have an outcome channel available for higher layers?

2. Should the Functions layer stop being "semantics by inlining" and instead get an independent function-call semantics?
   - Environment: function definitions, params, returns, local env, call stack / frame semantics.
   - Outcomes: regular, break, continue, leave, halt, error/fuel.
   - Function-call rule: evaluate args, bind params/returns, run body, consume `leave` at the function boundary, copy returns to call targets.

3. What is the right compiler representation of `leave` to lower to the existing Locals/Expressions/Structured tower?
   - Add `leave` syntax to Locals and compile it lower using a continuation/label target?
   - Add a new lower layer between Functions and Locals for delimited control / function exits?
   - Compile Functions directly to Structured or Assembly with explicit generated labels for function exits, bypassing Locals for control?
   - Use continuation-passing or defunctionalized contexts for statement lowering?

4. Should we use a monad somewhere?
   - For semantics: an `ExceptT Control`-style outcome monad over state/fuel?
   - For compilation: a state monad carrying fresh labels, local layout, and current delimiters (`break`, `continue`, `leave`)?
   - In Lean, would this help proofs or cause term blowup? What proof interface should we expose?

5. What theorem shape should we aim for?
   - Adjacent theorem from independent Functions semantics to lower layer execution.
   - How to handle `leave` as consumed at function boundaries but propagated through nested blocks/loops/calls?
   - How to avoid special-case fused lemmas like "leave inside loop inside call"?

## Constraints

- No `sorry`, `admit`, new `axiom`, `unsafe`, or proof-critical assumptions for compiler correctness.
- Avoid broad unfolding of opcode semantics; lower primitive semantics should pass through existing verified layers.
- Prefer generic compositional theorem families over combo-case lemmas.
- The final source-language goal is complete Yul, eventually checked against Nethermind Yul reference semantics.
- Current lower layers already have theorem-bearing paths to gas-aware EVM; we should preserve that tower if possible.

## Useful Failure

A useful answer can say:

- "The flag idea is acceptable if proven via X invariant," or "reject it for these precise reasons."
- "The right next layer is a delimited-control IR between Functions and Locals," with a minimal syntax/semantics/compiler theorem.
- "Do independent function semantics first; do not lower leave yet," with theorem shapes.
- "Use monadic semantics but relational proofs," or "avoid monads in Lean here because ..."

