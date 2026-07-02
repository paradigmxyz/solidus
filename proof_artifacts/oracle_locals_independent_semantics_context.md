# Oracle request: Locals independent semantics bridge theorem shape

We are in Lean 4, repo `/Users/dan/Projects/evm-compiler`.

Goal: repair a verified compiler tower so every source layer has an independent interpreter/evaluation relation over its own syntax. Structured and Expressions are already fixed. Locals currently has:

- `EvmCompiler/Locals/Syntax.lean`: Locals syntax adds variables/scopes/assignment to the expression/structured-control language.
- `EvmCompiler/Locals/Compiler.lean`: lowers Locals to Expressions by compiling variables to `DUPn`, assignments to `SWAPn; POP`, scope exit to cleanup `POP`s, and procedures to expression procedures.
- `EvmCompiler/Locals/Semantics.lean`: old public `Program.run` still delegates through `program.toExpressions?`; new `namespace Direct` contains an independent executable interpreter over Locals syntax, but it is not yet connected to the public theorem.
- `EvmCompiler/Locals/Preservation.lean`: existing public theorem still uses lowering-defined run. I added checked direct expression-code lemmas, but not the block/statement theorem yet.

Important definitions:

```lean
-- Locals.Compiler
structure Ctx where
  layout : Layout
  breakDepth? : Option Nat
  continueDepth? : Option Nat
  leaveDepth? : Option Nat

def Ctx.cleanupTo? (ctx : Ctx) (targetDepth : Nat) : Option Structured.Code :=
  if targetDepth ≤ ctx.layout.length then
    some (List.replicate (ctx.layout.length - targetDepth)
      (Structured.BasicInstr.op .pop))
  else
    none

-- Changed from erasing empty code to preserving no-op statement shape:
def codeStmt (code : Structured.Code) : List Expressions.Stmt :=
  [Expressions.Stmt.code code]

def finishScoped (outer final : Ctx) (stmts : List Expressions.Stmt) :
    Option Expressions.Block := do
  let cleanup ← final.cleanupTo? outer.layout.length
  some { stmts := stmts ++ codeStmt cleanup }

mutual
  def Expr.compileCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (expr : Expr results) : Option Structured.Code := ...

  def ExprSeq.compileCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (exprs : ExprSeq results) : Option Structured.Code := ...
end

mutual
  def Block.compileOpen (ctx : Ctx) (block : Block) :
      Option (List Expressions.Stmt × Ctx) := ...

  def Stmt.compile (ctx : Ctx) :
      Stmt → Option (List Expressions.Stmt × Ctx)
    | .expr expr => ...
    | .let_ name value => ...
    | .assign name value => ...
    | .assignTop name => ...
    | .block body => ...
    | .if_ cond body => ...
    | .switch scrutinee cases defaultBody => ...
    | .for_ init cond post body => ...
    | .brk => cleanup ++ [Expressions.Stmt.brk]
    | .cont => cleanup ++ [Expressions.Stmt.cont]
    | .leave => cleanup ++ [Expressions.Stmt.leave]
    | .call name => [Expressions.Stmt.call name]
    | .terminal kind => cleanupAll ++ [Expressions.Stmt.terminal kind]
    | .terminalArgs kind args => argsCode ++ [Expressions.Stmt.terminal kind]
end

def Block.compile (ctx : Ctx) (block : Block) : Option Expressions.Block := do
  let (code, finalCtx) ← Block.compileOpen ctx block
  finishScoped ctx finalCtx code
```

Direct interpreter:

```lean
namespace Locals.Direct

mutual
  def Expr.runCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (expr : Expr results) (state : EVMState) :
      Except EVMException EVMState := ...
  def Expr.ExprSeq.runCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (exprs : ExprSeq results) (state : EVMState) :
      Except EVMException EVMState := ...
end

def Expr.runState ...
def Expr.runCondition ...

def Ctx.runCleanupTo ...
def Ctx.runCleanupAll ...

mutual
  def Block.runOpen (program : Program) (ctx : Ctx) :
      Nat → Block → RunState → Except EVMException (Outcome × Ctx)
    | 0, _, _ => invalid
    | fuel+1, ⟨[]⟩, state => .ok (Outcome.regular state, ctx)
    | fuel+1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ← Stmt.run program ctx fuel stmt state
        match outcome.mode with
        | .regular => Block.runOpen program ctx' fuel { stmts := rest } outcome.state
        | .brk | .cont | .leave | .halt _ => .ok (outcome, ctx)

  def Block.runScoped (program : Program) (ctx : Ctx) (block : Block)
      (fuel : Nat) (state : RunState) : Except EVMException Outcome := do
    let (outcome, finalCtx) ← Block.runOpen program ctx fuel block state
    match outcome.mode with
    | .regular =>
        let state' ← Ctx.runCleanupTo finalCtx ctx.layout.length outcome.state
        .ok (Outcome.regular state')
    | .brk | .cont | .leave | .halt _ => .ok outcome

  def Stmt.runForLoop ...

  def Stmt.run (program : Program) (ctx : Ctx) :
      Nat → Stmt → RunState → Except EVMException (Outcome × Ctx)
    | _, .expr expr, state => ...
    | _, .let_ name value, state => ...
    | _, .assign name value, state => ...
    | _, .assignTop name, state => ...
    | _, .block body, state => ...
    | 0, .if_ _ _, _ => invalid
    | fuel+1, .if_ cond body, state => ...
    | 0, .switch _ _ _, _ => invalid
    | fuel+1, .switch scrutinee cases defaultBody, state => ...
    | 0, .for_ _ _ _ _, _ => invalid
    | fuel+1, .for_ init cond post body, state => ...
    | _, .brk, state => cleanup to breakDepth then Outcome.brk
    | _, .cont, state => cleanup to continueDepth then Outcome.cont
    | _, .leave, state => cleanup to leaveDepth then Outcome.leave
    | 0, .call _, _ => invalid
    | fuel+1, .call name, state => split args, push ghost frame,
        run callee body under proc entry ctx, pop/attach returns
    | _, .terminal kind, state => cleanupAll then terminal step/halt
    | _, .terminalArgs kind args, state => eval args then terminal step/halt
end

def Program.run fuel program state :=
  Block.runScoped program Ctx.initial program.body fuel
    (Structured.Program.initialState state)
```

Checked so far in `Locals.Preservation`:

```lean
theorem Direct.Expr.runCode_eq_compileCode
  (hCompile : Expr.compileCode ctx offset expr = some code) :
  Direct.Expr.runCode ctx offset expr state = Structured.Code.run code state

theorem Direct.Expr.ExprSeq.runCode_eq_compileCode ...

theorem Direct.Expr.runState_eq_compileCode ...
theorem Direct.Expr.runCondition_eq_compileCode ...
```

The hard part: choose and prove the right block/statement theorem. Same-fuel equality looks brittle because a Locals statement can lower to multiple `Expressions.Stmt`s (cleanup code plus break/leave, flattened block body plus cleanup, etc.). I changed `codeStmt` to always emit `[Expressions.Stmt.code code]`, so no-op statements are not silently erased, but a source statement may still lower to multiple lower statements. Existing Expressions/Structured fuel decreases per block/statement recursion.

Need advice:

1. What is the best adjacent preservation theorem shape for Locals.Direct -> Expressions? Options:
   - exact equality with same fuel;
   - exists lower fuel for every successful direct run;
   - use an inductive Direct Eval relation and prove Eval -> exists lower fuel;
   - alter Direct fuel accounting to match the flattened lower syntax exactly;
   - introduce a small intermediate “statement list with context” semantics to make the theorem compositional.
2. What helper lemmas/invariants should be introduced first to avoid Lean proof blowup?
3. Is preserving empty `codeStmt` as `[Stmt.code []]` the right move, or should fuel mismatch be handled explicitly?
4. How should procedure calls be handled in the theorem without reintroducing a public call oracle?

Constraints:

- No `sorry`, `axiom`, `unsafe`, or trusted replay certificate.
- The public higher-layer theorem must eventually use the independent Locals interpreter, not lowering-defined `Program.run`.
- It is okay if the theorem returns an existential lower fuel or uses a source-fuel/eval induction, as long as it is a checked compiler theorem and not a public replay witness.
- Keep the proof compositional and avoid repeating the earlier Structured mistake of public compiler-generated evidence.

Please critique the theorem shape and give a concrete Lean implementation plan.
