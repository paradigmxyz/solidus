# Oracle request: critique the locals abstraction refactor

Requested mode: architectural critique plus Lean theorem-interface advice.

We are building a verified compiler tower in Lean for an EVM/Yul compiler.
The current active goal is to repair abstraction leaks before completing the
bridge from imported Nethermind/EVMYulLean Yul semantics into our compiler
tower.

The principle we are enforcing:

- Each layer's source semantics should abstract the feature that layer adds.
- Lower-representation facts should live in that layer's lowering proof, not
  in the source interpreter or in the interface consumed by higher layers.
- For locals specifically: above the locals layer, source semantics should be
  named environments/scopes, not stack slots, stack layouts, `DUP`/`SWAP`/`POP`,
  cleanup depths, or concrete stack cleanup.
- Shared EVM primitive semantics may pass through; primitives are not the
  abstraction introduced by locals.

Please critique the current locals refactor and suggest the cleanest next
theorem/interface shape.

## Tower context

The public spine is:

```text
Nethermind Yul reference semantics
  -> source-complete Yul bridge
  -> objects/data
  -> functions
  -> locals/scopes
  -> expressions/literals
  -> structured control
  -> labeled assembly
  -> resolved EVM assembly
  -> encoded bytecode
  -> gas-aware EVMYulLean runner
```

Assembly/structured/expressions are mostly done. Structured is still an
abstract stack/control layer, so stack effects are legitimate there. The
locals layer is the first layer that should hide stack layout from higher
source semantics.

## Current locals syntax

File: `EvmCompiler/Locals/Syntax.lean`.

Important syntax:

```lean
mutual
  inductive Expr : Nat → Type where
    | lit (value : Word) : Expr 1
    | var (name : Name) : Expr 1
    | code {results : Nat} (code : Structured.Code) : Expr results
    | prim (op : Structured.BasicOp)
        (args : ExprSeq (Expressions.Structured.BasicOp.inputs op)) :
        Expr (Expressions.Structured.BasicOp.outputs op)

  inductive ExprSeq : Nat → Type where
    | nil : ExprSeq 0
    | cons {left right : Nat} (head : Expr left)
        (tail : ExprSeq right) : ExprSeq (left + right)
end

mutual
  structure Block where
    stmts : List Stmt

  inductive Stmt where
    | expr {results : Nat} (expr : Expr results)
    | exprs {results : Nat} (exprs : ExprSeq results)
    | let_ (name : Name) (value : Expr 1)
    | assign (name : Name) (value : Expr 1)
    | assignTop (name : Name)
    | assignTopWithOffset (offset : Nat) (name : Name)
    | block (body : Block)
    | if_ (cond : Expr 1) (body : Block)
    | switch (scrutinee : Expr 1) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Expr 1) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | call (name : Name)
    | terminal (kind : Assembly.HaltKind)
    | terminalArgs (kind : Assembly.HaltKind)
        (args : ExprSeq kind.argCount)
end
```

Some constructors are lower/backend artifacts at this layer:
`.exprs`, `.assignTop`, `.assignTopWithOffset`, `.call`, nonempty `procs`,
and `.code` expressions are rejected by the source-owned locals boundary.
They remain in syntax because the functions layer lowers into this language
and the direct backend still uses them.

## Stack-free locals source semantics

File: `EvmCompiler/Locals/SourceSemantics.lean`.

The stack-free source interpreter uses a named store:

```lean
abbrev Store := Name → Option Word

structure State where
  shared : EvmYul.SharedState .EVM
  vars : Store

structure PrimitiveSemantics where
  eval :
    Structured.BasicOp → EvmYul.SharedState .EVM → List Word →
      Except EVMException (EvmYul.SharedState .EVM × List Word)
  terminal :
    Assembly.HaltKind → EvmYul.SharedState .EVM → List Word →
      Except EVMException (EvmYul.SharedState .EVM)
  lowerCode :
    Structured.Code → State → Except EVMException (State × List Word)

structure Ctx where
  scope : List Name := []
  breakScope? : Option (List Name) := none
  continueScope? : Option (List Name) := none
  leaveScope? : Option (List Name) := none

inductive Mode where
  | regular
  | brk
  | cont
  | leave
  | halt (kind : Assembly.HaltKind)

structure Outcome where
  state : State
  mode : Mode
```

Source expression evaluation is named-store based:

```lean
def Expr.eval {results : Nat} (prim : PrimitiveSemantics)
    (expr : Expr results) (state : State) :
    Except EVMException (State × List Word) :=
  match expr with
  | .lit value => .ok (state, [value])
  | .var name =>
      match state.vars name with
      | some value => .ok (state, [value])
      | none => invalid
  | .code code => prim.lowerCode code state
  | .prim op args => ...
```

Source statements are also named-store/scoped:

- `let_ name expr`: evaluates `expr`, inserts `name` into the store, and
  conses `name` onto `ctx.scope`.
- `assign name expr`: requires `state.vars.contains name`, then updates by
  name.
- `block body`: runs `Block.runScoped`; regular block exit restricts the
  store to the incoming `ctx.scope`.
- `if`, `switch`, `for`, `break`, `continue`, `leave` are Yul-like modes.
- `terminal` / `terminalArgs` halt with explicit EVM terminal kind.
- `.assignTop`, `.assignTopWithOffset`, `.call` are invalid in the locals
  source interpreter.

Relevant block behavior:

```lean
def Block.runOpen ... :
    Nat → Block → State → Except EVMException (Outcome × Ctx)
  | fuel + 1, ⟨stmt :: rest⟩, state => do
      let (outcome, ctx') ← Stmt.run prim program ctx fuel stmt state
      match outcome.mode with
      | .regular => Block.runOpen prim program ctx' fuel { stmts := rest } outcome.state
      | .brk | .cont | .leave | .halt _ => .ok (outcome, ctx)

def Block.runScoped ... : Except EVMException Outcome := do
  let (outcome, _) ← Block.runOpen prim program ctx fuel block state
  match outcome.mode with
  | .regular => .ok (Outcome.regular (outcome.state.restrictTo ctx.scope))
  | .brk | .cont | .leave | .halt _ => .ok outcome
```

We already prove source-level cleanup facts:

```lean
Block.runScoped_regular_eq_restrict
Block.runScoped_regular_drops_not_mem
```

## Source-owned and scoped acceptance

File: `EvmCompiler/Locals/SourceSemantics.lean`:

```lean
def Expr.SourceOwned : Expr results → Prop
  | .lit _ => True
  | .var _ => True
  | .code _ => False
  | .prim _ args => ExprSeq.SourceOwned args

def Stmt.SourceOwned : Stmt → Prop
  | .expr (results := results) expr =>
      results = 0 ∧ Expr.SourceOwned expr
  | .exprs _ => False
  | .let_ _ value => Expr.SourceOwned value
  | .assign _ value => Expr.SourceOwned value
  | .assignTop _ => False
  | .assignTopWithOffset _ _ => False
  | .block body => Block.SourceOwned body
  | .if_ cond body => Expr.SourceOwned cond ∧ Block.SourceOwned body
  | .switch scrutinee cases defaultBody => ...
  | .for_ init cond post body => ...
  | .brk | .cont | .leave => True
  | .call _ => False
  | .terminal _ => True
  | .terminalArgs _ args => ExprSeq.SourceOwned args

def Program.SourceOwned (program : Program) : Prop :=
  program.procs = [] ∧ Block.SourceOwned program.body
```

New in `EvmCompiler/Locals/Syntax.lean`, we added source-level lexical scoping:

```lean
namespace Scope

def Contains (env : List Name) (name : Name) : Prop := name ∈ env

def ExprScoped (env : List Name) : Expr results → Prop
  | .lit _ => True
  | .var name => Contains env name
  | .code _ => False
  | .prim _ args => ExprSeqScoped env args

def Stmt.Scoped (env : List Name) : Stmt → Prop
  | .expr expr => ExprScoped env expr
  | .exprs exprs => ExprSeqScoped env exprs
  | .let_ name value => name ∉ env ∧ ExprScoped env value
  | .assign name value => Contains env name ∧ ExprScoped env value
  | .assignTop name => Contains env name
  | .assignTopWithOffset _ name => Contains env name
  | .block body => Block.Scoped env body
  | .if_ cond body => ExprScoped env cond ∧ Block.Scoped env body
  | .switch scrutinee cases defaultBody =>
      ExprScoped env scrutinee ∧ CaseList.Scoped env cases ∧ Default.Scoped env defaultBody
  | .for_ init cond post body =>
      Block.Scoped env init ∧
        let loopEnv := Block.outEnv env init
        ExprScoped loopEnv cond ∧ Block.Scoped loopEnv post ∧ Block.Scoped loopEnv body
  | .brk | .cont | .leave => True
  | .call _ => True
  | .terminal _ => True
  | .terminalArgs _ args => ExprSeqScoped env args
```

`Stmt.outEnv` only extends on `let`; blocks/if/switch/for do not leak their
inner declarations:

```lean
def Stmt.outEnv (env : List Name) : Stmt → List Name
  | .let_ name _value => name :: env
  | _ => env
```

We also added:

```lean
Stmt.scoped_outEnv_nodup
StmtList.scoped_outEnv_nodup
Block.scoped_outEnv_nodup

def Program.Scoped (program : Program) : Prop :=
  Scope.Block.Scoped [] program.body
```

And strengthened locals source acceptedness:

```lean
def Program.SourceAccepted (program : Program) : Prop :=
  program.WF ∧ Source.Program.SourceOwned program ∧ program.Scoped
```

Question: is it good that shadowing is rejected by source acceptedness while
the raw source interpreter still allows `let` to overwrite by `Store.insert`
when run outside `SourceAccepted`? Or should the source interpreter itself
return invalid on shadowing?

## Direct backend and lowering relation

The old/direct locals interpreter (`EvmCompiler/Locals/Semantics.lean`) is a
stack interpreter:

- Context has concrete `layout : List Name`, cleanup depths, leave depths.
- `let` evaluates an expression and extends `layout`.
- `assign` uses `lookupDepth?`, `SWAPn`, `POP`.
- `block` uses `Ctx.runCleanupTo` to clean back to outer layout.
- `break`/`continue`/`leave` clean to target depths.
- `call` uses hidden procedure return frames.

This direct interpreter is now considered backend/lowering machinery, not the
source contract for higher layers.

`EvmCompiler/Locals/SourceLowering.lean` owns the relation:

```lean
def CtxRel (source : Source.Ctx) (target : Ctx) : Prop :=
  target.layout = source.scope ∧
    target.breakDepth? = source.breakScope?.map List.length ∧
    target.continueDepth? = source.continueScope?.map List.length ∧
    target.leaveDepth? = source.leaveScope?.map List.length ∧
    target.leaveRetc = 0

def CleanupScopeRel (layout scope : List Name) : Prop :=
  layout.drop (layout.length - scope.length) = scope

def CtxHandlersRel (source : Source.Ctx) (target : Ctx) : Prop :=
  (∀ scope, source.breakScope? = some scope → CleanupScopeRel target.layout scope) ∧
  (∀ scope, source.continueScope? = some scope → CleanupScopeRel target.layout scope) ∧
  (∀ scope, source.leaveScope? = some scope → CleanupScopeRel target.layout scope)

def StackStoreRel (layout : List Name) (store : Source.Store)
    (stack : EvmYul.Stack Word) : Prop :=
  stack.length = layout.length ∧
    ∀ {idx name}, layout[idx]? = some name → stack[idx]? = store name

def StateRel (layout : List Name) (source : Source.State)
    (target : RunState) : Prop :=
  target.evm.toSharedState = source.shared ∧
    StackStoreRel layout source.vars target.evm.stack
```

`PrimitiveSound` connects shared primitive semantics to the structured/EVM
step semantics, including terminals.

## New access/scoping bridge

We just added source-lowering access widths:

```lean
namespace Access

def exprWidth : Expr results → Nat
  | .lit _ => 0
  | .var _ => 1
  | .code _ => 0
  | .prim _ args => exprSeqWidth args

def exprSeqWidth : ExprSeq results → Nat
  | .nil => 0
  | .cons (left := left) head tail =>
      max (exprWidth head) (left + exprSeqWidth tail)
```

Then checked:

```lean
SourceLowering.Scope.expr_sourceOwned_of_scoped :
  Locals.Scope.ExprScoped env expr →
    Source.Expr.SourceOwned expr

SourceLowering.Scope.exprSeq_sourceOwned_of_scoped :
  Locals.Scope.ExprSeqScoped env exprs →
    Source.ExprSeq.SourceOwned exprs

SourceLowering.CtxRel.expr_accessible_of_scoped :
  CtxRel source target →
  Locals.Scope.ExprScoped source.scope expr →
  offset + target.layout.length + Access.exprWidth expr ≤ 16 →
    Expr.Accessible source.scope offset expr

SourceLowering.CtxRel.exprSeq_accessible_of_scoped :
  CtxRel source target →
  Locals.Scope.ExprSeqScoped source.scope exprs →
  offset + target.layout.length + Access.exprSeqWidth exprs ≤ 16 →
    ExprSeq.Accessible source.scope offset exprs
```

Then we added scoped `StmtRunBridge` wrappers that derive old lower witnesses
internally:

```lean
StmtRunBridge.expr_from_scoped
StmtRunBridge.letExpr_from_scoped
StmtRunBridge.assign_expr_from_scoped
StmtRunBridge.terminalArgs_from_scoped
```

These consume:

- `CtxRel sourceCtx targetCtx`
- `CtxHandlersRel sourceCtx targetCtx` where relevant
- `sourceCtx.scope.Nodup`
- `Locals.Scope.Stmt.Scoped sourceCtx.scope stmt`
- explicit width bound like
  `targetCtx.layout.length + Access.exprWidth expr ≤ 16`
- `StateRel sourceCtx.scope source target`
- the concrete source run/eval fact

and internally derive:

- `SourceOwned`
- `Expr.Accessible` / `ExprSeq.Accessible`
- `let` freshness
- assignment membership, target slot index, and `idx + 1 ≤ 16`

This is intended to move raw stack/layout evidence out of higher callers.

## Current compositional proof interface

Still in `Locals.SourceLowering`:

```lean
def RunResultRel (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Outcome × Ctx) : Prop :=
  match sourceResult, targetResult with
  | (sourceOutcome, sourceCtx), (targetOutcome, targetCtx) =>
      match sourceOutcome.mode, targetOutcome.mode with
      | .regular, .regular =>
          StateRel sourceCtx.scope sourceOutcome.state targetOutcome.state ∧
            CtxRel sourceCtx targetCtx ∧
            CtxHandlersRel sourceCtx targetCtx
      | .brk, .brk =>
          ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
      | .cont, .cont =>
          ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
      | .leave, .leave =>
          ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
      | .halt sourceKind, .halt targetKind =>
          targetOutcome.state.evm.toSharedState = sourceOutcome.state.shared ∧
          sourceKind = targetKind
      | _, _ => False

def StmtRunBridge (...) : Prop :=
  ∃ sourceResult targetResult,
    Source.Stmt.run prim program sourceCtx fuel stmt source = .ok sourceResult ∧
    Direct.Stmt.run program targetCtx fuel stmt target = .ok targetResult ∧
    RunResultRel sourceResult targetResult

def BlockOpenRunBridge (...) : Prop :=
  ∃ sourceResult targetResult,
    Source.Block.runOpen prim program sourceCtx fuel block source = .ok sourceResult ∧
    Direct.Block.runOpen program targetCtx fuel block target = .ok targetResult ∧
    RunResultRel sourceResult targetResult
```

Checked constructors include:

```lean
RunResultRel.regular/brk/cont/leave/halt_shared
StmtRunBridge.expr/letExpr/assign_expr/brk/cont/terminal/terminalArgs
StmtRunBridge.expr_from_scoped/letExpr_from_scoped/assign_expr_from_scoped/terminalArgs_from_scoped
BlockOpenRunBridge.nil
BlockOpenRunBridge.cons_from_stmt_bridge
```

The current plan is to build a structural block theorem consuming
`Scope.Block.Scoped`, `Source.Block.SourceOwned`, width/resource bounds, and
exact source run evidence, and producing `BlockOpenRunBridge`, eventually
replacing the remaining public locals route through the direct stack
interpreter.

## Questions for the oracle

1. Is the overall locals abstraction boundary right?
   Source semantics = named store/scopes; direct backend = stack layouts and
   cleanup; `SourceLowering` owns the relation.

2. Should no-shadowing/freshness be enforced in the source interpreter itself,
   or is it cleaner to keep the interpreter total-ish over raw syntax and
   reject shadowing in `SourceAccepted`/`Scope.Scoped`?

3. Should `SourceOwned` and `Scope.Scoped` remain separate predicates?
   `SourceOwned` rejects backend-only constructs, while `Scoped` rejects
   unbound reads/shadowing and raw `.code` expressions but currently allows
   `.call` because calls are syntactically scoped at higher/function layers.
   Since `SourceAccepted` requires both, is this split good, or should there be
   one combined `Lowerable`/`SourceWellFormed` predicate?

4. Where should stack-width/accessibility bounds live?
   Current wrappers take explicit bounds like
   `targetCtx.layout.length + Access.exprWidth expr ≤ 16`.
   Should those be part of `SourceAccepted`, a separate `CompileAccepted`, a
   source-invariant record used only by lowering theorems, or bundled into a
   `Lowerable` predicate?

5. Is `RunResultRel` the right public adjacent relation?
   Regular fallthrough exposes next source context/handler relations; abrupt
   exits expose only some retained layout/state relation; terminal halts expose
   shared-state/kind relation. Is this too existential for future structural
   recursion, or exactly the right way to hide cleanup depths?

6. What theorem shape should we aim for next?
   I am considering something like:

```lean
BlockOpenRunBridge.of_source_run_scoped :
  PrimitiveSound prim →
  CtxRel sourceCtx targetCtx →
  CtxHandlersRel sourceCtx targetCtx →
  sourceCtx.scope.Nodup →
  Scope.Block.Scoped sourceCtx.scope block →
  Source.Block.SourceOwned block →
  BlockAccessBound sourceCtx targetCtx block →
  StateRel sourceCtx.scope source target →
  Source.Block.runOpen prim program sourceCtx fuel block source = .ok sourceResult →
    ∃ targetResult,
      Direct.Block.runOpen program targetCtx fuel block target = .ok targetResult ∧
      RunResultRel sourceResult targetResult
```

   Is this too many premises? Should these be bundled as a `SourceInvariant` or
   `LoweringInvariant` record, similar to what we started doing in the
   functions layer?

7. Are we accidentally leaking any stack concept upward by adding
   `Access.exprWidth` and width bounds to `Locals.SourceLowering`?
   My current view is that this is a compiler-resource bound, not source
   semantics, so it belongs in lowering/compile acceptance, not in
   `Locals.Source`.

8. Is the treatment of block scopes right?
   `Stmt.outEnv` for `.block`, `.if_`, `.switch`, and `.for_` is unchanged,
   while `for` conditions/post/body see declarations from init through
   `loopEnv := Block.outEnv env init`. Source `Block.runScoped` drops
   declarations at regular block exit. This is intended to match Yul/Solidity.

Please be a critic. Point out theorem smells, missing invariants, wrong
abstraction boundaries, or a better next proof interface. We do not need Lean
syntax for every proof, but concrete theorem shapes and bundling advice would
be especially helpful.
