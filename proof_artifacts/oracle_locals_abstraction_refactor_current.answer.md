## Short verdict

The boundary direction is right: **locals source = named store/scopes**, **direct locals = stack-layout backend**, and **`SourceLowering` owns the relation**.

But I see several interface smells that are worth fixing before building the big structural theorem:

1. `Source.PrimitiveSemantics.lowerCode` and the `program` parameter in source runs still expose lower/backend structure.
2. `Scope.Scoped` currently partly means “lexically scoped” and partly means “source-owned”; this is muddled.
3. `RunResultRel` is too existential for abrupt exits; it hides too much source-level handler information.
4. Width/access bounds should be compile/lowering acceptance, not source acceptance, and should mention source environments, not target layouts.
5. The raw interpreter silently overwriting active names is okay only if raw runs are not public. If you want runtime scope enforcement, do it consistently, not only for `let`.

Below is the concrete critique.

---

## 1. Boundary: basically right, but `lowerCode` is a leak

Your intended split is correct:

```text
SourceSemantics: named vars, source scopes, source modes
Direct/Semantics: stack layout, cleanup depths, DUP/SWAP/POP
SourceLowering: relation between them
```

However, this part is a real leak:

```lean
structure PrimitiveSemantics where
  ...
  lowerCode : Structured.Code → State → Except EVMException (State × List Word)
```

Since `.code` is `SourceOwned = False`, accepted locals source programs should never need `lowerCode`. But every source theorem currently carries a primitive semantics that knows how to execute lower structured code. That is lower-representation knowledge in the source interface.

I would split this:

```lean
structure SourcePrimSemantics where
  eval :
    Structured.BasicOp → SharedState .EVM → List Word →
      Except EVMException (SharedState .EVM × List Word)
  terminal :
    Assembly.HaltKind → SharedState .EVM → List Word →
      Except EVMException (SharedState .EVM)

structure RawPrimSemantics extends SourcePrimSemantics where
  lowerCode :
    Structured.Code → Source.State →
      Except EVMException (Source.State × List Word)
```

Then the actual source interpreter should either reject `.code` directly, or `.code` should live only in a raw/backend interpreter. If keeping the current interpreter, at least prove and use:

```lean
Expr.eval_irrel_lowerCode_of_sourceOwned
Stmt.run_irrel_lowerCode_of_sourceOwned
Block.runOpen_irrel_lowerCode_of_sourceOwned
```

Same issue with `Source.Stmt.run prim program ...`: source-owned locals reject `.call` and `procs`, so the source interpreter should ideally not take a `program` parameter. If raw syntax needs it, hide that behind a raw namespace.

---

## 2. Shadowing: static rejection is fine, but raw semantics is not a true raw lexical semantics

Rejecting shadowing in `SourceAccepted`/`Scope.Scoped` is semantically fine **if all public correctness theorems require acceptedness**.

But note: the raw interpreter is not merely permissive; it is semantically wrong for shadowing because

```lean
Store := Name → Option Word
```

cannot represent two active bindings with the same `Name`. Example:

```yul
let x := 1
{
  let x := 2
}
-- raw Store-based semantics leaves x = 2 unless shadowing is rejected
```

So you have two clean options.

### Option A — preferred if raw interpreter is internal

Keep the raw interpreter simple, but never expose it as “the” source semantics without acceptedness. Public APIs should use a subtype/record:

```lean
structure SourceProgram where
  program : Program
  accepted : program.SourceAccepted
```

Then the overwrite behavior is irrelevant outside invalid programs.

### Option B — if source interpreter is public

Make scope checking dynamic and consistent. Do **not** only check shadowing on `let`; that is only a partial fix. Currently `Expr.eval` has no environment parameter, so a stale out-of-scope store entry can make an unscoped variable read succeed.

A checked source evaluator would look more like:

```lean
Expr.evalChecked :
  List Name → PrimitiveSemantics → Expr results → State →
    Except EVMException (State × List Word)
```

with:

```lean
| .var name =>
    if name ∈ env then
      ...
    else
      invalid
```

and `let` should check `name ∉ ctx.scope`, not `state.vars name = none`, because stale out-of-scope store entries are intentionally possible/useful.

So: static `Scoped` is still necessary. A dynamic shadow check alone is not sufficient.

---

## 3. Keep `SourceOwned` and `Scoped` separate, but add a combined public predicate

The split is conceptually good:

- `SourceOwned`: rejects backend-only constructors.
- `Scoped`: checks local lexical binding/freshness.

But the current implementation muddies the split:

```lean
def ExprScoped env : Expr results → Prop
  | .code _ => False
```

Rejecting `.code` is not really lexical scoping; it is ownership/layering. This is why you now have a theorem like:

```lean
expr_sourceOwned_of_scoped :
  ExprScoped env expr → SourceOwned expr
```

That theorem is a smell. “Scoped” should not imply “source-owned”.

Cleaner shape:

```lean
def ExprLexicallyScoped (env : List Name) : Expr results → Prop
  | .lit _ => True
  | .var name => name ∈ env
  | .code _ => True      -- no named locals, if Structured.Code has none
  | .prim _ args => ExprSeqLexicallyScoped env args
```

Then:

```lean
def Expr.SourceWF env e :=
  Expr.SourceOwned e ∧ ExprLexicallyScoped env e
```

Likewise for statements/blocks:

```lean
structure Block.SourceWF (env : List Name) (block : Block) : Prop where
  owned  : Source.Block.SourceOwned block
  scoped : Scope.Block.Scoped env block
```

For lowering:

```lean
structure Block.Lowerable (env : List Name) (block : Block) : Prop where
  sourceWF : Block.SourceWF env block
  access   : Access.BlockBound env block
```

So low-level lemmas can still use the separate components, but theorem callers consume one bundled predicate.

One more concrete source-owned issue: if

```lean
Stmt.terminal kind
```

means “halt using already-stacked arguments”, then it is not source-owned except for nullary halts. In a stack-free source semantics, this should likely be:

```lean
| .terminal kind => kind.argCount = 0
```

or `.terminal` should be backend-only and source should use only `.terminalArgs`.

---

## 4. Width/access bounds belong to compile/lowering acceptance, not source acceptance

Do not put the EVM `DUP`/`SWAP` 16-bound into `SourceAccepted`. A source program with 30 live locals is source-valid even if this backend cannot lower it without spilling.

Recommended split:

```lean
def Program.SourceAccepted :=
  program.WF ∧ program.SourceOwned ∧ program.Scoped

def Program.CompileAccepted :=
  program.SourceAccepted ∧ Access.ProgramBound program
```

For theorem interfaces, bounds should be stated over the **source environment**, not the target layout:

```lean
def Access.ExprBound (env : List Name) (offset : Nat) (expr : Expr results) : Prop :=
  offset + env.length + Access.exprWidth expr ≤ 16
```

Then use `CtxRel` internally to rewrite `targetCtx.layout.length = sourceCtx.scope.length`.

So avoid public premises like:

```lean
targetCtx.layout.length + Access.exprWidth expr ≤ 16
```

Prefer:

```lean
Access.ExprBound sourceCtx.scope 0 expr
```

or bundled:

```lean
hstmt : Stmt.Lowerable sourceCtx.scope stmt
```

Also audit the off-by-one meaning of `exprWidth`. With:

```lean
exprWidth (.var _) = 1
```

and a bound

```lean
layout.length + exprWidth expr ≤ 16
```

a frame of length `16` cannot read even the deepest local, although EVM `DUP16` should access the 16th stack item. Maybe your old `Accessible` convention justifies this, but it looks suspicious. If `exprWidth` measures extra temporary results above locals, then `.var` probably wants width `0`, and `ExprSeq.cons` should account for produced results.

If the current bound is intentionally conservative, name it as a small-frame bound, not merely an access-width bound.

---

## 5. `RunResultRel` should expose source handler scopes for abrupt exits

Current abrupt cases:

```lean
| .brk, .brk =>
    ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
```

This hides too much. It is fine for propagation-only block proofs, but too weak for future constructs that catch modes, especially `for`.

A loop catching `break` needs to know that the target state corresponds to the source break target scope, not merely some layout.

Better:

```lean
def RunResultRelAt
    (entryCtx : Source.Ctx)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Direct.Outcome × Direct.Ctx) : Prop :=
  match sourceResult, targetResult with
  | (sourceOutcome, sourceCtx'), (targetOutcome, targetCtx') =>
      match sourceOutcome.mode, targetOutcome.mode with
      | .regular, .regular =>
          StateRel sourceCtx'.scope sourceOutcome.state targetOutcome.state ∧
          CtxInv sourceCtx' targetCtx'

      | .brk, .brk =>
          ∃ scope,
            entryCtx.breakScope? = some scope ∧
            StateRel scope sourceOutcome.state targetOutcome.state

      | .cont, .cont =>
          ∃ scope,
            entryCtx.continueScope? = some scope ∧
            StateRel scope sourceOutcome.state targetOutcome.state

      | .leave, .leave =>
          ∃ scope,
            entryCtx.leaveScope? = some scope ∧
            StateRel scope sourceOutcome.state targetOutcome.state

      | .halt sourceKind, .halt targetKind =>
          targetOutcome.state.evm.toSharedState = sourceOutcome.state.shared ∧
          sourceKind = targetKind

      | _, _ => False
```

Here `CtxInv` can bundle:

```lean
structure CtxInv (sourceCtx : Source.Ctx) (targetCtx : Direct.Ctx) : Prop where
  rel      : CtxRel sourceCtx targetCtx
  handlers : CtxHandlersRel sourceCtx targetCtx
  nodup    : sourceCtx.scope.Nodup
```

This still hides cleanup depths and stack layout from higher layers, but it preserves the source-level fact needed for catchers.

---

## 6. Bundle the next theorem, but keep static and dynamic invariants separate

Your proposed theorem has the right logical shape, but too many premises. I would bundle as follows.

```lean
structure LoweringStateRel
    (sourceCtx : Source.Ctx)
    (targetCtx : Direct.Ctx)
    (source : Source.State)
    (target : Direct.RunState) : Prop where
  ctx   : CtxInv sourceCtx targetCtx
  state : StateRel sourceCtx.scope source target
```

Then:

```lean
structure Block.Lowerable
    (env : List Name) (block : Block) : Prop where
  owned  : Source.Block.SourceOwned block
  scoped : Scope.Block.Scoped env block
  access : Access.BlockBound env block
```

Target theorem:

```lean
theorem BlockOpen.sound_of_source_run
    (hprim : PrimitiveSound prim)
    (hinv :
      LoweringStateRel sourceCtx targetCtx source target)
    (hblock :
      Block.Lowerable sourceCtx.scope block)
    (hrun :
      Source.Block.runOpen prim sourceCtx fuel block source = .ok sourceResult) :
    ∃ targetResult,
      Direct.Block.runOpen program targetCtx fuel block target = .ok targetResult ∧
      RunResultRelAt sourceCtx sourceResult targetResult
```

Then separately provide the compatibility wrapper:

```lean
theorem BlockOpenRunBridge.of_source_run_lowerable :
  ... → BlockOpenRunBridge ...
```

I would make the direct theorem returning `∃ targetResult, ...` the main proof theorem, and keep `BlockOpenRunBridge` as a convenience proposition. Existential bridge props are often awkward for recursive proofs.

You will likely also want the statement-level theorem mutually:

```lean
theorem Stmt.sound_of_source_run :
  PrimitiveSound prim →
  LoweringStateRel sourceCtx targetCtx source target →
  Stmt.Lowerable sourceCtx.scope stmt →
  Source.Stmt.run prim program sourceCtx fuel stmt source = .ok sourceResult →
    ∃ targetResult,
      Direct.Stmt.run program targetCtx fuel stmt target = .ok targetResult ∧
      RunResultRelAt sourceCtx sourceResult targetResult
```

The block theorem then uses it in the cons case.

---

## 7. `Access.exprWidth` is not an upward leak if isolated properly

Your current view is right: this is a backend/compiler-resource bound, not source semantics.

But enforce that by interface:

- no `Expr.Accessible` in higher-layer theorem statements;
- no `targetCtx.layout.length` in higher-layer theorem statements;
- no `DUP`/`SWAP` vocabulary outside `SourceLowering`/backend acceptance;
- define `CompileAccepted` separately from `SourceAccepted`.

So the bound should be visible as something like:

```lean
Access.BlockBound env block
```

not as:

```lean
Expr.Accessible layout offset expr
```

and not as direct stack evidence.

---

## 8. Block scope treatment looks right, modulo Yul-spec confirmation

Given the intended Yul/Solidity discipline, this is the right static behavior:

```lean
Stmt.outEnv env (.block _)  = env
Stmt.outEnv env (.if_ _ _)  = env
Stmt.outEnv env (.switch ...) = env
Stmt.outEnv env (.for_ ...) = env
```

and for loops:

```lean
let loopEnv := Block.outEnv env init
```

with `cond`, `post`, and `body` scoped under `loopEnv`.

That matches the usual Yul shape: declarations in the `for` init are visible in the condition/post/body, but do not leak after the loop. I am slightly uncertain about the exact Nethermind/Yul reference restriction here, so verify against the imported semantics, but architecturally this is the right model.

Add/keep theorems making this operationally explicit:

```lean
Block.runScoped_regular_eq_restrict
Stmt.run_for_regular_restricts_to_outer_scope
Stmt.run_for_break_restricts_to_break_scope
Stmt.run_for_continue_restricts_to_continue_scope
```

Even if source states retain stale out-of-scope store entries, prove an observational theorem:

```lean
def Store.EquivOn (env : List Name) (s₁ s₂ : Source.Store) : Prop :=
  ∀ name, name ∈ env → s₁ name = s₂ name
```

Then:

```lean
Expr.eval_congr_of_scoped :
  Scope.ExprScoped env expr →
  Store.EquivOn env s₁.vars s₂.vars →
  s₁.shared = s₂.shared →
  ...
```

This theorem justifies why `StateRel` may ignore source variables outside the current layout/scope.

---

## Main recommended next move

Before proving the big block theorem, I would do these three refactors:

1. **Introduce bundled invariants**:

```lean
CtxInv
LoweringStateRel
Block.SourceWF
Block.Lowerable
```

2. **Strengthen `RunResultRel` to `RunResultRelAt sourceCtx`**, with abrupt cases retaining source handler scopes.

3. **Move public bounds to source-env form**:

```lean
Access.ExprBound sourceCtx.scope offset expr
Access.BlockBound sourceCtx.scope block
```

Then prove:

```lean
BlockOpen.sound_of_source_run :
  PrimitiveSound prim →
  LoweringStateRel sourceCtx targetCtx source target →
  Block.Lowerable sourceCtx.scope block →
  Source.Block.runOpen prim sourceCtx fuel block source = .ok sourceResult →
    ∃ targetResult,
      Direct.Block.runOpen program targetCtx fuel block target = .ok targetResult ∧
      RunResultRelAt sourceCtx sourceResult targetResult
```

That theorem has the right abstraction level: source callers provide named-scope well-formedness and compile-resource bounds; all stack layout, cleanup depth, slot lookup, and `DUP`/`SWAP` evidence stays inside `SourceLowering`.