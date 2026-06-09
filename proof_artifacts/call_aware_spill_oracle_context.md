# CallAwareSpill Recursive Block Proof Strategy Request

Repository: `/Users/dan/Projects/evm-compiler`
File: `EvmCompiler/Functions/CallAwareSpill.lean`

## Goal

We are extending the checked function-layer spill compiler so `.block body`
inside Solidity-shaped Yul can recursively compile nested internal-call splice
points, instead of treating the entire block as a source-owned/non-call span.

Constraints:
- No `sorry`, no new axioms.
- Do not weaken scoped cleanup invariants.
- Compiler-generated evidence must remain checked, not public theorem input.
- The executable compiler currently has:

```lean
mutual
def compileStmt? ... : Stmt → Option Plan
  | .call targets functionName args => compileCall? ...
  | .leave => compileLeave? ...
  | .block body => compileBlockStmt? ... body
  | stmt => compileNonCallStmtSpan? ... stmt

def compileStmtList? ... : List Stmt → Option Plan := ...
def compileBlockOpen? ... (block : Block) : Option Plan := ...
def compileBlockStmt? ... (body : Block) : Option Plan := do
  let bodyPlan ← compileBlockOpen? ... body
  let restrictedLayout := SpillLayout.restrictToScope sourceScope bodyPlan.layout
  if SpillLayout.checked? range sourceScope bodyPlan.stackLayout restrictedLayout then
    some { sourceScope := sourceScope
           stackLayout := bodyPlan.stackLayout
           layout := restrictedLayout
           block := bodyPlan.block }
  else none
end
```

Support predicates were changed from transparent recursive `def`s to mutual
inductives:

```lean
mutual
inductive StmtRegularOpenSupported (returns : List Name) : Stmt → Prop
  | call : StmtRegularOpenSupported returns (.call targets functionName args)
  | block : BlockRegularOpenSupported returns body →
      StmtRegularOpenSupported returns (.block body)
  | sourceOwned : SourceLowering.SourceToLocals.Stmt.SourceOwned returns stmt →
      StmtRegularOpenSupported returns stmt

inductive StmtListRegularOpenSupported ...
inductive BlockRegularOpenSupported ...
end

mutual
inductive StmtOpenSupported (returns : List Name) : Stmt → Prop
  | call ...
  | leave : StmtOpenSupported returns .leave
  | block : BlockOpenSupported returns body →
      StmtOpenSupported returns (.block body)
  | sourceOwned : SourceLowering.SourceToLocals.Stmt.SourceOwned returns stmt →
      StmtOpenSupported returns stmt

inductive StmtListOpenSupported ...
inductive BlockOpenSupported ...
end
```

We added executable fuel-based support checkers and soundness theorems.

## Main Current Failure

The old theorem family is staged as separate declarations:

```lean
theorem compileStmt?_regular_sound_meta_given_callReplay ... :
  compileStmt? ... stmt = some plan →
  StmtRegularOpenSupported returns stmt →
  ... →
  Source.Stmt.run ... stmt source = .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
  global CallReplayFor ... →
  ∃ final exprFuel, Expressions.Block.run ... plan.block target =
    .ok (Expressions.Outcome.regular (target.withEVM final)) ∧ ...

theorem compileStmtList?_regular_sound_meta_given_callReplay ... : ...

theorem compileBlockOpen?_regular_sound_meta_given_callReplay ... : ...
```

`compileStmt?` now compiles `.block` through `compileBlockStmt?`, so the `.block`
branch can no longer call:

```lean
compileNonCallStmtSpan?_regular_sound_meta_of_source_run
```

The desired `.block` proof pattern is analogous to an earlier conservative
scoped-spill theorem:

1. Decompose `compileBlockStmt?`:

```lean
theorem compileBlockStmt?_eq_some ... :
  compileBlockStmt? ... body = some plan →
  ∃ bodyPlan restrictedLayout,
    compileBlockOpen? ... body = some bodyPlan ∧
    restrictedLayout = SpillLayout.restrictToScope sourceScope bodyPlan.layout ∧
    SpillLayout.checked? range sourceScope bodyPlan.stackLayout restrictedLayout = true ∧
    plan = { sourceScope := sourceScope
             stackLayout := bodyPlan.stackLayout
             layout := restrictedLayout
             block := bodyPlan.block }
```

2. From source `.block body` regular run, unfold `Source.Stmt.run` and
`Source.Block.runScoped`, extract an open body run:

```lean
Source.Block.runOpen ... body source =
  .ok (Source.Outcome.regular inner, finalCtx)
```

and final source state is `inner.restrictTo sourceCtx.scope`.

There is a lemma:

```lean
Source.runScoped_regular_eq_restrict :
  Block.runScoped prim program ctx block fuel state =
    .ok (Outcome.regular out) →
  ∃ inner finalCtx,
    Block.runOpen prim program ctx fuel block state =
      .ok (Outcome.regular inner, finalCtx) ∧
    out = inner.restrictTo ctx.scope
```

3. Recursively apply block-open regular preservation to `bodyPlan`.
4. Restrict target/source relation with:

```lean
SpillStateRel.restrictToScope hRestricted hCheck hBodyRel
SpillLayout.StoreDefined.restrictToScope
```

## Problem

Because `compileStmt?_regular_sound_meta_given_callReplay` needs
`compileBlockOpen?_regular_sound_meta_given_callReplay` for its `.block` case,
and the block-open theorem depends on the statement-list theorem, which depends
on the statement theorem, the regular proof family appears to need a `mutual`
theorem block.

The exact-length, callReplayBelow, halt, and leave theorem families have the
same issue for `.block`.

Current focused errors after mechanical support-inversion cleanup include:

```text
10134/10135: .block branch in compileStmt?_leave_sound_exact_given_callReplay
  still expects compileNonCallStmtSpan? and SourceOwned.
12693/12697: .block branch in compileStmt?_regular_sound_meta_given_callReplay
  still expects compileNonCallStmtSpan? and SourceOwned.
13095/13096, 13244/13245: exact and below .block branches still stale.
13794/13795: halt .block branch still stale.
```

There are also smaller inductive-conversion errors in support classifiers:
`StmtListRegularOpenSupported.nil/cons` should replace old `True`/pair proofs,
and block-open wrappers need `blockOpenSupported_stmtList` or
`blockRegularOpenSupported_stmtList`.

## Ask

What is the best Lean proof architecture here?

Please propose a concrete minimal refactor plan:
- Should regular statement/list/block preservation be converted to a mutual
  theorem family?
- Should exact/below/halt/leave also become mutual, or can they be derived from
  a smaller mutual core plus length/shared-state helpers?
- Is there a way to avoid duplicating the recursive block proof four times
  without weakening theorem statements?
- Please give Lean-shaped pseudocode for the `.block` branch and termination
  measures.
