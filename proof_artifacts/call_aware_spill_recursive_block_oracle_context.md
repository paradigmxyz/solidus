# CallAwareSpill recursive block proof approach question

Workspace: `/Users/dan/Projects/evm-compiler`

File under repair: `EvmCompiler/Functions/CallAwareSpill.lean`

Goal: make spill-based stack-too-deep fallback part of the main verified compiler spine for imported Solidity/Yul programs, especially Aave v3 and Permit2. The already-green checkpoint has an object-level checked fallback through `ScratchFrameMemory` with Aave/Permit2 `first_none=none`, but `call_aware_spill_*` still rejects nested block/call shapes. Current work is trying to make `Functions.CallAwareSpill` handle Solidity-shaped recursive `.block` statements with internal-call splice points.

## Current approach

We changed the executable statement compiler so `.block body` is compiled by a recursive block path:

```lean
def compileStmt? (range : ScratchRange) (program : Program)
    (returns sourceScope stackLayout : List Name)
    (layout : SpillLayout.Layout) : Stmt -> Option Plan
  | .call targets functionName args =>
      compileCall? range program sourceScope stackLayout layout targets
        functionName args
  | .leave =>
      compileLeave? range returns sourceScope stackLayout layout
  | .block body =>
      compileBlockStmt? range program returns sourceScope stackLayout layout
        body
  | stmt =>
      compileNonCallStmtSpan? range returns sourceScope stackLayout layout stmt
```

`compileBlockStmt?` compiles the body open, then restricts the resulting layout to the outer scope and re-checks it:

```lean
def compileBlockStmt? (range : ScratchRange) (program : Program)
    (returns sourceScope stackLayout : List Name)
    (layout : SpillLayout.Layout) (body : Block) : Option Plan := do
  let bodyPlan <-
    compileBlockOpen? range program returns sourceScope stackLayout layout body
  let restrictedLayout := SpillLayout.restrictToScope sourceScope
    bodyPlan.layout
  if
      SpillLayout.checked? range sourceScope bodyPlan.stackLayout
        restrictedLayout
  then
    some
      { sourceScope := sourceScope
        stackLayout := bodyPlan.stackLayout
        layout := restrictedLayout
        block := bodyPlan.block }
  else
    none
```

The intended proof pattern for `.block` in a regular statement theorem is:

1. Decompose `compileBlockStmt?_eq_some`.
2. Derive `BlockRegularOpenSupported`/`BlockOpenSupported` for the body from either an explicit `.block` support constructor or a broad `sourceOwned` support constructor.
3. Unfold `Source.Stmt.run` for `.block` and case on `Source.Block.runScoped`.
4. For regular scoped outcome, use `Source.Block.runScoped_regular_eq_restrict` to get the open body run and the source `restrictTo`.
5. Recursively call the relevant block-open theorem.
6. Use `SpillStateRel.restrictToScope` and `SpillLayout.StoreDefined.restrictToScope` to restore the outer scoped-layout invariant.

This pattern mostly worked for the non-exact regular family after wrapping statement/list/block theorems in a mutual block. I am now extending it to exact/below/halt/leave theorem families.

## Support predicates

Current support still has broad `sourceOwned` constructors, so `.block` can be supported either structurally or through `sourceOwned` evidence:

```lean
inductive StmtRegularOpenSupported (returns : List Name) : Stmt -> Prop
  | call {targets functionName args} :
      StmtRegularOpenSupported returns (.call targets functionName args)
  | block {body} :
      BlockRegularOpenSupported returns body ->
        StmtRegularOpenSupported returns (.block body)
  | sourceOwned {stmt} :
      SourceLowering.SourceToLocals.Stmt.SourceOwned returns stmt ->
        StmtRegularOpenSupported returns stmt

inductive StmtOpenSupported (returns : List Name) : Stmt -> Prop
  | call {targets functionName args} :
      StmtOpenSupported returns (.call targets functionName args)
  | leave : StmtOpenSupported returns .leave
  | block {body} :
      BlockOpenSupported returns body ->
        StmtOpenSupported returns (.block body)
  | sourceOwned {stmt} :
      SourceLowering.SourceToLocals.Stmt.SourceOwned returns stmt ->
        StmtOpenSupported returns stmt
```

A prior oracle answer warned that broad `sourceOwned` is semantically dangerous and suggested syntax-aligned leaf support excluding `.call`, `.leave`, `.block`, plus mutual theorem families that mirror compiler recursion.

## Current refactor state

I tried to:

- wrap the exact regular statement/list/block theorem families in `mutual`;
- strengthen statement-level replay premises from statement-local `stmt = .call ... -> CallReplayFor ... target source ...` to global replay:

```lean
(hCallReplay :
  forall {callTarget : Expressions.RunState} {callSource : Source.State}
    {targets : List Name} {functionName : Name}
    {args : List (Expr 1)},
    CallReplayFor range program exprProgram callTarget callSource targets
      functionName args)
```

- similarly use global `CallReplayForBelow` for below routes;
- start wrapping the halt statement/list/block route in `mutual`;
- strengthen halt statement preservation to take both regular replay and halt replay, plus stack-length evidence:

```lean
(hCallReplay :
  forall {callTarget : Expressions.RunState} {callSource : Source.State}
    {targets : List Name} {functionName : Name}
    {args : List (Expr 1)},
    CallReplayForBelow fuel range program exprProgram callTarget callSource
      targets functionName args)
(hHaltReplay :
  forall {callTarget : Expressions.RunState} {callSource : Source.State}
    {targets : List Name} {functionName : Name}
    {args : List (Expr 1)},
    CallHaltReplayForBelow fuel range program exprProgram callTarget
      callSource targets functionName args)
```

The current worktree is red. Some errors are from my in-progress edit, but the important architectural red surface is:

```text
EvmCompiler/Functions/CallAwareSpill.lean:10197:14: block branch in compileStmt?_leave_sound_exact_given_callReplay still tries non-call span
EvmCompiler/Functions/CallAwareSpill.lean:10198:14: same, support expected SourceOwned for .block
EvmCompiler/Functions/CallAwareSpill.lean:14374:24: halt list theorem still needs regular-support classifier before/in mutual
EvmCompiler/Functions/CallAwareSpill.lean:14424/14543 etc: parser/termination fallout from half-mutualized halt/support families
```

There is also an accidental/current local edit:

```diff
 theorem compileNonCallStmtSpan?_expressionsBlock_sound_of_source_run
 ...
     (hDefined : SpillLayout.StoreDefined source.vars layout)
+    (hLength : target.evm.stack.length = stackLayout.length)
     (hSourceRun : ...)
```

This hLength insertion appears to have landed in the wrong helper and now causes early application errors. I can revert that locally; it is not intended as an architectural requirement for non-call spans.

## Question for oracle

Please critique the approach, not just individual tactics:

1. Is the right architecture to keep making the theorem recursion mirror the compiler recursion, with separate mutual theorem families for regular exact, regular below, halt below, leave exact, and leave below?
2. Or should we stop duplicating `.block` proofs and introduce an outcome-polymorphic block/statement preservation core that handles regular/halt/leave uniformly, then derive the exact/below/leave/halt wrappers?
3. Should we first change the support predicates so `sourceOwned` is syntax-aligned leaf-only and `.block` is only supported structurally, even though that may force many proof updates?
4. For `compileBlockStmt?`, is the “compile open body, restrict layout/store/relation to outer source scope, and keep `bodyPlan.stackLayout`” representation semantically sound for all outcomes? It seems sound for regular. For halt/leave, does it correctly avoid scoped cleanup or should nonregular block statements be compiled with a different plan shape?
5. What is the smallest coherent next step to get back to a green Lean checkpoint without proving a false theorem or baking in bad public assumptions?

Constraints:

- No `sorry`, no new axioms.
- Do not claim public theorem coverage for compiler-generated replay/certificate evidence unless the checker constructs and discharges it.
- Avoid any fallback that promotes outer stack locals above inner locals in scoped blocks; cleanup assumes the outer layout remains a suffix.
- The end goal is real Solidity/Yul nested block/call support, not just diagnostic improvement.
