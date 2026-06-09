# CallAwareSpill Recursive Switch / Branch Normalization Question

Repository: `/Users/dan/Projects/evm-compiler`

File: `EvmCompiler/Functions/CallAwareSpill.lean`

Goal: make the spill-based stack-too-deep fallback part of the main compiler spine for real imported Solidity/Yul programs. The object path currently succeeds for the Aave v3 and Permit2 smokes via `scratch_frame_spill_*`, but `call_aware_spill_*` is still `none` on the deployed runtimes. We want to strengthen `Functions.CallAwareSpill` honestly, not hide unsupported source shapes.

Current checked checkpoint:

- `compileStmt?` handles `.call`, `.leave`, and now recursive `.block`.
- Recursive block proofs/checker build:
  - focused `CallAwareSpill` Lean check: green
  - `lake build EvmCompiler.Functions.CallAwareSpill`: green
  - frontend/bridge builds and Aave/Permit2 smokes: green
- The previous oracle response said recursive `.block` is the right direction, but support evidence must mirror the executable dispatcher and nonregular scoped outcomes must not use the restricted fallthrough layout.

Current remaining coverage facts:

- Permit2 hash deployed runtime:
  - ordinary/live/locals-adaptive/call-aware stages are `none`
  - `scratch_frame_spill_*` is `some`
  - trace shows surrounding `switch`/`block` as `none`
  - the sharp ordinary-path failure is inside a selected/default switch body:
    `assign:var_result` with target depth/accessDepth 17, RHS vars shallow (`__evm_compiler_tmp_27` depth 1, `expr_mpos_3` depth 2)
  - there are calls such as `call:finalize_allocation` inside switch/default/block paths, so a whole-switch `SourceOwned` span is not enough for call-aware.
- Aave interest deployed runtime similarly has nested blocks/switches and call-aware is still `none`.

Relevant executable source semantics:

```lean
-- Functions.SourceSemantics, shape paraphrased
| fuel + 1, .switch scrutinee cases defaultBody, state => do
    let (stateAfterScrutinee, value) ← Expr.evalOne prim scrutinee state
    match Switch.select value cases defaultBody with
    | none => .ok (Outcome.regular stateAfterScrutinee, ctx)
    | some body =>
        let outcome ← Block.runScoped prim program ctx body fuel stateAfterScrutinee
        .ok (outcome, ctx)
```

Current call-aware compiler dispatch:

```lean
def compileStmt? ... : Stmt → Option Plan
  | .call targets functionName args => compileCall? ...
  | .leave => compileLeave? ...
  | .block body => compileBlockStmt? ... body
  | stmt => compileNonCallStmtSpan? ... stmt
```

So `switch` currently goes through `compileNonCallStmtSpan?`, which delegates to Locals spill span compilation. That route mostly handles atom lists/scoped blocks and rejects complex `switch` shapes; if a switch body contains function calls, `SourceOwned` also fails.

Important representation issue:

`Plan` has one fallthrough metadata triple:

```lean
structure Plan where
  sourceScope : List Name
  stackLayout : List Name
  layout : SpillLayout.Layout
  block : Expressions.Block
```

An `Expressions.Stmt.switch` also has one post-state for the following code, but each selected branch body may leave a different stack layout. The existing `.block` statement compiler restricts layout to the outer `sourceScope` but keeps `bodyPlan.stackLayout`; this is okay for a single fallthrough path, but a switch needs all regular branches and the no-match path to agree on one plan layout.

Possible route under consideration:

1. Compile the scrutinee with `SpillExpr.compileCode?`.
2. Maybe pre-normalize the entry layout by spilling all live stack locals to scratch, giving all branches `stackLayout = []` and a stable scratch-backed outer layout.
3. Compile each case/default body recursively as a scoped block from that same normalized entry layout.
4. For each branch regular fallthrough, normalize again to a common post-layout before returning from the branch. The branch emitted block is `bodyPlan.block ++ cleanupCode`, and nonregular outcomes skip cleanup naturally by block append semantics.
5. For no-match/default-none, use a synthetic default block that just performs the same normalization, so the source `none` case is target-private-scratch cleanup rather than no target code.
6. The desired final switch plan would have `sourceScope` unchanged, `stackLayout = []`, and all live outer locals scratch-backed in a checked common layout.

Concern: existing `SpillPlan.spillAllStack?` only works when the stack top has a live layout binding. After scoped blocks, `stackLayout` may contain dead scoped names that are no longer in `restrictedLayout`, so `spillAllStack?` can fail. A more general scoped cleanup might need:

- if top stack name is live at `.stack 0`, store it to a scratch slot and decrement remaining stack depths (`evictTopStackLayout?`);
- if top stack name is dead/not in layout, emit `POP` and decrement remaining live stack depths without storing;
- repeat until `stackLayout = []`.

Questions:

1. Is this spill/drop-to-empty-stack normalization the right invariant for recursive call-aware `switch`?
2. Should normalization be applied only inside `switch` branch bodies, or should `compileBlockStmt?` itself normalize scoped regular fallthroughs so later assignments never get stuck behind dead scoped stack entries?
3. What is the smallest checked theorem family that would make this honest without exploding the existing `.block` proofs?
4. Are there soundness traps with `restrictToScope`, shadowing/name uniqueness, nonregular branch outcomes, or scratch-slot reuse across mutually exclusive switch branches?
5. If full preservation for recursive switch is too large, what is the best fail-closed executable checkpoint that improves real-program coverage while clearly marking the proof boundary?

Please critique the approach and suggest the smallest coherent next green checkpoint in Lean.
