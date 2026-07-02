# Oracle Request: Yul Bridge Architecture and Layer Placement

Mode: critique / architectural repair.

Repository: `/Users/dan/Projects/evm-compiler`

Active goal:

> Make the Yul/reference-boundary changes needed for a Nethermind Yul bridge, then implement and prove the checked bridge from the imported EvmYul.Yul semantics to the compiler-facing Yul semantics, composing it into the existing verified compiler theorem and auditing any semantic blockers.

Current verified tower:

```text
Nethermind Yul reference semantics
  -> compiler-facing Yul
  -> objects
  -> functions
  -> locals/scopes
  -> expressions/literals
  -> structured control/procedure control
  -> labeled assembly
  -> resolved EVM assembly
  -> encoded bytecode
  -> gas-aware EVMYulLean EVM runner
```

The lower layers have independent interpreters and preservation theorems. The current trouble is the bridge from imported Nethermind Yul to compiler-facing Yul/lower layers.

Recent smell:

We started with ad hoc theorem names like `TwoHiddenArgsBridgeWithLayoutSlotValues`, then generalized to:

```lean
inductive ArgSlotValues
    (layout : List Name) (stack : EvmYul.Stack Word) :
    List (Locals.Expr 1) → List Word → Prop
```

and

```lean
structure BoundArgsBridgeWithLayoutSlotValues ... where
  -- imported Yul evalArgs evidence for args.reverse
  -- target prelude execution
  -- full-layout target relation
  -- source-order ArgSlotValues for generated temp variables
```

We moved compiler-only `Expr.List.lowerBound1?` decomposition and `BoundLowering` into `EvmCompiler/Yul/Compiler.lean`, so `Yul.Reference` no longer owns compiler equations. We also proved imported-source schedule lemmas:

```lean
evalArgs_singleton_of_evalValues_single
evalArgs_pair_of_evalValues_single
evalArgs_append_singleton_scheduled
evalArgs_reverse_cons_scheduled_of_evalValues
boundArgsBridgeWithLayoutSlotValues_cons_scheduled
```

Now the remaining next step is a generic target replay theorem:

```lean
theorem exprSeq_runCode_toSeq_of_argSlots_aux
    (ctx : Locals.Ctx) (baseState currentState : EVMState)
    (layout : List Name) (offset : Nat) (pushed : List Word)
    {exprs : List (Locals.Expr 1)} {values : List Word}
    {results : Nat} {seq : Locals.ExprSeq results}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hCurrentStack : currentState.stack = pushed ++ baseState.stack)
    (hPushedLen : pushed.length = offset)
    (hSlots : ArgSlotValues layout baseState.stack exprs values)
    (hSeq : Expr.List.toSeq? exprs results = some seq)
    (hBound :
      ∀ {pos : Nat} {name : Name} {idx : Nat},
        exprs[pos]? = some (.var name) →
          layout[idx]? = some name →
            offset + pos + idx + 1 ≤ 16) :
    ∃ finalState : EVMState,
      Locals.Direct.Expr.ExprSeq.runCode ctx offset seq currentState =
        .ok finalState ∧
      finalState.stack = values.reverse ++ pushed ++ baseState.stack ∧
      finalState.toSharedState = currentState.toSharedState
```

This proof is currently not closed; the immediate Lean issue is just induction/IH argument order. But the user has raised the more important architectural question:

> I wonder if we should be proving any of these semantics a bit lower in our compiler tower.

Please critique the architecture:

1. Which proof obligations currently in `Yul.Reference` should be moved down to lower layers such as `Yul.Expr`, `Locals.Direct.Expr`, `Expressions`, or primitive/assembly semantics?
2. Where should the generic target replay theorem for `toSeq?` / `toStackSeq?` live?
3. Should `BoundArgsBridgeWithLayoutSlotValues` remain a reference-bridge relation, or should it split into:
   - source/imported evaluation schedule lemmas in `Yul.Reference`,
   - compiler-generated prelude/slot preservation in `Yul.Expr` or `Locals`,
   - primitive opcode execution in the primitive layer?
4. How do we avoid repeating this problem for terminals, external/world opcodes, function calls, and object builtins?
5. What should the public theorem boundary look like so it does not expose hidden args, layout slots, compiler-generated witnesses, replay certificates, or `SourceBridge.sourceRun`?

Constraints:

- No `sorry`, no new axioms.
- The public theorem must ultimately quantify over imported `EvmYul.Yul` source execution.
- Gas, PC, and external-call/create/world agreement can remain explicit top theorem assumptions where fundamentally necessary.
- Compiler-generated evidence should be computed or proved by checked Lean, not public premises.
- Avoid proof blowup and arity-specific special cases.

Please be candid if the current direction is still too high-level or if this bridge should be re-cut around lower-layer semantic theorems before continuing.
