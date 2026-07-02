# Oracle Request: Yul Bridge Tower Placement Critique

Mode: hostile architectural critique / repair plan.

Repository: `/Users/dan/Projects/evm-compiler`

Active goal:

> Make the Yul/reference-boundary changes needed for a Nethermind Yul bridge,
> then implement and prove the checked bridge from the imported EvmYul.Yul
> semantics to the compiler-facing Yul semantics, composing it into the existing
> verified compiler theorem and auditing any semantic blockers.

User's current nudge:

> I wonder if we should be proving any of these semantics a bit lower in our
> compiler tower.

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

Most lower layers have independent interpreters and adjacent preservation
theorems. The current pressure point is the top bridge from imported
`EvmYul.Yul` execution to the compiler-facing Yul/lower tower.

Important current public boundary:

```lean
structure SourceBridge (stateRel : StateRel) (outcomeRel : OutcomeRel)
    (program : Program) (referenceFuel : Nat)
    (referenceInitial : State) (referenceResult : Result) where
  accepted : Accepted program
  sourceFuel : Nat
  compilerInitial : EVMState
  outcome : Outcome
  referenceRun :
    runResult referenceFuel program referenceInitial = .ok referenceResult
  initialRel : stateRel (installContract program referenceInitial)
    compilerInitial
  sourceRun :
    Lowered.run sourceFuel program compilerInitial = .ok outcome
  outcomeRel : outcomeRel referenceResult outcome
```

This is intentionally not the final theorem shape: `sourceRun` is still a
trusted replay of the compiler-facing semantics and must be eliminated by
checked per-construct bridge proofs.

Recent refactor already done:

1. We had an arity-specific smell:
   `TwoHiddenArgsBridgeWithLayoutSlotValues`.
2. We replaced the active path with list-shaped generated-argument evidence:

```lean
inductive ArgSlotValues
    (layout : List Name) (stack : EvmYul.Stack Word) :
    List (Locals.Expr 1) -> List Word -> Prop

structure BoundArgsBridgeWithLayoutSlotValues ... where
  -- imported Yul evalArgs evidence in source order
  -- target prelude execution for generated temps
  -- full-layout target relation
  -- source-order ArgSlotValues for generated temp variables
```

3. We moved pure target stack replay below the imported-reference bridge:

```lean
Locals.ExprSeq.VarSlotValuesAt
Locals.Direct.Expr.ExprSeq.runCode_of_varSlotValuesAt
```

4. `Yul.Reference` now only adapts source-order `ArgSlotValues` through
   `Expr.List.toSeq?` / `toStackSeq?`:

```lean
exprSeq_runCode_toStackSeq_of_argSlots
```

5. `ADD` and noncommutative `SUB` now both use that generic argument replay
   path. This caught/guards argument order.

What still feels bad:

- `EvmCompiler/Yul/Reference.lean` is extremely large and owns too much proof
  glue: imported source semantics, target replay adapters, expression bridges,
  scoped block/result bridge interfaces, terminals, switch/if/loop wrappers,
  and the top theorem boundary.
- Many bridge lemmas still pass explicit `CompilerStateRelWithLayoutSlots`,
  `VisibleVarSlotRel`, layout suffixes, hidden locals, target fuel, and
  lower-block witnesses. These are conceptually proof machinery, but because the
  recursive imported-Yul bridge is not finished, they still show up in many
  exposed theorem statements.
- Primitive bridge expansion risks becoming a table of similar but bespoke
  proofs unless the source primitive semantics, target primitive semantics, and
  argument replay are factored at the right levels.
- Terminal primitives and external/world opcodes may repeat the same problem:
  argument scheduling belongs to imported Yul, argument stack replay belongs
  below, opcode effect agreement belongs near the shared EVM primitive layer,
  and the top bridge should only compose those facts.
- The tower currently has both compiler-facing `Yul.Lowered.run` and imported
  `Yul.Reference.runResult`; the final theorem must quantify over imported
  execution, not the lowered run.

Please critique:

1. Given the refactor above, are we still proving semantics too high in
   `Yul.Reference`?
2. Which current obligations should move lower, and exactly where?
   Candidate homes:
   - `Yul.Compiler` / `Yul.Expr`: lowering decomposition and generated-temp
     prelude facts.
   - `Locals.Direct.Expr`: stack-slot replay for generated local reads.
   - `Expressions` / `Structured`: generic primitive expression execution.
   - `Assembly.PrimSemantics`: opcode family agreement with Nethermind EVM/Yul
     shared primitives.
   - `Yul.Reference`: only imported Yul schedule/fuel/store facts and final
     state/outcome relation.
3. Should we introduce a new explicit intermediate "reference bridge IR" or
   "YulCore bridge" layer so that imported Yul is first normalized into the
   compiler-facing direct semantics, then lowered through the already-proved
   tower?
4. Or should we continue with the current compositional relation style but split
   the giant file into namespaces/files and push target-only lemmas down?
5. The user specifically asks whether some semantics should be proved lower in
   the tower. What is the strongest version of that critique?
6. What should the final public theorem boundary look like so it does not expose
   hidden args, layout slots, replay certificates, generated witnesses, or
   `SourceBridge.sourceRun`?

Constraints:

- No `sorry`, no new axioms.
- Public theorem must quantify over imported `EvmYul.Yul` execution.
- Fundamental top assumptions may remain explicit: gas/no-OOG, PC oracle for
  high-level `PC`, code-image/external-world agreement for call/create/code
  inspection until those relations are proved.
- Compiler-generated evidence must be computed/proved by checked Lean, not
  public premises.
- Avoid proof blowup and arity-specific/fused special cases.

Please be blunt. If the architecture should be re-cut before continuing, say so
and give a concrete staged repair. If the current architecture is basically
right, say what to move lower and what to leave at the reference boundary.
