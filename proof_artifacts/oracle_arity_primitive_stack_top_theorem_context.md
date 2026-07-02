# Oracle Request: eliminate strict primitive-stack contract from the top theorem

We are working in `/Users/dan/Projects/evm-compiler`, a Lean compiler proof
tower from Nethermind Yul through our source layers to labeled assembly/EVM.
The current audit goal is to stop the public theorem from taking a broad
semantic-contract package as an assumption. We have been replacing the package
with canonical, internally derived bridge facts for the imported Nethermind Yul
semantics.

The current blocker is architectural rather than a tiny tactic issue:

- The public no-call/top theorem still requires
  `RecursiveBridgePrimitiveStackContracts cfg prim`, whose field is the strict
  raw primitive bridge `PrimitiveStackSoundAt`.
- For several canonical imported Yul primitives, especially nullary
  environment/state reads, the raw Nethermind `primCall` layer is permissive
  about extra arguments. It may ignore extra raw `sourceValues`.
- Our source language and compiler do enforce exact primitive arity before the
  primitive call boundary is used. Therefore the honest contract is
  `PrimitiveStackSoundAtArity`, which includes the exact arity premise derived
  from successful argument evaluation/lowering.
- We added arity-aware contract packages and migrated one-result expression
  primitive lowering to them, but the top theorem and some zero-output statement
  bridges still pull the old strict contract back into the public boundary.

I want a Lean-friendly, compositional migration plan that eliminates the strict
top-boundary assumption without causing proof blowup or special-case fusion.

## Current strict primitive bridge

File: `EvmCompiler/Yul/Reference.lean`

```lean
def PrimitiveStackSoundAt
    (cfg : StateRelConfig) (layout : List Name)
    (prim : Objects.Source.PrimitiveSemantics) (sourceFuel : Nat)
    (yulPrim : EvmYul.Operation .Yul) (op : Structured.BasicOp) : Prop :=
  ∀ {sourceAfterArgs : State}
    {compilerAfterArgs : Objects.Source.State}
    {sourceValues : List Word} {sourceAfterPrim : State}
    {values' : List Word},
    SourceStateRel cfg layout sourceAfterArgs compilerAfterArgs →
    EvmYul.Yul.primCall sourceFuel sourceAfterArgs yulPrim sourceValues =
      .ok (sourceAfterPrim, values') →
    ∃ sharedAfter : EvmYul.SharedState .EVM,
      prim.eval op compilerAfterArgs.shared sourceValues.reverse =
        .ok (sharedAfter, values') ∧
      SourceStateRel cfg layout sourceAfterPrim
        (compilerAfterArgs.withShared sharedAfter)
```

This is too strong for raw imported primitive calls when `primCall` accepts an
ill-arity `sourceValues`.

## Current arity-aware primitive bridge

File: `EvmCompiler/Yul/Reference.lean`

```lean
def PrimitiveStackSoundAtArity
    (cfg : StateRelConfig) (layout : List Name)
    (prim : Objects.Source.PrimitiveSemantics) (sourceFuel : Nat)
    (yulPrim : EvmYul.Operation .Yul) (op : Structured.BasicOp) : Prop :=
  ∀ {sourceAfterArgs : State}
    {compilerAfterArgs : Objects.Source.State}
    {sourceValues : List Word} {sourceAfterPrim : State}
    {values' : List Word},
    SourceStateRel cfg layout sourceAfterArgs compilerAfterArgs →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    EvmYul.Yul.primCall sourceFuel sourceAfterArgs yulPrim sourceValues =
      .ok (sourceAfterPrim, values') →
    ∃ sharedAfter : EvmYul.SharedState .EVM,
      prim.eval op compilerAfterArgs.shared sourceValues.reverse =
        .ok (sharedAfter, values') ∧
      SourceStateRel cfg layout sourceAfterPrim
        (compilerAfterArgs.withShared sharedAfter)

theorem primitiveStackSoundAtArity_of_stackSoundAt
    {cfg : StateRelConfig} {layout : List Name}
    {prim : Objects.Source.PrimitiveSemantics} {sourceFuel : Nat}
    {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (h : PrimitiveStackSoundAt cfg layout prim sourceFuel yulPrim op) :
    PrimitiveStackSoundAtArity cfg layout prim sourceFuel yulPrim op
```

The strict-to-arity direction exists for compatibility. The converse is false
without a raw imported arity rejection theorem, which we do not have and should
not assume for permissive nullary primitives.

## Contract packages already added

File: `EvmCompiler/Yul/RecursiveBridgeSupport.lean`

```lean
structure RecursiveBridgeSemanticCoreContracts
    (cfg : Reference.StateRelConfig)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Program) : Prop where
  primitiveSound : Locals.SourceLowering.PrimitiveSound prim
  terminal : ...
  primitiveStack :
    ∀ {layout : List Name} {fuel : Nat}
      {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp},
      Reference.Safe.primitive yulPrim →
      Prim.toBasicOp? yulPrim = some op →
      Reference.SourceBridgeFacts.PrimitiveStackSoundAt cfg layout prim fuel
        yulPrim op
  exprResultOk : ...

structure RecursiveBridgeSemanticCoreArityContracts
    (cfg : Reference.StateRelConfig)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Program) : Prop where
  primitiveSound : Locals.SourceLowering.PrimitiveSound prim
  terminal : ...
  primitiveStack :
    ∀ {layout : List Name} {fuel : Nat}
      {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp},
      Reference.Safe.primitive yulPrim →
      Prim.toBasicOp? yulPrim = some op →
      Reference.SourceBridgeFacts.PrimitiveStackSoundAtArity cfg layout prim
        fuel yulPrim op
  exprResultOk : ...

structure RecursiveBridgePrimitiveStackContracts
    (cfg : Reference.StateRelConfig)
    (prim : Objects.Source.PrimitiveSemantics) : Prop where
  primitiveStack :
    ∀ {layout : List Name} {fuel : Nat}
      {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp},
      Reference.Safe.primitive yulPrim →
      Prim.toBasicOp? yulPrim = some op →
      Reference.SourceBridgeFacts.PrimitiveStackSoundAt cfg layout prim fuel
        yulPrim op

structure RecursiveBridgePrimitiveStackArityContracts
    (cfg : Reference.StateRelConfig)
    (prim : Objects.Source.PrimitiveSemantics) : Prop where
  primitiveStack :
    ∀ {layout : List Name} {fuel : Nat}
      {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp},
      Reference.Safe.primitive yulPrim →
      Prim.toBasicOp? yulPrim = some op →
      Reference.SourceBridgeFacts.PrimitiveStackSoundAtArity cfg layout prim
        fuel yulPrim op
```

We also added constructors:

```lean
RecursiveBridgeSemanticCoreContracts.ofNoSuccessfulOutOfFuelBoundaries
RecursiveBridgeSemanticArityContracts.of_canonical_observation_noSuccessfulOutOfFuel
RecursiveBridgePrimitiveStackArityContracts.of_strict
RecursiveBridgePrimitiveArityContracts.of_strict
RecursiveBridgePrimitiveArityContracts.of_stack
```

So the arity-aware public shape exists, but the old strict public theorem spine
still dominates.

## Current top theorem still strict

File: `EvmCompiler/Yul/NoCallRuntime.lean`

```lean
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner
    ...
    (hPrimitiveSound : Locals.SourceLowering.PrimitiveSound prim)
    (hPrimitiveStack : RecursiveBridgePrimitiveStackContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    ...
```

and the structured primitive wrapper is also strict:

```lean
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner
    ...
    (hPrimitiveStack :
      RecursiveBridgePrimitiveStackContracts cfg
        Locals.Source.PrimitiveSemantics.structured)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel
        Locals.Source.PrimitiveSemantics.structured program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    ...
```

The theorem underneath eventually consumes `RecursiveBridgeSemanticContracts`
and `RecursiveBridgeSemanticCoreContracts`, again with strict
`PrimitiveStackSoundAt`.

## Arity bridge already works for one-result primitive expressions

File: `EvmCompiler/Yul/RecursiveBridgeSupport.lean`

```lean
theorem exprValuePreludeSound_prim_of_arg_stack_preludeRegularAt_arity
    ...
    (hArgArity : args.length = Expressions.Structured.BasicOp.inputs op)
    (hArgs :
      SourceArgStackPreludeRegularAt cfg layout prim program ctx sourceFuel args
        codeOverride pre lowerArgs)
    (hPrim :
      PrimitiveStackSoundAtArity cfg layout prim sourceFuel yulPrim op) :
    ExprValuePreludeSound cfg layout prim program ctx sourceFuel.succ
      (.Call (.inl yulPrim) args) codeOverride pre
      (Locals.Expr.prim op lowerArgs) := by
  ...
      have hArity :
          rawValues.reverse.length =
            Expressions.Structured.BasicOp.inputs op := by
        have hLen :=
          Imported.evalArgs_length_of_ok hArgForBridge
        simpa [List.length_reverse, hArgArity] using hLen
      rcases hPrim hRelArgs hArity hPrimCall with
        ⟨sharedAfter, hPrimEval, hRelAfter⟩
  ...
```

and the dispatcher-level theorem uses it:

```lean
theorem lower1?_exprEvalPreludeSound_of_argRegularAllScopedAt_arity
    ...
    (hPrimSound :
      ∀ {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp},
        Safe.primitive yulPrim →
        Prim.toBasicOp? yulPrim = some op →
        Expressions.Structured.BasicOp.outputs op = 1 →
        PrimitiveStackSoundAtArity cfg layout prim sourceFuel yulPrim op)
    ...
```

## Remaining strict leak: zero-output primitive statement bridge

File: `EvmCompiler/Yul/RecursiveBridgeSupport.lean`

```lean
theorem checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal
    ...
    (hBasic : Prim.toBasicOp? yulPrim = some op)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 0)
    ...
    (hPrim : PrimitiveStackSoundAt cfg layout prim sourceFuel yulPrim op) :
    CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact cfg reserved layout
      outcomeLayout terminalRel revertRel prim program ctx
      sourceFuel.succ.succ.succ
      (.ExprStmtCall (.Call (.inl yulPrim) args)) codeOverride allowed := by
  ...
```

An attempted local migration of just this theorem to arity ran into deeper
callers still expecting strict contracts. I reverted rather than grow an ad hoc
chain. I suspect this is the point where the theorem spine should be migrated
top-down or where this bridge should get a reusable arity wrapper analogous to
the one-result expression wrapper.

## Canonical facts currently available

Strict `PrimitiveStackSoundAt` facts exist for many fixed-arity primitives:
arithmetic/comparison/bitwise, `iszero`, `not`, `addmod`, `mulmod`, memory reads
and writes/copies, calldata/returndata copies, etc.

Arity-only facts exist for canonical nullary imported state/environment reads:
`returndatasize`, `msize`, `gas`, `address`, `origin`, `caller`, `callvalue`,
`calldatasize`, `gasprice`, `prevrandao`, `basefee`, `blobbasefee`, `coinbase`,
`timestamp`, `number`, `gaslimit`, `chainid`, `selfbalance`, etc.

This is intentional: the raw imported Nethermind dispatcher behavior is not the
source language's accepted expression boundary. The compiler/source acceptance
is what ensures arity.

## Question for the oracle

What is the cleanest Lean architecture to eliminate the strict
`PrimitiveStackSoundAt` top-boundary problem?

Please critique these options and recommend a precise migration order:

1. Change `PrimitiveStackSoundAt` itself to include the arity premise, keep the
   old strict raw version under a different/private name, and update all uses.
2. Keep both definitions, but migrate the whole recursive bridge/top theorem
   spine from `RecursiveBridgePrimitiveStackContracts` /
   `RecursiveBridgeSemanticCoreContracts` to their arity-aware variants.
3. Create mixed contracts that require strict facts for zero-output statement
   primitives and arity facts for one-result expression primitives.
4. Prove enough local arity facts at the zero-output statement bridge, then
   wrap arity contracts into strict only at specific call sites.
5. Some better staged interface: e.g. make every primitive bridge theorem take
   a typed/accepted primitive-call evidence object containing both `toBasicOp?`
   and the successful argument-evaluation length theorem.

Constraints:

- No `sorry`, new axioms, or semantic assumptions just to make the theorem pass.
- Preserve compositionality. Avoid special-casing individual primitives in the
  recursive bridge proof; primitive-specific facts should live in canonical
  bridge constructors.
- The public top theorem should eventually take only fundamental assumptions:
  source acceptedness, source run/fuel, initial-state relation, explicit
  gas/resource bounds or compiler-derived runner completeness, etc. It should
  not ask for compiler-generated witnesses or false semantic contracts.
- Keep existing strict facts useful as compatibility, since strict implies
  arity.
- Minimize proof blowup in this already-large Lean file.

Most useful answer:

- A recommended theorem-boundary shape.
- A concrete migration sequence through the files above.
- How to handle the zero-output primitive statement bridge.
- Whether to mutate the original `PrimitiveStackSoundAt` definition or preserve
  it and migrate public packages.
- Any helper lemmas that should become the central reusable arity derivation.
