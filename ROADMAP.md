# Verified Stack Allocation Roadmap

## Objective

Build a general, horizontally proved Functions-to-Locals/Expressions allocator
that compiles the exact pinned Permit2 and linked Aave Pool efficiently through
the checked Yul-to-bytecode artifact path.

Aave must use stack-only allocation. Permit2 may spill only into a reservation
derived from its checked `memoryguard(size)` and the allocator's computed spill
plan. Without `memoryguard`, compilation either succeeds without compiler memory
accesses or honestly rejects the program.

The archived general-memory-virtualization research is preserved at
`codex/archive-general-memory-virtualization` commit `be87c07d`. This branch is
based on the last green pre-virtualization checkpoint `7cad5a87`.

## Public Spine

The primary compiler-correctness result remains forward preservation through
the existing adjacent passes:

```
Yul -> Functions -> allocated Locals/Expressions -> Structured
    -> TypedCfg -> Assembly -> bytecode
```

The allocation boundary computes liveness, layouts, shuffles,
rematerialization choices, and any guarded spill plan. Its public theorem takes
accepted source, related initial states, source execution/resource premises,
and compiler success; it does not take generated schedules, layouts,
certificates, or preservation oracles as premises. `Yul.EndToEnd` remains a
short composition module.

## Semantic Invariants

- `msize()` executes honest EVM `MSIZE`; its exact value and ordering are
  preserved through the established resource-observer replay.
- `gas()`, logs, CALL-family, and CREATE-family effects retain the existing
  ordered open-world semantics.
- Rematerialization duplicates only expressions proved effect-free and stable.
  It never duplicates resource observations, memory/storage reads, logs,
  calls, creates, or other observable/effectful operations.
- Every emitted EVM stack operation is checked for total depth and top-16
  accessibility.
- Dormant caller values survive internal calls and the caller's canonical
  return layout is restored.
- Compiler memory accesses are absent without a valid `memoryguard`.
- With `memoryguard(size)`, the compiler may reserve exactly `[size, ptr)`,
  where `ptr` and the size increase are derived from the checked spill plan.
- Allocation and proof code contain no Permit2/Aave names, hashes, paths,
  fixture addresses, or contract-specific branches.

## Work Plan

### 1. Baseline and Measurements

- [x] Preserve all virtualization work on the archive branch.
- [x] Verify `7cad5a87` as the green checkpoint immediately before general
  memory virtualization.
- [x] Re-run the 1,411-job verification root at the baseline.
- [x] Re-run the exact pinned Permit2/Aave smoke gate and record its current
  fixture reservation as evidence, not completion.
- [x] Audit the current monotone-slot allocator and Solidity's legacy and SSA
  stack-allocation strategies.
- [ ] Add allocation diagnostics that report peak live values, shuffle cost,
  rematerializations, spill words, compile time, and output bytes without
  changing compiler semantics.

### 2. Backward Liveness Owner

- [x] Add a Functions-owned, outcome-indexed backward liveness analysis for
  normal continuation, `break`, `continue`, `leave`, terminal outcomes, loops,
  and internal calls.
- [x] Compute loop facts by a terminating checked fixed point; retain totality
  over accepted finite source programs as an integration obligation.
- [ ] Record next-use information needed by scheduling without making it a
  public premise.
- [x] Prove the computed analyzer satisfies an independent structural relation
  covering uses, definitions, calls, joins, and abrupt-outcome successors.
- [x] Attach computed live-before/live-after facts recursively to statement,
  branch, loop, terminal, and internal-call regions in one compiler-owned
  artifact. Planner consumption remains in the layout phase.
- [x] Add focused source-analysis regressions for dead declarations, loops,
  terminal statements, and dormant caller values.

### 3. Layout and Shuffle Owner

- [x] Track a symbolic stack layout alongside the checked liveness point at
  each allocation program point.
- [x] Invoke the checked retain schedule at each program point so dead values
  are popped promptly; next-use ordering remains open.
- [x] Compute canonical layouts at branch, switch, and loop joins; exact
  internal-call return restoration remains in the call boundary.
- [x] Generate a checked symbolic retain transition using only accessible
  promotions and one suffix cleanup; inaccessible shuffles are rejected.
- [x] Prove the retain artifact executes to its recorded promoted layout,
  preserves the canonical relative order of survivors, and satisfies its
  target-suffix/depth checks. Expression `DUP` checks remain part of lowering.
- [x] Prove the ordinary adjacent Locals compiler realizes every checked retain
  schedule and finishes in its recorded target layout.
- [x] Check expression `DUP`, assignment `SWAP`, call-argument, returned-target,
  and function-return accessibility and prove successful checks compile through
  the ordinary adjacent Locals compiler.
- [x] Prove the ordinary compiler constructs each checked retain transition
  internally and that its promotion/cleanup code preserves the dynamic layout
  relation under open semantics without generated public evidence.
- [x] Lift the dynamic relation through the existing Locals-owned open
  expression preservation theorem, including zero-result statement expressions.
- [x] Prove fresh local binding against the ordinary open statement semantics
  using the dynamic layout relation and the canonical silent binding marker.
- [x] Prove assignment updates exactly its unique symbolic stack slot and
  preserves the dynamic layout and dormant suffix under open semantics.
- [x] Prove zero-result expression statements preserve the dynamic layout and
  inherit their complete ordered open-effect tree from expression semantics.
- [x] Compute each post-statement retain artifact internally and prove its
  emitted shuffle/cleanup code establishes the next regular statement relation.
- [x] Compose any regular statement theorem with any checked retain transition
  under independent source/target fuel, without exposing the generated artifact.
- [x] Add a block-owned generic regular-head/recursive-tail composition theorem
  over the dynamic relation and exact target fuel subtraction.
- [x] Prove the nonzero-fuel empty-block base case directly under the dynamic
  context/layout relation.
- [x] Make canonical Functions semantics and `Functions.Source.Ctx` the actual
  source of every dynamic leaf and block theorem; Locals is only the adjacent
  lowering/target layer.
- [x] Instantiate one compiler-owned `RegularPointPreserves` interface for
  expression, declaration, and assignment points followed by checked retention.
- [x] Expose syntax-generic lowering-owner equations for empty and nonempty
  scheduled statement lists, including fallthrough-tail versus abrupt-head.
- [x] Expose scheduler-owner inversion for list heads and regular leaf shapes,
  including the exact checked retain transition and recursive next layout.
- [x] Prove transition and regular-point execution at arbitrary sufficient
  target fuel so nonempty tails compose without a minimal-fuel shortcut.
- [x] Compose one regular scheduled point with an arbitrary recursive tail,
  expressing residual fuel only through the source schedule's promotion count.
- [x] Prove compiler-equation-driven recursive composition for arbitrary
  expression/declaration/assignment lists with computed target fuel and no
  generated semantic premise.
- [ ] Prove statement-list and structured-control layout composition.

### 4. Internal Calls

- [ ] Extend the existing allocation call decomposition rather than adding a
  second call interpreter.
- [ ] Preserve dormant caller frames across calls.
- [ ] Prove parameter entry, return-value placement, and exact caller-layout
  restoration for recursive and non-recursive call graphs.
- [ ] Keep call artifacts compiler-owned and absent from public theorem
  premises.

### 5. Rematerialization Owner

- [ ] Define a conservative `StableEffectFree` predicate over Functions
  expressions.
- [ ] Compute candidate cost and next-use benefit.
- [ ] Prove expression rematerialization preserves value, state, transcript,
  and outcome.
- [ ] Integrate rematerialization only when it relieves an otherwise
  inaccessible/deep live value.

### 6. Guarded Spill Fallback

- [ ] Compute the minimal spill set only after stack scheduling and
  rematerialization fail.
- [ ] Reject memory spilling when no consistent source `memoryguard(size)` is
  present.
- [ ] Derive spill words and returned pointer from the checked plan; remove
  frontend/fixture scratch addresses and the fixed `8193`-word default from
  the production path.
- [ ] Reuse the existing memory-contract relation to prove spill bounds,
  non-aliasing, and frame preservation.
- [ ] Preserve honest `MSIZE` observation; do not virtualize compiler memory.

### 7. Horizontal Composition

- [ ] Make the public allocation compiler compute and discharge all liveness,
  layout, shuffle, rematerialization, and spill obligations.
- [ ] Re-establish Functions-to-Locals/Expressions forward preservation for
  all source outcomes and ordered effects.
- [ ] Compose through existing lower pass theorems without recursive compiler
  reasoning in `Yul.EndToEnd`.
- [ ] Add architecture guards against generated public evidence,
  observer-specific compilers, cross-layer corridors, and contract-specific
  allocator code.

### 8. Exact Contracts and Scalability

- [ ] Exact pinned Aave compiles stack-only with no reservation or source
  non-alias premise.
- [ ] Exact pinned Permit2 compiles stack-only or uses only its checked,
  plan-sized `memoryguard` reservation.
- [ ] Both compile through `CompiledObjectArtifact` to exact raw bytecode under
  the full open-world/resource-observer theorem.
- [ ] Profile all analysis and compilation stages; remove algorithmic
  superlinearity on the exact contracts.
- [ ] Record compile time, peak memory, allocation statistics, and output size.

### 9. Optional Code Density

- [ ] If deployable output still requires it, implement compact `PUSH` encoding
  as a separate Assembly-owned pass with decoding and execution preservation.
  It must not be mixed into allocation correctness.

## Completion Gates

At each completed boundary:

- focused Lean build;
- `lake build EvmCompiler.Verification`;
- `scripts/verify_layer.sh proofs`;
- `scripts/check_architecture.sh`;
- repository hole, `unsafe`, and new-axiom scans;
- `#print axioms` for new public theorems;
- Python/frontend regressions;
- exact pinned Permit2/Aave gate where executable;
- `git diff --check`;
- a green git checkpoint.

The goal is incomplete while Aave needs compiler scratch memory, while a
fixture provides spill storage, while generated allocation evidence appears at
the public boundary, or while any new adjacent boundary lacks a checked
preservation theorem.
