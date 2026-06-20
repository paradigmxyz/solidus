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

- [ ] Add a Functions-owned, outcome-indexed backward liveness analysis for
  normal continuation, `break`, `continue`, `leave`, terminal outcomes, loops,
  and internal calls.
- [ ] Compute loop facts by a terminating fixed point over the finite set of
  source bindings.
- [ ] Record next-use information needed by scheduling without making it a
  public premise.
- [ ] Prove use/definition soundness and abrupt-outcome successor soundness.
- [ ] Integrate the computed artifact into allocation planning and add focused
  examples for branches, loops, terminal statements, and calls.

### 3. Layout and Shuffle Owner

- [ ] Track a symbolic stack layout at each allocation program point.
- [ ] Pop dead values promptly and choose live-value order by next use.
- [ ] Compute canonical layouts at branch, switch, loop, and call-return joins.
- [ ] Generate only checked `DUP`, `SWAP`, and `POP` transitions.
- [ ] Prove each transition preserves the environment/layout relation and
  respects EVM depth/top-16 limits.
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
