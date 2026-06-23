# Verified Stack Allocation Roadmap

## Objective

Build a general, horizontally proved Functions normalization and
Functions-to-Locals/Expressions allocator that compiles the exact pinned
Permit2, linked Aave Pool, and broad real-contract corpus through the checked
Yul-to-raw-bytecode artifact path with practical compile time.

The current completion target is semantic and proof completeness, not EVM
deployment-size compliance. Output size remains measured regression data, but
neither the 24 KiB deployment limit nor further code-density optimization is a
completion gate for this stage.

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
Yul -> Functions -> normalized Functions -> allocated Locals/Expressions
    -> Structured -> TypedCfg -> Assembly -> bytecode
```

The normalization boundary performs only proved, semantics-exact expression
reassociation/order rewrites. The allocation boundary computes liveness,
layouts, and shuffles. The exact contracts need neither rematerialization nor a
guarded spill plan. Its public theorem takes
accepted source, related initial states, source execution/resource premises,
and compiler success; it does not take generated schedules, layouts,
certificates, or preservation oracles as premises. `Yul.EndToEnd` remains a
short composition module.

## Viability Decision

The exact pinned-contract diagnostic now resolves the architecture fork:

- Permit2 reaches 39/39 Functions units under stack-only next-use scheduling;
  its un-ordered baseline had eight top-16 access failures in the dispatcher.
- Linked Aave Pool reaches 189/189 Functions units under the same policy; its
  baseline had one access failure and one depth-18 retain failure in
  `fun_flashLoan`.
- The sufficient policy is stable next-use ranking, at most 16 imminent
  promotions, and canonical join restoration over only the differing top
  prefix while preserving the common dormant suffix.

Permit2 and Aave do not require source optimization. The broader Uniswap v4
gate did expose a general expression-shape problem in solc's TickMath output:
semantically associative pure `or` trees and literal-left `and` trees could
force inaccessible intermediate operands despite a schedulable live set. A
checked Functions-to-Functions normalization now reassociates those pure trees
and orders literal conjunctions before physical allocation. Its all-fuel open
semantics theorem preserves the exact state, outcome, and ordered effect tree.
It is not a rematerializer and never duplicates an expression or effect.

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
- [x] Add allocation diagnostics that report peak live values, shuffle cost,
  rematerializations, spill words, compile time, and output bytes without
  changing compiler semantics.
- [x] Route exact pinned Permit2 and linked Aave Pool through liveness,
  scheduling, accessibility, join, and dormant-frame diagnostics; record the
  exact first baseline failures and verify that next-use physical scheduling
  resolves all 39 and 189 Functions units respectively.

### 2. Backward Liveness Owner

- [x] Add a Functions-owned, outcome-indexed backward liveness analysis for
  normal continuation, `break`, `continue`, `leave`, terminal outcomes, loops,
  and internal calls.
- [x] Compute loop facts by a terminating checked fixed point; retain totality
  over accepted finite source programs as an integration obligation.
- [x] Record next-use information needed by scheduling without making it a
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
  are popped promptly, and integrate stable next-use ordering as a
  compiler-owned checked artifact.
- [x] Compute canonical layouts at branch, switch, and loop joins, including
  outcome-indexed restoration before nested `break` and `continue`; exact
  internal-call return restoration remains in the call boundary.
- [x] Generate a checked symbolic retain transition using only accessible
  promotions and one suffix cleanup; inaccessible shuffles are rejected.
- [x] Define and prove compiler-owned direct dead-slot discards: each selected
  slot uses `POP` or one `SWAP` plus `POP`, preserves the dynamic relation and
  dormant suffix, and is computed without a public schedule premise.
- [x] Replace regular-point canonical retain transitions with direct discard
  schedules and carry their arbitrary live permutations to the next point;
  retain canonical restoration only at actual control joins and call returns.
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
- [x] Prove ordinary `leave` from canonical source scope through checked return
  accessibility, value-preserving return-slot anonymization, preserving frame
  cleanup, and non-fallthrough list composition.
- [x] Prove statement-list and structured-control layout composition.

### 4. Internal Calls

- [x] Bridge canonical ordered argument evaluation to `Lower.argExprs`, prove
  exact target splitting, and reuse the existing Functions/Expressions call
  interpreters without defining a second call semantics.
- [x] Prove canonical parameter entry, zero-return initialization, checked
  return-vector placement, and the scheduled callee body/epilogue relation at
  arbitrary sufficient target fuel.
- [x] Compose the real call-created frame, entry-layout marker, return prelude,
  scheduled body, epilogue, ordinary proc lookup, and target call attachment.
- [x] Attach the real target return frame through ordinary procedure lookup,
  argument splitting, frame popping, and return-value attachment; terminal
  halt ignores only now-irrelevant compiler return-frame metadata.
- [x] Perform checked caller target writeback in source `assignMany` order,
  deriving assignment success from arity and the caller layout rather than a
  generated premise.
- [x] Recover the exact entry marker, return prelude, scheduled body, return
  vector, and preserving cleanup from the actual `lowerFunction?` and ordinary
  Locals procedure compiler equations.
- [x] Attach the scheduler's post-call retain transition and restore the
  caller's retained symbolic layout through compiler-owned point equations.
- [x] Discharge the private callee-body premise by source-fuel recursion for
  recursive and non-recursive call graphs.
- [x] Keep call artifacts compiler-owned and absent from public theorem
  premises.

### 5. Functions Normalization and Rematerialization Contingency

- [x] Add a Functions-owned recursive normalization for pure associative `or`
  trees and literal-left `and` ordering, selected before physical allocation.
- [x] Prove expression, argument, statement, block, loop, switch, function, and
  whole-program exact open-semantics equality for every fuel and response tree.
- [x] Integrate normalization into `StackArtifact.compile?` and the adjacent
  public composition theorem without generated evidence or a Yul-to-bytecode
  proof corridor.

General dead-binding elimination and rematerialization remain deferred until a
program exhibits irreducible pressure after normalization and next-use
scheduling.

- [ ] Define a conservative `StableEffectFree` predicate over Functions
  expressions.
- [ ] Compute candidate cost and next-use benefit.
- [ ] Prove expression rematerialization preserves value, state, transcript,
  and outcome.
- [ ] Integrate rematerialization only when it relieves an otherwise
  inaccessible/deep live value.

### 6. Guarded Spill Contingency

The exact contracts compile stack-only. Guarded spilling remains a possible
future fallback for programs that cannot be scheduled stack-only; it is not a
premise or hidden memory access in the current checked artifact path.

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

- [x] Make the public allocation compiler compute and discharge all selected
  liveness, layout, and shuffle obligations; exact Aave/Permit2 need neither
  rematerialization nor spilling, so those remain dormant fallback tracks.
- [x] Re-establish Functions-to-Locals/Expressions forward preservation for
  all source outcomes and ordered effects.
- [x] Compose the checked root-code artifact through existing lower pass
  theorems to exact raw bytecode without recursive compiler reasoning in
  `Yul.EndToEnd`; recursive Solidity object-image composition remains in the
  exact-contract gate below.
- [x] Add architecture guards against generated public evidence,
  observer-specific compilers, cross-layer corridors, and contract-specific
  allocator code.

### 8. Exact Contracts and Scalability

- [x] Exact pinned Aave compiles stack-only with no reservation or source
  non-alias premise through the checked recursive object artifact and
  raw-bytecode theorem.
- [x] Exact pinned Permit2 compiles stack-only through the checked root-code
  artifact and recursive raw-bytecode theorem.
- [x] Both compile through the recursive `VerifiedStackObjectArtifact` to
  exact root-image raw bytecode under the horizontal open-world theorem, with
  compiler-owned child validity and no legacy allocation metadata. Resource
  observer replay remains the existing separately composed semantic boundary.
- [x] Make the selected stack artifact check Functions source acceptance and
  derive `WF`/`Scoped` internally; the exact code/object raw-bytecode theorems
  no longer expose either decidable compiler-input property as a premise.
- [x] Make the reproducible pinned-contract gate invoke
  `compileVerifiedStackObjectArtifactWithLinkerSymbols?` directly. It requires
  all 39 Permit2 and 189 Aave units to pass checked liveness, scheduling,
  accessibility, next-use, and lowering, and rejects any Aave scratch
  reservation; output size is informational only.
- [x] Profile all analysis and compilation stages; remove algorithmic
  superlinearity on the exact contracts.
- [x] Record compile time, peak memory, allocation statistics, and output size.
  After indexed label lookup and uniqueness checks, complete diagnostics take
  5.60 seconds and 108 MB RSS for Permit2, and 15.97 seconds and 140 MB RSS for
  Aave. Their recursive images are 22,970 and 43,983 bytes respectively; both
  have zero inaccessible-depth failures and use stack-only allocation.
- [x] Select proved direct discards at straight-line fallthrough points while
  preserving canonical entry/join/return transitions. Exact recursive images
  at that checkpoint were 20,712 bytes for Permit2 and 40,185 bytes for linked
  Aave; native diagnostics remained practical at 8.5s/107 MB and 24.2s/135 MB
  respectively. The current strict recursive artifact gate emits 90,723 and
  92,924 bytes after the broader scheduling/backend changes. These figures are
  diagnostics, not deployability requirements.
- [x] Treat abrupt-only conditional regions honestly at both adjacent owners:
  Functions scheduling emits no fictitious join, while Locals compilation
  omits unreachable lexical cleanup under a checked direct-exit theorem.
- [x] Rank physical expression operands by maximum evaluation offset, so deep
  nested expressions remain within `DUP1`-`DUP16` without source rewriting.
  The checked corpus now includes OpenZeppelin, Chainlink, PRBMath, Solbase,
  Balancer V3, Seaport, Compound Comet, Solmate, and Solady in addition to the
  exact pinned Permit2 and linked Aave gates.
- [x] Replace all Uniswap v4 summary/decode-only lanes with strict checked
  backend gates. SwapMath creation, TickMath, SqrtPriceMath, Lock,
  CurrencyDelta, Hooks, Extsload/Exttload, and linked PoolManager creation all
  produce complete checked artifacts.
- [x] Remove large-program native recursion failures with proved, stack-safe
  implementations of procedure traversal, compact preparation/alignment,
  block emission/equality, well-formedness, and byte-length checks. PoolManager
  schedules 770/770 units, compacts 639,081 logical instructions to 498,004
  runtime bytes, and its 500,624-byte creation artifact completes in about 26
  seconds. Output size remains diagnostic rather than a deployability gate.
- [x] Add pinned protocol-diversity gates for full Morpho Blue, Safe
  `CREATE`/`CREATE2`, ENS dynamic byte operations, and ERC-4337 packed calldata.
  All eight creation/runtime objects pass the checked backend and all 14
  differential call sequences match full-solc execution.

### 9. Optional Code Density

This track is deferred. Its checked lemmas and experiments are preserved, but
the production token-based return path is already the correctness baseline and
the unchecked return-PC migration below is not a prerequisite for the current
Permit2/Aave end-to-end proof.

- [x] Measure internal-return dispatch on exact contracts. Aave has 188
  dispatchers and 649 call sites; linear token tests and per-site cleanup are
  the largest remaining generic control-density cost.
- [x] Add Assembly-owned symbolic label pushes and raw dynamic jumps, with
  label resolution, closed/open execution preservation, observer silence, and
  exact wide-assembler emission. Compact rejects both persistent code-pointer
  forms, and ordinary accepted Assembly rejects raw dynamic jumps, until the
  invariant below is checked.
- [ ] Replace TypedCfg return tokens with typed return PCs using the existing
  `.returnPC` slot: ordinary words remain equal, while each return-PC slot
  relates the logical Assembly label PC to its compact physical PC. Prove this
  relation through only shuffles, calls, and returns; reject arithmetic or
  effectful consumption of code pointers.

  The checked first slice now covers token uniqueness, compiler-owned symbolic
  label pushes, typed dormant caller suffixes, return-PC stack lifting, dynamic
  return dispatch, and restoration of the post-return stack relation. The
  remaining part of this item is transport through complete call bodies and
  Compact's physical relocation map.
- [ ] Construct the return-PC annotation and relocation map inside the checked
  TypedCfg-to-Assembly/Compact artifact, select dynamic returns only after its
  adjacent forward and exact observer-replay theorems are checked, then
  re-profile Permit2 and Aave.
- [ ] If return-copy overhead is material, replace the current proved `ADD 0`
  local-to-word slot anonymization with a zero-byte Structured/TypedCfg relabel
  marker and prove that adjacent pass separately. The existing coercion remains
  the correctness baseline.
- [x] If deployable output still requires it, implement compact `PUSH` encoding
  as a separate Assembly-owned pass with decoding and execution preservation.
  It must not be mixed into allocation correctness.
- [x] Executable viability: minimum-width constants, bounded two-name
  growth-point lookahead, adjacent-fallthrough jump elision, and unreferenced
  label pruning produce 22855-byte Permit2 and 43933-byte Aave root code.
- [x] Prove exact variable-width byte decoding and connect decoded instructions
  to the shared Assembly open-step kernels.
- [x] Check physical program-counter independence and prove every compact
  instruction preserves runtime data and the exact open interaction tree.
- [x] Prove compiler-selected one-source-instruction execution over actual
  compact bytes, including relocated JUMP/JUMPI blocks and all open effects.
- [x] Prove PC-relocated preprocessing and open-run preservation, then integrate
  the checked bytes into recursive object planning.

## Production Drop-In Audit

The checked backend is a strong compiler-correctness result relative to the
project's canonical open, gas-erased semantics. Production replacement of
solc's backend additionally requires the following outer semantic and product
boundaries. Corpus acceptance alone does not discharge them.

- [x] Preserve one ordered open interaction tree for `gas`, `msize`, logs,
  calls, and creates across every adjacent compiler pass and exact raw-byte
  encoding.
- [x] Compile broad pinned solc-Yul corpora, including Permit2, linked Aave,
  Uniswap v4, Morpho, Safe, ENS, and ERC-4337, without contract-specific
  compiler behavior.
- [ ] Prove a fork-indexed refinement from actual gas-charging EVM execution to
  the open Assembly/bytecode semantics, including exact `GAS`, `MSIZE`, memory
  expansion, out-of-gas, exceptional halts, call gas, and transaction rollback.
- [ ] Replace the universally-terminal public boundary with forward
  preservation for every source outcome and a concrete-run corollary; retain
  the open-world theorem as the compositional compiler layer.
- [ ] Verify the solc Yul-AST import and Functions normalization performed by
  the Python bridge, or make that frontend an explicit audited trust boundary.
- [x] Replace the now-deleted, globally quantified
  `AllocationInteractionSafety.SourceSafety` with program/run-indexed safety.
  Stack-only artifacts require no scratch-reservation/non-alias promise;
  scratch-backed artifacts check only the concrete source run. The shared
  execution-safety premise still states host representability and EVM memory
  expansion bounds for actually reached operations; later derive those bounds
  from the gas-aware EVM theorem rather than unrelated source states.
  The replacement semantics is the ordinary parameterized Functions control
  interpreter instantiated with a primitive guard: safe operations delegate to
  the ordinary open primitive unchanged, while an actually reached violation
  traps. Prove successful guarded runs equal their ordinary runs, then consume
  that checked run in the adjacent Functions allocation proof. This preserves
  honest `GAS`/`MSIZE` and the exact CALL/CREATE/LOG interaction order without
  duplicating control semantics.
  - [x] Remove the uninstantiable mixed-allocation proposition and aliases from
    the public `Yul.EndToEnd` surface; the checked stack-object/raw-byte theorem
    is the sole production-facing compiler result and needs no memory premise.
  - [x] Prove guarded-run equality and reached-continuation composition through
    the Functions allocation owner.
  - [x] Thread guarded safety through nested control, loops, internal calls,
    stack-only/scratch program composition, and delete the legacy global API.
  - [x] Define canonical Yul guarded semantics whose reached primitive checks
    use the same terminal, CALL, CREATE, and ordinary-operation contracts as
    guarded Functions semantics; safe operations delegate unchanged.
  - [x] Prove the adjacent primitive safety transfer under the established
    Yul-to-Functions state relation, including honest GAS/MSIZE and unchanged
    CALL/CREATE/LOG requests.
  - [x] Prove accepted guarded Yul interaction trees equal ordinary canonical
    Yul execution through expressions, control, loops, and internal calls.
  - [ ] Lift actual-tree Yul execution safety through recursive expressions,
    control, loops, and internal calls to guarded Functions execution safety.
  - [ ] Replace the scratch-capable public Functions-facing safety premise with
    the Yul-facing execution premise; keep the premise-free stack theorem as a
    separate capability and rerun every completion gate.
- [ ] Carry the selected EVM fork/dialect in checked artifacts. Cover or
  honestly reject every solc-emittable builtin for that profile, including
  Osaka additions and supported `verbatim` forms.
- [ ] Bundle canonical initial target construction into the public theorem so
  the executed `CODESIZE`/`CODECOPY` image is definitionally the checked
  artifact's bytes.
- [ ] Prove or validate the imported cryptographic primitives, jump-destination
  scanner, and EVM helper semantics against an authoritative fork model.
- [ ] Meet deployment size and initcode limits, profile runtime gas, and add
  source maps, link/immutable references, metadata, diagnostics, and standard
  JSON artifact compatibility expected from a solc backend.

Until these items are complete, describe the result as a theorem-bearing,
checked Yul-to-bytecode backend relative to the project's semantics, not a
production-equivalent replacement for solc's backend.

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
the public boundary, while exact pinned Permit2 or linked Aave fails the checked
raw-bytecode artifact path, while any named real-contract corpus lane remains
summary/decode-only, or while any selected adjacent boundary lacks a checked
preservation theorem. Bytecode deployability and the deferred
return-PC density migration are explicitly outside this stage's completion
gate.
