# Roadmap

The exact release trust and semantic boundary is maintained in
[`PRODUCTION_ASSUMPTIONS.md`](PRODUCTION_ASSUMPTIONS.md).

## Production Boundary

The trusted frontend is a supported pinned `solc` producing optimized Yul
through `irOptimizedAst`. Solidity lowering, source optimization,
rematerialization, and source-level memory spilling belong to that frontend.
The checked backend starts at the resulting Yul program.

The executable adapter matrix currently pins solc 0.8.26 and 0.8.35 to Cancun;
the exact Permit2 gate retains solc 0.8.17 with an explicit London target.
Accepted frontend requests must name London, Paris, Shanghai, or Cancun;
newer fork targets fail closed until their instruction semantics are modeled.

## Public Spine

```text
optimized solc Yul
  -> Functions
  -> verified pressure normalization
  -> verified stack-only allocation
  -> Locals/Expressions
  -> Structured
  -> TypedCfg
  -> Assembly
  -> raw bytecode
```

`Compiler.StackArtifact` is the sole code-body artifact and
`Solidity.Frontend.VerifiedStackObjectArtifact` is the sole recursive object
artifact. Compilation fails closed when stack-only scheduling fails. The
backend performs no compiler-owned memory access.

## Migration

- [x] Preserve the mixed-allocation research line on
  `codex/archive-mixed-allocation-safety`.
- [x] Remove mixed/scratch allocation from production entrypoints, metadata,
  schemas, CLI routes, architecture exceptions, and verification roots.
- [x] Delete compiler-owned spill planning, slots, cells, frame setup/cleanup,
  and scratch-specific proof modules once unreachable.
- [x] Resolve every validated `memoryguard(size)` to exactly `size` and prove
  the frontend-owned resolution theorem.
- [x] Remove fixed `defaultReservedWords`/8,193-word behavior and explicit
  source scratch-reservation inputs.
- [x] Expose a short optimized-Yul-to-bytecode composition theorem using only
  adjacent pass-owned preservation results and checked compiler artifacts.
- [x] Ensure no generated schedule, layout, certificate, spill plan, replay
  witness, or semantic oracle appears as a public premise.

## Preserved Semantics

- [x] Honest ordered `GAS` and `MSIZE` observations.
- [x] Ordered logs and open-world CALL/CREATE-family effects.
- [x] Generic source `MLOAD`/`MSTORE`, dynamic memory, and solc-generated
  explicit memory spills.
- [x] Liveness, next-use scheduling, joins, dormant caller frames, internal
  calls, and pressure normalization.
- [x] Legitimate gas/OOG, host-memory, fork, initial-state, and trusted-frontend
  assumptions remain explicit.
- [x] Carry the requested EVM version through recursive frontend objects and
  validate primitive availability against that exact profile in Lean; bridge
  inputs without metadata and Cancun operations relabeled as London fail closed.

## Adversarial Coverage

- [x] Add a fixture retaining at least 30 non-rematerializable `SLOAD` values
  across an external call.
- [x] Confirm conventional codegen reports stack-too-deep.
- [x] Confirm optimized Yul contains solc-generated `memoryguard`, `MSTORE`,
  and `MLOAD` spills.
- [x] Compile creation and runtime objects through the checked stack-only path.
- [x] Add generated tuple, parameter, nested-control, loop, internal-call,
  dynamic-memory, CALL/CREATE, and memory-unsafe-assembly pressure cases.
- [x] Record honest rejection when memory-unsafe pressure prevents solc from
  producing stack-schedulable optimized output.

## Completion Gates

- [x] Exact pinned Permit2, linked Aave Pool, PoolManager, and complete strict
  corpus pass through checked raw-byte artifacts.
- [x] Focused and full `EvmCompiler.Verification` builds pass.
- [x] Architecture and proof-smoke checks pass.
- [x] Repository hole, trust, `unsafe`, and axiom audits pass.
- [x] Frontend regressions and adversarial tests pass.
- [x] `git diff --check` passes.
- [x] Green commits exist at coherent deletion and theorem boundaries.

Deployment-size optimization, source maps, and full gas-aware refinement remain
separate production-hardening goals; they are not prerequisites for this
stack-only correctness boundary.

## Release Hardening

- [x] Derive public initial-state/domain relations from canonical constructors
  wherever they are computational consequences rather than caller assumptions.
- [x] Classify every remaining public premise as trusted frontend input,
  source execution/resource fact, or unfinished derivation; remove the latter.
- [x] Inventory supported optimized-Yul primitives, control outcomes, object
  features, and compiler passes against executable creation/runtime coverage.
- [x] Separate structural proof-fuel exhaustion (`OutOfFuel`) from genuine EVM
  `INVALID` execution (`InvalidInstruction`) at every upper interpreter and
  derive checked call-arity facts instead of classifying malformed calls as
  truncation.
- [x] Extend adjacent preservation and the public theorem from halting outcomes
  to all supported non-truncated runtime errors, beginning with intentional
  `INVALID`; do not count executable bytecode generation as execution proof.
  Yul -> Functions, Functions -> allocated Expressions, and the transparent
  Expressions -> Structured adapter now expose checked finished/stopped
  interfaces. Structured -> TypedCfg now preserves all genuine runtime errors
  and halts through a compiler-owned static budget. TypedCfg -> ordinary
  Assembly source execution now preserves the same all-finished branches;
  compact Assembly encoding now preserves them through a compiler-sized
  `INVALID` sentinel before object payload. The allocation relation now proves
  the one-way structural invariant `target OutOfFuel -> source OutOfFuel`, and
  the public optimized-solc-Yul theorem composes all finished branches through
  the exact recursive object image.
- [ ] Add pinned real-world suites and generated adversarial cases for uncovered
  semantic families, then fix every backend rejection generically or record an
  honest supported-version/input-boundary rejection. The strict corpus now
  includes full pinned Safe and ERC-4337 EntryPoint creation/runtime objects,
  in addition to their smaller executable helper probes; Safe is deliberately
  compile-only because solc's own optimized-Yul backend rejects that pinned
  source with stack-too-deep. The generated execution matrix also covers an
  upgradeable EIP-1967-style proxy with delegated storage, reentrant self-calls,
  revert rollback, event ordering, CREATE-based upgrade, and post-upgrade
  dispatch under both supported solc pins.
  A separate fork-adversarial gate checks honest London and Cancun compilation
  and rejects a schema-valid Cancun object whose metadata is changed to London.
  Raw frontend validation also preserves solc's opcode `0x44` spelling split:
  London accepts `difficulty()`, Paris and later accept `prevrandao()`, and the
  opposite cross-fork relabelings fail before those names reach the shared core
  operation.
- [x] Separate genuine source completion/fuel sufficiency from malformed-source
  exclusion in the all-finished theorem. `truncated_iff_outOfFuel` proves the
  public truncation predicate is exactly structural source `OutOfFuel`;
  validation, scoped variable lookup, and compiler-success inversions discharge
  missing contracts/functions, invalid expressions, unknown identifiers,
  duplicate declarations, and obsolete unsupported failures internally.
- [ ] Keep exact Permit2, Aave Pool, PoolManager, adversarial pressure, broad
  corpus, Lean, architecture, trust, frontend, and diff gates green.

Pinned solc 0.8.26 rejects explicit `msize()` whenever its Yul optimizer is
enabled. This is an honest trusted-frontend limitation, not a backend semantic
restriction: the Yul proof retains real ordered `MSIZE`, while optimized
Solidity coverage records the solc rejection explicitly.

## Unconditional Prefix Theorem

The primary compiler-correctness result will be an unconditional
`Simulation.Interaction.ForwardRel`. Its truncation constructor is the finite
prefix boundary: every ordered request before source semantic-fuel exhaustion
must match exactly, while the theorem makes no claim about the unobserved target
suffix. The all-finished theorem remains a corollary, not the primary boundary.

- [x] Add shared composition for adjacent `ForwardRel` theorems when the first
  pass reflects second-pass truncation back to source truncation.
- [x] Expose Yul -> Functions -> allocated Expressions forward preservation
  with compiler-computed target fuel and no `hFinished` premise.
- [x] Lift the transparent Expressions -> Structured adapter without changing
  the prefix relation.
- [x] Extend Structured -> TypedCfg with source-`OutOfFuel` prefix preservation
  at the existing compiler-owned uniform target budget.
- [x] Compose TypedCfg -> Assembly source prefixes with branch-local terminal
  safety and exact structural-truncation reflection.
- [x] Compose Assembly -> compact decoded bytecode through pass-owned
  preparation and physical-encoding prefix theorems.
- [x] Compose compact bytecode through recursive objects
  without requiring terminal or finished source trees.
- [x] Publish a short canonical `Yul.EndToEnd` forward theorem requiring only
  checked compilation and canonical related initial states.
- [x] Derive the canonical all-finished theorem from the forward
  theorem plus their explicit run properties.
- [x] Guard the public theorem against `hFinished`, generated evidence, replay
  witnesses, or imports that cross nonadjacent compiler owners.
