# Roadmap

## Production Boundary

The trusted frontend is a supported pinned `solc` producing optimized Yul
through `irOptimizedAst`. Solidity lowering, source optimization,
rematerialization, and source-level memory spilling belong to that frontend.
The checked backend starts at the resulting Yul program.

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
- [ ] Legitimate gas/OOG, host-memory, fork, initial-state, and trusted-frontend
  assumptions remain explicit.

## Adversarial Coverage

- [ ] Add a fixture retaining at least 30 non-rematerializable `SLOAD` values
  across an external call.
- [ ] Confirm conventional codegen reports stack-too-deep.
- [ ] Confirm optimized Yul contains solc-generated `memoryguard`, `MSTORE`,
  and `MLOAD` spills.
- [ ] Compile creation and runtime objects through the checked stack-only path.
- [ ] Add generated tuple, parameter, nested-control, loop, internal-call,
  dynamic-memory, CALL/CREATE, and memory-unsafe-assembly pressure cases.
- [ ] Record honest rejection when optimized Yul remains unschedulable.

## Completion Gates

- [ ] Exact pinned Permit2, linked Aave Pool, PoolManager, and complete strict
  corpus pass through checked raw-byte artifacts.
- [ ] Focused and full `EvmCompiler.Verification` builds pass.
- [ ] Architecture and proof-smoke checks pass.
- [ ] Repository hole, trust, `unsafe`, and axiom audits pass.
- [ ] Frontend regressions and adversarial tests pass.
- [ ] `git diff --check` passes.
- [ ] Green commits exist at coherent deletion and theorem boundaries.

Deployment-size optimization, source maps, and full gas-aware refinement remain
separate production-hardening goals; they are not prerequisites for this
stack-only correctness boundary.
