# Roadmap

The exact release trust and semantic boundary is maintained in
[`PRODUCTION_ASSUMPTIONS.md`](PRODUCTION_ASSUMPTIONS.md).

## Production Boundary

The trusted frontend is a supported pinned `solc` producing optimized Yul
through `irOptimizedAst`. Solidity lowering, source optimization,
rematerialization, and source-level memory spilling belong to that frontend.
The checked backend starts at the resulting Yul program.

The executable raw-frontend adapter matrix currently pins solc 0.8.26 and
0.8.35 to Cancun because those pins emit structured `irOptimizedAst` for the
production corpus. Older exact-version suites, including Permit2 on solc
0.8.17/London, may remain legacy bridge regression coverage, but they do not
join the raw production theorem unless that solc output contains structured
`irOptimizedAst`.
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

## Raw solc Frontend Migration

Goal: remove Python semantic normalization from the trusted production path.
Python may invoke solc, transport Standard JSON, and run differential tests,
but the checked compiler source program must be derived in Lean from raw solc
Standard JSON `irOptimizedAst`.

Current split:

- Raw decoding: `Solidity.RawAst` owns Standard JSON contract selection,
  `irOptimizedAst` object selection, pinned fork metadata decoding, raw Yul
  object/code/data syntax, and fail-closed malformed-node rejection.
- Checked elaboration: `Solidity.RawAst.Elab` owns literal decoding, canonical
  call classification, lexical binding checks, nested-function hoisting with
  alpha-renamed generated functions, and `clz` helper insertion.
- Source normalization: existing `Solidity.Frontend` still owns memoryguard
  inference, object-builtin resolution, local data/object layout, linker and
  immutable resolution, fork spelling validation, and object image planning.
- Orchestration: Python remains temporarily as solc transport and old-bridge
  differential tooling; it must stop constructing the theorem's
  `Solidity.Frontend.Program` before this migration is complete.

Transformation inventory from `scripts/solidity_to_yul_lean.py`:

- [x] Literal decoding moved into Lean for raw numbers, booleans, strings, and
  hex bytes.
- [x] Call classification moved into Lean using `Frontend.Primitive.ofName?`,
  object-builtin, unsupported-dialect, and user-call tables.
- [x] Lexical scope checking and name resolution moved into Lean for the raw
  elaborator.
- [x] Nested-function hoisting and alpha-renamed generated callees implemented
  in Lean; nested `Stmt.functionDef` nodes are preserved, not erased.
- [x] `clz` lowering moved into the Lean raw elaborator as a generated helper;
  the generated helper/call now has a local source-reference preservation
  theorem, with broader frontend theorem composition still tracked below.
- [x] Object/data ordering preserved and fail-closed in Lean through explicit
  raw-derived `ObjectItemRef`s plus `itemRefsPreserveOrder?` validation.
- [ ] Standalone Yul data-name recovery remains Python-only and is not part of
  the raw Solidity `irOptimizedAst` production theorem.
- [x] Source/contract/object selection moved into Lean for raw Standard JSON.
- [x] Fork/linker metadata moved for the raw Standard JSON output path: fork
  metadata and selected-contract `metadata.settings.libraries` linker symbols
  are decoded in Lean. Explicit linker-symbol arguments remain only as a
  transition/differential hook.
- [x] Memoryguard inference remains reused in `Solidity.Frontend`; Python does
  not need to normalize it for the raw path.

Next raw frontend layer:

- [x] Add a local raw-vs-normalized bridge differential gate over both pinned
  solc versions, creation/runtime selection, recursive frontend digests, and
  checked artifact sizes for representative real fixtures, including a linked
  library fixture that exercises raw metadata linker-symbol decoding.
- [x] Add a pinned Aave Pool raw corpus gate over both pinned solc versions and
  creation/runtime object selection; Lean raw elaboration consumes the raw
  Standard JSON, preserves seven metadata linker symbols, matches the legacy
  bridge frontend object shape, and reproduces the checked artifact sizes.
- [x] Add a pinned Uniswap v4 PoolManager raw corpus gate for the compatible
  exact-pragma solc 0.8.26 source; creation/runtime raw Lean elaboration
  matches the legacy bridge frontend object shape and reproduces checked
  artifact sizes, while solc 0.8.35 fails closed before raw AST production
  because the source pins `pragma solidity 0.8.26`.
- [x] Add pinned Safe and ERC-4337 EntryPoint raw corpus gates over both
  supported solc pins. Safe is covered through raw optimized Yul plus metadata
  because solc's own bytecode backend rejects the pinned source
  stack-too-deep; EntryPoint includes solc bytecode and raw Lean artifact
  checks for creation/runtime. Both now compare raw Standard JSON Lean
  elaboration against the legacy bridge frontend object shape across both
  pins and creation/runtime selections.
- [x] Add a pinned Permit2 version-boundary gate: unmodified full Permit2 pins
  `pragma solidity 0.8.17`; exact solc 0.8.17 compiles Permit2 bytecode under
  London but emits no `irOptimizedAst`, so the Lean raw path fails closed.
  Supported raw solc 0.8.26 and 0.8.35 also fail closed before raw AST
  production because of the exact pragma. The legacy
  solc-0.8.17/Python-normalized bridge path remains regression coverage, not
  production raw-theorem coverage.
- [ ] Differentially compare raw Lean elaboration against the old bridge over
  both pinned solc versions and the full corpus: Aave frontend shape now
  compares raw Standard JSON against the legacy bridge for creation/runtime on
  both pins, and PoolManager frontend shape now compares raw Standard JSON
  against the legacy bridge for creation/runtime on its compatible exact
  solc 0.8.26 pin. Safe and EntryPoint frontend shapes now compare raw
  Standard JSON against the legacy bridge for creation/runtime on both pins.
  Permit2 remains fail-closed legacy coverage because solc 0.8.17 emits no
  structured `irOptimizedAst`. All real suites and adversarial fixtures remain
  to be widened.
- [x] Add a raw-bridge transition path: `evm-compiler-backend raw-*` consumes
  raw solc Standard JSON directly through `RawAstPublic`, and the transition
  smoke proves normalized-bridge mutations cannot affect raw input compilation.
- [ ] Add local preservation/validation theorems for raw elaboration,
  nested-function hoisting, and `clz` expansion. `elaborateCode_parts`
  reconstructs the checked raw elaboration core state from successful public
  code elaboration, and `decodeAndElaborateSolcIrJson_parts` reconstructs the
  selected raw Standard JSON source/contract/object plus checked raw-object
  elaboration from a successful frontend program decode.
  `decodeAndElaborateSolcIr?_parts` lifts that evidence to the public raw
  string interface. `Raw.Object.elaborate?_parts`,
  `decodeAndElaborateSolcIrJson_objectParts`, and
  `decodeAndElaborateSolcIr?_objectParts` reconstruct the successful checked
  code elaboration, object-item elaboration, and final `Frontend.Object`
  fields. `itemRefsPreserveOrder?` validates that the elaborated frontend
  object keeps the mixed raw object/data order through raw-derived
  `ObjectItemRef`s; the raw string and artifact wrapper theorems expose this
  checked condition. `compileArtifactFromRawSolcIr?_rawParts` and the
  explicit-linker variant lift the same raw parse/selection/elaboration
  evidence through the artifact-facing wrappers, including Lean-decoded linker
  metadata for the default path. First checked `clz` validation invariant:
  successful code
  elaboration that returns generated `clz` helper/argument/result names also
  returns the corresponding generated helper function definition. First checked
  nested-hoist validation invariant: every function accumulated in the raw
  elaborator's `hoistedFunctions` state is retained in the successful returned
  function list. `Raw.Object.ClzExpansionOk` and
  `Raw.Object.HoistedFunctionsRetained` lift these invariants through raw
  object elaboration, raw string decoding, and artifact-wrapper success. The
  generated `clz` helper theorem now also exposes its one-argument/one-result
  shape plus successful Yul function-definition conversion. The helper is
  factored through a named `ClzHelperSpec` over the generated binary-search
  schedule and exact helper body. Successful raw object elaboration, raw string
  decoding, and artifact-wrapper compilation now expose
  `Raw.Object.ClzHelperSpecOk`. The local `ClzHelperModel` now gives the
  generated schedule a checked executable semantic target: it proves the
  highest-bit schedule returns `255 - highestBit` for all 256 nonzero bit
  positions and checks representative `UInt256` executions against the
  `255 - log2(x)` reference. `ClzHelperExecution` executes the exact generated
  helper-body frontend fragment over the same `UInt256` primitives and proves
  its returned word equals `ClzHelperModel.run`; the spec and raw-code
  elaboration lift theorems expose that fact for generated helper entries
  returned by successful elaboration. `ClzCallReplacement` now proves that an
  evaluated raw `clz(x)` replacement call to the generated helper returns
  `ClzHelperModel.run x`, and successful production raw object elaboration
  exposes that theorem for its generated helper entry. The word/log bridge now
  proves the helper branch condition: for nonzero values and solc's checked
  shifts below 256, the generated `shr`/`iszero` test is equivalent to
  `log2(value) < checkShift`. It also proves that checked non-overflowing
  helper left shifts add the shift amount to `log2`. Production raw elaboration
  now composes those branch/shift facts through the generated eight-step
  schedule: `ClzHelperModel.runNonzero_ret_eq_runHighestBit` proves the nonzero
  fold result, `ClzHelperModel.run_eq_reference` proves the all-word model
  equals the declared `255 - log2(x)` source reference, and
  `ClzCallReplacement.evalHelperCallExpr_eq_reference` plus the production raw
  object wrapper expose that a generated helper-call replacement returns the
  source reference value. Production raw elaboration
  now fail-closes unless the generated `clz` argument/result names are distinct,
  and exposes the checked condition through a wrapper theorem that discharges
  the helper-execution theorem's name premise. Retained
  nested function-definition statements are alpha-renamed to generated function
  names before their checked frontend no-op lowering. Raw production elaboration
  now also fail-closes on any
  frontend object that still contains an unlowered callee named exactly `clz`,
  with decode and artifact wrapper theorems exposing
  `Frontend.Object.noRawClzCall? = true`. It also fail-closes unless every
  retained nested-function staging node has an identical callable entry in the
  same frontend object's function table, with decode and artifact wrapper
  theorems exposing `Frontend.Object.functionDefStubsRetained? = true`.
  Production Yul
  conversion now separately fail-closes unless every retained nested-function
  staging node lowers through the frontend Yul lowering function to one of the
  exact ordered Yul function entries consumed by the backend, with
  `Frontend.Object.toSolcYulOrderedProgram?_functionDefStubsLoweredToEntries`
  pinned in the verification root. The nested-stub no-silent-erasure facts now
  expose the local boolean evidence at the exact erased node: a retained
  `functionDef` staging node has a matching callable `FunctionDef` entry, and
  a staging node erased during Yul conversion has an ordered lowered Yul
  function entry for its body. Raw production elaboration now also fail-closes
  unless every frontend `.call .user` resolves to a function entry in the
  current frontend object's function table, checking each child object against
  its own function table. The raw object, raw JSON/string decode, and
  artifact-wrapper theorems expose
  `Frontend.Object.userCallsResolved? = true` for successful production raw
  elaboration. The raw elaborator now also exposes local alpha-resolution
  equations: singleton and cons-case nested-function scope construction create
  the raw-name to generated-name mapping, ordinary user-call elaboration
  rewrites a raw source callee to the generated name returned by that active
  function-scope resolver, and nested function-definition elaboration emits the
  retained frontend stub under that same resolved generated name. The hoist
  pass also exposes the corresponding single-definition equation: when the
  active local function scope maps a raw nested name to a generated name,
  hoisting inserts the elaborated function entry under that generated name in
  `hoistedFunctions`.
  The remaining raw frontend semantic gap is source-level preservation for
  alpha-renamed nested-function call resolution plus broader composition into
  the final source theorem.
- [x] Expose the production interface
  `decodeAndElaborateSolcIr? rawJson selection = some frontendProgram` without
  public certificate premises, and expose artifact-facing raw wrappers whose
  success reconstructs the internally selected raw source/contract/object,
  checked object elaboration, and artifact validity.
- [x] Add the isolated raw theorem composition:
  `Solidity.RawAst.optimizedRawSolcIrToRawBytecode` composes checked raw
  Standard JSON decoding, Lean-decoded linker metadata, frontend validation,
  and artifact construction into the unconditional optimized-Yul
  finite-prefix theorem without a normalized Python program premise.
- [ ] Close the remaining raw frontend semantic-preservation work by proving
  nested-function hoist/alpha-renaming preservation and composing the local raw
  frontend facts into the final source theorem; do not create a Yul-to-bytecode
  proof corridor or depend on the parallel hFinished work.

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

- [x] Raw-capable pinned corpus gates pass through checked raw-byte artifacts,
  including linked Aave Pool, PoolManager on its compatible exact 0.8.26 pin,
  Safe, EntryPoint, and adversarial fixtures. Exact Permit2 remains covered as
  a fail-closed solc-0.8.17 version-boundary/legacy-bridge regression because
  that compiler emits no structured `irOptimizedAst`.
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
