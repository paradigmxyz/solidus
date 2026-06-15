# Verified EVM Compiler Architecture Migration

Last updated: 2026-06-14 PDT.

## Objective

Migrate the verified compiler from parallel feature-specific interpreters,
lowerers, and proof corridors to a compositional architecture with:

- one reusable source effect semantics;
- one outcome-indexed simulation interface;
- one allocation-plan-driven lowering path;
- one allocated typed control-flow IR;
- compositional certificates for generated code;
- a small, stable public theorem surface;
- verification and build feedback suitable for parallel worktrees.

The migration is complete only when gas/msize support and stack-too-deep
handling use the common architecture, the public compiler spine has cut over,
superseded routes have been deleted, and the end-to-end Lean verification gates
pass.

## Active End-to-End Theorem

The architecture migration is complete, but the stronger independent-Yul
theorem is not. The current public resource theorem starts from compiler-owned
Structured evaluation and target entry/block simulation. It does not yet prove
that the original imported Yul program consumes the target's complete ordered
`gas()`/`msize()` transcript or produces a related final result.

Target public spine:

```text
imported Yul replay
  -> observer-aware Functions semantics
  -> allocation-lowered Locals/Expressions semantics
  -> Structured outcome
  -> TypedCfg whole-program path
  -> Assembly whole-program execution
  -> bytecode target observer result
```

Completion theorem shape:

```text
accepted Yul + successful compilation + related initial states
  + concrete target observer run
  => exact source transcript consumption
  + related source/target outcomes
```

This is a backward adequacy theorem. Forward source preservation plus target
determinism is insufficient because it does not construct a source run from a
target run. Each compiler boundary therefore needs a lower-to-upper
no-extra-behavior theorem, and the final public theorem should be a short
composition of those adjacent adequacy results.

### Enforced Observer Architecture

Observer verification is organized by adjacent compiler ownership:

```text
Yul.FunctionsObserverPreservation
  -> Functions allocation observer preservation
  -> Locals/Expressions observer preservation
  -> Structured observer preservation
  -> TypedCfg.ObserverPreservation
  -> Assembly observer preservation
  -> Public.Observer
  -> Yul.EndToEnd
```

`Simulation.ObserverPass.Interface` is the stable common contract. Its
forward-preservation and backward-adequacy interfaces expose only the actual
compiler equality, related semantic inputs, source/target runs, and an
outcome relation. Compiler-generated layouts, replay certificates, call
oracles, and emitted-code witnesses are not part of that interface.

Ownership rules now enforced by `scripts/check_architecture.sh`:

- observer modules cannot define observer-specific compilers or lowerers;
- the Yul observer proof cannot import or reason about Locals, Structured,
  TypedCfg, Assembly preservation, or public target execution;
- `Yul.EndToEnd` cannot import lower-pass preservation modules or perform
  recursive lower-pass execution reasoning;
- TypedCfg observer execution must specialize
  `TypedCfg.EffectSemantics`, not define a second recursive CFG interpreter;
- `Functions.Source.Effectful` is the canonical exported parameterized
  Functions semantics for new pass and observer proofs;
- the retired vertical `Yul.ObserverPreservation` and mixed
  `Yul.ObserverOracle` modules cannot be restored.

Adjacent boundary status:

- [ ] Yul -> Functions: gas/msize primitive, expression, and let-statement
  leaves are checked in the pass-owned module; complete expression,
  statement, function, and program forward/backward theorems remain.
- [ ] Functions -> allocated Locals/Expressions: shared allocation artifacts
  exist, but observer-aware forward/backward theorems remain. The frontend now
  retains Solidity `memoryguard` declarations and threads a source-owned
  `MemoryContract.Contract` through Yul, Functions, object lowering, allocation,
  and checked artifacts. Scratch plans must be authorized by that contract.
  The runtime backend uses a private allocator cell and frame interval inside
  the reservation; the old free-memory-pointer bump allocator has been
  deleted. `Compiler.MemoryRelation.MachineRel` now permits differences only
  inside the reservation and in target memory growth, while preserving return
  data and output. Remaining proof work is to connect source memory-access
  safety, dynamic frame-depth bounds, named-variable locations, outcomes, and
  observer cursors to this relation. `Functions.AllocationObserverRelation`
  now supplies the allocation-indexed live-store relation, stack-prefix index,
  source/target machine relation, outcome modes, and depth-indexed frame
  budget. Successful scratch configuration constructs its reservation facts
  and rejects empty reservations. Fuel-indexed frame safety derives every
  smaller active depth. The allocation relation now also preserves the complete
  shared EVM world state (execution environment, accounts/storage, transaction
  data, blocks, and substate), rather than relating only machine memory and
  locals; this is required before ordinary environment and storage primitives
  can be lifted soundly. Replay consumption is checked in both directions.
  `Functions.AllocationObserverPreservation` proves forward preservation and
  backward classification for compiled `gas()` and `msize()` expression
  leaves, including the temporary result above stack-allocated locals.
  Literal and stack-resident variable reads are also checked in both
  directions through concrete `PUSH32` and `DUPn` execution. Scratch reads
  use the stronger `ScratchStateRel`, which records the hidden frame pointer,
  active-memory coverage, no-wrap frame bound, and live scratch-slot bounds.
  It is preserved by expression stack transformations and replay consumption.
  Gas/msize leaves and full scratch-variable reads are checked in both
  directions. The spill read executes the canonical frame-pointer `DUP`, slot
  `PUSH`, `ADD`, and preallocated `MLOAD` sequence; the proof derives that the
  load cannot expand memory and returns the source named-variable value.
  Location lookup is now owned canonically by `Locals.Allocation.Plan`;
  well-formed plans derive live scratch-slot bounds, and successful
  `Locals.Expr.compileCode` execution constructs the exact spill-read code
  consumed by the observer theorem instead of requiring caller-supplied code.
  Static plan regions certify frame width independently of the current
  activation's dynamic frame base, so recursive activations can construct the
  same relation from allocator depth rather than an impossible base equality.
  Scratch-frame configuration now rejects malformed wrapping reservations and
  derives each budgeted activation's no-wrap and concrete host-addressability
  invariants from checked compiler configuration. `Compiler.MemoryRelation`
  now proves exact byte locality for `writeWord`, reservation-preserving
  target writes, monotone active-memory growth, and `MachineRel` preservation
  for every compiler-owned `MSTORE`. Exact same-slot and disjoint-slot
  read-after-write theorems are checked. `ScratchStateRel.assign_scratch_live`
  now preserves the allocation relation for both newly declared and already
  live spilled names, including every unaffected stack/scratch binding,
  frame coverage, memory-size behavior, and observer cursor. Compiler-derived
  spill writes now execute the actual `DUP`/`PUSH`/`ADD`/`MSTORE` sequence and
  are checked in both directions. The private allocator initialization,
  frame-pointer advance, last-slot preallocation, complete frame acquisition,
  and frame release sequences have checked execution theorems. Acquisition
  establishes allocator depth, frame activity, frame allocation, and machine
  relation; release restores the previous allocator depth without changing the
  data stack. Proving release exposed and fixed an operand-order bug in the
  emitted `SUB`: the compiler now pushes frame bytes before loading the current
  allocator value, so EVM subtraction computes `current - frameBytes`.
  `Functions.AllocationObserverSafety` defines source-facing primitive and
  terminal memory-safety contracts relative to the authorized reservation.
  Memory-touching primitives additionally require ordinary source-memory
  consistency and a source-facing non-wrapping expansion bound, preventing
  target spill allocation from exposing dormant bytes or invalidating later
  `msize()` observations. Canonical `mload`, `mstore`, and `mstore8` now have checked
  adjacent forward theorems: padded reads agree outside the reservation,
  synchronized source writes preserve reservation-relative memory, active
  memory grows monotonically without wrapping, every live spill lookup remains
  stable, and the real one-op Structured executions return the source results.
  Fixed-length byte writes share an exact decomposition, locality,
  monotone-growth, synchronized-relation, and disjoint spill-lookup interface;
  arbitrary offset/padded `ByteArray.write` now has the corresponding
  destination-independent inside/outside locality, monotone size,
  synchronized-relation, disjoint padded-read, and spill-lookup interface.
  The complete copy family is checked through one pass-owned `CopySpec`
  interface and adjacent primitive-forward theorem: `calldatacopy`,
  `codecopy`, bounds-sensitive `returndatacopy`, world-updating
  `extcodecopy`, and overlapping-memory `mcopy`. `mcopy` additionally proves
  that source-approved reads obtain equal bytes from reservation-related
  memories before writing them to the destination.
  Arbitrary source-approved padded reads now share one machine theorem that
  preserves reservation-relative memory and synchronized active-memory
  expansion. Canonical `keccak256` instantiates a pass-owned `ReadSpec`, so its
  digest equality and spill preservation reuse the same adjacent allocation
  theorem intended for logging and terminal reads.
  `LOG0` through `LOG4` now share a proof-only `LogInvocation` classifier,
  `logOp_both`, and the same `ReadSpec` allocation theorem. Their concrete
  Functions argument reversal, topic order, appended log bytes, world update,
  active-memory growth, and live spill preservation are checked once per
  semantic family rather than through five allocation proofs.
  `canonicalPrimitiveForward` is exhaustive over `Structured.BasicOp`:
  ordinary operations use `SharedFamily`, memory operations use their
  pass-owned families, `gas`/`msize` use observer instances, call/create are
  excluded by the source-facing no-external-effects safety judgment, and
  backend-only DUP/SWAP plus `INVALID` are impossible successful source cases.
  `ScratchStateRel` retains an actual reservation witness for its active frame,
  ruling out impossible unrestricted scratch states and making source-write
  disjointness an allocation-owned invariant.
  Its checked `Expr.MemorySafeEval` and `ExprSeq.MemorySafeEval` derivations
  reuse the canonical parameterized Functions evaluator and erase back to
  ordinary evaluation; they are not alternate interpreters or compiler
  certificates. Exact expression-result relations now compose produced values,
  target stack prefixes, allocation offsets, active scratch-frame invariants,
  and observer state. Forward and backward wrappers are checked for literals,
  stack variables, scratch variables, `gas()`, and `msize()`.
  Terminal memory behavior is now checked through the pass-owned
  `AllocationObserverTerminal` family. `STOP`, `RETURN`, `REVERT`, and
  `SELFDESTRUCT` share one source-memory-safe invocation interface; return and
  revert use reservation-relative read preservation, terminal execution
  replays over an arbitrary caller stack suffix, and halting outcomes retain
  only observable shared state after compiler cleanup discards dead locals.
  `AllocationObserverSafety.Stmt.LeafMemorySafeRun` now classifies every
  nonrecursive source statement family using equations from the canonical
  Functions evaluator rather than a second interpreter. The first adjacent
  statement theorem is checked in both directions for expression statements:
  it derives the singleton target block from the real `lowerStmt` and
  `Locals.Block.compileOpen` passes and relates their regular outcomes. The
  allocation store relation now derives current stack depths from the final
  plan order filtered to currently live names; final-scope plan depths are no
  longer treated as runtime depths before later declarations execute. The
  hidden frame-pointer depth consequently changes with stack declarations.
  `AllocationObserverContext.classify_let_transition` derives those dynamic
  stack-order and frame-depth transitions from the real lowerer, and
  `AllocationObserverStatement.LetLeaf.forward_of_compilers` checks declaration
  forwarding through both emitted shapes: a stack declaration retains the
  expression result as a named local, while a scratch declaration executes the
  canonical frame-pointer `DUP`/offset/`ADD`/`MSTORE` sequence. Declaration
  backward adequacy is also checked by exact singleton-code execution
  uniqueness. `ActivationStateRel`, `ActivationExprResultRel`, and
  `ActivationOutcomeRel` now provide one representation-neutral recursive
  interface for stack-only and scratch-frame activations. Stack assignment has
  checked dynamic-depth replacement and concrete `SWAP`/`POP` execution;
  scratch assignment reuses the canonical frame store. The real assignment
  lowerer and Locals compiler now have pass-owned forward preservation and
  backward adequacy for both placements. Observer-aware expression evaluation
  additionally proves that it preserves the named-variable store.
  The single recursive expression forward/backward proof now runs through the
  activation interface for both genuinely stack-only and scratch-frame
  artifacts, with one exhaustive primitive family and no parallel interpreter.
  Declaration and assignment consumers now expose activation-general
  forward/backward APIs. Canonical Functions fuel monotonicity and Structured
  block append lemmas are owned by their semantic modules; the allocation
  statement boundary composes them through checked empty, regular-head, and
  abrupt-head block interfaces. Expression, declaration, and assignment leaves
  lift into the regular interface. Terminal arguments execute through the real
  lowerer/compiler, the shared expression-sequence theorem, and a terminal-owned
  halt relation; `RETURN`, `REVERT`, and `SELFDESTRUCT` therefore lift into the
  nonregular interface without retaining dead local/frame realization.
  Plain cleanup and real compiler leaves for `break` and `continue` are checked
  forward and backward. Preserving `SWAP`/`POP` cleanup for `leave` is checked
  forward and backward, and the forward statement theorem now evaluates the
  canonical named-return sequence, removes the complete activation layout, and
  establishes the exact returned-value stack relation. Return lowering has one
  indexed implementation shared by the executable compiler and proof.
  Complete `leave` backward adequacy now inverts that same real three-statement
  expansion. Scoped blocks have checked regular and abrupt composition:
  regular execution appends and proves the compiler-owned cleanup, while
  nonregular execution skips the unreachable cleanup in both semantics. The
  actual `.block` lowerer/compiler expansion has a pass-owned decomposition
  theorem exposing only its adjacent open-body and `finishScoped` components.
  `ActivationInvariant` now bundles the compiler context, plan
  well-formedness, live-source definedness, allocation state relation, and
  exact active-stack/layout equality. Zero-result expressions, declarations,
  and assignments preserve that invariant through the real lowering and
  Locals compilation paths; declaration and assignment preservation retain
  exact pass-owned stack-effect equations, including scratch stores. The
  stable `RegularStmtInvariantForward` interface is ready for recursive
  statement-list induction without reconstructing leaf stack facts. Regular
  open blocks now compose inductively while retaining that invariant. Lexical
  scope exit uses a semantic `PlanAgreesOn` transport relation: the inner and
  outer plans may assign different plan-local stack depths, but must realize
  surviving locals in the same runtime stack order and the same scratch slots.
  Plans certified against one concrete activation context derive that relation
  automatically. Exact cleanup stack balance plus a checked context-restoration
  theorem re-establishes the complete outer activation invariant from ordinary
  layout-prefix and surviving-slot facts, without accepting plan agreement as
  recursive proof evidence or pretending nested scopes share one plan. The real
  open-block lowerer now proves those facts for every well-scoped statement
  list: new stack locals form a fresh removable layout prefix and incoming
  names retain their allocation slots. `SameFrame` tracks that regular lexical
  execution may move a scratch frame pointer but cannot change backend mode or
  frame width. These facts construct the exact cleanup transition internally,
  and regular `.block` preservation is checked through the actual lowerer,
  Locals compiler, cleanup, and canonical effect semantics.
  Both regular `switch` paths are now checked in a construct-specific module.
  The real scrutinee lowerer/compiler, exact target stack pop, and pass-owned
  branch-selection lemmas handle unmatched fallthrough; selected cases and
  defaults expose their ordinary scoped lowering/compilation equations to the
  recursive body theorem and restore the common outer activation invariant.
  All `for` outcomes are now checked through a construct-specific adjacent
  module. Canonical source-fuel inversion proves regular recursion, body
  breaks, direct body/post leave or halt, and leave/halt reached after
  arbitrarily many regular or continuing iterations. The public statement
  boundary derives recursive loop evidence internally from one-step body/post
  preservation. It also covers initializer leave/halt and proves the ordinary
  compiler-emitted outer cleanup unreachable for every abrupt outcome.
  Validated function artifacts now construct the exact all-stack or
  scratch-frame parameter/return prelude, execute it, and package the
  compiler-derived body context as the standard `ActivationInvariant`.
  `ActivationRuntimeInvariant` extends that local boundary with the global
  allocator depth and exact ownership of the current scratch frame. Allocator
  readiness transports across ordinary machine-preserving and monotone-memory
  steps, and owned caller spill words are proved to end before the next frame
  base. Remaining work at this boundary is source-fuel recursive
  statement/function/call composition, propagation of source-facing memory
  safety and fuel, and the whole-program adjacent forward/backward theorem.
  The final scratch theorem must expose or derive an actual-execution source
  memory-safety contract; no-external-effects alone does not prove that source
  memory accesses avoid the reserved spill interval.
- [ ] Locals/Expressions -> Structured: generic effect semantics exists;
  complete allocation-sensitive observer theorem remains. The transparent
  Expressions-to-Structured adapter now has checked forward and backward
  `ObserverPass` theorems in `Expressions.ObserverPreservation`, reusing the
  canonical Structured control interpreter rather than defining an
  observer-specific interpreter.
- [x] Structured -> TypedCfg: complete observer-aware forward preservation is
  checked for statements, blocks, recursive switch/loop/call control, halts,
  and whole-program artifacts. Terminal stack-suffix preservation is now a
  checked shared semantic theorem rather than a public premise. Backward
  straight-line code, condition evaluation, compiler-facing code, and the
  false conditional branch are checked across active frames without a
  caller-supplied reflection or shape premise. `Code.FrameReflectingAt` is
  derived structurally from the actual body typing and source stack lower
  bound, and relates framed target execution back to source execution through
  the existing `ReplayStateRel`. The false unindexed reflection hierarchy was
  deleted. Checked instruction-family stack deltas and `Code.shapeSound`
  ensure typed code cannot consume compiler-owned return data. Terminal and
  false-if leaves also remain checked at the closed no-frame boundary. Halt
  typing enforces operand arity, so compiler-owned return data cannot satisfy
  missing source operands. Backward execution now uses the existing TypedCfg
  `runN` through a checked minimal first-boundary relation and shared
  `AdequateAt` interface; empty blocks and straight-line statements implement
  the interface, and conditional composition is checked with strictly smaller
  target fuel in the taken branch. The interface now generalizes to
  `AdequateWithin`, which stops at any checked enclosing target boundary while
  retaining the pass-owned compiler fallthrough shape and source stack bound
  for regular source outcomes. Generic earliest-prefix selection, residual
  jump-fuel composition, and shared source-evaluation fuel monotonicity are
  checked. Conditional lowering now rejects a regularly completing body whose
  output shape disagrees with the branch join, preventing subsequent code from
  consuming compiler-owned frame data. The regular-fallthrough half of
  recursive statement-list composition is checked through exact residual
  target fuel and a reconstructed `StateRel.At` tail boundary. The
  no-fallthrough branch and compiler-driven sequence dispatcher are also
  checked, as are the `break`, `continue`, `leave`, and terminal
  `AdequateWithin` leaves. Compiler contexts now carry typed break, continue,
  and leave destinations; switch bodies and loop body/post fragments must pass
  checked fallthrough joins before lowering succeeds. Ordinary and observer
  preservation, plus the existing adequacy leaves, consume pass-owned
  decomposition theorems for those checks. Recursive switch backward adequacy
  is now checked end to end within this adjacent pass: scrutinee inversion,
  matched and skipped cases, nonempty and empty defaults, `switch_some`,
  `switch_none`, exact residual target fuel, and regular stack-shape artifacts
  compose through a private `AdequateWithin` rule. Recursive loop backward
  adequacy is also checked: condition inversion, exact first-prefix splitting,
  body break/continue/regular/leave/halt outcomes, post execution, strictly
  decreasing residual target fuel, initializer composition, and checked
  fallthrough joins all live in the pass-owned
  `Structured.ObserverLoopAdequacy` module. Internal-call backward adequacy has
  a checked callback rule in `Structured.ObserverCallAdequacy`: call entry,
  optional allocation relabeling, callee execution, exact source-frame
  reconstruction, and return dispatch compose through one `AdequateWithin`
  rule. Procedure lowering now rejects allocation entry shapes that move or
  erase the hidden return token and rejects regular procedure fallthrough that
  disagrees with the declared return shape.
  `Structured.ObserverActivationBoundary` defines the pass-owned
  `FrameMatches`/`JumpAt` interface and derives it from the indexed state
  relation. Statement sequencing, recursive loops, and internal calls now use
  `JumpAt` for every internal continuation, so a nested recursive activation
  cannot satisfy its caller's boundary merely by reaching the same static
  label. The label-only `JumpOr` predicate and adapters have been deleted and
  an architecture guard prevents their restoration. Recursive loop adequacy
  now carries the enclosing semantic closure through each smaller-fuel
  iteration, so the compiler-facing loop theorem composes under arbitrary
  activation-indexed boundaries. Internal calls expose a fixed-target-fuel
  theorem whose callee obligation is strictly smaller, and pushed return-frame
  realization proves that a recursive callee exit cannot satisfy its caller's
  same-label continuation. The generated-context mutual statement/block
  theorem and whole-program terminal backward adequacy are now checked.
  Shared outcome artifacts and terminal leaves were extracted into sibling
  modules. Source-frame typing now distinguishes token-free caller frames,
  which retain a stack lower bound, from active procedure frames, whose
  source-visible stack length is exact above the compiler-owned return token.
  The invariant is preserved by accepted instructions, observer handlers,
  straight-line code, condition pops, statement sequencing, switches, and
  loops, and is carried by the outcome-indexed adequacy artifact. The
  frame-invariant proofs live in `Structured.ObserverFrameInvariant`.
  `Structured.ObserverSequenceAdequacy` now owns recursive statement-list
  composition and exposes one compiler-driven adjacent-pass theorem for the
  forthcoming mutual proof. Both central observer modules remain below the 5K
  soft limit. `Structured.TypedCfgCompilerFreshness` now proves monotone supply
  allocation for blocks, lists, cases, and defaults, plus strict supply growth
  for every successful statement lowering; the generated-context mutual proof
  can therefore derive nested-label freshness from the existing compiler pass.
  `Structured.ObserverGeneratedBoundary` owns generated-label age and
  acceptance contracts. Sequence and conditional adequacy now expose
  fixed-target-fuel forms while preserving their unbounded APIs as wrappers.
  Switch adequacy now does the same in its pass-owned sibling module. Loop
  adequacy is also fixed-fuel: initializer prefixes are non-increasing and
  body, post, and iteration callbacks are strictly decreasing. The mutual
  theorem can now use one lexicographic fuel/compiler measure across every
  recursive Structured control form. Switch tests, dispatch entries, and case
  bodies now use disjoint named label constructors, eliminating arithmetic tag
  collisions with statement tails and with one another. Recursive calls now
  expose an activation-protected fixed-fuel interface: accepted jumps are
  owned by the current activation or a checked dynamic ancestor, while
  compiler-derived CFG input shapes separate proc entry, body entry, and exit
  across arbitrary recursion depth without public label or call-oracle
  premises. Statement-list composition uses the exact outer boundary for
  non-fallthrough heads and passes checked tail-entry shape plus source-return
  preservation to recursive callbacks. `ActivationFreshExcept` now treats
  reused generated labels as valid only when the accepted jump belongs to a
  strict ancestor activation, and `RecursiveBoundary` bundles that contract
  with activation ownership. The call-body callback receives the checked
  activation extension constructed by the existing call proof. Procedure
  `leave` adequacy derives its nonempty source return stack from the active
  return-token realization instead of taking it as a separate source premise.
  `Structured.ObserverGeneratedAdequacy` now owns the mutual-proof context:
  source control permissions, original procedure lookup, active return-token
  availability, same-activation boundary transport, and pushed procedure-body
  boundaries. Its checked leaf family covers code, break, continue, leave, and
  terminal statements at fixed target fuel. Loop callbacks now receive
  source-return preservation and reject loop/body/post entries using exact
  activation frames rather than a global generated-label blacklist.
  `Structured.TypedCfgCompilerActive` proves from the existing compiler that
  every emitted block input and regular fallthrough preserves an active
  procedure return token, including sequences, conditionals, switches, loops,
  calls, and allocation-shaped procedure fragments. Observer modules consume
  this checked result invariant rather than accepting generated shape evidence.
  Conditional and statement-list adequacy now reject generated entries only
  at the exact activation frame recovered from CFG input shape; the
  generated-context module checks the corresponding conditional wrapper and
  transports recursive boundaries across same-activation joins.
  The compiler-generated whole-program terminal backward theorem is checked in
  `Structured.ObserverProgramAdequacy`; it constructs the generated context
  internally, selects the first activation-owned program-end-or-halt boundary,
  rules out the compiler's invalid program-end sentinel for terminal target
  runs, and exposes only source evaluation plus the adjacent outcome relation.
  Generic first-boundary execution and residual-fuel lemmas now live in
  `Structured.ObserverFirstReaches`, returning the central adequacy module below
  the 5K-line architecture limit.
- [x] TypedCfg -> Assembly: checked replay safety now lifts through
  instructions, bodies, terminators, blocks, program steps, fuel-indexed CFG
  execution, and whole-run terminal backward adequacy. The checked-artifact
  theorem hides block lookup, entry offset, acceptedness, PC fit, and lowering.
- [x] Assembly -> bytecode: exact block simulation and terminal target-run
  inversion are checked.
- [ ] End-to-end: `ClosedResourceCorrect` remains an unproved proposition
  until every unchecked adjacent boundary above is composed. Its current
  exact-machine-state result relation is intentionally under correction:
  resource replay determines all `gas()`/`msize()` observations, while the
  final relation must erase remaining gas and relate memory modulo checked
  compiler allocation. Scratch compilation additionally needs a source
  memory-noninterference premise; replay alone cannot justify arbitrary
  source/frame aliasing.

The first exact Lean statement is now
`Yul.EndToEnd.ClosedResourceCorrect`. It quantifies over a checked
no-external-effects resource artifact, a related Yul/EVM initial state, and a
concrete terminal target run. Its conclusion constructs a fuel-hidden exact
Yul replay that consumes the full target transcript and satisfies the concrete
terminal result relation. `Yul.EndToEnd.ClosedArtifact` packages the accepted
source, successful compilation, and checked no-call/create boundary.

Roadmap:

- [x] Preserve effect state on Yul failures, halts, and reverts.
- [x] Make replay state transcript-indexed and define checked exact
  consumption for every source result.
- [x] Define a concrete Yul/EVM world, machine, variable-store, and replay
  relation, parameterized only by the unavoidable Yul-code/bytecode relation.
- [x] Add generic effect-carrying Functions semantics and verify that resource
  observations survive function-local store setup and caller-store restoration.
- [x] Add fuel-hiding exact source termination and explicit target terminal-run
  predicates. Regular program-end completion still needs a separate artifact
  boundary because the generated CFG currently uses an invalid end terminator.
- [x] State the first theorem for a checked no-external-effects fragment,
  including concrete initial-state and terminal-result relations.
- [ ] Freeze the open external call/create request-response protocol for the
  later unrestricted theorem.
- [ ] Prove observer-aware Yul-to-Functions lowering for every accepted Yul
  expression, statement, function, control outcome, and primitive family.
  Generic observer primitives, resource expressions, and `let` declarations
  for both `gas()` and `msize()` are checked.
- [ ] Prove allocation-driven Functions-to-Locals/Expressions preservation
  under the same observation protocol. Compiler-derived function entry,
  parameter/return preludes, body activation invariants, argument evaluation,
  and generic stack-or-scratch multi-return target assignment are checked.
  Real scratch-frame acquire/release now preserve suspended caller spills,
  observer/world state, allocator readiness, and exact activation ownership.
  Source-facing selected calls now compose real argument evaluation, either
  regular or `leave` callee bodies, return reattachment, target assignment, and
  optional scratch-frame release. The generic mutual statement/block
  dispatcher, whole-program lift, and matching backward theorem remain.
- [x] Lift observer-aware semantics through Structured-to-TypedCfg using the
  existing outcome-indexed path proof.
- [x] Complete the pass-owned Structured code/terminal typing invariant that
  tracks source-visible stack capacity above compiler-owned return-token
  slots. Generated call/procedure fragments still need the indexed backward
  replay theorem, but no public generated-code premise is required by the
  invariant.
- [x] Prove exact observer-aware Assembly-step/assembled-target-block
  equivalence, including target `runN`, oracle remainder, errors, and the
  two-instruction jump encodings.
- [x] Lift the exact Assembly block theorem to arbitrary terminal target runs
  by proving that completed source steps remain at source-instruction
  boundaries and recursively decomposing target fuel.
- [x] Specialize the shared parameterized TypedCfg effect interpreter and prove
  exact observer-aware lowering for every typed instruction and complete block
  body, including zero-byte bindings, stack shuffles, and unwind.
- [x] Prove observer-aware lowering for every TypedCfg terminator, including
  generated return-dispatch tests, selected cleanup/jump, unknown-token
  invalidation, and missing-token stack failure; compose this through complete
  blocks and accepted resolved program steps.
- [x] Strengthen compiled TypedCfg steps to positive target fuel and prove
  one-step backward classification against a concrete terminal Assembly run:
  every continuing step consumes a strict target-fuel prefix, while a halt
  agrees exactly on terminal result and transcript.
- [x] Prove whole-run TypedCfg-to-Assembly terminal backward adequacy and a
  checked-artifact entry theorem with no generated block, label, certificate,
  or emitted-code premise.
- [ ] Prove backward adequacy from target bytecode runs through Assembly,
  TypedCfg, Structured, allocation-lowered Locals, Functions, and imported Yul.
- [ ] Compose the unconditional public Yul-to-bytecode theorem without replay,
  layout, call, or generated-code certificate premises.
- [ ] Cover repeated observations, branches, switch, loops, internal calls,
  halt, revert, stack fallback, and representative real contracts.
- [ ] Run full build, proof-hole, axiom, architecture, importer, and
  real-contract gates.

## Current Checkpoint

Implemented in this migration:

- stable public root and a separate proof-bearing verification aggregate;
- composable compiler passes, checked artifacts, and backend policy;
- one shared checked-artifact target projection and success inversion theorem
  used by Objects, Public, Yul, and Solidity wrappers;
- generic effectful Locals semantics used by observer expression replay;
- shared outcome-indexed simulation contracts;
- canonical allocation-plan vocabulary and well-formedness checker;
- scoped `ProgramPlan` allocation with unique main/function/lexical scope
  identities and per-scope well-formedness;
- a public planner/lowerer boundary where plans carry Functions source plus
  canonical allocation, never an already emitted Expressions program;
- one generic allocation lowerer, with an executable `LoweredFrom` certificate
  proving that the selected plan was consumed by the successful public route;
- one canonical mixed-allocation planner and shared Functions-to-Locals
  lowerer for all source-derived stack/scratch mixtures, including conditional
  scratch-frame procedure ABI, mixed parameters/returns/call targets, and
  allocation-witnessed TypedCfg output;
- an executable source-compatibility contract at the allocation boundary:
  successful lowering proves the plan is well formed, reconstructs exactly
  from the source recipe and inferred mixed placement, and is recorded in the
  public `LoweredFrom` certificate;
- lowering strategy is now derived from the accepted allocation plan and
  returned with the emitted Expressions program; backend policy validates that
  result instead of selecting a separate emitter or asserting metadata;
- a code-free scratch-frame `Allocation.Planner` that computes exact
  per-function/main slot bindings and frame size before emission, paired with a
  shared-interface lowerer that emits once and rejects allocation drift;
- explicit TypedCfg block outputs, unwind, fallthrough, return dispatch,
  caller-frame rows, typing, lowering, and generated certificates;
- entry-directed TypedCfg block ordering, explicit return-dispatch case labels,
  emitted-label uniqueness, checked Assembly acceptedness/PC bounds, and a
  proved per-instruction lowering theorem against fetched Assembly execution;
- an error-preserving Assembly execution-outcome contract with checked
  TypedCfg simulation for every instruction, return-dispatch path, complete
  block execution, and whole-program block stepping;
- certified whole-program stepping that constructs emitted block fragments,
  PC-fit prefixes, target resolution, internal-label resolution, and exact
  entry byte offsets from successful TypedCfg or AllocatedTypedCfg compilation;
- an `AllocatedTypedCfg` checked pass that pairs scoped allocation with the
  generated CFG and makes both allocation and CFG certificates mandatory
  successful-artifact metadata;
- a hidden-witness public artifact simulation relation that composes successful
  public compilation, allocated TypedCfg stepping, emitted-label resolution,
  and final Assembly target execution; its source-facing form now also owns the
  hidden allocation-lowered Structured program, complete source-to-CFG outcome
  path, canonical entry label, and the checked Assembly entry execution;
- a direct proof-carrying Structured-to-TypedCfg compiler with branch, switch,
  loop, break, nonzero-arity internal-call, resource-observer, and external-call
  smokes;
- an independent fuel-indexed TypedCfg multi-block interpreter whose residual
  jump boundary composes with source continuations;
- certified ambient-fragment containment derived from final CFG label
  uniqueness and generated block membership, so source theorems do not expose
  caller-supplied lookup evidence;
- compositional regular-execution certificates carrying both compiler
  fallthrough shape and finite CFG execution, with checked append and
  statement-list composition;
- an outcome-indexed fragment certificate that retains compiler fallthrough
  metadata exactly for regular source outcomes, with checked empty and
  nonempty statement-list composition across every control mode;
- checked mutual Structured-to-TypedCfg statement/block preservation through
  every source constructor and every regular or abrupt outcome, including
  arbitrary selected switch-body outcomes, complete loop recursion, and
  concrete procedure calls;
- concrete call-entry stack execution, ghost-frame realization, source
  pop/attach restoration, globally unique return-token dispatch lookup, and
  recursive callee preservation across regular, leave, and halt outcomes;
  successful whole-program generation now rejects duplicate return tokens,
  exposes checked direct-or-relabel-adapted procedure-fragment provenance, and
  yields an artifact-facing Structured-to-TypedCfg simulation theorem without
  a call oracle;
- a source-to-CFG state relation that realizes ghost procedure frames as
  concrete return-token/caller-stack suffixes while preserving gas and erasing
  only lowering-owned control counters, with reusable primitive, code,
  condition-pop, and regular-fragment congruence theorems;
- a zero-byte, preservation-proved CFG relabel instruction plus allocation-
  derived inline procedure adapters: calls retain generic row-polymorphic entry
  shapes while canonical parameter locations name the internal body shape and
  subsequent symbolic value flow;
- zero-byte, preservation-proved local-binding instructions emitted at
  declaration and assignment boundaries, so canonical main, function, and
  lexical stack-local identities survive source lowering into TypedCfg;
- an allocated-pass witness gate that rejects every nonempty canonical stack
  layout unless the generated CFG exposes the same symbolic local prefix or an
  exact local-binding instruction;
- a symbolic scratch-frame base plus preservation-proved scratch-binding
  instructions emitted beside real frame loads/stores; scratch loads recover
  canonical local identity, and allocated certification rejects every
  canonical scratch binding absent from the generated CFG;
- dedicated TypedCfg `POP`, `DUP`, and `SWAP` lowering from Structured stack
  operations, preserving symbolic local and scratch-base identities without
  changing emitted bytecode;
- a primitive stack-contract interface independent of the historical
  closed-world proof whitelist, so `gas`, `msize`, and call/create operations
  can be typed without duplicating the CFG compiler;
- a stable public compiler cut over to
  `Expressions -> Structured -> TypedCfg -> Assembly`;
- enforced syntax/semantics/compiler dependency directions;
- layered verification, architecture metrics, and shared Lake dependency cache.

The remaining observer-proof critical path is explicit:

1. [x] Complete the indexed call-entry replay theorem.
2. [x] Complete internal-call/return-dispatch adequacy.
3. [x] Complete the generated-context mutual Structured theorem and
   whole-program backward adequacy.
4. [ ] Lift the checked mutual source-fuel statement/block dispatcher through
   whole Functions programs.
5. [ ] Prove Functions/allocation/Expressions backward adequacy.
6. [ ] Complete the adjacent Yul forward/backward boundary.
7. [ ] Compose `ClosedResourceCorrect` and run the final gates.

The recursive Functions boundary now has checked preservation for leaves,
lexical blocks, both `if` paths, both switch-selection paths, and pass-owned
statement theorems for every `for` outcome. Condition evaluation consumes its
single target result through a reusable activation relation theorem; recursive
loop preservation descends on canonical source fuel and abrupt outcomes skip
compiler cleanup through the
  shared outcome relation. Calls now have canonical effect-semantic
  returned/halted decomposition and a checked allocation-lowering decomposition
  for the argument/frame/call/store/release sequence. Source-facing argument
  safety now follows the canonical `ArgList.eval`, and the complete real
  function prelude artifact is constructed by
  `AllocationObserverContext.FunctionPreludeContext.of_validated_function`
  from the validator and actual Functions/Locals compiler outputs.
  `ActivationCalleeEntryRel` now gives raw parameter entry one
  activation-indexed interface, and the complete stack-only parameter and
  return preludes are checked through the actual compiler output without a
  synthetic frame. The existing scratch prelude proofs remain on the real
  frame-backed path and have checked conversions to the shared entry
  interface. `FunctionPrelude.forward` now composes both phases for either
  compiler-selected activation mode, tracks exact scratch-frame depth, and
  proves the final target stack length equals the compiler body layout.
  `lowerExprList`/`exprSeqOfList` path has checked forward preservation and
  deterministic backward classification. Function and Locals compiler owners
  expose exact procedure-entry, prelude, open-body, return-expression, and
  preserving-cleanup components. Canonical source-store lemmas now prove that
  function entry realizes parameter arguments and zero-initialized returns,
  including reversed entry-stack order. The allocation relation can construct
  a stack-local store realization directly from a checked source lookup and
  concrete entry stack, and metadata-only entry markers have checked
  compilation and no-op execution. Generic multi-return call writeback is
  checked for both stack and scratch targets. The validated prelude now yields
  the body `ActivationInvariant`, while `ActivationRuntimeInvariant` names the
  additional allocator-readiness and top-frame-ownership facts required by
  recursive calls. The real acquire sequence preserves every caller-owned
  spill below the next allocator base, and the real release sequence restores
  the caller activation and allocator depth. Functions-owned
  `ScratchFrame.acquire_from_runtime` and `ScratchFrame.release_to_runtime`
  expose those checked transitions without a second compiler or interpreter.
  Canonical expression evaluation now preserves `AllocatorReady` across every
  primitive family, including observer consumption, read-only memory
  expansion, source-owned stores, and byte copies. The checked
  `forwardExprRuntime` / `forwardExprSeqRuntime` interfaces retain the ordinary
  adjacent result relation and thread allocator metadata without duplicating
  semantics. `Frame.AllocatorEffect` protects the active frame during
  expressions, while the pass-owned `Frame.SuspendedEffect` preserves every
  strictly suspended caller frame across statements that may update the
  current activation. Allocator-aware preservation is now checked and
  compositional for expression statements, declarations, assignments, both
  `if` paths, regular block sequencing and scoped cleanup, both
  switch-selection paths, and the first-condition-false loop path. Spill
  writes use the shared owned disjoint-`MSTORE` theorem; condition-result pops
  and lexical cleanup expose machine-neutral effects. Internal-call argument
  evaluation and arbitrary multi-return writeback are also allocator-aware;
  stack targets are machine-neutral and scratch targets use the same owned
  disjoint-store interface. The selected callee body/return artifact and exact Structured
  procedure lookup are now recovered from the real whole-program lowerer.
  Argument evaluation also transports target memory growth, so both stack-only
  and scratch-frame calls construct the compiler-selected callee-entry
  relation after the real call-frame transition. Compiler-selected frame
  membership is now equivalent to the selected callee artifact's activation
  mode. Regular and source-`leave` callee bodies both compose through the real
  Structured return-frame pop, `Frame.resume_after_call`, target assignment,
  and optional frame release using one outcome-indexed writeback theorem.
  `AllocationObserverForward.Compilation` now constructs the shared validated
  allocation/lowering context directly from the real compiler equation.
  `Callee.prepared_regular` and `Callee.prepared_leave` execute the selected
  procedure's real entry markers and parameter/return prelude, invoke the
  recursive body boundary, and compose the complete procedure body for both
  source outcomes under the compiler-selected stack or scratch activation
  mode. `Call.regular_of_selected` now composes the canonical source call,
  real argument lowering, compiler-selected stack-or-scratch entry, one
  recursively supplied selected callee activation, return-frame restoration,
  target writeback, and optional real frame release into the adjacent
  statement runtime invariant. Its body-start premise is ordinary Functions
  semantic data, not compiler-generated evidence.
  `Frame.SuspendedEffect` supplies the protected-prefix transition without a
  caller-memory oracle.
  `ForLoop.RegularRuntimeInvariantForward.of_safe_source_run` now performs the
  guarded source-fuel induction for regular loops, preserving allocator and
  mode-indexed activation effects through condition, body, post, and recursive
  iterations. Guarded body cursors now expose checked runtime results for
  expressions, assignment, declaration, both `if` paths, every selected
  `switch` path, lexical blocks, `break`, `continue`, and `leave`.
  Machine-neutral cleanup supplies the allocator effect for abrupt loop
  control without a second semantics. Shared return-frame availability is now
  threaded through loop iteration, and source loop destinations use
  extensional scope equivalence rather than representation-specific list
  equality. Initializer, post, and body recursive boundaries are checked.
  `Functions.AllocationObserverRecursive` now packages the exact loop heads,
  canonical call inversion, selected-callee recursion, and regular-tail
  composition into one checked source-fuel statement/block theorem across
  every compiler-owned root. The whole-program lift now has a
  compiler-owned decomposition of the distinguished main body, including the
  preserved no-variable source prelude, allocator/frame setup, allocation-
  lowered body, final cleanup, exact main plan, and lexical-scope ownership.
  `BodyCursor.RootArtifact` and `BodyCursor.CoreCursor` provide the shared
  owner-neutral recursive interface for selected functions and `.main`;
  selected functions have a checked compatibility adapter and main constructs
  the same interface directly from the real compiler. Generic head/tail,
  runtime dispatch, selected-call recursion, and final-tail construction are
  checked on that interface. `RecursiveProgramForward` now quantifies over any
  `RootArtifact`, so the same source-fuel induction applies directly to `.main`
  without a synthetic function or vertical observer proof corridor.
  `mainRecursiveForward` now constructs the main allocation artifact, Locals
  compilation split, root, and generic recursive theorem internally from the
  real compiler equation and ordinary program scoping. The immediate remaining
  work is to compose the source prelude and compiler-selected runtime setup
  around that checked main-body theorem. `MainComponents.RuntimeSelection`
  now proves from successful ordinary lowering that the program is either
  stack-only, with no frame-using functions and empty allocator/frame preludes,
  or scratch-backed by the exact concrete configuration consumed by the
  compiler. `Frame.ResourceMode`, `ActivationResourceInvariant`,
  `BodyCursor.ResourceBoundary`, and `MainRoot.resourceBoundary` now expose
  that compiler selection without fabricating allocator state. The recursive
  result tower and `ResourceRecursiveBlockForward` are now generalized over
  this resource index, and the complete scratch recursion lifts into that API.
  The stack-only regular-loop head now composes initializer, guarded loop
  induction, body/post recursion, cleanup, and break/continue destinations
  through the same resource-indexed API. The neutral activation-exit loop
  theorem now also consumes guarded no-external-effects semantics, strict
  recursive fuel, return-frame transport, and exact initializer compiler
  artifacts. The stack-only controlled dispatcher now selects all three
  checked loop outcomes directly from the canonical source run. No-frame
  selected calls now compose all-stack argument preparation, the real selected
  procedure prelude/body/epilogue, caller restoration and writeback, and
  terminal short-circuiting through the same resource-indexed dispatcher. The
  shared stack-only strong induction now dispatches every statement form,
  composes exact regular tails, preserves abrupt outcomes, and recursively
  enters selected no-frame roots through the resource-indexed function-body
  boundary. Main now also has a compiler-selected resource theorem that
  constructs its artifact/root internally and chooses the checked stack-only
  or scratch recursion from the ordinary compilation. The remaining forward
  proof is main source-prelude and target setup/body/cleanup composition,
  followed by matching
  whole-function/whole-program backward adequacy.

The CallAware/LiveLayout/recursive-Yul compatibility corridor, `LayerAudit`,
`StackGuardAudit`, `Legacy`, the direct Structured-to-Assembly compiler, and
its preservation/spill/call-depth cone have been deleted. The retained source
tree is 46,066 Lean lines across 75 modules, down by about 975K lines from the
recorded baseline.

## Baseline Diagnosis

The conceptual source tower is sound:

`Solidity -> Yul -> Objects -> Functions -> Locals -> Expressions ->
Structured -> Assembly`.

The implementation cost comes from missing cross-cutting abstractions:

1. Effects are not part of source interpreter state. Resource observation
   therefore copied the Yul and Locals interpreters.
2. Stack allocation policy is fused with lowering. Live-layout, adaptive spill,
   call-aware spill, and scratch-frame spill therefore became separate
   compilers and proof stacks.
3. Preservation is stated separately for regular, halt, break, continue, and
   leave outcomes.
4. Every layer republishes compiler variants, acceptance predicates, and proof
   wrappers.
5. Backend selection leaks into Objects, Yul, and Solidity.
6. TypedCfg names the intended control/stack invariant but is not yet the
   executable verified lowering path.
7. LayerAudit exposes internal proof structure instead of a stable public API.
8. Each worktree rebuilds a large dependency graph, lengthening every proof
   iteration.

Baseline hotspots:

- `Yul/RecursiveBridgeSupport.lean`: about 360K lines, deleted.
- `Yul/OpenLowering.lean`: about 98K lines, deleted.
- `Yul/Reference.lean`: about 85K lines, deleted.
- `Functions/CallAwareSpill.lean`: about 65K lines, deleted.
- `Yul/ObserverOracle.lean`: formerly about 55K lines, replaced by a roughly
  350-line handler/public-proof module.
- `Functions/LiveLayoutPreservation.lean`: about 50K lines, deleted.
- `LayerAudit.lean`: 613 `abbrev` aliases and 425 `example` pins, deleted.

## Target Architecture

```text
Solidity / imported Yul
          |
          v
Canonical source core
  - named locals and functions
  - structured control
  - typed effect requests/events
  - one source Outcome
          |
          v
Analysis and planning
  - liveness
  - stack/scratch placement
  - call frame and memory-region planning
          |
          v
Allocated TypedCfg
  - explicit block input/output shapes
  - explicit locations
  - typed terminators and continuations
  - generated fragment certificates
          |
          v
Assembly / bytecode
```

Existing layers may remain as compatibility adapters during migration. They are
not permanent independent compiler products unless they introduce a genuine
semantic abstraction.

## Migration Invariants

Every phase must preserve these rules:

- The ordinary verified public route remains available until its replacement is
  checked and connected to the same source semantics.
- Source semantics never imports compiler or preservation modules.
- Syntax modules import only syntax/core dependencies, never aggregate layer
  modules.
- Compiler-generated evidence is produced by checked code or hidden behind a
  checked constructor theorem.
- No public theorem accepts an all-callees, replay, layout, generated-code, or
  continuation proof obligation supplied by the caller.
- Fundamental resource premises may remain explicit: source acceptedness,
  source execution, initial-state relation, fuel/gas bounds, scratch ownership,
  and code-size/no-overflow bounds.
- Each new route has an equivalence or preservation bridge before cutover.
- Once a public route cuts over, the old route is deleted rather than retained
  indefinitely as a second architecture.

## Phase 0: Baseline And Guardrails

Status: complete.

- [x] Inventory modules, imports, line counts, declarations, compiler entry
  points, acceptance predicates, and recent churn.
- [x] Trace the actual public compile path from Solidity/Yul to Assembly.
- [x] Identify gas/msize duplication and stack-too-deep backend proliferation.
- [x] Confirm TypedCfg is currently a scaffold, not a cutover-ready IR.
- [x] Add a script that records per-module Lean build time, peak memory, source
  lines, and imported module count.
- [x] Add architecture checks for forbidden dependency directions.
- [x] Record baseline counts for public compiler variants, `OutcomeRel`
  declarations, and audit aliases.

Authoritative artifacts:

- `scripts/architecture_metrics.sh`
- `proof_artifacts/architecture_baseline.json`
- dependency-direction check in the default verification gate

Exit gate:

- Metrics are reproducible from a clean checkout.
- The migration can show reductions rather than relying on anecdotal size.

## Phase 1: Reusable Effect Semantics

Status: complete.

Goal: adding an effect changes a handler and adjacent simulation lemmas, not the
source interpreter.

- [x] Introduce `Locals.Source.Effectful.StateModel`.
- [x] Introduce effectful primitive and terminal handlers over arbitrary source
  state.
- [x] Factor expression, statement, block, loop, and program interpretation
  over that interface.
- [x] Prove the ordinary Locals source interpreter is definitionally equivalent
  or bisimilar to the identity-state specialization.
- [x] Specialize the generic semantics to resource replay.
- [x] Replace duplicated Locals and imported-Yul replay evaluator definitions
  with aliases/wrappers around generic effect specializations.
- [x] Keep existing resource-observer theorem names as temporary compatibility
  wrappers.
- [x] Move observer classification to one shared primitive-effects table.
- [x] Generalize the interpreter state/handler interface so external
  requests/responses can be added without copying control evaluation.
- [x] Keep Functions and Objects adapters over the shared Locals source
  semantics instead of adding feature-specific evaluators.
- [x] Migrate imported-Yul source replay to `Yul.Source.Effectful`.

Required proofs:

- Ordinary specialization preserves every source result exactly.
- Observer specialization consumes exactly the executed trace prefix.
- Effect-free programs preserve auxiliary state.
- Effect projection commutes with scope restriction and named-store updates.
- Existing gas/msize target replay theorems consume the new generic run.

Cutover gate:

- [x] `Yul/ObserverOracle.lean` defines only an effect handler specialization;
  the architecture guard rejects local Yul control evaluator definitions.

Deletion gate:

- [x] Delete the old replay evaluator bodies and the 55K-line direct-Structured
  observer proof corridor. The retained observer module is about 350 lines.

## Phase 2: Unified Outcome-Indexed Simulation

Status: complete.

Goal: one recursive proof family covers regular and abrupt control outcomes.

- [x] Define a generic source/target `OutcomeRel` indexed by source and target
  modes.
- [x] Package mode-specific cleanup, target shape, and state relation in an
  `OutcomeContract`.
- [x] Provide projections for regular, break, continue, leave, and halt.
- [x] Prove generic append, scoped-block, branch, switch, and loop composition.
  The Structured-to-TypedCfg path now instantiates `OutcomeRel` with concrete
  continuation and halt contracts, proves all `For.Eval` loop constructors,
  composes outcome-indexed statement lists, and closes the mutual statement/
  block proof for every source constructor, including concrete call entry,
  recursive callee outcomes, and selected return dispatch.
- [x] Migrate Locals spill preservation to the generic contract.
- [x] Validate the outcome-indexed package against the former CallAware route,
  then retire that parallel compiler and proof family.
- [x] Migrate observer replay onto the shared semantic contract. The retained
  `ObserverOracle` is a primitive-handler specialization of the common effect
  semantics and reuses the public artifact simulation; the disconnected
  mode-indexed observer proof package was deleted instead of preserved.
- [x] Remove the mode-specific bounded-fuel weakening family. Its only
  consumers were in the disconnected open/gas proof corridor, which is now
  deleted.

Cutover gate:

- `SwitchFallbackStmtPackagesBelow` is represented by one outcome-indexed
  package, not one field per mode.

Deletion gate:

- [x] Delete separate regular/halt/brk/cont recursive statement proof families
  once all public consumers use projections from the generic simulation.

## Phase 3: Uniform Pass And Artifact Contracts

Status: complete.

Goal: every compiler pass has one recognizable checked interface.

Define a conservative Lean interface, not a dependent mega-framework:

```lean
structure Artifact (Target Meta : Type) where
  target : Target
  meta : Meta

structure PassContract (Source Target Meta : Type) where
  compile? : Source -> Option (Artifact Target Meta)
  Accepted : Source -> Prop
  MetaValid : Source -> Artifact Target Meta -> Prop
```

Preservation remains pass-specific but consumes `MetaValid` produced by the
checked compiler.

- [x] Introduce common compiler error/result vocabulary and composable passes.
- [x] Introduce checked artifact records for every retained public pass. The
  historical parallel passes were deleted instead of receiving permanent
  wrappers.
- [x] Separate source well-formedness from backend/resource acceptance at the
  Objects/public boundary.
- [x] Replace all `compileChecked?_eq_some` boilerplate with common projections.
  `Compiler.Artifact.target?`, `target?_of_eq_some`, and
  `target?_eq_some_iff` now own artifact-to-target projection and inversion;
  retained Objects/Public/Yul/Solidity wrappers and frontend recovery theorems
  use that shared API.
- [x] Stop the stable public API from republishing every lower backend variant.
- [x] Introduce one backend policy/configuration value at the public compiler
  entry point.

Exit gate:

- Objects and Yul expose one checked compiler result type regardless of planner.

## Phase 4: Allocation Plan

Status: complete.

Goal: stack-too-deep is an analysis/planning concern, not a separate compiler.

Canonical location vocabulary:

```lean
inductive LocalLocation
  | stack (depth : Nat)
  | scratch (region : Region) (slot : Nat)
```

- [x] Promote the existing Locals stack/scratch layout into a stable allocation
  plan.
- [x] Add explicit scope, liveness interval, call boundary, return-layout, and
  memory-region
  data.
- [x] Define `Plan.WellFormed` once:
  - each live name has exactly one accessible location;
  - stack depths are valid and within EVM DUP/SWAP limits;
  - scratch slots are distinct and inside owned regions;
  - call boundaries preserve required values;
  - return locations match function signatures.
- [x] Introduce a scoped `ProgramPlan` with unique main/function/lexical scope
  IDs and per-scope `Plan.WellFormed`.
- [x] Make one lowerer consume any well-formed, source-compatible plan.
  Bare `ProgramPlan.WellFormed` is intentionally insufficient because a
  structurally valid plan can belong to a different source program. The shared
  lowerer therefore checks `WellFormed` plus an executable `Compatible`
  contract that reconstructs the exact source recipe, inferred mixed
  placement, procedure/stack executability, and submitted allocation.
- [x] Convert every retained allocation policy into a plan generator.
  Ordinary stack, scratch-frame, and explicit mixed allocation use code-free
  `MixedAllocation` planners with source-derived main/function/nested lexical
  bindings and exact frame sizing. Live-layout, adaptive-spill, and CallAware
  policies were removed rather than preserved as parallel compilers.
- [x] Remove post-hoc plan projection from retained public artifacts. The
  scratch-frame route plans first, emits once, and rejects allocation drift;
  `PlannedProgram` has no backend discriminator that can disagree with the
  emitted strategy.
- [x] Prove one lowering contract theorem quantified over every successful
  well-formed, source-compatible plan. The theorem recovers both
  `ProgramPlan.WellFormed` and an exact compatibility witness; public
  `LoweredFrom` artifacts carry that compatibility fact into the compositional
  certificate path.
- [x] Add deterministic planner selection/fallback policy.

Stack-too-deep validation:

- [x] Existing ordinary programs produce stack-only plans.
- [x] Former live-layout success criteria are covered by canonical mixed
  plans: the 17-local, lexical-scope, mixed-call, and multi-return regressions
  all compile through the one lowerer. The retired policy and its distinct
  plan format no longer exist.
- [x] A 17-local public regression rejects inline planning and selects the
  source-derived scratch-frame backend.
- [x] A 17-local mixed regression retains 14 stack locals and spills three
  canonical scratch locations through the shared lowerer.
- [x] Mixed procedure calls cover stack/scratch parameters, return values, and
  multi-result target assignment through the allocated TypedCfg pass.
- [x] Scratch-frame examples use source-derived root and lexical slot plans,
  reject insufficient frame bounds, lower in one emission pass, and reject
  altered allocations.
- [x] Aave and Permit2 smoke programs compile through the same public lowerer.

Cutover gate:

- [x] `Objects.Program.compile?` selects a planner and calls one lowerer; it
  does not chain independent target emitters.

Deletion gate:

- [x] Delete independent compiler frontends after their planners and proof
  obligations have migrated. CallAware and the superseded 6K-line
  ScratchFrameSpill emitter are deleted. The 296-line `AllocationSupport`
  module retains only code-free source allocation recipes and frame-code
  primitives used by the shared lowerer.

## Phase 5: Complete Allocated TypedCfg

Status: complete.

Goal: make stack/control invariants explicit before Assembly.

- [x] Replace anonymous stack positions with symbolic local/temp/return value
  identities suitable for
  joins and calls.
- [x] Give every block explicit input and output shapes.
- [x] Complete `unwind` lowering.
- [x] Complete return-dispatch lowering.
- [x] Represent fallthrough explicitly between labeled blocks.
- [x] Add block/terminator typing for halt and return dispatch.
- [x] Build Structured/SourceCore to TypedCfg rather than emitting labeled
  Assembly directly. Successful generation returns a proof-carrying
  well-typed artifact.
- [x] Replace exact whole-stack procedure entry shapes with a caller-frame-tail
  abstraction.
- [x] Add an `AllocatedTypedCfg.Program` and checked pass pairing scoped
  allocation with TypedCfg, rejecting malformed allocation before CFG
  certification.
- [x] Make CFG value locations and block shapes derive directly from the
  canonical allocation rather than pairing the plan with a separately
  generated CFG. The allocated IR now materializes canonical per-scope stack
  shapes and scratch bindings from `ProgramPlan`, stores them in the
  certificate, and rejects stale layouts. Inline procedure parameters now
  enter the generated CFG through a checked zero-byte relabel adapter whose
  named body shape is derived from the function allocation. Procedure shape
  selection is allocation-derived rather than backend-tag-driven. Declaration
  and assignment lowering now emits zero-byte local-binding instructions, so
  main, function, and nested lexical stack-local identities are retained in
  TypedCfg. The allocated pass rejects canonical nonempty stack layouts that
  are not witnessed by generated block shapes or binding instructions.
  Scratch-frame lowering now emits typed scratch-base/binding instructions
  beside its actual memory accesses, loaded values recover canonical local
  identities, and every canonical scratch binding must be witnessed in the
  generated CFG. Structured stack shuffles lower to dedicated TypedCfg
  instructions so those identities survive `POP`, `DUP`, and `SWAP`.
  Fully generic mixed-plan lowering remains a Phase 4 allocation concern.
- [x] Prove TypedCfg step preservation.
  The complete instruction slice now proves every push, primitive, pop,
  DUP/SWAP depth, and unwind against `Assembly.Source.runN`; block bodies,
  every terminator including return dispatch, and complete entry-label/body/
  terminator block execution are proved against the shared Assembly
  execution-outcome contract. Whole-program stepping constructs and composes
  the selected emitted block fragment.
- [x] Prove TypedCfg-to-Assembly lowering preservation.
- [x] Prove label uniqueness and PC bounds from the certified artifact.
  Successful TypedCfg and AllocatedTypedCfg artifacts now project acceptedness,
  global label uniqueness, exact block-entry PCs, per-fragment PC fit, resolved
  targets, and whole-program step simulation without caller-supplied generated
  layout evidence.

Cutover gate:

- [x] The public compiler reaches Assembly only through TypedCfg. The
  architecture check rejects direct legacy target emitters in
  `Objects/Compiler.lean`.

Deletion gate:

- [x] Delete direct Structured-to-Assembly control emission. Stable
  Expressions/Locals/Functions compile aliases now reach the same certified
  TypedCfg executable route as the public Objects compiler.

## Phase 6: Generated Fragment Certificates

Status: complete.

Goal: generated code properties compose mechanically.

Each emitted fragment records:

- entry and exit stack shape;
- maximum additional stack depth;
- defined and referenced labels;
- possible terminal behavior;
- memory-read/write, resource-observer, and external-call/create effects.

The combined allocated certificate separately carries source-owned scope
layouts and scratch bindings. It deliberately does not claim static
disjointness for arbitrary dynamic EVM addresses.

- [x] Define `FragmentCert`.
- [x] Certify primitive, push, stack movement, cleanup, terminal, and return
  dispatch
  return fragments.
- [x] Prove branch, switch, loop, and procedure composition. The semantic
  proofs compose every generated control form through the uniform outcome
  relation, while associative `ProgramCert.append` composes block, label,
  stack-bound, terminal, and effect summaries. Focused artifacts certify
  generated branch, switch, loop, and procedure-call programs.
- [x] Generate certificates during lowering.
- [x] Make successful public metadata carry mandatory allocation, TypedCfg, and
  combined allocated-CFG certificates, plus an executable source-to-artifact
  `LoweredFrom` relation.
- [x] Derive runner, frame/layout, terminal, call/create, observer, stack-bound,
  and memory-effect projections. `SafetySummary` is the flat compositional CFG
  view; `AllocatedTypedCfg.Certificate.SafetyView` adds witnessed scope layouts
  and scratch ownership; runner safety remains the executable
  `compileCertified?_step_eventually` theorem.

Cutover gate:

- [x] Structured acceptance consumes generated certificates instead of
  rechecking unrelated semantic predicates independently.

## Phase 7: Thin Frontends And Public Spine

Status: complete.

Goal: Yul and Solidity adapt source syntax; they do not host backend proof
corridors.

- [x] Define `EvmCompiler.Public` with stable compile/result/theorem interfaces.
- [x] Reduce Yul lowering to syntax and primitive conversion plus the public
  Objects compiler. Source semantics remain in the separate generic
  `Yul.Source.Effectful` interpreter.
- [x] Move external-operation handling and resource observation onto common
  effect events. Custom source primitive handlers reuse `Yul.Source.Effectful`;
  retained resource replay specializes it in `ObserverOracle`.
- [x] Route Objects through the uniform artifact and backend-policy API.
- [x] Compose successful public compilation with the hidden allocation-lowered
  Structured evaluation, complete TypedCfg outcome path, canonical CFG entry,
  checked Assembly entry-block execution, and executable target trace. The
  public relation deliberately preserves the current gas-erasing backend
  boundary rather than claiming an unsupported flattened multi-block Assembly
  trace.
- [x] Route Solidity through the same public Objects artifact result. Checked
  object images now compile through `Objects.Program.CompileArtifact`, and
  generated Lean modules expose that artifact instead of importing
  `Yul.Preservation` and rebuilding an intermediate Assembly program.
- [x] Replace `LayerAudit` as the default root with a small public import/build
  smoke and delete the historical aliases.
- [x] Thin the Assembly/Structured/Expressions/Locals/Functions/Objects/Yul
  aggregate modules so they no longer import preservation and runtime proof
  corridors by default.
- [x] Move internal regression assertions to focused allocation and TypedCfg
  proof artifacts. Production modules retain only reusable fixture values.

Public theorem modes:

- ordinary compilation and entry simulation;
- resource-observer replay over the same compiled artifact;
- custom source primitive/effect handlers through the shared effect semantics.

The retired open/gas proof corridors are no longer represented as independent
public compiler modes.

Deletion gate:

- [x] Delete obsolete OpenRuntime/NoCallRuntime/RecursiveBridge compatibility
  wrappers and the disconnected OpenExternal/OpenAssembly/OpenGasAware/
  Assembly.GasAware proof corridor.

## Phase 8: Module And Build Architecture

Status: complete.

- [x] Enforce dependency direction:
  `Syntax <- Semantics`, `Syntax <- Compiler`, and
  `Semantics + Compiler <- Preservation`.
- [x] Remove compiler imports from semantics.
- [x] Remove aggregate imports from syntax.
- [x] Split files at stable abstraction boundaries, not arbitrary line counts.
  `Structured/TypedCfgPreservation` is now a 2,690-line core relation/context
  module plus a 4,693-line control-preservation module.
- [x] Set a soft maximum of 5K lines per module and report modules above
  10K.
- [x] Configure a shared dependency package cache keyed by Lean toolchain and
  `lake-manifest.json`, while retaining per-worktree project build output.
- [x] Add layered verification targets: core, effects, allocator, TypedCfg,
  public spine,
  proof artifacts, frontend smokes.
- [x] Add forbidden-import checks. Lean/Lake remains the import-cycle check.

Exit gate:

- A new worktree can run a focused module check without rebuilding Mathlib.
- Editing one planner does not rebuild Yul reference/open-runtime modules.

## Phase 9: Final Cutover And Deletion

- [x] Freeze old public routes. Unused Objects compatibility target emitters
  were removed, the CallAware backends were retired from the stable policy,
  and architecture guards pin both the TypedCfg route and the two-planner
  inline/scratch-frame policy.
- [x] Run output comparisons on representative contracts. The post-cutover
  Permit2 smoke passed 3 SafeCast, 5 NonceBitmap, and 3
  SignatureVerification call comparisons; Aave math and interest runtime
  backend checks also passed.
- [x] Run source grammar and acceptedness audits. The bundled-Python importer,
  schema, and rendering suite passes all 244 tests.
- [x] Run proof-hole and axiom audits for the migrated/public modules and the
  resource-observer proof artifact.
- [x] Cut the default root import and public compiler API to the new stable
  architecture.
- [x] Delete old observer replay interpreters. Imported-Yul resource replay is
  now a primitive-handler specialization of the generic effect semantics.
- [x] Delete parallel allocation compilers. The stable policy contains only
  inline-stack and source-planned scratch-frame allocation.
- [x] Delete direct Structured-to-Assembly control lowering and its closed
  preservation, spill-source, stack-resource, and call-depth proof cone.
- [x] Delete compatibility theorem corridors and stale audit aliases.
- [x] Recompute architecture metrics and compare to baseline. The current
  snapshot records 75 modules, 46,066 source lines, 59 compiler-variant
  declarations, and one outcome-relation declaration, versus 104 modules,
  1,021,199 lines, 145 variants, and 43 outcome relations at baseline.

Completion evidence:

- `lake build` (passing at the current checkpoint)
- focused builds for every migration layer
- `EvmCompiler.Verification`
- resource observer proof artifact
- stack-too-deep/Aave/Permit2 smoke artifacts
- Solidity bridge and bytecode smokes
- no `sorry`, `admit`, or unexpected `sorryAx` in migrated/public modules
- dependency-direction check
- architecture metrics showing one Locals interpreter, one allocation lowerer,
  one TypedCfg-to-Assembly path, and one public compiler spine

Latest verified checkpoint:

- deleted the retired compatibility, observer, direct Structured emitter,
  preservation, spill-source, stack-resource, and call-depth corridors:
  about 934K lines removed from the recorded baseline;
- architecture dependency and retired-module guards: pass;
- stable verification aggregate, including observer, scratch-frame, object
  semantics, public API, public artifact simulation, generic Yul effects, and
  relational Structured-to-TypedCfg code/condition/switch preservation: pass
  (1,156 jobs);
- nonempty switch dispatch now has reusable checked certificates for generated
  test execution, matched-head selection, skipped-head delegation, and both
  empty and nonempty default paths; source `Switch.select` is lifted through
  the generated case chain, and top-level regular switch outcomes compose
  through the scrutinee block and selected/default body path;
- Structured compiler continuations now pair labels with checked TypedCfg
  shapes. `break`, `continue`, and `leave` compilation rejects mismatched
  source stack shapes, and switch/loop joins reject regularly completing
  fragments with incompatible fallthrough shapes. Compiler facts, ordinary
  preservation, observer preservation, and adequacy leaves use the shared
  pass-owned interface;
- Structured-to-TypedCfg preservation now instantiates the shared
  outcome-indexed simulation interface with concrete regular, break, continue,
  leave, and halt contracts. Reusable projections turn related outcomes back
  into CFG paths, and all ten independent `For.Eval` constructors compose
  condition, body, post, break/continue handling, leave/halt propagation, and
  recursive backedges. A canonical `.for_` compiler decomposition and
  compiler-facing theorem now add init regular/leave/halt and exact generated
  fragment containment; loop-specific preservation is complete;
- outcome-indexed compiler fragments now carry a semantic path for every mode
  and fallthrough metadata exactly when the source result is regular. Empty
  and nonempty statement lists compose through this certificate, including
  abrupt head outcomes and the compiler's static no-tail branch;
- the mutual Structured statement/block theorem now covers code, both
  conditional paths, arbitrary switch outcomes, all loop outcomes,
  break/continue/leave, terminal execution, and procedure calls through one
  outcome-indexed certificate;
- generated call entry and return restoration now have checked relational stack
  theorems, global dispatch lookup follows from an executable token-uniqueness
  gate, and recursive procedure lowering exposes one fragment certificate that
  covers both direct and allocation-driven relabel entries. The concrete
  mutual proof recursively preserves selected callees, dispatches regular and
  leave returns, propagates halts with existentially hidden active return
  tokens, and eliminates the temporary `CallCertificate`;
- successful generation and checked artifacts now project a source-facing
  Structured-to-TypedCfg outcome path without exposing compiler results, call
  tables, or generated-context witnesses;
- successful public compilation now composes that path with the exact hidden
  Expressions-to-Structured lowering witness, canonical generated entry label,
  AllocatedTypedCfg certificate, checked Assembly entry execution, and
  executable target trace in
  `compileArtifactWithPolicy?_structuredSimulation`;
- stale-import scan over retained Lean modules: clean;
- allocated TypedCfg layer: pass, including certified whole-program stepping,
  emitted block fragments, label/PC projections, and lowering-invariant
  regressions;
- source-derived inline-allocation and 17-local scratch fallback proof artifact:
  pass;
- `EvmCompiler.Yul.ObserverOracle`: pass;
- public-artifact and resource-observer proof artifacts and axiom prints: pass;
- full `lake build EvmCompiler.Verification`: pass (1,158 jobs);
- retained architecture metrics: 75 modules, 46,066 Lean lines, 59 compiler
  variants, and one outcome relation;
- bundled-Python importer/schema suite: 244 tests pass;
- Permit2 guarded scratch compilation reaches an object image and its
  SignatureVerification call comparison passes after retaining `memoryguard`;
  the diagnostic raw-unresolved route now correctly reports
  `to_yul_contract = none`.
- Aave v3 math and interest fixtures currently expose no `memoryguard`; the
  checked scratch backend therefore rejects them instead of relying on the
  former unproved unrestricted-memory spill assumption.

## Execution Order

The migration critical path is complete. Further work can add compiler
features through the shared effect, allocation, TypedCfg, certificate, and
public-artifact interfaces without restoring a parallel backend or proof
corridor.

## End-to-End Observer Proof

- [x] Derive selected callee preludes and complete procedure-body phases from
  the real Functions allocation and Locals expression compilers.
- [x] Recover the compiled procedure selected by a source function name through
  the real function-list lowerer.
- [x] Compose the selected callee's real entry/prelude and complete procedure
  execution for regular, source-`leave`, and terminal recursive body outcomes.
- [x] Compose the source-facing call statement from argument evaluation,
  compiler-selected callee entry, recursive body execution, outcome-indexed
  return restoration, optional frame release, and caller target assignment.
- [x] Lift statement, block, loop, and call preservation by source fuel without
  a public call oracle. The checked dispatcher now has one fuel-bounded
  recursive open-block interface over real synchronized cursors. Every `for`
  outcome is checked through pass-owned source-fuel theorems, including
  initializer exit, regular completion, exact break/continue handling, and
  body/post leave or halt. Compiler-selected calls now reconstruct the whole
  compilation from the selected artifact, derive the callee's scoped root
  boundary from `Program.Scoped`, and consume a strictly smaller recursive body
  result through the real call prelude. Regular and source-`leave` results run
  the real epilogue, frame release, and caller assignment; terminal results
  prove those generated phases unreachable while preserving the caller-owned
  allocator prefix. `Functions.AllocationObserverRecursive` now owns the
  checked strong induction across every selected function artifact. Its
  downward-closed fuel interface handles lexical recursion, loop components,
  regular tails, and recursive calls; `Frame.FuelSafe` plus the call-owned
  callee-depth bound supplies each nested scratch budget. The main-root
  boundary is now compiler-selected between stack-only and scratch modes. The
  resource-indexed recursive theorem and scratch conversion are checked.
  Stack-only leaves, lexical blocks, and all `if` and `switch` outcomes now
  use the same resource-indexed cursor and controlled-dispatch interfaces.
  Stack-only loop initializer exits now compose through the same recursive
  resource interface and activation-exit transport. Resource-generic loop
  body/post boundaries and regular/abrupt recursive scoped adapters are also
  checked through statement-owned cleanup and canonical control destinations.
  The complete regular stack-only loop head is checked through the neutral
  guarded source-fuel theorem and exact compiler cursors. The matching neutral
  guarded theorem for post-initializer activation exits is checked, including
  strict recursive fuel and return-frame transport. Its stack-only dispatcher
  adapter is also checked: body/post exits are reindexed only after genuine
  activation exits, and the resource lift occurs at the enclosing statement
  boundary. A single controlled-head theorem now selects initializer exit,
  regular completion, or activation exit from the canonical source run. The
  configuration-free caller restoration, all-stack callee prelude and return,
  pure callee phase composition, and caller writeback interfaces are checked.
  Selected no-frame regular and halting calls now reconstruct the ordinary
  compiler artifact, prove frame absence from the compiler-selected
  `frameFunctions`, consume the recursive resource body result, and package
  the outcome in the shared controlled dispatcher. The stack-only recursive
  constructor is now checked over every compiler-owned root using the same
  resource block result, control destinations, exact cursors, and selected
  function-body boundary as scratch recursion. The remaining Functions work
  is whole-program source-prelude/setup/cleanup packaging and matching
  backward adequacy. The recursive main-body theorem already selects its
  resource mode directly from the ordinary compilation and accepts no
  generated artifact premise.
- [ ] Prove the matching backward-adequacy boundary and compose the short Yul
  end-to-end theorem.

## Progress Discipline

- Update this file only when phase status, scope, or gates change.
- Append concrete work, proof results, failed approaches, and metrics to
  `PROGRESS_LOG.md`.
- Create a verified git checkpoint after each phase boundary or meaningful
  theorem/cutover.
- Do not mark a phase complete from grep alone; inspect the current public
  theorem path and run the phase verification gate.
