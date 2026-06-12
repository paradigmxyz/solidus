# Verified EVM Compiler Architecture Migration

Last updated: 2026-06-11 20:48 PDT.

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
  exist, but observer-aware forward/backward theorems remain.
- [ ] Locals/Expressions -> Structured: generic effect semantics exists;
  complete allocation-sensitive observer theorem remains.
- [ ] Structured -> TypedCfg: complete observer-aware forward preservation is
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
  `Structured.ObserverLoopAdequacy` module. Internal calls/return dispatch, the
  mutual statement/block theorem, and whole-program backward adequacy remain.
  Shared outcome artifacts and terminal leaves were extracted into sibling
  modules. Source-frame typing now distinguishes token-free caller frames,
  which retain a stack lower bound, from active procedure frames, whose
  source-visible stack length is exact above the compiler-owned return token.
  The invariant is preserved by accepted instructions, observer handlers,
  straight-line code, condition pops, statement sequencing, switches, and
  loops, and is carried by the outcome-indexed adequacy artifact. The
  frame-invariant proofs live in `Structured.ObserverFrameInvariant`; both
  central observer modules remain below the 5K soft limit.
- [x] TypedCfg -> Assembly: checked replay safety now lifts through
  instructions, bodies, terminators, blocks, program steps, fuel-indexed CFG
  execution, and whole-run terminal backward adequacy. The checked-artifact
  theorem hides block lookup, entry offset, acceptedness, PC fit, and lowering.
- [x] Assembly -> bytecode: exact block simulation and terminal target-run
  inversion are checked.
- [ ] End-to-end: `ClosedResourceCorrect` remains an unproved proposition
  until every unchecked adjacent boundary above is composed.

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
  under the same observation protocol.
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

1. Complete the indexed call-entry replay theorem.
2. Complete internal-call/return-dispatch adequacy and the generated-context
   mutual Structured theorem.
3. Prove the Functions/allocation/Expressions and Yul adjacent backward
   boundaries, compose `ClosedResourceCorrect`, and run the final gates.

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
- Aave v3 math and interest public backend smokes: pass;
- Permit2 public bytecode/call-comparison smoke: pass, including 3 SafeCast,
  5 NonceBitmap, and 3 SignatureVerification call comparisons. The
  SignatureVerification runtime now reports only the independent
  `solc_validation` frontend round-trip limitation; no retired compiler is
  present in the backend diagnostic path.

## Execution Order

The migration critical path is complete. Further work can add compiler
features through the shared effect, allocation, TypedCfg, certificate, and
public-artifact interfaces without restoring a parallel backend or proof
corridor.

## Progress Discipline

- Update this file only when phase status, scope, or gates change.
- Append concrete work, proof results, failed approaches, and metrics to
  `PROGRESS_LOG.md`.
- Create a verified git checkpoint after each phase boundary or meaningful
  theorem/cutover.
- Do not mark a phase complete from grep alone; inspect the current public
  theorem path and run the phase verification gate.
