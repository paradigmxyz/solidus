# Verified EVM Compiler Architecture Migration

Last updated: 2026-06-10 14:27 PDT.

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

## Current Checkpoint

Implemented in this migration:

- stable public root and explicit legacy compatibility import;
- composable compiler passes, checked artifacts, and backend policy;
- generic effectful Locals semantics used by observer expression replay;
- shared outcome-indexed simulation and CallAware statement package;
- canonical allocation-plan vocabulary and well-formedness checker;
- scoped `ProgramPlan` allocation with unique main/function/lexical scope
  identities and per-scope well-formedness;
- a public planner/lowerer boundary where plans carry Functions source plus
  canonical allocation, never an already emitted Expressions program;
- one generic allocation lowerer, with an executable `LoweredFrom` certificate
  proving that the selected plan was consumed by the successful public route;
- a code-free scratch-frame `Allocation.Planner` that computes exact
  per-function/main slot bindings and frame size before emission, paired with a
  shared-interface lowerer that emits once and rejects allocation drift;
- explicit TypedCfg block outputs, unwind, fallthrough, return dispatch,
  caller-frame rows, typing, lowering, and generated certificates;
- an `AllocatedTypedCfg` checked pass that pairs scoped allocation with the
  generated CFG and makes both allocation and CFG certificates mandatory
  successful-artifact metadata;
- a direct proof-carrying Structured-to-TypedCfg compiler with branch, switch,
  loop, break, nonzero-arity internal-call, resource-observer, and external-call
  smokes;
- a primitive stack-contract interface independent of the historical
  closed-world proof whitelist, so `gas`, `msize`, and call/create operations
  can be typed without duplicating the CFG compiler;
- a stable public compiler cut over to
  `Expressions -> Structured -> TypedCfg -> Assembly`;
- enforced syntax/semantics/compiler dependency directions;
- layered verification, architecture metrics, and shared Lake dependency cache.

The remaining critical path is deliberately narrow and explicit:

1. Convert the remaining legacy allocation backends into true plan generators.
   Scratch-frame planning is now code-free with exact frame sizing and
   main/function/nested lexical bindings. Call-aware planning still runs the
   legacy emitter once to discover its layout and then re-emits while checking
   exact agreement.
2. Make canonical per-local locations directly drive Expressions/TypedCfg
   generation and CFG shapes across main and function scopes.
3. Prove source-to-CFG and CFG-to-Assembly semantic preservation, plus label
   uniqueness and PC bounds from generated certificates.
4. Finish the generic effects/outcomes migration, then delete duplicate replay
   control evaluators, parallel backend compilers, direct Assembly lowering,
   and legacy theorem corridors.

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

- `Yul/RecursiveBridgeSupport.lean`: about 360K lines.
- `Yul/OpenLowering.lean`: about 98K lines.
- `Yul/Reference.lean`: about 85K lines.
- `Functions/CallAwareSpill.lean`: about 65K lines.
- `Yul/ObserverOracle.lean`: about 55K lines.
- `Functions/LiveLayoutPreservation.lean`: about 50K lines.
- `LayerAudit.lean`: 613 `abbrev` aliases and 425 `example` pins.

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

Status: in progress.

Goal: adding an effect changes a handler and adjacent simulation lemmas, not the
source interpreter.

- [x] Introduce `Locals.Source.Effectful.StateModel`.
- [x] Introduce effectful primitive and terminal handlers over arbitrary source
  state.
- [x] Factor expression, statement, block, loop, and program interpretation
  over that interface.
- [ ] Prove the ordinary Locals source interpreter is definitionally equivalent
  or bisimilar to the identity-state specialization.
- [x] Specialize the generic semantics to resource replay.
- [ ] Replace the duplicated Locals `SourceReplay` evaluator definitions with
  aliases/wrappers around the specialization. Expression and expression-list
  evaluation have cut over; control evaluation remains a compatibility facade.
- [x] Keep existing resource-observer theorem names as temporary compatibility
  wrappers.
- [ ] Move observer classification to one shared primitive-effects table.
- [x] Generalize the interpreter state/handler interface so external
  requests/responses can be added without copying control evaluation.
  without copying the interpreter again.
- [ ] Migrate Functions and Objects source adapters to pass the effect handler
  parametrically.
- [ ] Migrate Yul source replay to the same event carrier or prove its imported
  interpreter bridge once at the frontend boundary.

Required proofs:

- Ordinary specialization preserves every source result exactly.
- Observer specialization consumes exactly the executed trace prefix.
- Effect-free programs preserve auxiliary state.
- Effect projection commutes with scope restriction and named-store updates.
- Existing gas/msize target replay theorems consume the new generic run.

Cutover gate:

- `Yul/ObserverOracle.lean` no longer defines a second Locals expression,
  statement, block, loop, or program interpreter.

Deletion gate:

- Delete the old `SourceReplay` evaluator bodies and their duplicate structural
  lemmas after all consumers use the generic specialization.

## Phase 2: Unified Outcome-Indexed Simulation

Status: in progress.

Goal: one recursive proof family covers regular and abrupt control outcomes.

- [x] Define a generic source/target `OutcomeRel` indexed by source and target
  modes.
- [x] Package mode-specific cleanup, target shape, and state relation in an
  `OutcomeContract`.
- [ ] Provide projections for regular, break, continue, leave, and halt.
- [ ] Prove generic append, scoped-block, branch, switch, and loop composition.
- [x] Migrate Locals spill preservation to the generic contract.
- [x] Migrate CallAwareSpill statement packages to one outcome-indexed `sound`
  field with compatibility projections.
- [ ] Migrate observer replay preservation. Its effectful source outcome now
  shares the generic effect representation, but target simulation packages have
  not cut over.
- [ ] Replace mode-specific bounded-fuel weakening lemmas with one theorem.

Cutover gate:

- `SwitchFallbackStmtPackagesBelow` is represented by one outcome-indexed
  package, not one field per mode.

Deletion gate:

- Delete separate regular/halt/brk/cont recursive statement proof families once
  all public consumers use projections from the generic simulation.

## Phase 3: Uniform Pass And Artifact Contracts

Status: in progress.

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
- [ ] Introduce checked artifact records for every legacy pass. Objects and
  TypedCfg are migrated; lower legacy passes still expose historical APIs.
- [x] Separate source well-formedness from backend/resource acceptance at the
  Objects/public boundary.
- [ ] Replace all `compileChecked?_eq_some` boilerplate with common projections.
- [x] Stop the stable public API from republishing every lower backend variant.
- [x] Introduce one backend policy/configuration value at the public compiler
  entry point.

Exit gate:

- Objects and Yul expose one checked compiler result type regardless of planner.

## Phase 4: Allocation Plan

Status: in progress.

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
- [ ] Make one lowerer consume any well-formed plan.
  The public generic lowerer now consumes a checked scoped plan, and successful
  artifacts carry an executable `LoweredFrom` certificate. It still accepts
  backend-shaped plan subsets rather than lowering arbitrary canonical
  per-local placements.
- [ ] Convert ordinary layout, live layout, adaptive spill, call-aware spill,
  and scratch-frame allocation into plan generators.
  Scratch-frame allocation now has a code-free shared-interface planner with
  exact frame sizing and main/function/nested lexical bindings. The
  ordinary/live/call-aware families remain.
- [ ] Remove post-hoc plan projection from CallAware/ScratchFrame artifacts:
  planners must produce the canonical plan before any code is emitted.
  Call-aware planning currently emits once to discover a plan and re-emits
  through the checked lowerer. Scratch-frame no longer uses post-hoc projection
  or its historical probe/recompile cycle on the public path.
- [ ] Prove one lowering theorem quantified over a well-formed plan.
  Exact executable plan-consumption theorems exist for each public backend,
  but semantic preservation for arbitrary well-formed plans does not.
- [x] Add deterministic planner selection/fallback policy.

Stack-too-deep validation:

- [x] Existing ordinary programs produce stack-only plans.
- [ ] Former live-layout successes produce equivalent canonical plans.
- [x] Call-aware examples use mixed stack/scratch plans.
- [x] Scratch-frame examples use source-derived root and lexical slot plans,
  reject insufficient frame bounds, lower in one emission pass, and reject
  altered allocations.
- [x] Aave and Permit2 smoke programs compile through the same public lowerer.

Cutover gate:

- [x] `Objects.Program.compile?` selects a planner and calls one lowerer; it
  does not chain independent target emitters.

Deletion gate:

- Delete independent CallAwareSpill and ScratchFrameSpill compiler frontends
  after their planners and proof obligations have migrated.

## Phase 5: Complete Allocated TypedCfg

Status: in progress.

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
- [ ] Make CFG value locations and block shapes derive directly from the
  canonical allocation rather than pairing the plan with a separately
  generated CFG.
- [ ] Prove TypedCfg step preservation.
- [ ] Prove TypedCfg-to-Assembly lowering preservation.
- [ ] Prove label uniqueness and PC bounds from the artifact certificate.

Cutover gate:

- [x] The public compiler reaches Assembly only through TypedCfg. The
  architecture check rejects direct legacy target emitters in
  `Objects/Compiler.lean`.

Deletion gate:

- Delete direct Structured-to-Assembly control emission after equivalence and
  end-to-end preservation pass.

## Phase 6: Generated Fragment Certificates

Goal: generated code properties compose mechanically.

Each emitted fragment records:

- entry and exit stack shape;
- possible outcomes/terminators;
- maximum additional stack depth;
- labels and PC span;
- memory regions read and written;
- effect requests/observations;
- external-call/create behavior;
- gas/resource summary where applicable.

- [x] Define `FragmentCert`.
- [x] Certify primitive, push, stack movement, cleanup, terminal, and return
  dispatch
  return fragments.
- [ ] Prove branch, switch, loop, and procedure composition. Sequential
  certificate composition is implemented.
- [x] Generate certificates during lowering.
- [x] Make successful public metadata carry mandatory allocation, TypedCfg, and
  combined allocated-CFG certificates, plus an executable source-to-artifact
  `LoweredFrom` relation.
- [ ] Derive runner safety, frame safety, terminal safety, no-call/create,
  observer safety, stack bounds, and memory disjointness as projections.

Cutover gate:

- Structured acceptance consumes generated certificates instead of rechecking
  unrelated semantic predicates independently.

## Phase 7: Thin Frontends And Public Spine

Goal: Yul and Solidity adapt source syntax; they do not host backend proof
corridors.

- [x] Define `EvmCompiler.Public` with stable compile/result/theorem interfaces.
- [ ] Reduce Yul lowering to syntax conversion plus one imported-semantics
  bridge.
- [ ] Move open external execution and resource observation onto common effect
  events.
- [x] Route Objects through the uniform artifact and backend-policy API.
- [x] Route Solidity through the same public Objects artifact result.
- [x] Replace `LayerAudit` as the default root with a small public import/build
  smoke; the historical aliases remain behind `EvmCompiler.Legacy`.
- [x] Thin the Assembly/Structured/Expressions/Locals/Functions/Objects/Yul
  aggregate modules so they no longer import preservation and runtime proof
  corridors by default.
- [ ] Move internal regression examples to focused proof artifacts.

Public theorem modes:

- closed deterministic execution;
- open external call/create execution;
- resource-observing execution;
- gas/resource-bounded execution.

All modes return projections of one compiled artifact and one semantic result
relation.

Deletion gate:

- Delete obsolete OpenRuntime/NoCallRuntime/RecursiveBridge compatibility
  wrappers once no public theorem imports them.

## Phase 8: Module And Build Architecture

- [x] Enforce dependency direction:
  `Syntax <- Semantics`, `Syntax <- Compiler`, and
  `Semantics + Compiler <- Preservation`.
- [x] Remove compiler imports from semantics.
- [x] Remove aggregate imports from syntax.
- [ ] Split files at stable abstraction boundaries, not arbitrary line counts.
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
  were removed and an architecture guard pins the TypedCfg route.
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
- [ ] Delete old replay interpreters.
- [ ] Delete parallel allocation compilers.
- [ ] Delete direct Structured-to-Assembly control lowering.
- [ ] Delete compatibility theorem corridors and stale audit aliases.
- [x] Recompute architecture metrics and compare to baseline. The initial
  cutover snapshot is `proof_artifacts/architecture_current.json`; it records
  the expected temporary increase from new abstractions before legacy deletion.

Completion evidence:

- `lake build` (passing at the current checkpoint)
- focused builds for every migration layer
- public LayerAudit replacement
- resource observer proof artifact
- call-family external-world proof artifacts
- stack-too-deep/Aave/Permit2 smoke artifacts
- Solidity bridge and bytecode smokes
- no `sorry`, `admit`, or unexpected `sorryAx` in migrated/public modules
- dependency-direction check
- architecture metrics showing one Locals interpreter, one allocation lowerer,
  one TypedCfg-to-Assembly path, and one public compiler spine

Latest verified checkpoint:

- stable/default build: pass (1,153 jobs);
- allocator layer after code-free scratch-frame cutover: pass (1,146 jobs);
- allocated TypedCfg focused layer: pass (1,115 jobs);
- `EvmCompiler.Yul.ObserverOracle`: pass;
- `EvmCompiler.Legacy`: pass;
- resource-observer proof artifact and axiom print: pass;
- bundled-Python importer/schema suite: 244 tests pass;
- Aave v3 math and interest public backend smokes: pass;
- Permit2 public bytecode/call-comparison smoke: pass, including 3 SafeCast,
  5 NonceBitmap, and 3 SignatureVerification call comparisons. The existing
  SignatureVerification diagnostic still reports `live_layout_to_locals` for
  one legacy backend check, while the overall public smoke passes.

## Execution Order

The remaining critical path is:

1. Replace emitter-derived CallAware plans with pure scoped plan generators,
   migrate ordinary/live allocation families, and make canonical locations
   drive lowering and CFG shapes.
2. Prove direct Structured-to-TypedCfg and TypedCfg-to-Assembly preservation,
   including label/PC certificate projections.
3. Finish the generic effect/outcome migrations and remove replay evaluators.
4. Delete the legacy emitters, parallel backend compilers, and theorem
   corridors after their replacement gates pass.

## Progress Discipline

- Update this file only when phase status, scope, or gates change.
- Append concrete work, proof results, failed approaches, and metrics to
  `PROGRESS_LOG.md`.
- Create a verified git checkpoint after each phase boundary or meaningful
  theorem/cutover.
- Do not mark a phase complete from grep alone; inspect the current public
  theorem path and run the phase verification gate.
