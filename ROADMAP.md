# Verified EVM Compiler Architecture Migration

Last updated: 2026-06-11 06:41 PDT.

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

- stable public root and a separate proof-bearing verification aggregate;
- composable compiler passes, checked artifacts, and backend policy;
- generic effectful Locals semantics used by observer expression replay;
- shared outcome-indexed simulation contracts;
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
  and final Assembly target execution;
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
- checked Structured-to-TypedCfg semantic preservation for primitive
  instructions, straight-line code, both `if` branches, compiled code
  statements, empty statement lists, break/continue/leave/terminal leaves, and
  the empty/no-default switch path;
- a source-to-CFG state relation that realizes ghost procedure frames as
  concrete return-token/caller-stack suffixes while preserving gas and erasing
  only lowering-owned control counters, with reusable primitive, code,
  condition-pop, and regular-fragment congruence theorems;
- a zero-byte, preservation-proved CFG relabel instruction plus allocation-
  derived inline procedure adapters: calls retain generic row-polymorphic entry
  shapes while canonical parameter locations name the internal body shape and
  subsequent symbolic value flow;
- a primitive stack-contract interface independent of the historical
  closed-world proof whitelist, so `gas`, `msize`, and call/create operations
  can be typed without duplicating the CFG compiler;
- a stable public compiler cut over to
  `Expressions -> Structured -> TypedCfg -> Assembly`;
- enforced syntax/semantics/compiler dependency directions;
- layered verification, architecture metrics, and shared Lake dependency cache.

The remaining critical path is deliberately narrow and explicit:

1. Extend canonical location binding from inline procedure parameters to
   main/lexical local transitions and the remaining generic-plan lowering
   boundary.
2. Finish the mutual statement/block lift, extend the checked source-to-CFG
   semantic package through procedure calls/return dispatch, then compose the
   result into the public artifact theorem.
3. Finish the generic outcome migration and replace remaining mode-specific
   proof families with projections and composition theorems.

The CallAware/LiveLayout/recursive-Yul compatibility corridor, `LayerAudit`,
`StackGuardAudit`, `Legacy`, the direct Structured-to-Assembly compiler, and
its preservation/spill/call-depth cone have been deleted. The retained source
tree is 91,889 Lean lines across 79 modules, down by about 929K lines from the
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

Status: in progress.

Goal: one recursive proof family covers regular and abrupt control outcomes.

- [x] Define a generic source/target `OutcomeRel` indexed by source and target
  modes.
- [x] Package mode-specific cleanup, target shape, and state relation in an
  `OutcomeContract`.
- [x] Provide projections for regular, break, continue, leave, and halt.
- [ ] Prove generic append, scoped-block, branch, switch, and loop composition.
  The Structured-to-TypedCfg path now instantiates `OutcomeRel` with concrete
  continuation and halt contracts, proves all `For.Eval` loop constructors,
  and composes outcome-indexed statement lists; leaf statements, the mutual
  statement/block lift, and calls remain.
- [x] Migrate Locals spill preservation to the generic contract.
- [x] Validate the outcome-indexed package against the former CallAware route,
  then retire that parallel compiler and proof family.
- [ ] Migrate observer replay preservation fully onto `OutcomeContract`. Its
  source evaluator and public target theorem now use the shared effect and
  public artifact surfaces, but the mode-indexed proof package has not cut over.
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
- [x] Introduce checked artifact records for every retained public pass. The
  historical parallel passes were deleted instead of receiving permanent
  wrappers.
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
- [x] Convert every retained allocation policy into a plan generator.
  Ordinary stack and scratch-frame allocation have code-free shared-interface
  planners with source-derived main/function/nested lexical bindings;
  scratch-frame also computes exact frame sizing. Live-layout, adaptive-spill,
  and CallAware policies were removed rather than preserved as parallel
  compilers.
- [x] Remove post-hoc plan projection from retained public artifacts. The
  scratch-frame route plans first, emits once, and rejects allocation drift.
- [ ] Prove one lowering theorem quantified over a well-formed plan.
  Exact executable plan-consumption theorems exist for each public backend,
  but semantic preservation for arbitrary well-formed plans does not.
- [x] Add deterministic planner selection/fallback policy.

Stack-too-deep validation:

- [x] Existing ordinary programs produce stack-only plans.
- [ ] Former live-layout successes produce equivalent canonical plans.
- [x] A 17-local public regression rejects inline planning and selects the
  source-derived scratch-frame backend.
- [x] Scratch-frame examples use source-derived root and lexical slot plans,
  reject insufficient frame bounds, lower in one emission pass, and reject
  altered allocations.
- [x] Aave and Permit2 smoke programs compile through the same public lowerer.

Cutover gate:

- [x] `Objects.Program.compile?` selects a planner and calls one lowerer; it
  does not chain independent target emitters.

Deletion gate:

- Delete independent compiler frontends after their planners and proof
  obligations have migrated. CallAware is deleted; ScratchFrameSpill now owns
  the retained scratch planner/lowerer implementation rather than a public
  compiler entry point.

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
  generated CFG. The allocated IR now materializes canonical per-scope stack
  shapes and scratch bindings from `ProgramPlan`, stores them in the
  certificate, and rejects stale layouts. Inline procedure parameters now
  enter the generated CFG through a checked zero-byte relabel adapter whose
  named body shape is derived from the function allocation; main/lexical
  local transitions and fully generic arbitrary-plan lowering remain.
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
- [x] Route Solidity through the same public Objects artifact result. Checked
  object images now compile through `Objects.Program.CompileArtifact`, and
  generated Lean modules expose that artifact instead of importing
  `Yul.Preservation` and rebuilding an intermediate Assembly program.
- [x] Replace `LayerAudit` as the default root with a small public import/build
  smoke and delete the historical aliases.
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
  snapshot records 79 modules, 88,771 source lines, 65 compiler-variant
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
- stale-import scan over retained Lean modules: clean;
- allocated TypedCfg layer: pass, including certified whole-program stepping,
  emitted block fragments, label/PC projections, and lowering-invariant
  regressions;
- source-derived inline-allocation and 17-local scratch fallback proof artifact:
  pass;
- `EvmCompiler.Yul.ObserverOracle`: pass;
- public-artifact and resource-observer proof artifacts and axiom prints: pass;
- full `lake build`: pass (1,137 jobs);
- retained architecture metrics: 79 modules and 91,535 Lean lines;
- bundled-Python importer/schema suite: 244 tests pass;
- Aave v3 math and interest public backend smokes: pass;
- Permit2 public bytecode/call-comparison smoke: pass, including 3 SafeCast,
  5 NonceBitmap, and 3 SignatureVerification call comparisons. The
  SignatureVerification runtime now reports only the independent
  `solc_validation` frontend round-trip limitation; no retired compiler is
  present in the backend diagnostic path.

## Execution Order

The remaining critical path is:

1. Make canonical allocation locations determine generated CFG values and block
   shapes instead of certifying a separately generated CFG.
2. Finish the mutual statement/block source-to-CFG lift, concrete call/return
   dispatch, and the public source-to-artifact theorem; then discharge the
   remaining certificate safety projections.
3. Finish outcome-indexed projections/composition, then rerun the final
   verification, frontend, benchmark, and architecture gates.

## Progress Discipline

- Update this file only when phase status, scope, or gates change.
- Append concrete work, proof results, failed approaches, and metrics to
  `PROGRESS_LOG.md`.
- Create a verified git checkpoint after each phase boundary or meaningful
  theorem/cutover.
- Do not mark a phase complete from grep alone; inspect the current public
  theorem path and run the phase verification gate.
