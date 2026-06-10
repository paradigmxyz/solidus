# Request: hostile critique of an architecture migration plan (Lean 4 verified compiler)

**Mode: critique/refute.** Do NOT solve anything. Attack the plan below. Specifically:
1. What is FALSE in it (claims about what Lean 4 can or can't do, about proof scaling, about what collapses to what)?
2. What will NOT ELABORATE in Lean 4 as sketched (universes, structure fields holding polymorphic functions, termination/fuel interaction with trace threading, simp behavior through an opaque handler parameter, `FueledSem` with a field `run : {H : Type} → Handler H → ...`)?
3. What does CompCert (and CakeML/Vellvm/interaction-trees) experience say this gets WRONG? Prior reviews of this project critiqued proof organization but never the semantic representation; this review must attack the representation: the unified `Event` type, the handler-parameterized fuel interpreters, the big-step fueled refinement structure, trace-equality (not trace-relation) across refinements, response-script quantification replacing a free-monad-style suspension carrier.
4. Where are the plan's cost estimates and "collapses to one lemma" claims most likely wrong?
5. What would you do differently, concretely, given the constraints below?

Useful failure modes: a specific Lean elaboration counterexample; a named CompCert/CakeML lesson the plan violates; a demonstration that one of the "retired" premise packages cannot actually be retired; a feature on the inventory that does NOT fit the event model.

## Hard constraints (do not relitigate)
- Lean 4, no Mathlib-style monad-transformer stacks on the proof path; interpreters stay first-order and fuel-based (`Nat` fuel, `Except` results). No interaction-tree library port (none mature in Lean 4).
- ~955k lines of existing Lean; proofs must be absorbable incrementally (build-alongside, not retrofit).
- Another constraint from the project: the per-shape wrapper zoo (near-identical lemmas per statement-shape × argument-shape × feature-flag) is the failure mode this plan exists to kill.

## Ground truth from the repository (verified today)

The current CALL/CREATE suspension carrier (EvmCompiler/Yul/OpenExternal.lean:1503):
```lean
inductive OpenResult (ε : Type u) (α : Type v) : Type (max u v) where
  | done : Except ε α → OpenResult ε α
  | call : OpenCall (OpenResult ε α) → OpenResult ε α
  | create : OpenCreate (OpenResult ε α) → OpenResult ε α
-- OpenCall pairs a CallSite with `resume : CallResponse → OpenResult ε α`
```

The gas/msize observation types (EvmCompiler/Assembly/Observer.lean:13):
```lean
inductive ResourceObserver where | gas | msize
structure ResourceObservation where kind : ResourceObserver; value : Word
abbrev ResourceTrace := List ResourceObservation
```

Current interpreter idiom (Assembly target path, Assembly/Semantics.lean:138):
```lean
def runN (target : TargetProgram) : Nat → EVMState → Except EVMException EVMState
def runNResult (target : TargetProgram) : Nat → EVMState → Except EVMException StepResult
-- StepResult := running EVMState | halted Halt
-- 18 hand-written WithObservers/WithOracle clones of these exist across 3 paths,
-- with 26+ hand-proved equivalence theorems tying them to the base interpreters.
```

The Yul source semantics is BIG-STEP structural recursion over the AST with Nat fuel
(Reference.run : Nat → Program → State → Except Exception State, Reference.lean:4670).
There is no small-step source semantics. The Functions layer has a 15+-function mutual
block with Prod.Lex well-founded termination measures (Functions/Semantics.lean:82).

Scale facts: RecursiveBridgeSupport.lean is 360,235 lines / 3,745 theorems and contains a
39-rung ladder of `compile_whole_program_result_sound_of_*` top-theorem variants (first
rung has 22 hypotheses). ~40 premise-package structures (*TopAssumptions/*Ready/*Checked)
exist in the Yul layer. The gas/msize feature cost ~35k lines because the trace parameter
changed every signature and the whole Structured-layer proof stack plus source semantics
were re-derived under oracle threading.

Known Lean pain incidents in this repo (PROGRESS_LOG): a loop-theorem rollback because
putting the loop theorem into the mutual statement/block theorem family broke
termination/elaboration, and a generic lambda hid the fuel decrease from the termination
checker; CompilerPreservation.block/stmt needs maxHeartbeats/maxRecDepth wrappers; an
overly broad runOpen no-overwrite theorem was abandoned for heavy elaboration.

---

# THE PLAN UNDER CRITIQUE FOLLOWS

# Event-Spine Migration Plan for the Verified EVM Compiler Tower

**Date:** 2026-06-09
**Status:** Plan only — no Lean code was refactored in producing this document.
**Author context:** follows the 2026-06-09 architectural audit; all file/line pointers below
were re-verified against the tree on 2026-06-09 (they drift daily — re-verify before acting).

---

## 0. Executive summary and verified baseline

The tower's feature-addition cost is multiplicative because *observation* and *environment
interaction* were grown as three incompatible mechanisms — `OpenResult` continuation
suspension for CALL/CREATE, `ResourceTrace` recording/replay for gas()/msize(), and bare
premise packages for everything else — and because every soundness statement is indexed by
a concrete interpreter and a concrete premise set. This plan replaces that with:

1. **One `Event` type and one `Trace`** (a `List Event`) shared by every layer.
2. **Handler-parameterized interpreters**: each layer's fuel-based big-step interpreter is
   written once, taking a small first-order handler record; plain / recording / replaying
   semantics are instances, and the per-variant equivalence zoo collapses to one
   handler-simulation congruence lemma per layer.
3. **One generic fueled-refinement structure** with transitive composition, replacing the
   bespoke per-corridor soundness statements and the top-theorem ladder.
4. **One canonical top theorem** quantified over external-response scripts, whose premises
   are only fundamental inputs (acceptedness, compile success, fuel, initial-state
   relation). Feature restrictions (no-call, no-observers, …) become *corollaries* derived
   from program predicates — not parallel corridors and not interpreter flags.

**Amendments to the audit's recommendation** (justified in §2.4 and §7): (a) the generic
simulation is *big-step fueled refinement*, not a CompCert small-step diagram with
stuttering measure — the Yul source semantics is structural recursion over the AST with no
step machine, so a per-step diagram cannot be stated at the Yul→Assembly boundary without
first inventing a small-step source semantics (a large cost with no consumer); small-step
diagrams remain available *inside* the Assembly layer where step machines exist. (b)
Own-code-image reads (CODESIZE/CODECOPY of the executing code) are **not** events; they are
deterministic functions of the pinned code image in the state relation. (c) `FeatureConfig`
is **not** an interpreter parameter — flags on the interpreter would recreate the corridor
multiplication inside the spine. There is one interpreter with the full event surface;
restriction is by theorem-level program predicates.

**Verified baseline numbers (2026-06-09):**

| Fact | Value | Where |
|---|---|---|
| Lean lines under `EvmCompiler/` | 955,705 | `find … wc -l` |
| `Yul/RecursiveBridgeSupport.lean` | 360,235 lines, 3,745 theorems | — |
| Top-theorem ladder `compile_whole_program_result_sound_of_*` | **39** rungs (audit said 38; it grew) | lines 348388–360124 |
| Hypotheses on first ladder rung | 22 | line 348388 |
| `Yul/Reference.lean` | 84,709 lines, 1,837 theorems (audit's 72k/1438 has grown) | — |
| Induction core `RecursiveSourceBridgeWhenUpToAt` | confirmed | `Reference.lean:19934` |
| `TopAssumptions`/`Ready`/`Checked` declarations, Yul layer alone | 40 (audit's ~64 also counted `*Facts`/`*Assumptions` packs) | `rg` census |
| Concrete interpreter functions across layers | ~85 (base ~35; observer/oracle variants 26; open/no-call/code-image variants the rest) | Explore sweep |
| `Assembly/Observer.lean` | 18 `WithObservers`/`WithOracle` interpreter variants over 3 paths, 26+ equivalence theorems | lines 133–1140 |
| gas()/msize() feature cost on current architecture | ~35k lines (`Yul/ObserverOracle.lean` 33,535 + `Assembly/Observer.lean` 2,286) | — |
| Other mega-files | `OpenLowering.lean` 98,007; `OpenRuntime.lean` 28,598; `NoCallRuntime.lean` 24,486; `GasAware.lean` 23,155; `OpenGasAware.lean` 14,883 | — |

---

## 1. Complete feature inventory

For each lane: **(a)** what it becomes on the spine (Event constructors / config / premise),
**(b)** which premise packages it retires, **(c)** what is genuinely *not* an event and
where it lives instead.

### 1.1 CALL / CALLCODE / DELEGATECALL / STATICCALL suspension
- **Today:** `OpenResult` (`Yul/OpenExternal.lean:1503`) — a continuation-carrying
  suspension carrier (`.call : OpenCall (OpenResult ε α)` with
  `resume : CallResponse → OpenResult ε α`), threaded through `OpenRuntime.lean` (28.6k),
  `OpenLowering.lean` (98k), `OpenGasAware.lean` (14.9k).
- **(a) Becomes:** `Event.call (req : CallRequest) (resp : CallResponse)`. The request part
  is emitted deterministically (computed from machine state); the response part is
  **oracle-resolved**: supplied by the handler, which in the canonical instance reads it
  from a universally-quantified response script. The suspension/continuation representation
  disappears — the interpreter consumes the response inline and keeps running, exactly as
  the oracle-replay interpreters already do for gas/msize. The existing
  `BoundaryKind` unification from the external-boundary refactor (ROADMAP.md, adopted
  2026-06-08) is the precedent: this plan completes that direction.
- **(b) Retires:** `RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsTopAssumptions`
  and the `CanonicalEntry` sibling (`OpenRuntime.lean`), `OpenXBoundaryFamilyResponseGas*ReadyFor`,
  `OpenCallActualPostGasBudgetFacts`, the `OpenResultRel*` relation family, and ultimately
  the `OpenResult` carrier itself (demoted to private compat during Phase 5).
- **(c) Not an event:** the *return-window* layout (`ReturnWindow`, `CallSite` operand
  plumbing) is compiler-strategy material; it stays in the lowering proof. The "all
  responses satisfy X" predicates (`OpenTrace.BoundaryResponsesSatisfy`) become ordinary
  propositions about the script, stated once.

### 1.2 CREATE / CREATE2
- **Today:** a parallel constructor of the same suspension carrier (`OpenResult.create`,
  `OpenCreate`, `CreateRequest/CreateResponse` in `OpenExternal.lean`), with its own
  premise packs (`OpenCreateActualPostGasBudgetFacts`).
- **(a) Becomes:** `Event.create (req : CreateRequest) (resp : CreateResponse)` — same
  request-emitted / response-scripted split as CALL. No separate carrier, no separate
  corridor; the CALL and CREATE proofs share the one external-event lemma parameterized by
  boundary kind (the `BoundaryKind` classifier survives as the shared request shape).
- **(b) Retires:** the create-side halves of the packages in §1.1.
- **(c) Not an event:** deploy-code construction and the init-code/runtime-code split are
  object-layer compilation concerns (§1.7).

### 1.3 RETURNDATACOPY and return-data buffer replay
- **Today:** static bounds predicates (`targetProgramNoReturnDataCopy`,
  `CurrentNoCallReturnDataCopyBoundsReady` at `OpenGasAware.lean:9023`,
  `StackGuardedReturnDataCopyBounds*` in `StackGuardAudit.lean:1670+`) plus
  buffer-preservation reasoning after call/create responses; 202 old no-RDC declarations
  were already demoted to private bricks by the boundary refactor.
- **(a) Becomes:** **not an event.** The return-data buffer is machine state, populated
  deterministically by the *response* component of the most recent `Event.call`/`Event.create`.
  RETURNDATACOPY is then a deterministic state operation. Bounds-validity moves into the
  acceptance/WF predicate (a static check on the program), discharged by the existing
  checked decision procedures.
- **(b) Retires:** the `*ReturnDataCopyBoundsReady` premise packs as *public* premises —
  they become fields of acceptance discharged by checked constructors.
- **(c) Lives in:** state semantics + acceptance; the buffer-content lemma ("buffer after
  event = resp.returnData") is one lemma on the spine interpreter.

### 1.4 gas() / msize() observer oracle
- **Today:** `ResourceObserver`/`ResourceObservation`/`ResourceTrace`
  (`Assembly/Observer.lean:13–23`), 18 `WithObservers`/`WithOracle` interpreter variants
  across the three Assembly paths, 26+ hand-proved equivalence theorems, and
  `Yul/ObserverOracle.lean` (33.5k lines) re-deriving the Structured-layer stack and source
  semantics under trace threading. Design rationale in
  `proof_artifacts/resource_observer_oracle_approach_question.md`: the *conditional oracle*
  — no claim that gas/msize are deterministic at source level; instead "if source replay
  consumes exactly the dry-run-recorded trace, all parties agree."
- **(a) Becomes:** `Event.observe (kind : ResourceObserver) (value : Word)`. At the
  **Assembly/target layer** the value is emitted deterministically (computed from
  `EVMState` by the recording handler instance). At **source layers** the value is
  oracle-resolved (script handler). The conditional-oracle insight is preserved *verbatim*
  as the composition: target run with recording handler produces trace τ; source run with
  script handler fed τ agrees — this is exactly the spine's round-trip theorem (§2.3)
  instantiated at `kind ∈ {gas, msize}`.
- **(b) Retires:** all 18 `With*` interpreter variants and their 26+ equivalence theorems
  (replaced by one congruence lemma per path); `OraclePrimitiveSemantics`,
  `PrimitiveAssemblyOracleSound`, and the SourceReplay duplicate interpreter family in
  `ObserverOracle.lean` (`runWithOracle`, `runStateWithOracle`, `SourceReplay.run*`).
- **(c) Not an event:** nothing here; this lane is the purest event lane and is the
  template for the others.

### 1.5 Code image (`runWithCodeImage`, CODESIZE/CODECOPY)
- **Today:** `runResultWithCodeImage` (`Reference.lean:4683`), `Program.runWithCodeImage`
  (`Yul/Semantics.lean:67`), `RecursiveBridgeObjectCodeImageTopAssumptions`
  (`ObjectRuntime.lean:219`), `RecursiveBridgeInitialCodeImageRel` (`NoCallRuntime.lean:58`),
  premise `shared.executionEnv.codeBytes = codeImage`.
- **(a) Becomes:** **not an event** (amendment to the audit, which listed code-image reads
  as a candidate constructor). Own-code reads are deterministic functions of the pinned
  image, which is part of the initial-state relation (`StateRelConfig`); making them events
  adds trace noise and forces every code-image-free theorem to reason about observe-erasure.
  The `WithCodeImage` interpreter variants collapse because the image is just a component
  of the (related) initial states.
- **(b) Retires:** `RecursiveBridgeObjectCodeImageTopAssumptions` and the
  bare/suffix/image trio of object premise packs — they become three choices of initial
  state, three one-line corollaries of one theorem.
- **(c) Foreign-code reads** (EXTCODECOPY) are different — they query the unmodeled world
  and *are* events (§1.11).

### 1.6 No-CALL corridor (`NoCallRuntime`, `NoCallCreate`)
- **Today:** a 24.5k-line parallel corridor (`RecursiveBridgeTopNoCallAssumptions`,
  `RecursiveBridgeActualXTrace*Facts` ×5, `compileCheckedAssemblyTarget?_noCallCreate`)
  proving programs that don't use CALL/CREATE sound without external machinery.
- **(a) Becomes:** a **corollary by vacuity**. The canonical top theorem quantifies over
  response scripts; the premise "every emitted call event's response satisfies …" is
  vacuous when the program emits no call/create events. Statically:
  `programEventKinds p ∩ {.call, .create} = ∅` (decided by the existing checked
  `usesCallCreate` scan) ⟹ the run is script-independent (one parametricity corollary of
  the congruence lemma: a program that emits no external events produces the same result
  under any handler).
- **(b) Retires:** the entire corridor as a *parallel proof route*;
  `compileCheckedAssemblyTarget?_noCallCreate` survives as the checked static classifier
  feeding the corollary.
- **(c) Not an event:** nothing; this lane is pure premise-trivialiization.

### 1.7 Object / contract boundaries (Objects, ObjectRuntime, deploy/runtime split)
- **Today:** `Objects.Object/Program` with `Source.run`/`Runtime.run`
  (`Objects/SourceSemantics.lean`, `Objects/Semantics.lean`), three top-assumption variants
  (`RecursiveBridgeObject{,CodeImage,Suffix}TopAssumptions`, `ObjectRuntime.lean:84/219/357`).
- **(a) Becomes:** **structure, not events.** Deploy and runtime executions are two
  applications of the canonical top theorem with different initial states/code images,
  composed by trace concatenation (`Trace` is a list; the deploy trace prepends to the
  runtime trace in the whole-contract statement). A constructor-time CREATE of another
  contract is an `Event.create` like any other.
- **(b) Retires:** the three object premise-pack variants → one theorem + three
  initial-state corollaries.
- **(c) Lives in:** the Objects layer keeps its syntax/lowering/preservation; only its
  *soundness statement* re-targets the spine refinement.

### 1.8 Stack spill and scratch-frame memory
- **Today:** `Functions/CallAwareSpill.lean`, `ScratchFrameSpill.lean` (5.6k),
  `ScratchFrameMemory.lean` (`FrameStoreRel` at :1644), `LiveLayout.lean`,
  `LiveLayoutPreservation.lean`.
- **(a) Becomes:** **not an event and not config — untouched.** Spill is a
  compilation-strategy proof: it certifies that the Functions→Locals lowering's use of
  scratch memory preserves source semantics. It is invisible at the observation level (the
  scratch region is erased by the state relation). It lives exactly where it lives now, as
  internal machinery of the Functions-layer preservation proof. The spine *helps* it only
  indirectly: its preservation lemmas re-state over the handler-parameterized interpreter
  once (mechanical), instead of once per observation variant (which is what the gas/msize
  lane is currently being forced to do).
- **(b) Retires:** nothing.
- **(c)** The one interaction to watch: scratch-memory writes can change `msize`. The
  existing `SameData`/scratch-readiness premise in the oracle design already handles this;
  on the spine it becomes a hypothesis of the Functions-layer refinement instance, stated
  once.

### 1.9 Gas accounting / sufficient-gas premises
- **Today:** `Assembly/GasAware.lean` (23.2k; `GasExecRel` at :732, `XStepTrace` at :6469),
  `Yul/OpenGasAware.lean` (14.9k), `*GasBudget*` packs in `OpenRuntime.lean`.
- **(a) Becomes:** a **fundamental resource premise**, not an event. "Initial gas ≥ bound"
  is in the allowed premise class (like fuel). Gas *consumption* stays inside the machine
  state; gas *observation* (the gas() opcode) is `Event.observe .gas`. The gas-erased
  equivalence `GasExecRel` becomes part of the Assembly-layer refinement's state relation
  choices.
- **(b) Retires:** the `OpenX*GasBudget*`/`GasAdmissible*ReadyFor` packs as public
  premises; the budget arithmetic lemmas in `GasAware.lean` are reusable leaves.
- **(c) Lives in:** the Assembly refinement instance and the acceptance-level gas-bound
  computation.

### 1.10 Stack-bound / resource certificates (`StackResource`, `StackGuardAudit`)
- **Today:** static `Effect`/`Summary` bound tables (`Structured/StackResource.lean:13/49`),
  `OpenStackResource.lean`, checked by `StackGuardAudit.lean` (4k).
- **(a) Becomes:** **not an event.** Stack bounds are compiler-output properties discharged
  by checked constructors (already the design). Under the spine they appear only inside
  the Assembly refinement instance's proof, never as a public premise — consistent with
  the final acceptance criterion "no compiler-generated certificate as public premise."
- **(b) Retires:** any remaining public `StackGuarded*`/bound-table premises (audit shows
  these are already mostly internal).
- **(c) Lives in:** where it is.

### 1.11 Roadmap state queries: EXTCODESIZE / EXTCODECOPY / EXTCODEHASH / BALANCE / SELFBALANCE
- **Today:** not implemented; ROADMAP.md (lines ~7376–7378, ~10418) plans them as state
  queries with `StateRelConfig.balanceRel`-style contracts, explicitly *not* open-boundary
  suspension.
- **(a) Becomes:** `Event.query (q : StateQuery) (answer : Word)` for word-valued queries
  (BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODEHASH) and
  `Event.queryBytes (q : BytesQuery) (answer : ByteArray)` for EXTCODECOPY. Responses are
  **oracle-resolved at every layer** (the tower does not model the external world); the
  emitted request is deterministic. This family is the chosen proof-of-concept lane (§3,
  Phase 3) — it is new work that must be done anyway, exercises the full
  request/response/script machinery, and has the simplest state effect (push one word).
- **(b) Retires:** nothing yet (greenfield); *prevents* a fourth observation mechanism.
- **(c)** SELFBALANCE after a value-bearing CALL is world-dependent — treating it as a
  query event (not a state read) is semantically honest and avoids modeling balance flow.

### 1.12 Block/chain environment reads (BLOCKHASH, TIMESTAMP, NUMBER, CHAINID, …)
- **Today:** checked nullary bridge constructors reading `ExecutionEnv` (ROADMAP ~7495).
- **(a) Becomes:** **not events** — they are deterministic reads of the pinned execution
  environment, already covered by the state relation. (BLOCKHASH with a non-recent block
  argument could be made a query event later if the env model doesn't carry the hash map;
  decide when implementing — the spine supports either without restructuring.)

### 1.13 LOG0–LOG4
- **Today:** LOG0/LOG1 checked with shared log-effect preservation (ROADMAP ~10429).
- **(a) Becomes:** `Event.logEmit (entry : LogEntry)` — a **deterministically emitted,
  response-free** event (the environment doesn't answer; the world observes). This is the
  one event kind with no oracle component; on replay it is checked for equality, not
  consumed for a value. (Today logs live in machine substate; moving them to the trace
  makes "the compiled program emits the same logs" part of the one observation-equality
  conclusion instead of a separate substate-preservation premise. The substate
  representation can be kept too; the event is then derived.)

### 1.14 Storage (SLOAD/SSTORE/TLOAD/TSTORE)
- **Today:** modeled state with `StateRelConfig.sloadRel` contracts, writable-context
  premise for SSTORE (ROADMAP ~10418–10427).
- **(a) Becomes:** **not events** — storage is modeled machine state related by the state
  relation; this is working and representation-correct. No change.

### 1.15 Solidity frontend
- **Today:** syntax + JSON bridge only (`Solidity/Frontend.lean`, 397 lines;
  `BridgeJson.lean`); no semantics, no soundness theorem.
- **(a) Becomes:** out of spine scope. When Solidity semantics are added they sit above
  Objects and inherit the same `Trace`. The spine makes that future theorem statable as
  one more refinement composed onto the chain.

### 1.16 Summary table

| Lane | Spine representation | Determinism on emit | Resolution on replay |
|---|---|---|---|
| CALL family | `Event.call req resp` | req deterministic | resp from script (all layers) |
| CREATE/CREATE2 | `Event.create req resp` | req deterministic | resp from script (all layers) |
| gas()/msize() | `Event.observe kind v` | v deterministic at target | v from script at source layers |
| EXTCODE*/BALANCE | `Event.query q a` / `Event.queryBytes q a` | q deterministic | a from script (all layers) |
| LOG0–4 | `Event.logEmit e` | fully deterministic | equality-checked, never consumed |
| RETURNDATACOPY | state (buffer set by call/create resp) + WF bounds | — | — |
| Own code image | `StateRelConfig` field / initial-state relation | — | — |
| Block env reads | state relation (pinned env) | — | — |
| Storage | state relation | — | — |
| No-call corridor | corollary by vacuity over script | — | — |
| Object/deploy split | two theorem applications + trace append | — | — |
| Spill/scratch frames | Functions-layer lowering proof (unchanged) | — | — |
| Gas budget | fundamental premise (allowed class) | — | — |
| Stack bounds | checked constructor inside Assembly instance | — | — |

---

## 2. Core Lean interfaces (candidate signatures)

These are design sketches — they need not elaborate as written, but they are specific
enough to falsify. Names live under a new top-level `EvmCompiler/Spine/` directory.
Conventions deliberately match current idiom: first-order, fuel-`Nat` structural
recursion, `Except` results, accumulator-style traces (the style `Assembly/Observer.lean`
already uses).

### 2.1 Events and traces (`Spine/Event.lean`)

```lean
namespace EvmCompiler.Spine

/-- One observable interaction with the environment. Request data is computed by the
    machine; response data is supplied by the handler (canonically, a script). -/
inductive Event where
  | call       (req : OpenExternal.CallRequest)   (resp : OpenExternal.CallResponse)
  | create     (req : OpenExternal.CreateRequest) (resp : OpenExternal.CreateResponse)
  | query      (q : StateQuery)  (answer : Word)        -- BALANCE, EXTCODESIZE, EXTCODEHASH, SELFBALANCE
  | queryBytes (q : BytesQuery)  (answer : ByteArray)   -- EXTCODECOPY
  | observe    (kind : Assembly.ResourceObserver) (value : Word)   -- gas, msize
  | logEmit    (entry : LogEntry)
  deriving BEq, Repr   -- BEq, not DecidableEq: ByteArray fields; upgrade if needed

abbrev Trace := List Event
-- Monoid structure and append lemmas are List's own (++, append_assoc, append_nil).
-- The spine-specific lemma set is about *interpreters*, stated once each in §2.2:
--   run-append (fuel splitting), trace-prefix monotonicity, emitted-kinds inventory:
def Trace.kinds : Trace → List EventKind
def Program.eventKinds : Program → Finset EventKind   -- static over-approximation, checked
```

`StateQuery`/`BytesQuery` are small flat inductives (`| balance (a : Word) | extCodeSize
(a : Word) | …`). New observables = new constructors here + one emit site per interpreter
+ zero new interpreters. That is the entire point.

### 2.2 Handlers and the parameterized interpreter (`Spine/Handler.lean`, per-layer files)

```lean
/-- Environment hook. H is handler-private state (e.g. the unconsumed script).
    Returning none = environment refusal → interpreter raises a designated error,
    mirroring today's oracle-mismatch behavior. -/
structure Handler (H : Type) where
  observe    : Assembly.ResourceObserver → EVMState → H → Option (Word × H)
  call       : OpenExternal.CallRequest  → H → Option (OpenExternal.CallResponse × H)
  create     : OpenExternal.CreateRequest → H → Option (OpenExternal.CreateResponse × H)
  query      : StateQuery → H → Option (Word × H)
  queryBytes : BytesQuery → H → Option (ByteArray × H)
```

Three canonical instances (each ~20 lines, written once globally):

```lean
/-- Target-side recording: observers computed from machine state; external interaction
    still script-fed (the target machine cannot answer CALL either). -/
def recordingHandler (script : Trace) : Handler Trace   -- observe from state, call/… from script
/-- Pure replay: every hook pops the matching event from the script. -/
def scriptHandler : Handler Trace
/-- Closed handler: refuses all environment interaction (call/query = none),
    observers from state. Programs with no external event kinds run identically
    under this and any other handler (no-call corollary, §1.6). -/
def closedHandler : Handler Unit
```

The parameterized interpreter, Assembly Target path (today:
`Target.runNResult : TargetProgram → Nat → EVMState → Except EVMException StepResult`,
`Assembly/Semantics.lean:144`, plus 6 hand-written observer/oracle clones in
`Observer.lean`):

```lean
def Target.runNResultE (h : Handler H) (target : TargetProgram) :
    Nat → EVMState → H → Except EVMException (StepResult × Trace × H)
  | 0,        s, hs => .ok (.running s, [], hs)
  | fuel + 1, s, hs => do
      let (r, τ₁, hs₁) ← stepResultE h target s hs
      match r with
      | .running s' => do
          let (r', τ₂, hs₂) ← Target.runNResultE h target fuel s' hs₁
          .ok (r', τ₁ ++ τ₂, hs₂)
      | .halted halt => .ok (.halted halt, τ₁, hs₁)
```

Yul source semantics (today `Reference.run : Nat → Program → State → Except Exception
State`, `Reference.lean:4670`, big-step structural over the AST):

```lean
def Reference.runE (h : Handler H) :
    Nat → Program → State → H → Except Exception (Result × Trace × H)
-- same recursion structure as Reference.run; primitive evaluation calls h.observe /
-- h.call / h.query at exactly the sites where the current code branches into the
-- OpenResult / oracle special cases.
```

**Compatibility (this kills the 35k-line re-derivation problem):** the existing
interpreters are *not* redefined. Per layer, one theorem links them:

```lean
theorem Target.runNResult_eq_runE_closed (target) (fuel) (s) :
    Target.runNResultE closedHandler target fuel s () =
      (Target.runNResult target fuel s).map (fun r => (r, pureTrace …, ()))
```

so the existing 3,745-theorem corpus about concrete interpreters remains consumable: any
fact about `runNResult` transfers to `runNResultE closedHandler` by rewriting, and new
features are proved against `runE` only.

**The one congruence lemma per layer** (replaces the 26+ Observer equivalences and every
future "WithX agrees with base" family):

```lean
/-- Handler simulation lifts to run equality. R relates the private states of two
    handlers; if every hook answers equally under R, runs agree and emit equal traces. -/
theorem Target.runE_congr {H₁ H₂} (R : H₁ → H₂ → Prop)
    (h₁ : Handler H₁) (h₂ : Handler H₂)
    (hooks : HandlerSim R h₁ h₂)            -- 5 fields, one per hook
    (target fuel s) {hs₁ hs₂} (hR : R hs₁ hs₂) :
    RelRun R (Target.runNResultE h₁ target fuel s hs₁)
             (Target.runNResultE h₂ target fuel s hs₂)
```

and **the round-trip theorem** (the generalized conditional-oracle insight, §1.4):

```lean
/-- Recording then replaying its own trace reproduces the run. -/
theorem Target.runE_record_replay (target fuel s script) :
    Target.runNResultE (recordingHandler …) target fuel s script = .ok (r, τ, rest) →
    Target.runNResultE scriptHandler target fuel s (τ ++ rest') = .ok (r, τ, rest')
```

Both are proved by the same induction as the interpreter, once per layer (~6 layers).
Today's `runNResultWithOracle_of_withObservers` (`Observer.lean:496`) and its 25 siblings
are instances.

### 2.3 The generic refinement structure (`Spine/Refinement.lean`)

Amendment (§0): big-step fueled refinement, not small-step diagram. A "semantics" is:

```lean
structure FueledSem where
  State  : Type
  Result : Type
  Err    : Type
  run    : {H : Type} → Handler H → Nat → State → H → Except Err (Result × Trace × H)
```

(One value of this per (layer, program): e.g. `yulSem cfg p`, `asmSem target`.) Refinement:

```lean
structure Refinement (Hi Lo : FueledSem) where
  rel       : Hi.State → Lo.State → Prop
  resultRel : Hi.Result → Lo.Result → Prop
  sound     : ∀ {H} (h : Handler H) fuel s t hs r τ hs',
      rel s t →
      Hi.run h fuel s hs = .ok (r, τ, hs') →
      ∃ fuel' r', Lo.run h fuel' t hs = .ok (r', τ, hs') ∧ resultRel r r'
```

Key choices: **the trace is equal, not related** (representation erasure happens in
`rel`/`resultRel`, never in observations — same discipline as the current
`SameData`-modulo-`eraseGas` design, which lives inside `rel`); **fuel is existential**
(matches every current theorem shape; a monotone `fuelMap` can be added as a derived
convenience but is not part of the interface); **the handler is universally quantified
through the refinement** — this is what makes one proof serve plain/recording/replay
simultaneously.

```lean
def Refinement.comp (ab : Refinement A B) (bc : Refinement B C) : Refinement A C :=
  { rel := fun a c => ∃ b, ab.rel a b ∧ bc.rel b c
    resultRel := …, sound := …  /- 15-line transitivity proof, proved ONCE -/ }

/-- Behavior preservation: terminal corollary unfolding a composed refinement at the
    concrete endpoints. -/
theorem Refinement.behavior (r : Refinement Hi Lo) … : <the ∃-shape from sound>
```

Stuttering: fuel-existential big-step refinement absorbs stuttering trivially (fuel'
free). If a future need for genuine small-step simulation arises inside Assembly
(e.g. peephole passes), a separate `StepSim` structure with measure can be added *locally*
there; it is not on the cross-layer spine.

### 2.4 The canonical top theorem (`Spine/Top.lean`)

```lean
/-- Everything the user must supply. NO compiler-generated certificates: no layout
    witnesses, replay witnesses, call-preservation oracles, label tables. -/
structure TopInputs (cfg : Reference.StateRelConfig) where
  program  : Yul.Program
  accepted : Reference.Accepted program                    -- source acceptedness (incl. static
                                                            -- bounds: RDC windows, stack, names)
  target   : Assembly.TargetProgram
  compiled : compileCheckedAssemblyTarget? program = some target
  src₀     : Reference.State
  tgt₀     : EVMState
  initRel  : Reference.SharedStateRel cfg src₀ tgt₀         -- incl. code-image pinning, gas bound

theorem compile_whole_program_sound (cfg) (inp : TopInputs cfg)
    {H} (h : Handler H) (fuel : Nat) (hs : H) {r τ hs'}
    (hrun : (yulSem cfg inp.program).run h fuel inp.src₀ hs = .ok (r, τ, hs')) :
    ∃ fuel' r',
      (asmSem inp.target).run h fuel' inp.tgt₀ hs = .ok (r', τ, hs') ∧
      Reference.ResultRel cfg r r' := by
  exact ((refinementOfCompile cfg inp).behavior …)
```

where `refinementOfCompile : TopInputs cfg → Refinement (yulSem cfg p) (asmSem t)` is the
composed chain Yul→Functions→Locals→Expressions/Structured→Assembly, each link produced by
that layer's preservation theorem restated as a `Refinement`. The existing induction core
`RecursiveSourceBridgeWhenUpToAt` (`Reference.lean:19934`) is the engine inside the
Yul-layer link — reused, not rebuilt.

**FeatureConfig dissolves.** What the audit called `FeatureConfig` becomes:
1. The universally-quantified handler/script — features that interact with the
   environment need no flag because an unused hook is never called.
2. `StateRelConfig` fields (already exist) — code image, storage/balance relations.
3. **Static event-kind predicates for corollaries**:

```lean
theorem compile_sound_closed (inp : TopInputs cfg)
    (hclosed : inp.program.eventKinds ∩ {.call, .create, .query, .queryBytes} = ∅)
    (hrun : Reference.run fuel inp.program inp.src₀ = .ok r) :
    ∃ fuel' r', Assembly.Target.runN inp.target fuel' inp.tgt₀ = .ok r' ∧ … :=
  -- one-line: specialize compile_whole_program_sound to closedHandler, use
  -- runE_closed compatibility + script-independence corollary of runE_congr
```

This is the replacement for `NoCallRuntime` and the pattern for every "program does not
use feature X" specialization: a *predicate hypothesis that trivializes premises*, never a
parallel corridor, never an interpreter flag. The 39 ladder rungs become at most a handful
of such one-line corollaries (closed, no-observer, object/deploy, code-image) — most are
deleted outright because their distinguishing premise-packagings no longer exist.

### 2.5 Determinism / nondeterminism per event kind (normative table)

| Event kind | Emit side | Replay side | Who resolves |
|---|---|---|---|
| `observe` (gas/msize) | deterministic from `EVMState` at Assembly target | script-consumed at all source layers | conditional oracle (preserved insight) |
| `call`, `create` | request deterministic | response script-consumed at **all** layers incl. target | external world; theorem ∀-quantifies the script |
| `query`, `queryBytes` | request deterministic | answer script-consumed at all layers | external world; ∀ script |
| `logEmit` | deterministic | **equality-checked**, never consumed | nobody — pure output |

Script mismatch (wrong head event on replay) = designated error, exactly today's oracle
behavior. Nondeterminism never appears as a relation on traces: traces are equal across a
refinement; nondeterminism enters only through which script the top theorem is
instantiated at.

---

## 3. Phased migration plan

Strategy: **build alongside, never retrofit.** The spine grows in `EvmCompiler/Spine/` and
per-layer `*E.lean` files; nothing existing is edited until a phase explicitly absorbs it.
Every phase is independently green and independently valuable; rollback for any phase is
"stop importing the new files" (they have no reverse dependencies until Phase 6).

**Coordination constraint:** the gas/msize oracle lane and the call-aware-spill lane are
*actively in flight* on the old architecture (PROGRESS_LOG 2026-06-09). Phases 0–3 touch
nothing they touch. Phase 4 (absorb observers) starts only after the oracle lane lands its
theorem (`TargetDryRun.sourceOracle_run_matches_targetOracle_of_compile`), which then
becomes Phase 4's regression target.

### Phase 0 — Mechanical mega-file split (zero semantic risk)
- **What:** split `Yul/RecursiveBridgeSupport.lean` (360k) into
  `Yul/RecursiveBridgeSupport/` parts (per-construct: `Seq.lean`, `If.lean`, `Switch.lean`,
  `For.lean`, `Call.lean`, `Leaves.lean`, `Ladder.lean`, …) with an umbrella file
  re-importing them in order; same for `Yul/OpenLowering.lean` (98k) and, if cheap,
  `Yul/Reference.lean` (84.7k — harder: definitions + early lemmas are widely imported;
  split only its trailing lemma sections). Mutual blocks stay within one part. No
  statement changes, no renames.
- **Files:** created ~20 part files; touched: the 2–3 umbrellas + `lakefile` glob if any.
- **Deleted:** nothing.
- **Gate:** `lake build EvmCompiler` green; `#print axioms` output on the pinned
  `LayerAudit` boundaries byte-identical before/after; `git diff` shows only moves.
- **Size / time:** ~1–2 agent-days (mostly build-wait; scripted splitting).
- **Rollback:** `git revert` of a pure-move commit.
- **Timing caveat:** requires a quiet window on those files (both active lanes edit
  `RecursiveBridgeSupport.lean`); announce in PROGRESS_LOG, do it between their
  checkpoints, or defer Reference/RBS and split only `OpenLowering.lean` first.

### Phase 1 — Spine core (greenfield, no old code touched)
- **What:** `Spine/Event.lean` (Event, Trace, kinds, static `eventKinds` scan + checked
  decision procedure), `Spine/Handler.lean` (Handler, three canonical instances,
  `HandlerSim`), `Spine/Refinement.lean` (FueledSem, Refinement, `comp`, `behavior`), plus
  a toy two-layer instantiation in `Spine/Smoke.lean` proving `comp` actually composes on
  a 20-line pair of interpreters.
- **Deliverable theorems:** `Refinement.comp_sound` (via the `comp` def), `Refinement.behavior`,
  `Trace`/kinds lemma set, smoke-test end-to-end theorem.
- **Gate:** `lake build EvmCompiler.Spine`; `#print axioms` on the smoke theorem = standard
  axioms only; risk experiments R1+R2 (§4) run and recorded in PROGRESS_LOG.
- **Size:** ~2–4k lines, ~2 agent-days.
- **Rollback:** delete directory.

### Phase 2 — Handler-parameterize one Assembly path (Target)
- **What:** `Assembly/SemanticsE.lean`: `Target.stepInstrResultE` / `runNResultE`
  (§2.2); the compatibility lemma `runNResult_eq_runE_closed`; the congruence lemma
  `Target.runE_congr`; the round-trip `Target.runE_record_replay`. Then re-derive, as
  one-line corollaries, three representative existing Observer theorems
  (`runNResultWithObservers_sound`, `runNResultWithOracle_of_withObservers`,
  `runNResultWithOracle_running_bind` — `Observer.lean:283/496/553`) *without editing
  Observer.lean* (corollaries live in `SemanticsE.lean`'s test section).
- **Deleted/demoted:** nothing yet (Observer.lean untouched; it is the regression oracle).
- **Gate:** the three corollaries each ≤ ~15 lines; heartbeat measurements within 3× of
  the bespoke originals (experiment R1's threshold); `lake build EvmCompiler.Assembly`.
- **Size:** ~3–5k lines, ~3 agent-days.
- **Rollback:** delete `SemanticsE.lean`.

### Phase 3 — Proof of concept: BALANCE / EXTCODESIZE / EXTCODEHASH end-to-end (then EXTCODECOPY)
- **Why this lane:** it is on the roadmap and must be built regardless, so its cost is
  amortized; it exercises the full request/response/script machinery (unlike gas/msize,
  which has no request payload) with the simplest state effect (push one word — no memory
  writes, no control flow); it has zero legacy corridor to be compatible with; and success
  here is the cleanest falsification test for the whole design. EXTCODECOPY follows as a
  second slice inside the phase (memory-writing answer — exercises `queryBytes` and the
  return-window-style bounds reasoning).
- **What:** add `StateQuery` evaluation to: Yul `Reference.runE` source semantics, each
  intermediate layer's `runE`, Assembly `runE`, the compiler (new opcodes already exist in
  the target instruction set), and acceptance. Build the per-layer `Refinement` instances
  for the query-bearing fragment and compose to the first spine top theorem:
  - `Spine.compile_sound_queries` — canonical-shape (§2.4) statement covering programs
    whose `eventKinds ⊆ {.query, .queryBytes, .observe-free…}` (fragment explicit in name).
- **Important scope honesty:** Phase 3's theorem covers the *query fragment* on the spine;
  the full-language canonical theorem arrives in Phase 6. Per-layer `runE` for this phase
  needs only the constructs the existing layers already support — the new code is the
  query emit sites plus the refinement restatements of existing preservation lemmas.
- **Gate (the go/no-go for the whole migration):** `#print axioms` standard-only; no
  `sorry/admit/axiom/unsafe/partial` on the path; **no certificate premises** (grep gate:
  `Certificate|Replay|Witness|Oracle|Layout|CallPreserves` absent from the public
  statement); total new-lemma count for the feature ≤ ~1/5 of the gas/msize baseline
  (i.e. ≤ ~7k lines vs 35k) — if it lands near 35k, the spine has failed its purpose:
  stop and rethink before any absorption phase.
- **Size:** ~5–8k lines, ~4–6 agent-days.
- **Rollback:** the query opcodes ship as executable-only (compiler emits, no theorem) —
  same state as any not-yet-verified roadmap feature.

### Phase 4 — Absorb the gas/msize observer lane
- **Precondition:** old lane's top theorem landed (it is in flight); it becomes the
  regression spec.
- **What:** extend the Phase 2/3 `runE` family's `observe` emit sites (they exist from
  Phase 2 at Assembly; add source-layer sites); prove the old lane's top theorem
  `TargetDryRun.sourceOracle_run_matches_targetOracle_of_compile` as a corollary of the
  spine round-trip + refinement. Re-pin `LayerAudit` observer boundaries to the spine
  route. Demote `Assembly/Observer.lean` interpreter variants and
  `Yul/ObserverOracle.lean`'s duplicate interpreters (`runWithOracle`,
  `SourceReplay.run*`) to `private`/compat modules with a deprecation header; stop
  importing them from `LayerAudit`.
- **Gate:** old top theorem derivable from spine in ≤ ~100 lines; `LayerAudit` green; no
  public import of the demoted modules.
- **Size:** ~4–6k lines new, ~35k demoted (not yet deleted), ~3–5 agent-days.
- **Rollback:** keep the old pins (both routes coexist harmlessly).

### Phase 5 — Absorb the open CALL/CREATE boundary (the big one)
- **What:** add `call`/`create` emit sites to the `runE` family; restate the
  `OpenRuntime`/`OpenLowering` corridor's per-construct lemmas as refinement-instance
  internals; prove the open-boundary soundness as the canonical-shape theorem; demote
  `OpenResult` & friends to private compat. The 98k-line `OpenLowering.lean` per-construct
  proofs are the main reuse target: their statements change shape (suspension → script
  threading) but their *case analyses and state-relation reasoning* port; expect heavy
  but mechanical editing, done per-construct (sequencing → if → switch → for → call),
  each construct a separate green commit.
- **Gate:** existing open-corridor public boundaries (`FunctionsProgramToCompiledOpenSoundAt`
  route, the checked CALL/CREATE entry wrappers from the 2026-06-08 refactor) re-derived
  as corollaries; `LayerAudit` re-pinned; storage-equality concern from ROADMAP ~7267–7274
  resolved or explicitly carried as a named premise (it is a real semantic gap, not a
  representation artifact — the spine does not magic it away).
- **Size:** the dominant cost: ~15–25k new lines, **~10–15 agent-days**, with ~140k lines
  (OpenRuntime+OpenLowering+OpenGasAware+NoCallRuntime) demoted at the end.
- **Rollback:** per-construct commits; the old corridor remains the public route until the
  final re-pin commit.

### Phase 6 — Canonical top theorem, ladder collapse, corridor deletion
- **What:** `Spine/Top.lean` with `TopInputs` + `compile_whole_program_sound` (§2.4) over
  the full accepted language; the ≤5 surviving corollaries (closed/no-call, object ×3
  initial-state choices, deploy+runtime composition); delete or `private`-ize the 39-rung
  ladder and the ~40 premise packages; `LayerAudit` re-pinned to exactly the canonical
  theorem + corollaries; PROGRESS_LOG `deletion` entries for everything removed.
- **Definition of done (acceptance criteria, verbatim gates):**
  1. One canonical top theorem (`Spine.compile_whole_program_sound`).
  2. `#print axioms` on it: standard Lean/library axioms only.
  3. No `sorry`/`admit`/new `axiom`/`unsafe`/`partial` on the public path
     (scripted grep over the import closure of `LayerAudit`).
  4. No compiler-generated certificate as a public premise — scripted grep of the top
     statement and `TopInputs` for `Certificate|Replay|Witness|Oracle|Layout|LabelTable|
     CallPreserves|Obligation`; only fundamental inputs remain (acceptedness, compile
     equation, fuel/gas bounds, initial-state relation).
  5. The 39-rung ladder reduced to one-line corollaries or deleted; premise-package count
     on the public path = 1 (`TopInputs`).
- **Size:** ~3–5k lines new, ~5 agent-days; large net deletion.
- **Rollback:** the re-pin commit is the only irreversible-feeling step and is still one
  revert.

**Total estimated spine cost: ~28–38 agent-days** (Phases 0–6), of which Phase 3 (~5
days) is work the roadmap requires anyway.

---

## 4. Risk register and falsification experiments

Each row: failure mode *in Lean specifically* → cheap early experiment that exposes it
before a phase commits to it.

| # | Risk | Lean-specific failure mode | Falsification experiment (cheap, early) | Phase gated |
|---|---|---|---|---|
| R1 | Handler parameter breaks automation | Goals that today close by defeq/`simp` on a concrete interpreter stop closing when `h : Handler H` is opaque; heartbeat blowup in `simp only` chains through `runE` unfoldings (cf. PROGRESS_LOG ~25866: `CompilerPreservation.block/stmt` already needs `maxHeartbeats` wrappers) | Scratch file under `proof_artifacts/`: parameterize `Target.stepInstrResult` only, re-prove 3 representative Observer lemmas generically, compare `count_heartbeats` vs originals; threshold 3× | P1→P2 |
| R2 | Trace threading × mutual recursion × termination | `Functions/Semantics.lean:82` mutual block (15+ functions, `Prod.Lex` well-founded measures) must thread `(Trace × H)`; known incident class: 2026-05 loop-theorem rollback ("passing the recursive block bridge through a generic lambda hides the fuel decrease from the termination checker", PROGRESS_LOG ~23074) | Scratch copy of the mutual block with an accumulator pair added; check it elaborates and `termination_by` still fires without `maxRecDepth` hacks; ½ day | P1→P3 |
| R3 | Trace-append normalization churn | Long `τ₁ ++ (τ₂ ++ …)` rewriting in every sequencing lemma; `simp [List.append_assoc]` fights | Accumulator-style threading (trace built tail-first, reversed once at the boundary) tried in the R1 scratch; pick the cheaper style **before** Phase 2 freezes signatures | P2 |
| R4 | `FueledSem` bundling hurts elaboration | Packing `run` as a structure field with implicit `{H}` produces universe/metavariable churn; `Refinement.sound` applications fail to unify the handler | Phase 1 smoke test is exactly this; if it fights, fall back to unbundled per-layer refinement theorems with a shared *statement shape* (macro/abbrev) instead of a structure — the plan degrades gracefully | P1 |
| R5 | `Event` payload typeclass gaps | `CallResponse`/`ByteArray` lack `DecidableEq`; replay matching needs decidable equality | Use `BEq` + lawfulness where needed; replay matcher written against `BEq`; checked in Phase 1 | P1 |
| R6 | Congruence lemma weaker than needed | `runE_congr` as stated relates same-program runs; cross-layer proofs need congruence *through the state relation* too — risk of needing a second, relational congruence per layer | Phase 3 will hit this on the first refinement instance; mitigation: state `runE_congr` with a state relation slot from the start (costs nothing when instantiated with `Eq`) | P3 |
| R7 | Spine vs in-flight lanes collision | Phase 4/5 absorb corridors that other agents are *currently extending*; merge conflicts in 360k-line files; stale-olean confusion | Hard sequencing rule (§3 preamble): absorption phases start only after the corresponding lane lands; PROGRESS_LOG announcements before touching shared files; Phase 0 split makes subsequent conflicts file-local | P0,P4,P5 |
| R8 | Storage-equality gap surfaces as spine gap | ROADMAP ~7267–7274: open-call public proof may not force contract-storage equality; restating in spine form makes the gap *visible* (trace-equal but state-relation-weak) and could be mistaken for a spine defect | Name it in Phase 5's gate explicitly; if unresolved, carry as a named premise with a `bottleneck` log entry — semantic work, not representation work | P5 |
| R9 | Mega-file split breaks import order | Lean section variables / `open` scoping / `set_option` regions in a 360k-line file don't survive naive splitting; mutual theorem blocks crossing a cut point fail | Split scripted with a checker: cut only at top-level `section`/`namespace` boundaries; build after each part; `OpenLowering.lean` first (lower churn) | P0 |
| R10 | Ladder consumers outside the repo/scripts | `scripts/test_solidity_to_yul_lean.py` or LayerAudit pins reference rung names | `rg` for each rung name across scripts/ and LayerAudit before deletion; deprecate via `abbrev` aliases for one phase | P6 |

### Asset triage: what survives, what is written off

**Reusable as-is (leaves under the spine):**
- `Reference.lean`'s semantic core: `StateRelConfig`, `SharedStateRel`, `ResultRel`, the
  induction core `RecursiveSourceBridgeWhenUpToAt` (:19934) and its per-construct leaf
  lemmas — the spine's Yul-layer refinement instance is *built from* these.
- The compiler itself and all compile-output structure lemmas (label resolution, PC-fit,
  assembler/encoder correctness, `Assembly/Assembler.lean`).
- The entire spill/layout/scratch corpus (`Functions/*`) — orthogonal to observation.
- `GasAware.lean` budget arithmetic and `XStepTrace` machinery (internal to the Assembly
  instance).
- Stack-bound tables and `StackGuardAudit` checked constructors.
- The static classifiers: `usesCallCreate` scan, RDC-bounds deciders, `BoundaryKind`.

**Reusable after mechanical restatement (statements change, proofs port):**
- `OpenLowering.lean`'s ~98k lines of per-construct open-corridor lemmas (Phase 5's main
  porting surface); `ObserverOracle.lean`'s expression/statement replay lemmas (Phase 4).

**Written off (deleted or permanent private compat):**
- The 39-rung ladder (~12k lines of `RecursiveBridgeSupport.lean`), the ~40
  premise-package structures and their plumbing lemmas, the 18 `With*` interpreter clones
  and 26+ equivalence theorems in `Observer.lean`, `NoCallRuntime.lean`'s parallel
  corridor (~24k), the `OpenResult` suspension algebra (`bind`, `OpenResultRel*`).
  Rough total written off: **~60–80k lines** — under 10% of the tree, concentrated
  exactly where maintenance cost is highest.

---

## 5. Cost/benefit honesty

**Observed baseline:** the gas/msize lane — a "small" feature pair — cost ~35k lines and
multiple multi-session weeks (PROGRESS_LOG shows the lane running 2026-06-07 → present);
the prompt's working figure is ~48h of agent time per small feature, and gas/msize ran
well past that. The driver is structural: each feature currently pays (re-derive
N interpreters) × (re-prove M equivalences) × (re-package premises) × (add ladder rungs).

**Spine cost:** ~28–38 agent-days total (§3), of which ~5 are roadmap work happening
anyway (Phase 3) and ~2 are pure hygiene with standalone value (Phase 0). Net new
architectural investment: **~21–31 agent-days**.

**Post-spine feature cost:** a new observable = 1 Event constructor + ~6 emit sites +
per-layer refinement-case additions + 1 corollary. Phase 3 measures this; target ≤ 1/5 of
baseline, i.e. **~1–2 agent-days per feature** instead of ~6–10 (gas/msize-class).

**Remaining roadmap demand (verified against ROADMAP.md):** EXTCODE family, BALANCE/
SELFBALANCE, EXTCODECOPY, LOG2–4 completion, TSTORE completion, SSTORE general contexts,
BLOCKHASH-family completion, open-argument semantics completion, return-data replay
completion, plus the Solidity semantic layer beyond. That is **8–12 feature-lane units**
of work on the books.

**Break-even:** at ~4–8 agent-days saved per feature unit, the spine pays for itself after
**~4–6 features** — i.e., within the *existing* roadmap, before counting (a) the
comprehension/maintenance cost of 360k-line files, (b) the compounding risk that each new
corridor multiplies against all previous ones (the gas×call×object product is already
visible in names like `RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsTopAssumptions`),
and (c) the audit cost of re-checking 39 ladder rungs whenever a premise changes.

**The honest downside case:** if the roadmap were to stop after ~3 more features, the
spine would not pay for itself in agent-time alone, and Phases 4–6 should then be skipped
— Phases 0–3 are still net-positive in that world (file hygiene + a roadmap feature
delivered + the corridor multiplication stopped from getting worse). This is why the
phase order front-loads the standalone-value work and puts the go/no-go gate at Phase 3.

---

## 6. Oracle consultation (hostile critique) and disposition

*(This section records the mandated pre-finalization review. The draft above was submitted
to the oracle with the prompt: "what is false, what will not elaborate in Lean 4, what
does CompCert experience say this gets wrong — attack the representation choices." The
consultation and disposition are summarized below; the PROGRESS_LOG `oracle` entry records
the session.)*

<!-- ORACLE_SECTION_PLACEHOLDER -->

---

## 7. Appendix: corrections to the audit's stated evidence

Verified 2026-06-09; future readers should re-verify, the tree moves daily.

1. The ladder has **39** rungs, not 38 (lines 348388–360124); it grew during the audit's
   own window — itself evidence for the diagnosis.
2. `Reference.lean` is 84,709 lines / 1,837 theorems (audit: 72k / 1,438) — same.
3. The premise-package census in the Yul layer is **40** `TopAssumptions|Ready|Checked`
   declarations (structures+defs+abbrevs); the audit's "~64" is reachable only by also
   counting `*Facts`/`*Assumptions` packs. The order of magnitude — dozens — stands.
4. The "2026-05-17 mutual-recursion timeout" cited as a named incident does not appear in
   PROGRESS_LOG on that date; the real incident cluster is: the loop-theorem rollback
   (mutual statement/block family + fuel-hiding lambda, ~line 23074), the
   `CompilerPreservation.block/stmt` `maxHeartbeats` wrapper (~line 25866), the abandoned
   generic static-mode helper (~line 20414), and the heavy-elaboration retreat on the
   runOpen no-overwrite theorem (~line 18941). The risk register (R1, R2) cites these.
5. The audit's "per-step diagram + stuttering measure" recommendation is amended (§0,
   §2.3): the cross-layer spine uses big-step fueled refinement because source layers are
   big-step structural interpreters with no step relation; small-step simulation remains a
   local option inside Assembly only.
6. The audit's "code-image reads become events" is amended (§1.5): own-code reads are
   state-relation material; only foreign-code queries are events.
7. The audit's `FeatureConfig` as a bundled hypothesis record is amended (§2.4): an
   interpreter-level or theorem-level feature *record* would re-multiply paths; features
   dissolve into the quantified handler, `StateRelConfig`, and static event-kind
   predicates feeding one-line corollaries.
