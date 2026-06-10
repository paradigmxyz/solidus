# Event-Spine Migration Plan for the Verified EVM Compiler Tower

**Date:** 2026-06-09 (revised same day after hostile oracle review — see §6)
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

1. **One `Event` type, with a strict separation between input *scripts* (environment
   responses consumed by a handler) and output *traces* (observations emitted by the
   interpreter).** These are different roles; conflating them in one list breaks
   record/replay (oracle finding, §6.A2).
2. **Handler-parameterized interpreters**: each layer's fuel-based big-step interpreter is
   written once, taking a small first-order handler record whose hooks see *only the
   request data, never the machine state* (§6.A3); plain / recording / replaying semantics
   are instances, and the per-variant interpreter zoo collapses to one congruence lemma
   per layer.
3. **One generic fueled-refinement structure** with transitive composition, replacing the
   bespoke per-corridor soundness statements and the top-theorem ladder.
4. **One canonical top theorem** quantified over external-response scripts, whose premises
   are only fundamental inputs (acceptedness, compile success, fuel, initial-state
   relation, script admissibility). Feature restrictions (no-call, no-observers, …) become
   *corollaries* derived from program predicates plus per-layer emission lemmas — not
   parallel corridors and not interpreter flags.

**What the spine does and does not retire (post-review honesty):** the spine retires the
*packaging* — duplicated interpreters, per-corridor premise structures as public
hypotheses, the top-theorem ladder. It does **not** retire semantic content: request
preservation, response admissibility (gas budgets, return-data adequacy), and world-effect
contracts survive as (a) proof obligations *inside* refinement instances and (b) a single
script-admissibility predicate at the top. Claims of "premise packages disappear" in the
audit should be read as "premise packages stop being public API and stop being
per-corridor" (§6.A4).

**Amendments to the audit's recommendation** (justified in §2, §6, §7):
(a) the generic simulation is *big-step fueled refinement*, not a CompCert small-step
diagram with stuttering measure — the Yul source semantics is structural recursion over
the AST with no step machine; small-step simulation stays a local option inside Assembly.
(b) Own-code-image reads are **not** events; they are deterministic functions of the
pinned code image in the state relation.
(c) `FeatureConfig` is **not** an interpreter parameter — flags on the interpreter would
recreate the corridor multiplication inside the spine. One interpreter, full event
surface; restriction by theorem-level program predicates.
(d) *(post-oracle)* Input scripts and output traces are distinct objects (§2.1).
(e) *(post-oracle)* Handler hooks are stateless with respect to the machine: event kinds
are split by **authority** — world-authoritative kinds (call/create/query) are
script-resolved at every layer; machine-authoritative kinds (gas/msize) are computed by
the target semantics and script-resolved only at source layers, which makes the canonical
theorem *conditional* on observer agreement, exactly preserving the existing
conditional-oracle insight (§2.4–2.5).
(f) *(post-oracle)* LOG0–LOG4 stay in machine substate (revert/rollback semantics);
they are not trace events in the initial spine (§1.13).
(g) *(post-oracle)* `OpenResult` is **not** deleted up front: Phase 5 builds a script
interpreter over `OpenResult` as an adapter theorem, reusing the 98k-line open-corridor
lemma corpus as-is; carrier retirement is a separate optional phase (§3, Phase 5).

**Verified baseline numbers (2026-06-09):**

| Fact | Value | Where |
|---|---|---|
| Lean lines under `EvmCompiler/` | 955,705 | `find … wc -l` |
| `Yul/RecursiveBridgeSupport.lean` | 360,235 lines, 3,745 theorems | — |
| Top-theorem ladder `compile_whole_program_result_sound_of_*` | **39** rungs in RBS (audit said 38; it grew), plus `…_topNoCall*` extension rungs in `NoCallRuntime.lean:15376+` | lines 348388–360124 |
| Hypotheses on first ladder rung | 22 | line 348388 |
| `Yul/Reference.lean` | 84,709 lines, 1,837 theorems (audit's 72k/1438 has grown) | — |
| Induction core `RecursiveSourceBridgeWhenUpToAt` | confirmed | `Reference.lean:19934` |
| `TopAssumptions`/`Ready`/`Checked` declarations, Yul layer alone | 40 (audit's ~64 also counted `*Facts`/`*Assumptions` packs) | `rg` census |
| Concrete interpreter functions across layers | ~85 (base ~35; observer/oracle variants 26; open/no-call/code-image variants the rest) | Explore sweep |
| `Assembly/Observer.lean` | 18 `WithObservers`/`WithOracle` interpreter variants over 3 paths, 26+ equivalence theorems | lines 133–1140 |
| gas()/msize() feature cost on current architecture | ~35k lines (`Yul/ObserverOracle.lean` 33,535 + `Assembly/Observer.lean` 2,286) | — |
| Other mega-files | `OpenLowering.lean` 98,007; `OpenRuntime.lean` 28,598; `NoCallRuntime.lean` 24,486; `GasAware.lean` 23,155; `OpenGasAware.lean` 14,883 | — |
| Call-site **equality** (not mere relation) already proved at the open boundary | `CallKind.callSite_eq_of_args`, pinned as `sourceStateRelOpenExternalPrimitiveCallSiteEqOfArgs` | `LayerAudit.lean:21,1206` |
| `Functions/Semantics.lean` mutual interpreter block | needs `set_option maxHeartbeats 800000` to elaborate its *definition* | `Functions/Semantics.lean:80` |

---

## 1. Complete feature inventory

For each lane: **(a)** what it becomes on the spine (Event constructors / script predicate /
state-relation field / premise), **(b)** which premise packages it retires *as public,
per-corridor API* (their semantic content moves inside refinement instances or the script
predicate), **(c)** what is genuinely *not* an event and where it lives instead.

### 1.1 CALL / CALLCODE / DELEGATECALL / STATICCALL suspension
- **Today:** `OpenResult` (`Yul/OpenExternal.lean:1503`) — a continuation-carrying
  suspension carrier (`.call : OpenCall (OpenResult ε α)` with
  `resume : CallResponse → OpenResult ε α`), threaded through `OpenRuntime.lean` (28.6k),
  `OpenLowering.lean` (98k), `OpenGasAware.lean` (14.9k).
- **(a) Becomes:** `Event.call (req : CallRequest) (resp : CallResponse)` in the output
  trace; the response is **script-resolved** at every layer (the external world answers).
  The suspension/continuation representation is *adapted, not deleted*: Phase 5 defines a
  script interpreter over `OpenResult` (`OpenResult.runScript`) plus one adapter-soundness
  theorem, so the continuation-style lemma corpus keeps working underneath while the spine
  exposes linear script semantics (§6.A6). Request preservation across layers is an
  *equality* obligation inside the refinement instances — with direct precedent: the repo
  already proves `CallKind.callSite_eq_of_args` (pinned in `LayerAudit.lean:1206`).
- **(b) Retires as public API:**
  `RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsTopAssumptions`
  and the `CanonicalEntry` sibling, `OpenXBoundaryFamilyResponseGas*ReadyFor`,
  `OpenCallActualPostGasBudgetFacts`, the `OpenResultRel*` relation family. Their
  *content* — response gas budgets, post-call world facts, return-data adequacy —
  consolidates into one `Script.Admissible` predicate (§2.1) stated once, not per
  corridor. A `CallResponse` must continue to carry the post-call world facts the source
  semantics consumes (storage/balance/return-data effects of reentrancy) — these are
  semantic premises about the environment, not wrapper noise (§6.A5).
- **(c) Not an event:** the *return-window* layout (`ReturnWindow`, `CallSite` operand
  plumbing) is compiler-strategy material; it stays in the lowering proof.

### 1.2 CREATE / CREATE2
- **Today:** a parallel constructor of the same suspension carrier (`OpenResult.create`,
  `CreateRequest/CreateResponse`), with its own premise packs.
- **(a) Becomes:** `Event.create (req : CreateRequest) (resp : CreateResponse)` — same
  script-resolved treatment as CALL, sharing the `BoundaryKind` classifier and one
  external-event lemma family parameterized by boundary kind.
- **(b) Retires as public API:** the create-side halves of §1.1's packages, same caveat.
- **(c) Not an event:** deploy-code construction and the init/runtime split (§1.7).

### 1.3 RETURNDATACOPY and return-data buffer replay
- **Today:** static bounds predicates (`targetProgramNoReturnDataCopy`,
  `CurrentNoCallReturnDataCopyBoundsReady` at `OpenGasAware.lean:9023`,
  `StackGuardedReturnDataCopyBounds*` in `StackGuardAudit.lean:1670+`); 202 old no-RDC
  declarations already demoted by the boundary refactor.
- **(a) Becomes:** **not an event** — the buffer is machine state populated by the
  response component of the most recent call/create event; RETURNDATACOPY is then
  deterministic. **Split of the bounds obligation (post-oracle, §6.A7):** the *static
  shape* of copy windows moves into acceptance/WF; the *dynamic adequacy* (the response
  actually returned enough bytes) **cannot** be static — it becomes a clause of the one
  `Script.Admissible` predicate. The premise does not vanish; it stops being per-corridor.
- **(b) Retires as public API:** the `*ReturnDataCopyBoundsReady` packs.
- **(c) Lives in:** state semantics + acceptance + script admissibility.

### 1.4 gas() / msize() observer oracle
- **Today:** `ResourceObserver`/`ResourceTrace` (`Assembly/Observer.lean:13–23`), 18
  `WithObservers`/`WithOracle` interpreter variants across three Assembly paths, 26+
  equivalence theorems, and `Yul/ObserverOracle.lean` (33.5k) re-deriving the
  Structured-layer stack and source semantics under trace threading. Design rationale in
  `proof_artifacts/resource_observer_oracle_approach_question.md`: the *conditional
  oracle* — no source-determinism claim; "if source replay consumes exactly the dry-run
  observations and reaches the same result, all parties agree."
- **(a) Becomes:** `Event.observe (kind) (value)` — the **machine-authoritative** kind:
  the Assembly target semantics *computes* the value from `EVMState` and emits the event
  (its hook is never consulted); source layers *script-resolve* it. Consequently the
  canonical top theorem's observer clause is conditional (§2.4) — the conditional-oracle
  insight is preserved structurally, not as a special case.
- **(b) Retires as public API:** all 18 `With*` interpreter variants and their
  equivalence theorems (replaced by one congruence + one round-trip lemma per layer);
  `OraclePrimitiveSemantics`, `PrimitiveAssemblyOracleSound`, and `ObserverOracle.lean`'s
  duplicate interpreter family.
- **(c) Not an event:** nothing; this is the purest event lane.

### 1.5 Code image (`runWithCodeImage`, CODESIZE/CODECOPY)
- **Today:** `runResultWithCodeImage` (`Reference.lean:4683`), `Program.runWithCodeImage`
  (`Yul/Semantics.lean:67`), `RecursiveBridgeObjectCodeImageTopAssumptions`
  (`ObjectRuntime.lean:219`), `RecursiveBridgeInitialCodeImageRel` (`NoCallRuntime.lean:58`).
- **(a) Becomes:** **not an event** (amendment (b)). Own-code reads are deterministic
  functions of the pinned image, part of the initial-state relation (`StateRelConfig`).
  The `WithCodeImage` interpreter variants collapse because the image is a component of
  the related initial states.
- **(b) Retires:** the bare/suffix/image trio of object premise packs → three choices of
  initial state, three one-line corollaries of one theorem.
- **(c) Foreign-code reads** (EXTCODECOPY) query the unmodeled world and *are* events (§1.11).

### 1.6 No-CALL corridor (`NoCallRuntime`, `NoCallCreate`)
- **Today:** a 24.5k-line parallel corridor (`RecursiveBridgeTopNoCallAssumptions`,
  `RecursiveBridgeActualXTrace*Facts` ×5, `compileCheckedAssemblyTarget?_noCallCreate`),
  plus its own extension rungs of the top-theorem ladder (`NoCallRuntime.lean:15376+`).
- **(a) Becomes:** a **corollary**, but not by syntax alone (§6.A8): it needs, per layer,
  one *emission lemma* — "if the static scan excludes kind K, the run's trace contains no
  K-events and the K-hooks are never consulted" — proved once by the interpreter's
  induction, analogous to the existing checked `compileCheckedAssemblyTarget?_noCallCreate`
  (which proves `asm.usesCallCreate = false`). Handler-independence then follows from the
  congruence lemma. Precision matters: the "closed program" corollary must exclude
  `{call, create, query, queryBytes}` *and*, for source-layer script-independence,
  `observe` — a program using `gas()` is handler-dependent at source layers even with no
  external interaction.
- **(b) Retires as public API:** the corridor as a parallel proof route, including its
  ladder extension rungs; the static classifier survives feeding the corollary.
- **(c) Not an event:** nothing; pure premise-trivialization plus one emission lemma per layer.

### 1.7 Object / contract boundaries (Objects, ObjectRuntime, deploy/runtime split)
- **Today:** `Objects.Object/Program` with `Source.run`/`Runtime.run`, three
  top-assumption variants (`RecursiveBridgeObject{,CodeImage,Suffix}TopAssumptions`,
  `ObjectRuntime.lean:84/219/357`).
- **(a) Becomes:** **structure, not events.** Deploy and runtime executions are two
  applications of the canonical top theorem with different initial states/code images,
  composed by trace/script splitting (deploy's consumed script prefix + emitted trace
  prefix precede runtime's). Constructor-time CREATE is an ordinary `Event.create`.
- **(b) Retires:** the three object premise-pack variants → one theorem + three
  initial-state corollaries.
- **(c) Lives in:** the Objects layer keeps syntax/lowering/preservation; only its
  soundness statement re-targets the spine refinement.

### 1.8 Stack spill and scratch-frame memory
- **Today:** `Functions/CallAwareSpill.lean`, `ScratchFrameSpill.lean` (5.6k),
  `ScratchFrameMemory.lean` (`FrameStoreRel` at :1644), `LiveLayout.lean`,
  `LiveLayoutPreservation.lean`.
- **(a) Becomes:** **not an event and not config — untouched.** Spill is a
  compilation-strategy proof certifying the Functions→Locals lowering's scratch-memory
  use; it is erased by the state relation and lives where it lives. The spine helps only
  indirectly: its preservation lemmas restate over the handler-parameterized interpreter
  once, instead of once per observation variant.
- **(b) Retires:** nothing.
- **(c)** Watch-item: scratch writes can change `msize`; the existing
  `SameData`/scratch-readiness premise handles this and becomes a hypothesis of the
  Functions-layer refinement instance, stated once.

### 1.9 Gas accounting / sufficient-gas premises
- **Today:** `Assembly/GasAware.lean` (23.2k; `GasExecRel` :732, `XStepTrace` :6469),
  `Yul/OpenGasAware.lean` (14.9k), `*GasBudget*` packs.
- **(a) Becomes:** a **fundamental resource premise** (initial gas ≥ bound — allowed
  premise class, like fuel) plus, for post-call gas facts, clauses of `Script.Admissible`.
  Gas *consumption* stays in machine state; gas *observation* is `Event.observe .gas`.
  `GasExecRel` (gas-erased equivalence) becomes a state-relation choice inside the
  Assembly refinement instance.
- **(b) Retires as public API:** the `GasAdmissible*ReadyFor` packs; budget arithmetic
  lemmas are reusable leaves.
- **(c) Lives in:** the Assembly instance, acceptance-level bound computation, and the
  script predicate.

### 1.10 Stack-bound / resource certificates (`StackResource`, `StackGuardAudit`)
- **Today:** static `Effect`/`Summary` bound tables (`Structured/StackResource.lean:13/49`),
  `OpenStackResource.lean`, checked by `StackGuardAudit.lean`.
- **(a) Becomes:** **not an event.** Compiler-output properties discharged by checked
  constructors (already the design); under the spine they appear only inside the Assembly
  refinement instance's proof, never as public premises.
- **(b) Retires:** any remaining public bound-table premises.
- **(c) Lives in:** where it is.

### 1.11 Roadmap state queries: EXTCODESIZE / EXTCODECOPY / EXTCODEHASH / BALANCE / SELFBALANCE
- **Today:** not implemented; ROADMAP.md (~7376–7378, ~10418) plans them as state queries
  with `StateRelConfig.balanceRel`-style contracts, explicitly not suspension.
- **(a) Becomes:** `Event.query (q : StateQuery) (answer : Word)` for word-valued
  queries; `Event.queryBytes` for EXTCODECOPY. **World-authoritative**: script-resolved at
  every layer; the emitted request is deterministic. This is the chosen proof-of-concept
  lane (§3, Phase 3) — with scope discipline (§6.A9): the initial slice models *neither*
  warm/cold access accounting *nor* balance-flow coherence; those are gas-model and
  world-model extensions, declared out of the Phase 3 fragment by name. Script coherence
  (answers consistent with prior calls) is deliberately **not** required for the compiler
  theorem — the compiler preserves behavior under any script; coherence axioms are a
  user-side strengthening (CompCert quantifies over external behaviors satisfying axioms
  similarly).
- **(b) Retires:** nothing (greenfield); *prevents* a fourth observation mechanism.
- **(c)** SELFBALANCE after a value-bearing CALL is world-dependent — a query event, not
  a state read; semantically honest without modeling balance flow.

### 1.12 Block/chain environment reads (BLOCKHASH, TIMESTAMP, NUMBER, CHAINID, …)
- **Today:** checked nullary bridge constructors reading `ExecutionEnv` (ROADMAP ~7495).
- **(a) Becomes:** **not events** — deterministic reads of the pinned execution
  environment, covered by the state relation. (BLOCKHASH for non-recent blocks can become
  a query event later if the env model doesn't carry the hash map; the spine supports
  either without restructuring.)

### 1.13 LOG0–LOG4
- **Today:** LOG0/LOG1 checked with shared log-effect preservation in machine substate
  (ROADMAP ~10429).
- **(a) Becomes (revised post-oracle, §6.A10):** **logs stay in machine substate.** EVM
  logs are transactional: they are discarded when a frame reverts, so an irrevocable
  trace-append at the opcode point is semantically wrong without
  commit/rollback structure in the trace. The initial spine therefore has **no
  `logEmit` event**; log preservation continues through the state relation as today. If a
  committed-log observation is wanted at the top theorem, it is *derived* from final
  state at the boundary ("the compiled program's committed logs equal the source's") —
  one corollary, no trace machinery. Revisit only if a future consumer needs streaming
  log observation, at which point scoped commit markers must be designed first.

### 1.14 Storage (SLOAD/SSTORE/TLOAD/TSTORE)
- **Today:** modeled state with `StateRelConfig.sloadRel` contracts, writable-context
  premise for SSTORE (ROADMAP ~10418–10427).
- **(a) Becomes:** **not events** — modeled machine state related by the state relation;
  working and representation-correct. No change.

### 1.15 Solidity frontend
- **Today:** syntax + JSON bridge only (`Solidity/Frontend.lean`, 397 lines); no
  semantics, no soundness theorem.
- **(a) Becomes:** out of spine scope. Future Solidity semantics sit above Objects and
  inherit the same `Trace`; the spine makes that theorem statable as one more composed
  refinement.

### 1.16 Summary table

| Lane | Spine representation | Authority / resolution |
|---|---|---|
| CALL family | `Event.call req resp` in trace | world: resp script-resolved at all layers; req equality proved (precedent: `callSite_eq_of_args`) |
| CREATE/CREATE2 | `Event.create req resp` | world: as CALL |
| gas()/msize() | `Event.observe kind v` | machine: computed+emitted at target; script-resolved at source layers; conditional clause in top theorem |
| EXTCODE*/BALANCE | `Event.query q a` / `Event.queryBytes q a` | world: script-resolved at all layers |
| LOG0–4 | machine substate (NOT a trace event); committed-log corollary at boundary | — |
| RETURNDATACOPY | state (buffer from call/create resp); static shape in WF + dynamic adequacy in `Script.Admissible` | — |
| Own code image | `StateRelConfig` / initial-state relation | — |
| Block env reads | state relation (pinned env) | — |
| Storage | state relation | — |
| No-call corridor | corollary: static scan + per-layer emission lemma + congruence | — |
| Object/deploy split | two theorem applications + script/trace splitting | — |
| Spill/scratch frames | Functions-layer lowering proof (unchanged) | — |
| Gas budget | fundamental premise + `Script.Admissible` clauses | — |
| Stack bounds | checked constructor inside Assembly instance | — |

---

## 2. Core Lean interfaces (candidate signatures)

Design sketches — falsifiably specific, not yet elaborated. All spine files set
`set_option autoImplicit false`; every sketch below is read with explicit binders even
where elided for brevity (§6.A11). Names live under `EvmCompiler/Spine/`. Conventions
match current idiom: first-order, fuel-`Nat` structural recursion, `Except` results,
**accumulator-style traces** (trace built via an accumulator argument, exposed reversed
at the boundary — avoids recursive `τ₁ ++ τ₂` in the executable semantics, §6.A12).

### 2.1 Events, traces, scripts (`Spine/Event.lean`)

**Prerequisite (Phase 1a):** the payload types (`CallRequest`, `CallResponse`,
`CreateRequest`, `CreateResponse`, `ResourceObserver`, the new `StateQuery`/`BytesQuery`)
must live *below* every layer that emits them. Today `CallRequest` lives in
`Yul/OpenExternal.lean` (which imports only `Yul.PrimSemantics` — low in the graph, so
relocation is a contained mechanical move, but the import graph must be checked first;
§6.A13). `ResourceObserver` moves out of `Assembly/Observer.lean` (which imports
`Assembly.Preservation`) into the shared module.

```lean
namespace EvmCompiler.Spine

/-- One observed interaction, as recorded in an OUTPUT trace. For world-authoritative
    kinds the response was supplied by the environment; for machine-authoritative kinds
    the value was computed by the machine. -/
inductive Event where
  | call       (req : CallRequest)   (resp : CallResponse)
  | create     (req : CreateRequest) (resp : CreateResponse)
  | query      (q : StateQuery)      (answer : Word)
  | queryBytes (q : BytesQuery)      (answer : ByteArray)
  | observe    (kind : ResourceObserver) (value : Word)
  -- NO logEmit: logs are revertible substate (§1.13).

abbrev Trace  := List Event          -- output only
abbrev Script := List Event          -- input only: the environment's answers, in order.
                                      -- Distinct abbrevs for distinct roles; replay
                                      -- consumes Script, emission appends to Trace.
                                      -- They share the element type so the round-trip
                                      -- theorem can state `script = recorded trace's
                                      -- resolved-event projection`.

def Event.kind : Event → EventKind
def Trace.kinds (τ : Trace) : List EventKind
/-- Projection: the sub-sequence of events whose resolution came from the environment
    (call/create/query/queryBytes — and observe, at layers that script-resolve it). -/
def Trace.scriptOf (resolvedKinds : EventKind → Bool) (τ : Trace) : Script

/-- Static over-approximation of the event kinds a program can emit, with a checked
    decision procedure (the existing `usesCallCreate` scan generalized). -/
def Program.eventKinds : Program → Finset EventKind

/-- THE consolidated environment contract, replacing per-corridor Ready/Facts packs:
    response gas budgets, return-data adequacy for the windows the program declares,
    post-call world facts. One predicate, clauses per event kind. -/
def Script.Admissible (cfg : StateRelConfig) (p : Program) (σ : Script) : Prop
```

Instance obligations checked in Phase 1 before anything else (§6.A14): `BEq` *and*
`LawfulBEq` (or bespoke `beq_iff_eq` lemmas) for every payload type — replay matching via
`==` is useless for propositional trace reasoning without lawfulness. If
`DecidableEq CallResponse` is derivable (ByteArray has `DecidableEq`), prefer it.

### 2.2 Handlers and the parameterized interpreter (`Spine/Handler.lean`, per-layer files)

**Hooks never see machine state** (§6.A3): a handler that could inspect `EVMState` both
fails to typecheck at source layers (their state is `Reference.State`) and — worse — can
distinguish states the refinement's relation is meant to hide, making ∀-handler
refinement false. Where a value is deterministic from machine state (gas/msize at the
target), the *semantics computes it and emits the event without consulting any hook*.

```lean
structure Handler (H : Type) where
  call       : CallRequest   → H → Option (CallResponse × H)
  create     : CreateRequest → H → Option (CreateResponse × H)
  query      : StateQuery    → H → Option (Word × H)
  queryBytes : BytesQuery    → H → Option (ByteArray × H)
  /-- Consulted ONLY by layers that cannot compute the value (source layers).
      The Assembly target semantics never calls this. -/
  observe    : ResourceObserver → H → Option (Word × H)
```

`H : Type` is deliberately universe-0 and monomorphic in instances; nothing in the tower
needs handler state above `Type` (§6.A15). `none` = environment refusal → designated
error, mirroring today's oracle-mismatch behavior.

Canonical instances (each ~15 lines, written once):

```lean
/-- Replay/world handler: every hook pops the matching event from the script. -/
def scriptHandler : Handler Script
/-- Closed handler: refuses all interaction. Programs whose emitted kinds are empty
    run identically under any handler (corollary of congruence + emission lemma). -/
def closedHandler : Handler Unit
-- There is NO "recordingHandler": recording is not a handler behavior. The TARGET
-- interpreter records by computing machine-authoritative values itself; world values
-- are recorded by echoing whatever the handler supplied into the emitted event.
```

Parameterized interpreter, Assembly Target path (today
`Target.runNResult : TargetProgram → Nat → EVMState → Except EVMException StepResult`,
`Assembly/Semantics.lean:144`, plus 6 observer/oracle clones in `Observer.lean`):

```lean
def Target.runNResultE {H : Type} (h : Handler H) (target : TargetProgram) :
    Nat → EVMState → H → Trace →                  -- Trace = accumulator (reversed)
    Except EVMException (StepResult × Trace × H)
-- gas/msize: value computed from EVMState, event pushed to accumulator, h not consulted.
-- CALL/CREATE/queries: request computed from state, response from the hook, event pushed.
```

Yul source semantics (today `Reference.run : Nat → Program → State → Except Exception
State`, `Reference.lean:4670`, big-step structural over the AST):

```lean
def Reference.runE {H : Type} (h : Handler H) :
    Nat → Program → State → H → Trace →
    Except Exception (Result × Trace × H)
-- identical recursion structure; h.observe consulted at gas()/msize() sites (the source
-- cannot compute them), world hooks at call/create/query sites.
```

**Compatibility is projection, not equality with a reconstructed trace** (§6.A16 — the
old interpreter cannot reproduce intermediate observations from its result alone):

```lean
theorem Target.runNResult_eq_runE_proj {H} (h : Handler H) (target fuel s hs acc)
    (hclosed : <target program emits nothing, or h = closedHandler and program is closed>) :
    (Target.runNResultE h target fuel s hs acc).map (fun (r, _, _) => r)
      = Target.runNResult target fuel s
-- and unconditionally for the result component when the run succeeds under any handler
-- whose answers match the base semantics' behavior — stated per layer, proved by the
-- interpreter induction.
```

Existing theorems about concrete interpreters therefore remain consumable through the
projection; new features are proved against `runE` only. **What this collapses and what
it does not** (§6.A4): the congruence lemma below collapses the *handler-variant
equivalence* family (the 26 Observer theorems and every future "WithX agrees with base").
It does **not** collapse compiler-preservation content — request preservation, response
threading, and continuation reasoning remain per-construct work inside refinement
instances; they are the honest residue of the compiler proof.

```lean
/-- Handler simulation lifts to run agreement: one lemma per layer, proved by the same
    induction as the interpreter. Stated with a state-relation slot from the start
    (instantiable with Eq) so it also serves cross-representation congruence needs. -/
theorem Target.runE_congr {H₁ H₂ : Type} (R : H₁ → H₂ → Prop)
    (h₁ : Handler H₁) (h₂ : Handler H₂) (hooks : HandlerSim R h₁ h₂)
    (target fuel s) {hs₁ hs₂} (hR : R hs₁ hs₂) (acc) :
    RelRun R (Target.runNResultE h₁ target fuel s hs₁ acc)
             (Target.runNResultE h₂ target fuel s hs₂ acc)

/-- Round-trip: a successful run's emitted trace, projected to its script-resolved
    events, replays against scriptHandler to the same result and trace. The generalized
    conditional-oracle theorem. -/
theorem Target.runE_record_replay {H} (h : Handler H) (target fuel s hs) :
    Target.runNResultE h target fuel s hs [] = .ok (r, τ, hs') →
    Target.runNResultE scriptHandler target fuel s (τ.scriptOf targetResolved) []
      = .ok (r, τ, [])
```

### 2.3 The generic refinement structure (`Spine/Refinement.lean`)

Big-step fueled refinement (amendment (a)); a "semantics" is one value per
(layer, program):

```lean
structure FueledSem where
  State  : Type
  Result : Type
  Err    : Type
  run    : {H : Type} → Handler H → Nat → State → H → Trace →
           Except Err (Result × Trace × H)

structure Refinement (Hi Lo : FueledSem) where
  rel       : Hi.State → Lo.State → Prop
  resultRel : Hi.Result → Lo.Result → Prop
  sound     : ∀ {H : Type} (h : Handler H) (fuel : Nat) s t (hs : H) r τ hs',
      rel s t →
      Hi.run h fuel s hs [] = .ok (r, τ, hs') →
      ∃ fuel' r', Lo.run h fuel' t hs [] = .ok (r', τ, hs') ∧ resultRel r r'
```

Key choices, with their post-review caveats:
- **Trace equality, not a trace relation, is the default conclusion.** Justification:
  representation erasure lives in `rel`/`resultRel` (the `SameData`-modulo-erasure
  discipline), and the repo's own boundary already proves call-site *equality*
  (`callSite_eq_of_args`) — requests are canonicalized, so equality is achievable here,
  unlike CompCert's memory-injection-sensitive events (§6.R2). **Fallback registered as
  risk R11:** if any layer's requests turn out to be only relation-equal (address
  truncation, payload representation), `Refinement` gains an `eventRel` field defaulted
  to `Eq` — the structure is designed so this is an additive change.
- **Fuel is existential** (matches every current theorem shape).
- **The handler is universally quantified through the refinement** — sound because hooks
  see only request data, and requests are proved equal across the relation (this is
  exactly where the per-construct proof content lives; §6.A3/A4).
- The conclusion's `hs` threading asserts both sides consume the *same* script prefix —
  the script-consumption discipline that replaces suspension-tree alignment.

```lean
def Refinement.comp (ab : Refinement A B) (bc : Refinement B C) : Refinement A C :=
  { rel := fun a c => ∃ b, ab.rel a b ∧ bc.rel b c
    resultRel := …, sound := …  /- transitivity, proved once -/ }
```

`run` as a structure projection will not unfold by `simp`/`rfl` against concrete
interpreters; each per-layer `FueledSem` value is declared `@[reducible]`/`abbrev` and the
refinement instances are stated against the concrete `runE` with the `FueledSem` wrapper
used only at composition time (§6.A15). If Phase 1's smoke test still fights unification,
the fallback is unbundled per-layer theorems sharing a *statement shape* via `abbrev` —
the plan degrades gracefully (risk R4).

Stuttering: fuel-existential big-step refinement absorbs stuttering trivially. Small-step
`StepSim` with a measure remains a local option inside Assembly only.

### 2.4 The canonical top theorem (`Spine/Top.lean`)

```lean
/-- Fundamental inputs ONLY: no layout witnesses, replay witnesses, call-preservation
    oracles, or label tables. -/
structure TopInputs (cfg : Reference.StateRelConfig) where
  program  : Yul.Program
  accepted : Reference.Accepted program          -- incl. static RDC shape, stack, names
  target   : Assembly.TargetProgram
  compiled : compileCheckedAssemblyTarget? program = some target
  src₀     : Reference.State
  tgt₀     : EVMState
  initRel  : Reference.SharedStateRel cfg src₀ tgt₀   -- incl. code image, gas bound

theorem compile_whole_program_sound (cfg) (inp : TopInputs cfg)
    (σ : Script) (hσ : Script.Admissible cfg inp.program σ)
    (fuel : Nat) {r : Reference.Result} {τ : Trace} {σ' : Script}
    (hrun : (yulSem cfg inp.program).run scriptHandler fuel inp.src₀ σ []
              = .ok (r, τ, σ')) :
    ∃ fuel' r' τ',
      (asmSem inp.target).run scriptHandler fuel' inp.tgt₀ σ [] = .ok (r', τ', σ') ∧
      -- world events agree unconditionally:
      τ'.scriptOf worldKinds = τ.scriptOf worldKinds ∧
      -- observer clause: IF the script's observer answers coincide with what the target
      -- machine actually computes, everything agrees exactly. Programs that never
      -- observe make this clause vacuous, giving τ = τ' outright.
      (τ'.observeEvents = τ.observeEvents →
        τ' = τ ∧ Reference.ResultRel cfg r r')
```

**Why the conditional clause is honest and necessary** (§6.A3): the source semantics
cannot compute gas/msize; for an arbitrary script the source's observed values may simply
be wrong about the machine, and no target run matches. The current architecture's
dry-run design (`TargetDryRun.sourceOracle_run_matches_targetOracle_of_compile`) has
exactly this conditional shape; the spine states it once, structurally, instead of once
per lane. For the (vast) class of programs with no `observe` events, the corollary

```lean
theorem compile_sound_noObserve (… hnoobs : .observe ∉ inp.program.eventKinds …) :
    … ∃ fuel' r', run … = .ok (r', τ, σ') ∧ ResultRel cfg r r'
```

is one line from the emission lemma. The fully closed corollary
(`eventKinds = ∅`, replacing `NoCallRuntime`):

```lean
theorem compile_sound_closed (… hclosed : inp.program.eventKinds = ∅ …)
    (hrun : Reference.run fuel inp.program inp.src₀ = .ok r) :
    ∃ fuel' r', Assembly.Target.runN inp.target fuel' inp.tgt₀ = .ok r' ∧ …
```

derived via: emission lemma (no hooks consulted, trace empty) + congruence
(handler-independence) + the projection compatibility lemma. One short proof, not 24k
lines.

**FeatureConfig dissolves** into: (1) the quantified script + `Script.Admissible`; (2)
`StateRelConfig` fields; (3) static event-kind predicates + per-layer emission lemmas
feeding corollaries. The ladder's 39+ rungs become ≤5 corollaries (closed, no-observe,
object ×3 initial states / deploy+runtime composition); the rest are deleted because the
premise-packagings they vary over no longer exist.

### 2.5 Determinism / authority per event kind (normative table)

| Event kind | Authority | Emit at target | Resolution at source layers | Top-theorem treatment |
|---|---|---|---|---|
| `call`, `create` | world | req computed; resp from hook | same | unconditional, script-quantified, `Script.Admissible` |
| `query`, `queryBytes` | world | req computed; answer from hook | same | unconditional, script-quantified |
| `observe` (gas/msize) | machine | value computed from `EVMState`, hook NOT consulted | value from hook (script) | conditional clause (dry-run insight) |
| logs | (substate, not an event) | — | — | committed-logs corollary via state relation |

Script mismatch on replay = designated error (today's oracle behavior). Nondeterminism
never appears as a relation on traces; it enters only through which script the theorem is
instantiated at.

---

## 3. Phased migration plan

Strategy: **build alongside, never retrofit.** The spine grows in `EvmCompiler/Spine/`
and per-layer `*E.lean` files; nothing existing is edited until a phase explicitly
absorbs it. Every phase is independently green and valuable; rollback for any phase is
"stop importing the new files" (no reverse dependencies until Phase 6).

**Coordination constraint:** the gas/msize oracle lane and the call-aware-spill lane are
actively in flight on the old architecture (PROGRESS_LOG 2026-06-09). Phases 0–3 touch
nothing they touch. Phase 4 starts only after the oracle lane lands its theorem, which
becomes Phase 4's regression target.

### Phase 0 — Mechanical mega-file split (low risk, not zero)
- **What:** split `Yul/OpenLowering.lean` (98k) first, then `Yul/RecursiveBridgeSupport.lean`
  (360k), into per-construct part files under a directory, umbrella file re-importing in
  order; `Yul/Reference.lean` only its trailing lemma sections, if cheap. Cut only at
  top-level `section`/`namespace` boundaries (verified: 52 and 210 such markers
  respectively; 12/26 `mutual` blocks stay intact within parts). **Pre-split checklist
  (oracle §6.A17):** scan each file for `private` declarations used later in the file,
  `local notation`/`local attribute`/scoped instances, and `set_option` region extents
  (7/14 occurrences) — any of these crossing a cut point must move or be re-declared. No
  statement changes, no renames.
- **Gate:** `lake build EvmCompiler` green; `#print axioms` on the pinned `LayerAudit`
  boundaries byte-identical before/after; diff shows only moves.
- **Size / time:** ~2 agent-days. **Rollback:** revert the pure-move commit.
- **Timing caveat:** needs a quiet window (both active lanes edit
  `RecursiveBridgeSupport.lean`); announce in PROGRESS_LOG; `OpenLowering.lean` first.

### Phase 1 — Spine core (greenfield)
- **What:** Phase 1a: relocate payload types below all layers after an import-graph
  check (`rg "^import"` on `OpenExternal.lean`, `Observer.lean`, `Reference.lean`,
  `Assembly/Semantics.lean`) — `OpenExternal.lean` imports only `Yul.PrimSemantics`, so
  this is contained (§6.A13). Phase 1b: `Spine/Event.lean` (Event, Trace/Script,
  projections, `eventKinds` scan + checked decision procedure, `Script.Admissible`
  skeleton), `Spine/Handler.lean` (Handler, scriptHandler/closedHandler, `HandlerSim`),
  `Spine/Refinement.lean` (FueledSem, Refinement, comp), `Spine/Smoke.lean` — a toy
  two-layer instantiation proving comp fires end-to-end.
- **Up-front checks (oracle-mandated, §6.A14):** `#check (inferInstance : BEq CallRequest)`
  etc. for all payloads; `LawfulBEq` or bespoke `beq_iff_eq`; all files
  `set_option autoImplicit false`.
- **Gate:** `lake build EvmCompiler.Spine`; `#print axioms` standard-only on the smoke
  theorem; risk experiments R1+R2 run and logged.
- **Size:** ~2–4k lines, ~2–3 agent-days. **Rollback:** delete directory.

### Phase 2 — Handler-parameterize one Assembly path (Target)
- **What:** `Assembly/SemanticsE.lean`: `Target.stepInstrResultE`/`runNResultE`
  (accumulator traces); projection compatibility lemma; `Target.runE_congr`;
  `Target.runE_record_replay`. Re-derive three representative Observer theorems
  (`runNResultWithObservers_sound`, `runNResultWithOracle_of_withObservers`,
  `runNResultWithOracle_running_bind` — `Observer.lean:283/496/553`) as short corollaries
  *without editing Observer.lean* (it is the regression oracle).
- **Gate:** corollaries ≤ ~15 lines each; heartbeats within 3× of bespoke originals
  (R1 threshold); `lake build EvmCompiler.Assembly`.
- **Size:** ~3–5k lines, ~3 agent-days. **Rollback:** delete `SemanticsE.lean`.

### Phase 3 — Proof of concept: BALANCE / EXTCODESIZE / EXTCODEHASH end-to-end (then EXTCODECOPY)
- **Why this lane:** roadmap work that must happen anyway; exercises the full
  request/script machinery with the simplest state effect; zero legacy corridor; the
  cleanest falsification test for the design.
- **Scope discipline (post-oracle §6.A9):** the Phase 3 fragment explicitly excludes
  warm/cold access-cost modeling, balance-flow coherence across calls, and account
  existence subtleties — query answers are arbitrary script words; gas costs use the
  existing gas model unchanged. Named fragment, named exclusions, revisited when the gas
  model is extended.
- **What:** `StateQuery` evaluation in Yul `Reference.runE`, each intermediate layer's
  `runE`, Assembly `runE`; compiler emit; acceptance; per-layer `Refinement` instances
  for the query fragment; composed `Spine.compile_sound_queries`.
- **Gate (go/no-go for the whole migration):** `#print axioms` standard-only; no
  `sorry/admit/axiom/unsafe/partial`; no certificate premises (grep gate per §3 Phase 6
  list); total feature cost ≤ ~1/4 of the gas/msize 35k-line baseline. If it lands near
  baseline, **stop: the spine has failed its purpose; do not proceed to absorption.**
- **Size:** ~6–10k lines, ~5–7 agent-days. **Rollback:** queries ship executable-only.

### Phase 4 — Absorb the gas/msize observer lane
- **Precondition:** old lane's top theorem landed; it is the regression spec.
- **What:** add source-layer `observe` resolution sites; prove
  `TargetDryRun.sourceOracle_run_matches_targetOracle_of_compile` as a corollary of
  round-trip + refinement; re-pin `LayerAudit` observer boundaries to the spine route;
  demote `Observer.lean` interpreter variants and `ObserverOracle.lean` duplicate
  interpreters to private compat.
- **Gate:** old top theorem derivable in ≤ ~100 lines; `LayerAudit` green; no public
  import of demoted modules.
- **Size:** ~4–6k lines new, ~35k demoted; ~3–5 agent-days.

### Phase 5 — Absorb the open CALL/CREATE boundary (the big one, restructured post-oracle)
- **Strategy (§6.A6): adapter over `OpenResult`, not carrier replacement.**
  - **5a (pilot, mandatory gate):** define `OpenResult.runScript : OpenResult ε α →
    Script → Except ε (α × Script)` (linearize the suspension tree along a script) and
    prove the adapter theorem for ONE construct corridor (sequencing) end-to-end:
    existing `OpenLowering` lemmas stay *unchanged underneath*; the spine's refinement
    instance for that construct consumes them through the adapter. Measure cost.
  - **5b:** roll the adapter across the remaining constructs (if → switch → for → call),
    each a separate green commit; `Script.Admissible` absorbs
    `BoundaryResponsesSatisfy`/gas-budget/return-data packs; canonical-shape open-boundary
    theorem; re-pin `LayerAudit`; demote `OpenRuntime`/`NoCallRuntime` public routes.
  - **5c (optional, separately justified):** retire the `OpenResult` carrier itself.
    Default is to keep it permanently as internal machinery — the adapter already gives
    the spine its linear interface, and the continuation algebra is Lean-friendly.
- **Gate:** 5a pilot cost ≤ ~2 agent-days for sequencing, else stop and re-plan; existing
  open-corridor public boundaries re-derived as corollaries; the storage-equality concern
  (ROADMAP ~7267–7274) resolved or carried as a named premise — it is a semantic gap the
  spine exposes but does not create (§6.A5).
- **Size:** ~15–25k new lines; **15–30 agent-days** (revised upward per §6.A18; the 5a
  pilot exists precisely because this estimate is the least certain number in this plan).

### Phase 6 — Canonical top theorem, ladder collapse, corridor deletion
- **What:** `Spine/Top.lean` (`TopInputs`, `compile_whole_program_sound` per §2.4); the
  ≤5 surviving corollaries; delete or `private`-ize the 39 RBS ladder rungs *and* the
  `NoCallRuntime` extension rungs (the only Lean consumer of rung names — verified
  2026-06-09; deprecate via `abbrev` aliases for one phase); retire the ~40 premise
  packages; `LayerAudit` re-pinned to the canonical theorem + corollaries; PROGRESS_LOG
  `deletion` entries.
- **Definition of done (acceptance criteria, verbatim gates):**
  1. One canonical top theorem (`Spine.compile_whole_program_sound`).
  2. `#print axioms` on it: standard Lean/library axioms only.
  3. No `sorry`/`admit`/new `axiom`/`unsafe`/`partial` on the public path (scripted grep
     over the import closure of `LayerAudit`).
  4. No compiler-generated certificate as a public premise — scripted grep of the top
     statement and `TopInputs` for `Certificate|Replay|Witness|Oracle|Layout|LabelTable|
     CallPreserves|Obligation`; only fundamental inputs remain (acceptedness, compile
     equation, fuel/gas bounds, initial-state relation, script admissibility — the last
     being an environment contract, not compiler output).
  5. The ladder (RBS + NoCall extensions) reduced to one-line corollaries or deleted;
     premise-package count on the public path = 1 (`TopInputs`) + 1 (`Script.Admissible`).
- **Size:** ~3–5k lines new, ~5 agent-days; large net deletion.

**Total estimated spine cost: ~35–50 agent-days** (revised from 28–38 after the oracle
review), of which Phase 3 (~6 days) is roadmap work happening anyway and Phase 0 (~2
days) is standalone hygiene.

---

## 4. Risk register and falsification experiments

| # | Risk | Lean-specific failure mode | Falsification experiment (cheap, early) | Phase gated |
|---|---|---|---|---|
| R1 | Handler parameter breaks automation | Goals that close by defeq/`simp` on concrete interpreters stop closing with opaque `h : Handler H`; heartbeat blowup (cf. `CompilerPreservation.block/stmt` already needs `maxHeartbeats` wrappers, PROGRESS_LOG ~25866) | Scratch file: parameterize `Target.stepInstrResult` only, re-prove 3 Observer lemmas generically, compare heartbeats; threshold 3× | P1→P2 |
| R2 | Trace threading × mutual recursion × termination | `Functions/Semantics.lean:81` mutual block (15+ functions, `Prod.Lex` measures) must thread `(H × Trace)`; the block **already needs `set_option maxHeartbeats 800000` for its definition** (`:80`); incident class: 2026-05 loop-theorem rollback (fuel decrease hidden by a lambda, PROGRESS_LOG ~23074) | Scratch copy of the mutual block + accumulator pair; elaborates within the existing heartbeat budget, `termination_by` fires; ½ day | P1→P3 |
| R3 | Trace-append normalization churn | Recursive `τ₁ ++ τ₂` in executable semantics → simp fights | **Resolved by design:** accumulator-style traces adopted up front (§2.2, oracle-concurred); R1 scratch validates | P2 |
| R4 | `FueledSem` bundling hurts elaboration | Projection `run` won't unfold; universe/metavariable churn; handler unification failures | Phase 1 smoke test is exactly this; fallback: unbundled per-layer theorems sharing a statement shape via `abbrev` | P1 |
| R5 | Payload typeclass gaps | `BEq` derivable but not `LawfulBEq`; replay matching can't reach propositional equality | `#check (inferInstance : BEq/LawfulBEq CallRequest/CallResponse/…)` in Phase 1 before anything builds on matching | P1 |
| R6 | Congruence lemma weaker than needed | Cross-layer proofs need congruence *through the state relation*, not just handler-state relation | `runE_congr` stated with a relation slot from the start (costs nothing instantiated at `Eq`) | P3 |
| R7 | Spine vs in-flight lanes collision | Phases 4/5 absorb corridors other agents are extending; merge conflicts in mega-files; stale oleans | Hard sequencing rule (§3); PROGRESS_LOG announcements; Phase 0 makes conflicts file-local | P0,P4,P5 |
| R8 | Storage-equality gap surfaces as spine gap | ROADMAP ~7267–7274: open-call proof may not force contract-storage equality; spine restatement makes it visible and it could be misread as a spine defect; oracle confirms post-call world effects are genuine semantic premises | Named in Phase 5 gate; if unresolved, carried as a named `Script.Admissible` clause with a `bottleneck` log entry | P5 |
| R9 | Mega-file split breaks file-local structure | `private` decls, `local notation`/attributes, scoped instances, `set_option` regions crossing cut points | Pre-split scan (checklist in Phase 0); split `OpenLowering.lean` first; build after each part | P0 |
| R10 | Ladder consumers | Checked 2026-06-09: LayerAudit/scripts clean; the only Lean consumer is `NoCallRuntime.lean`, which extends the ladder (`:15376+`) — Phase 6 deletes extensions with/before base rungs; `abbrev` aliases for one phase | — | P6 |
| R11 | Request equality unachievable at some layer (post-oracle) | Trace equality forces `req₁ = req₂`; if any layer only achieves relation-equal requests (representation differences), the ∀-handler refinement is false there | Phase 2/3: inspect existing call/request preservation lemmas (`rg "CallSiteEq\|RequestRel\|OpenResultRel" EvmCompiler/Yul`) — current evidence (`callSite_eq_of_args`) says equality holds; if a counter-case appears, add the `eventRel` field (additive change) | P2–P3 |
| R12 | Import cycles from central Event module (post-oracle) | `Spine/Event.lean` needs payload types whose homes import upper layers | Phase 1a import-graph check; relocate payloads (`OpenExternal.lean` imports only `Yul.PrimSemantics` — contained) | P1 |
| R13 | Script/trace conflation regression (post-oracle) | Response-free or machine-computed events entering the replay script desynchronize replay (the oracle's `Ev.log/Ev.obs` counterexample) | **Resolved by design:** Script vs Trace separation + `scriptOf` projection; round-trip theorem stated over the projection; logs excluded from events entirely | P1 |
| R14 | autoImplicit/universe hygiene (post-oracle) | Sketches relying on auto-bound `H`, `r`, `τ` fail under `autoImplicit false`; `H : Type` blocks exotic handler states | All spine files `set_option autoImplicit false` from day one; `H : Type` accepted deliberately (no consumer above `Type`) | P1 |

### Asset triage: what survives, what is written off

**Reusable as-is (leaves under the spine):**
- `Reference.lean`'s semantic core: `StateRelConfig`, `SharedStateRel`, `ResultRel`, the
  induction core `RecursiveSourceBridgeWhenUpToAt` (:19934) and its per-construct leaves.
- The compiler and all compile-output structure lemmas (labels, PC-fit, assembler/encoder).
- The spill/layout/scratch corpus (`Functions/*`).
- `GasAware.lean` budget arithmetic and `XStepTrace`; stack-bound tables and
  `StackGuardAudit` checked constructors.
- Static classifiers: `usesCallCreate` scan, RDC-bounds deciders, `BoundaryKind`.
- **(post-oracle)** the `OpenResult` algebra and the `OpenLowering` per-construct lemma
  corpus — consumed through the Phase 5 adapter rather than rewritten.

**Reusable after restatement:** `ObserverOracle.lean`'s expression/statement replay
lemmas (Phase 4); `OpenRuntime` boundary-threading lemmas not covered by the adapter.

**Written off (deleted or permanent private compat):** the 39+ ladder rungs (RBS +
NoCall extensions), the ~40 premise-package structures and their plumbing, the 18 `With*`
interpreter clones and their 26+ equivalence theorems, `NoCallRuntime`'s parallel
corridor. Rough total: **~50–70k lines** — concentrated exactly where maintenance cost
is highest. (Down from the draft's 60–80k: the `OpenResult` algebra moved to the
"reusable" column.)

---

## 5. Cost/benefit honesty

**Observed baseline:** gas/msize — a "small" feature pair — cost ~35k lines and weeks of
multi-session agent time (the lane is still finishing); working figure ~48h+ per small
feature. Driver: each feature pays (re-derive N interpreters) × (re-prove M equivalences)
× (re-package premises) × (extend the ladder).

**Spine cost:** ~35–50 agent-days total (§3, post-oracle revision), of which ~6 are
roadmap work happening anyway (Phase 3) and ~2 standalone hygiene (Phase 0). Net new
architectural investment: **~27–42 agent-days**, with the two largest uncertainties
(automation through the handler parameter; Phase 5 porting) each gated by a cheap pilot
whose failure stops the spend (Phase 3 gate; Phase 5a gate).

**Post-spine feature cost:** a new observable = 1 Event constructor + ~6 emit sites +
per-layer refinement-case additions + 1 corollary; target ≤ 1/4 of baseline measured at
Phase 3 — **~1.5–2.5 agent-days per feature** instead of ~6–10.

**Remaining roadmap demand:** EXTCODE family, BALANCE/SELFBALANCE, EXTCODECOPY, LOG2–4
completion, TSTORE completion, SSTORE general contexts, BLOCKHASH-family completion,
open-argument semantics completion, return-data replay completion, then the Solidity
semantic layer. **8–12 feature-lane units.**

**Break-even:** at ~4–7 agent-days saved per unit, the spine pays for itself after
**~5–8 features** — inside the existing roadmap, before counting maintenance/
comprehension costs of 360k-line files and the compounding corridor-product risk (visible
in names like `RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsTopAssumptions`).

**The honest downside case:** if the roadmap stopped after ~3 more features, the spine
would not pay for itself in agent-time; Phases 4–6 should then be skipped. Phases 0–3
are net-positive even in that world (hygiene + a roadmap feature delivered + the
multiplication stopped from worsening). The phase order front-loads standalone value and
puts the go/no-go at Phase 3; Phase 5 carries its own internal kill-switch (5a pilot).

---

## 6. Oracle consultation (hostile critique) and disposition

Consultation: oracle conversation
`20260609-192915-event-spine-migration-plan-hostile-critique-5717b78a`
(GPT-5.5 Pro, effort xhigh, response `resp_02923f2e37d6b595006a28698c95a48199af40a7b1b4c2c370`),
prompt = the full draft plan + repository ground truth, mode = refute. The oracle's
bottom line on the draft: *"the proposed event spine is not a safe semantic
representation. The first thing that breaks is the universally quantified,
state-inspecting handler plus a single list serving as both input script and output
trace."* Both named breakages were real and are fixed in this revision. Disposition of
every finding:

### Accepted and incorporated

- **A2 — Script/trace conflation breaks record/replay.** The draft used one `List Event`
  as input script, output trace, and witness; the oracle's `Ev.log/Ev.obs` toy
  counterexample shows replay desynchronizing on response-free events. **Fix:** `Script`
  vs `Trace` as distinct roles, `Trace.scriptOf` projection, round-trip stated over the
  projection (§2.1–2.2); risk R13.
- **A3 — State-inspecting universal handler is untypeable and too strong.** The draft's
  `observe : … → EVMState → …` fails at source layers (`Reference.State ≠ EVMState`) and
  lets handlers distinguish relation-hidden states, falsifying ∀-handler refinement.
  **Fix:** stateless hooks; event kinds split by authority; machine-authoritative values
  computed by the target semantics without hook consultation; the canonical theorem gains
  the conditional observer clause — which is exactly the existing dry-run design,
  generalized (§2.2, §2.4–2.5).
- **A4 — "Collapses to one lemma" overstated; premise packages don't vanish.** Conceded
  and reframed throughout: the congruence lemma collapses *handler-variant equivalences*
  only; compiler-preservation content (request equality, response threading) remains
  per-construct work inside refinement instances; premise-pack *content* consolidates
  into `Script.Admissible` instead of disappearing (§0, §1.1, §2.2).
- **A5 — CALL/CREATE world effects are semantic premises.** Responses must carry post-call
  world facts; storage/balance/reentrancy contracts survive as script-admissibility
  clauses; the storage-equality gap (R8) is semantic work the spine exposes, not removes.
- **A6 — Don't delete `OpenResult` first.** Adopted wholesale: Phase 5 restructured
  around an `OpenResult.runScript` adapter with a mandatory single-construct pilot (5a);
  carrier retirement demoted to optional 5c; the 98k-line lemma corpus moves to the
  "reusable as-is" column.
- **A7 — RETURNDATACOPY bounds are not purely static.** Split: static window shape →
  acceptance; dynamic response adequacy → `Script.Admissible` clause (§1.3).
- **A8 — No-call corollary needs a semantic emission lemma, and precision about
  `observe`.** Both incorporated (§1.6, §2.4).
- **A9 — Phase 3 is not trivially cheap.** Scope discipline added: warm/cold access,
  balance-flow coherence, account-existence subtleties explicitly out of the named
  fragment; estimate raised (§3 Phase 3).
- **A10 — LOG events break on revert/rollback.** Conceded fully: logs stay in substate;
  no `logEmit` in the initial Event type; committed-logs corollary at the boundary (§1.13).
- **A11 — autoImplicit reliance.** All spine files `set_option autoImplicit false`;
  sketches read with explicit binders (§2 preamble; R14).
- **A12 — Recursive `++` traces.** Accumulator-style threading adopted as the design,
  not an option (§2.2; R3 resolved-by-design).
- **A13 — Import cycles from a central Event module.** Phase 1a payload relocation with
  an import-graph check; verified today that `OpenExternal.lean` imports only
  `Yul.PrimSemantics`, so the move is contained (§2.1; R12).
- **A14 — `deriving BEq` unverified / `LawfulBEq` needed.** Phase 1 `#check` gate (R5).
- **A15 — `FueledSem` universe/unfolding caveats.** `H : Type` accepted deliberately;
  reducible per-layer semantics values; unbundled fallback registered (§2.3; R4).
- **A16 — Exact compatibility equation false as drafted.** Replaced by
  projection-shaped compatibility (§2.2).
- **A17 — Phase 0 not zero-risk.** Renamed "low risk"; pre-split scan checklist added
  (private decls, local notation/attributes, scoped instances, `set_option` regions) (§3
  Phase 0; R9).
- **A18 — Phase 5 underestimated.** Raised to 15–30 agent-days; the 5a pilot is the
  internal kill-switch; total plan cost and break-even recomputed (§3, §5).

### Rebutted (with evidence) or partially rebutted

- **R1 — "Use trace relations, not equality; CompCert avoids global event equality."**
  Partially rebutted. CompCert needs `eventval_match`-style relations because its events
  carry memory-injection-sensitive values; this tower *canonicalizes requests at the
  boundary* and already proves call-site **equality** — `CallKind.callSite_eq_of_args`,
  publicly pinned (`LayerAudit.lean:1206`). Trace equality is therefore the right
  *default* here, and it is what makes corollaries one-liners. The oracle's concern is
  retained as risk R11 with a designed-in escape hatch (additive `eventRel` field) if any
  layer falsifies the equality assumption.
- **R2 — "Arbitrary scripts admit impossible worlds; query events prove preservation in
  impossible worlds."** Rebutted for the compiler theorem, conceded for end-to-end EVM
  claims. Compiler correctness should hold under *every* environment behavior — that is
  what makes it compositional; demanding world-coherence in the compiler theorem would
  weaken it. World-coherence axioms belong to the consumer of the theorem (as in
  CompCert, where external calls satisfy separately-stated axioms) and can be added as a
  strengthening of `Script.Admissible` without touching the spine.
- **R3 — "Safer alternative: normalize premise packages around existing interpreters
  first; no semantic refactor."** Rejected with history: this repo has run four-plus
  proof-organization consolidations (the oracle_*.md series, 2026-05-12…05-25, and the
  2026-06-08 boundary refactor) that did exactly this, and the multiplicative cost
  returned within weeks each time — the gas/msize lane's 35k lines arrived *after* those
  cleanups, and the ladder grew from 38 to 39 rungs during the audit itself. Packaging
  normalization without changing the representation is the strategy that produced the
  current state. The oracle's underlying caution — keep the existing corpus load-bearing —
  is honored by the build-alongside strategy and the adapter route (A6).
- **R4 — "ITrees exist for a reason; scripts trade local continuation obligations for
  global script-splitting obligations."** Partially conceded — that trade is real and is
  why Phase 5a pilots script-splitting on one construct before committing. But the
  trade's other side is decisive for this codebase: continuation-style `OpenResult`
  proofs could not be shared with the gas/msize lane (which had to invent a second,
  list-based mechanism) or the query lane (which would have needed a third). Linear
  scripts with one admissibility predicate are the only shape all three lanes share. The
  adapter keeps the continuation algebra where it is strongest (per-construct lowering
  proofs) and the script view where *it* is strongest (cross-layer statements).

### Oracle findings adopted as standing falsification tests

The oracle's Tests 1–5 (§7 of its response) are folded into the phase gates: Test 1
(handler/state mismatch) is moot under the stateless-hook design but kept as a Phase 1
negative test; Test 2 → R5/Phase 1 gate; Test 3 → R13 (resolved by design, re-checked by
the Phase 2 round-trip theorem); Test 4 → R11/Phase 2–3 inspection; Test 5 → §1.3's
dynamic-adequacy clause (confirmed: `BoundaryResponsesSatisfy`-class premises depend on
response return-data length and cannot be static).

---

## 7. Appendix: corrections to the audit's stated evidence

Verified 2026-06-09; re-verify before acting, the tree moves daily.

1. The ladder has **39** rungs in `RecursiveBridgeSupport.lean`, not 38 (lines
   348388–360124); it grew during the audit's own window — itself evidence for the
   diagnosis. It also continues *across files*: `NoCallRuntime.lean:15376+` stacks
   further `…_topNoCall*` rungs on `…_AllBoundsReserved_top`, so the real variant count
   is materially above 39.
2. `Reference.lean` is 84,709 lines / 1,837 theorems (audit: 72k / 1,438) — same file,
   grown.
3. The premise-package census in the Yul layer is **40** `TopAssumptions|Ready|Checked`
   declarations; the audit's "~64" is reachable only by also counting `*Facts`/
   `*Assumptions` packs. The order of magnitude — dozens — stands.
4. The "2026-05-17 mutual-recursion timeout" cited as a named incident does not appear in
   PROGRESS_LOG on that date; the real incident cluster: the loop-theorem rollback
   (~line 23074), the `CompilerPreservation.block/stmt` `maxHeartbeats` wrapper
   (~line 25866), the abandoned generic static-mode helper (~line 20414), the
   heavy-elaboration retreat on the runOpen no-overwrite theorem (~line 18941). R1/R2
   cite these.
5. The audit's "per-step diagram + stuttering measure" is amended (§0a, §2.3): the
   cross-layer spine uses big-step fueled refinement; small-step simulation stays local
   to Assembly.
6. The audit's "code-image reads become events" is amended (§1.5): own-code reads are
   state-relation material; only foreign-code queries are events.
7. The audit's `FeatureConfig` as a bundled hypothesis record is amended (§2.4): features
   dissolve into the quantified script + `Script.Admissible`, `StateRelConfig` fields,
   and static event-kind predicates feeding one-line corollaries.
8. *(post-oracle)* The audit's "one global Event type … as the universal observation"
   needs the §6 qualifications: scripts ≠ traces; logs are not events; observer events
   are conditional, not refinement-preserved; and `OpenResult` is adapted, not replaced.
