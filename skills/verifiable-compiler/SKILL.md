---
name: verifiable-compiler
description: "Use when the user wants Codex to build or make sustained progress on an end-to-end formally verified compiler in Lean."
---

# Verifiable Compiler

Use this skill for Lean-first verified compiler work. The primary artifacts are
Lean definitions, compiler functions, semantics, relations, and checked
theorems. Tests, fixtures, docs, and external tools are support
evidence only.

The default shape is: start near
the target, add one semantic abstraction layer at a time, prove the adjacent
lowering completely for the source language in scope, then move up.

## Start Or Resume

1. Inspect local state before planning:
   - `git status --short` (if this is not a git repo, initialize with a commit);
   - `lakefile.lean`, `lean-toolchain`, root modules, theorem files, tests, and
     recent build scripts;
   - `ROADMAP.md` and `PROGRESS_LOG.md`, if present.
2. Call `get_goal`. If no active goal exists, create one whose objective
   matches the user's concrete request in this turn. For sustained build
   requests, include the requested compiler scope and the end-to-end theorem
   standard. For narrower work, keep the objective scoped to that audit,
   proof-debugging, refactor, architecture review, skill edit, or pass-specific
   task.
3. When starting or resuming sustained verified-compiler work, say explicitly
   that this workflow is using `$verifiable-compiler`, and remind the user
   that future continuation requests should mention `$verifiable-compiler`.
   Do this at start/resume or handoff, not in every status update.
4. Use exactly two project docs by default:
   - `ROADMAP.md`: sparse checklist and current public spine.
   - `PROGRESS_LOG.md`: flat timestamped log of proofs, tests, bottlenecks,
     architecture risks, deletions, and status.
5. Every time the agent restarts from conversation compaction, append a short
   timestamped `PROGRESS_LOG.md` entry before continuing, including for narrow
   follow-up tasks. Name it as a compaction resume, summarize the current
   objective/checkpoint in one sentence, and keep it concise.
6. Do not create feature matrices, trust ledgers, design histories, or incident
   reports unless the user asks. If legacy docs exist, read them as context but
   do not keep adding synchronized truth there.

## Git Checkpoints

- Commit verified checkpoints as you go. After a meaningful theorem, boundary
  cleanup, refactor, or audit passes its relevant build/axiom checks, create a
  focused git commit before starting the next substantial proof thread.
- Keep commits honest: include only project files that belong to the verified
  checkpoint, and mention the Lean build or axiom audit that passed. Do not
  commit huge build logs, scratch outputs, or unrelated generated clutter.
- If the user says all current work belongs to the agent, treat the dirty tree
  as owned work for staging purposes, while still keeping commits coherent and
  avoiding accidental inclusion of temporary logs or secrets.

For a broad build request, the goal is not complete until concrete Lean theorem
statements connect every source-language feature in scope to the declared target
interpreter. Do not silently reinterpret a request for a source language as a
request for a convenient accepted fragment.

For any active goal that asks to complete a layer or compiler pass, do not stop
while the public theorem still takes compiler-generated evidence as an
unproved input. Treat these as blockers, not residual assumptions: generated
layout records, compilation certificates, replay certificates, whole-program
call or callee-preservation obligations, return-layout obligations, generated
label/token uniqueness tables, and proof-carrying emitted-code segments. It is
acceptable to expose fundamental semantic or resource premises such as source
acceptedness, input run/evaluation, initial-state relation, fuel/gas bounds, or
explicit code-size/no-overflow bounds, but any compiler artifact that can be
computed from the source program must either be constructed by a checked Lean
theorem or remain an explicitly unfinished goal.

## Theorem-Truth Checks

Before major proof grinding, check whether the theorem is true as quantified.
Try to find small counterexamples involving arbitrary target PC, fuel-zero
states, stack height, static-context restrictions, gas observations, external
calls, revert/error outcomes, and unsupported source constructs.

If a target fact is only true for traces produced by accepted source programs,
state it over those actual traces or derive it from source-facing premises. Do
not keep a globally quantified target premise just because it is convenient for
the proof.

When a theorem is false or overbroad, fix the statement before adding wrappers,
compatibility lemmas, or local heartbeats. Record the correction in
`PROGRESS_LOG.md` as `theorem-boundary`, `deletion`, or `architecture-risk`.

Once the project freezes its public specification — hash-pinned theorem
statements, a frozen-closure checker, or a challenge/scoring regime that
measures rewrites against a fixed theorem — this workflow changes mode. A
frozen statement is an immutable interface: do not restate, weaken, or
"improve" it, even when the boundary looks fixable; rewrites and
optimizations must reprove the exact frozen statement. If a frozen statement
turns out to be false or overbroad, that is a project-level incident — report
it and get an explicit unfreeze decision from the user instead of editing
around it. Run the project's freeze gates (hash and closure checks) alongside
the usual build and axiom audits before calling any change complete.

## No Unproven Compiler Paths

Do not introduce, wire in, or commit an unproven path that emits compiler output
or deployable bytecode. This includes paths named `unchecked`, `unsafe`,
`artifact-only`, benchmark-only, fallback, fast path, or executable shortcut.
If such a path is used by the compiler, bytecode/artifact generation, bridge
runner, benchmark harness, or user-facing validation, it must either be the
checked theorem path or have a Lean theorem proving equality/refinement to the
checked theorem path, with an axiom audit showing only standard Lean axioms.

Executable variants are allowed only when a checked equality/refinement
theorem connects them to the proof-facing definition, and all
callers that emit bytecode can be transported back to the public preservation
theorem through checked lemmas. Existing unproven output paths are blockers to
remove, prove equivalent/refining, or quarantine as non-compiler diagnostics;
do not commit new work that relies on them.

## Core Strategy

Build a target-up semantic tower, one complete layer at a time:

1. Choose or define the declared target interpreter and observation model.
2. Define the lowest useful layer above that target.
3. Add exactly one real semantic abstraction in the next higher layer.
4. Give that layer syntax, semantics, wellformedness/acceptance, a relation to
   the lower layer, compiler/lowering, and preservation theorem. You can add slices
   to that layer one at a time, but the layer needs to be feature-complete,
   not a toy version of the language, before moving on. Its feature set should
   cover the whole abstraction that belongs at that layer and, as far as possible
   before higher abstractions exist, match how that feature works in the source
   language being targeted.
   The semantics must be an independent interpreter or evaluation relation over
   that layer's own syntax. Defining the layer's run/eval as "lower/compile this
   program, then run the lower layer" is not a valid source semantics, except for
   an explicitly named transparent adapter boundary with no new source constructs
   and a recorded audit note.
   The semantics must also abstract the feature this layer introduces. Do not
   define a new source construct by exposing the lower representation it is meant
   to hide. For example, a locals/frame layer should have a named-environment
   source semantics; stack slots, layout depths, swaps, pops, or frame encodings
   belong in that layer's compiler/lowering relation and proof, not in the
   source interpreter used by higher layers.
5. Compose the new theorem into the public spine.
6. Run a brief theorem-boundary checkpoint before moving on.
7. Only then add the next layer.

Example of good abstraction steps include labels over byte offsets, structured control over
jumps, locals/frames over stack slots, expressions over primitive stack code,
functions over entry labels, or objects/modules over flat functions.

Bad layers are story-shaped features (`let-if-assign-return`), parser fixtures,
one-off combinations (`if` inside `for`), or helper representations with no
independent semantic contract.

Before implementing a broad layer, run this checklist. This is a thinking
checkpoint, not a request to create new documents:

- Grammar frozen: every construct in scope is named, and every tempting
  construct out of scope is explicitly excluded.
- Prior art checked: inspect the existing lower layer, adjacent completed
  layers, and any sibling worktree or earlier implementation the user points to
  before inventing a new proof route. Reuse proven theorem shapes when they
  fit; record why they do not if you diverge.
- Semantics frozen: outcomes, errors, effects, divergence/fuel behavior, and
  observable state are clear for the accepted subset.
- Theorem-truth checked: known counterexample shapes such as arbitrary PC,
  fuel-zero target states, stack/resource exhaustion, static context, gas
  observability, and external effects have been ruled out or reflected in the
  theorem boundary.
- Interpreter independence checked: `run`/`Eval` is not merely lower-layer
  execution after compiling/elaborating the source; any exception is an explicit
  transparent adapter boundary, not a completed compiler layer.
- Abstraction boundary checked: the layer's source semantics hides the lower
  representation that its new feature abstracts. Any proof terms, layouts,
  slots, continuations, frame encodings, return tokens, cleanup code, or other
  lower-level machinery needed to implement the feature live in the compiler
  and preservation proof, not in the source interpreter or the interface used by
  higher layers.
- Lower capabilities pass through: the layer does not silently shrink the
  already-verified lower language surface.
- Accepted restrictions classified: every nontrivial `Accepted`/`WF` predicate
  is checked against the requested scope. An explicit predicate name is not by
  itself a justification; if it excludes lower-layer behavior because the proof
  route or representation is unfinished, keep the layer incomplete unless the
  user explicitly narrowed the language.
- Public theorem sketched: adjacent theorem and composed theorem have the right
  shape before helper proofs begin.
- Proof interface sketched: layout, freshness, state relation, continuation,
  resource, or environment assumptions are bundled when they are conceptually
  one invariant.
- External/resource boundary classified: gas, fuel, code size, stack depth,
  static-context restrictions, storage/account state, and external responses
  are either modeled by source semantics, rejected by acceptance, or exposed as
  explicit source-facing premises.
- Temporary scaffolds named: replay/certificate/helper routes have a planned
  replacement theorem or are kept private.
- Public certificate boundary checked: if a theorem still takes a compiler
  certificate, layout witness, replay witness, proof-carrying emitted-code
  segment, or generated-label table as an input, do not call the pass complete
  unless that certificate is itself generated by a checked compiler theorem or
  the user explicitly accepted it as a trusted input format.
- No public call oracle: for recursive source features, the public theorem must
  not take an all-callees-preserve, all-functions-preserve, replay, or call
  obligation premise. Discharge those obligations by source-fuel, evaluation,
  or well-founded induction, leaving only explicit resource bounds or source
  acceptedness assumptions at the public boundary.
- Public theorem grep: before declaring success, search the public spine for
  names like `Certificate`, `CompilationCertificate`, `Replay`, `Obligation`,
  `ProcPreserves`, `Layout`, `Evidence`, `CallPreserves`, and project-specific
  certificate names. Any remaining public occurrence must be either generated by
  a checked constructor theorem or justified as a fundamental resource/input
  premise in the audit entry.

## Source-Language Completeness

When the user asks for a verified compiler for a named source language or layer,
the default obligation is the complete semantics of that source language layer.
`Accepted`/`WF` may reject malformed, ill-scoped, ill-typed, or otherwise
semantically invalid programs, but it must not reject implemented source
constructs merely because they are proof-inconvenient unless the user explicitly
approved a fragment.

Before marking such a goal complete:

1. Inventory the source grammar against the source semantics and compiler.
2. For every construct, record one status: supported and covered by the theorem;
   semantically invalid and rejected by WF/Accepted; or explicitly out of scope
   by user-approved fragment boundary. Apply the same classification to every
   `Accepted`/`WF` field, not only to syntax constructors.
3. If the source is a named external or imported language, name the exact
   reference semantics being targeted and require a checked theorem from that
   semantics to the compiler source semantics; elaboration through the compiler
   is not enough by itself.
4. Confirm the source semantics is an independent interpreter or evaluation
   relation over the source syntax. If `run`/`Eval` delegates through `compile`,
   `lower`, `elaborate`, `toLower?`, or similar, the layer is incomplete until
   it has its own semantics and a checked equivalence/preservation theorem, or
   the user explicitly accepts it as a transparent adapter boundary.
5. Check that supported constructs include all outcomes their source semantics
   admits, including errors, halts, resource failures, divergence/fuel behavior,
   traces, and external observations claimed by the theorem.
6. Confirm theorem statements quantify over the real source semantics, not only
   over a compiler-success witness or replay certificate.
7. If any source construct is missing semantics or theorem coverage, keep
   working or report a blocker; do not call the compiler fully verified.

Add this source-language audit as its own `audit` entry in `PROGRESS_LOG.md` at
major layer boundaries and before declaring an end-to-end theorem complete.

Share source and target components where this reduces real proof burden:
values, arithmetic, memory/storage models, errors, traces, environments, and
external state. Do not share away the compiler obligation. Source and target
control semantics, layout, resource assumptions, and observations must remain
explicit.

It is valid for shared primitive operations to pass through the same semantics
across many layers when they are not the abstraction being introduced by that
layer. For example, arithmetic, hashing, memory/storage operations, and
explicitly shared external effects may reuse the same primitive meaning all the
way up to the source language. That exception does not apply to a feature whose
purpose is to hide a lower representation: locals should hide stack slots,
structured control should hide jump encodings, functions should hide
return-token/frame conventions, and so on.

## Boundary Checkpoints

At major semantic pass boundaries, pause briefly before moving upward:

1. Name the adjacent preservation theorem and the composed public spine theorem.
2. Confirm syntax, semantics, acceptance/WF, lowering, relation, and
   observation/outcome model exist for the accepted feature set.
3. Check for silent narrowing: `Accepted`/`WF` predicates must not exclude
   supported behavior only because the proof route is unfinished.
4. Check for theorem-boundary leaks: public theorem statements should not expose
   lower representation details, generated certificates, replay witnesses, or
   stale compatibility routes unless those are explicitly trusted inputs.
5. Run the narrowest meaningful build, and `#print axioms` or the local
   equivalent for public theorem(s) when practical.
6. Record one concise `audit` entry in `PROGRESS_LOG.md` with theorem names,
   command run, axiom result, and any remaining assumptions or unsupported
   behavior.

If the checkpoint finds a shortcut, stale public route, or accepted feature
outside theorem coverage, fix it, explicitly narrow the layer with the user, or
report the blocker.

## External Effects And Resources

For external effects such as calls, chain state, storage, balances, precompiles,
or environment responses, default to an open request/response protocol at the
compiler theorem boundary. Concrete world simulation is useful only when the
theorem is explicitly about that world model.

For resource-sensitive behavior such as gas, fuel, stack limits, code-size
limits, static context, memory growth, or no-overflow obligations, prefer
source-facing premises and actual-trace lemmas. A target-side runtime fact is
acceptable only when it is derived from the accepted source run, the checked
compiler output, and explicitly named resource bounds.

If a source primitive observes target resource state directly, either include
that observation in the source semantics and prove it end to end, or reject the
primitive in the accepted language. Do not patch it with future-answer or replay
oracles in the main public theorem.

## Preservation Shape

The main public theorem for an adjacent pass is a same-observation theorem.
Replay certificates, traces, and local simulations are proof machinery; they
should not be the public theorem boundary once the layer is stable.

Use this shape, adapted to local names:

```lean
theorem compile_sound
    (hWF : Hi.WF program)
    (hCompile : Hi.compile program = lower)
    (hEval : Hi.Eval program initial obs)
    (hRel : StateRel initial lowerInitial) :
    Exists fun lowerObs =>
      And (Lo.Eval lower lowerInitial lowerObs) (ObsRel obs lowerObs) := by
  ...
```

When both semantics are executable and deterministic, this may be an equality
theorem over `run`; when the layer erases representation details, use `ObsRel`.
The important claim is that the lower semantics has the same observable program
result, not merely that some hand-written replay witness exists.

Prefer strengthened, compositional theorem statements from the beginning.

Lean theorem boundaries matter. If witness data is derived from a `Prop`
relation such as a source run, evaluation derivation, or preservation theorem,
the public result should usually expose `∃` or `Nonempty` evidence. Do not make
the public route depend on returning an arbitrary structure in `Type` unless
that structure is produced by computation or is passed in as explicit data.

For expression-like code generation, use an arbitrary continuation/suffix:

```lean
theorem compile_correct_aux (e : Expr) (k : Code) (s : Stack) :
    run (compile e ++ k) s = run k (eval e :: s) := by
  induction e generalizing k s with
  | ... => ...
```

For statement/control layers, generalize this idea. Use whichever local shape
matches the layer:

- arbitrary code suffix;
- continuation or defunctionalized continuation;
- evaluation/control context;
- entry/destination labels;
- layout and no-wrap assumptions;
- state relation at an exact target PC, such as `RelAt`;
- outcome relation for normal return, halt, revert, throw, break/continue, or
  other abrupt exits.

The public proof route should be structural: sequence, context, branch, loop,
call, frame/layout, and outcome lemmas compose into the same-observation theorem.
If theorem names start encoding whole programs or feature combinations, stop and
replace them with generic recursive/compositional theorems.

If a proof is becoming a long run of nearly identical constructors or opcodes,
pause before continuing. Look for a semantic-family classifier, pass-through
lemma, source syntax traversal, or relation-preservation theorem that proves the
common case once and leaves only genuinely distinct cases as wrappers.

If several consecutive changes add wrappers, adapters, callbacks, bridge
aliases, or compatibility routes without shrinking the public assumptions, stop
and inspect the theorem boundary. Usually the right next patch is deletion or
restatement, not another adapter.

After a few helper lemmas for a new construct, inspect the next theorem
statement. If it needs many independent PC, label, freshness, layout, resource,
or environment premises, introduce a small structure or relation that names that
interface. Long premise lists are usually missing abstraction, not proof
progress.

Wherever feasible, derive full preservation proofs from accepted source runs;
treat assumed replay/certificate witnesses as temporary scaffolding, not the
public theorem boundary.

Compiler-generated evidence is not a fundamental assumption. Before declaring a
layer done, try to prove a checked constructor for every public certificate:
layout, freshness, label resolution, call-site table inclusion, PC-fit, typed
continuation boundary, and compiler-output equality. If construction is not yet
proved, the layer is not complete; log the missing constructor and keep working
or explicitly report the blocker.

Do not hide unfinished compiler evidence inside source acceptance. `Accepted`
may bundle source wellformedness, source semantic safety, checked resource
limits, or user-approved trusted-input contracts, but it must not contain a
compiler-generated layout, replay witness, call-site table, label-resolution
proof, procedure-body preservation proof, or semantic call oracle unless the
skill user explicitly chose proof-carrying source input as the trusted source
format. If a preservation theorem needs such evidence, either generate it with
a checked compiler theorem or keep the layer incomplete.

For recursive source features such as procedure calls, function calls,
recursive loops expressed through fuel, or mutually recursive declarations, the
default discharge route is induction on source fuel or on the relational
evaluation derivation. Do not replace this with an assumed "all callees
preserve" oracle. If a temporary all-callee/call obligation is introduced, keep
it private, give it a fuel-bounded replacement plan immediately, and do not
report the layer complete until the public theorem derives it.

Avoid brittle fusion lemmas. A lemma about `if` inside `loop`, `switch` inside
`for`, or assignment plus branch plus return is not a milestone unless it is a
private stepping stone being replaced immediately by generic `seq`/`if`/`switch`
`loop`/`outcome` composition. If a fused lemma remains useful, log it as a
`shortcut` or `architecture-risk` and keep it out of the public spine.

CPS is a tool, not a mandate. Raw higher-order continuations can make Lean
terms huge. Prefer a small continuation/context interface that keeps compiled
programs folded and lets induction hypotheses apply under arbitrary suffixes.

## Accepted Subsets

Full preservation means full semantics for the accepted subset, but an accepted
subset is allowed only when the user requested a fragment or when the source
language definition itself is intentionally smaller than its parser or host AST.
If the user asks for a compiler for the whole source language, the accepted
subset must be source-complete except for malformed or semantically invalid
programs.

Do prove all relevant outcomes of accepted programs: success, errors, halts,
resource failures, traces, divergence/fuel behavior, and external observations
that the theorem claims to model.

Do not prove only the terminating happy path unless the theorem name and
accepted checker explicitly say that is the claim. Unsupported behavior should
be rejected by `Accepted`/`WF`, guarded by explicit theorem assumptions, or
called executable-only.

Keep these notions separate:

- parser/decoder success;
- semantic acceptance or wellformedness;
- compiler success;
- certificate checking;
- target execution success.

Accepted input must not mean "the compiler returned `some`." Compiler-success
theorems are useful, but they are weaker than accepted-input theorems.

## Lean Blowup Rules

Treat timeouts and heartbeat explosions as architecture feedback, not merely
tactic problems.

Do not let Lean normalize whole compiled programs as a proof strategy.

## Context Hygiene

Preserve context for theorem state, not logs or repo tours:

- Before every read, search, or build, name the narrow question it should
  answer; avoid fresh "getting bearings" sweeps after a handoff identifies the
  next target.
- Keep build output out of context: redirect noisy `lake build` logs to `/tmp`
  and inspect only `error:` lines plus the smallest needed neighborhood.
- Scope searches tightly. Prefer module-specific `rg`, `rg -n -m`,
  `rg --files`, `git diff --stat`, and short line windows; broad repo-wide
  `rg`, full diffs, generated-file searches, and wide `sed` ranges are last
  resorts.
- On resume, trust the latest handoff/progress log unless a specific line must
  be checked.
- After any large tool output, retain only theorem names, file/line pointers,
  failing goals, and the concrete next patch.

Prefer:

- structural lemmas over syntax/control contexts;
- one-step semantic interface lemmas;
- semantic classifiers for large opcode/operator families;
- small public wrapper theorems around imported or recursive definitions;
- explicit state/layout relations instead of massive record equalities;
- named intermediate definitions to share structure;
- `simp only [...]` with local simp sets;
- controlled unfolding of one definition at a time;
- narrow module builds: `lake build Module.Name` or `lake env lean path/File.lean`.
- recursive theorem families whose structurally decreasing syntax argument comes
  early in the argument list, with `termination_by` added before the proof grows.

Avoid:

- broad `simp_all` over compiler and interpreter definitions;
- unfolding imported dispatchers across many constructors;
- one theorem that case-splits over a large instruction set and tries many
  `first | change ...` branches;
- exposing large recursive compiler definitions as global simp rules;
- proof terms that inline every compiled instruction or generated label;
- broad imports in theorem files;
- adding local heartbeats before checking whether the theorem/interface shape is
  wrong.
- continuing a proof whose statement has become a page of plumbing. Bundle the
  invariant and prove the compiler supplies it.

When widening primitive operations, classify by semantic family or require a
small proof-carrying/accepted primitive interface. Prove PC/resource/state
insensitivity once per family, then use a one-line wrapper per constructor. Do
not ask Lean to rediscover the same dispatcher facts for every opcode.

## Primitive Classifiers

For large primitive or opcode surfaces, introduce a small semantic-family API
before broadening the source layer. This API should be a proof boundary, not a
second unverified semantics.


## Documentation And Logs

Code and theorem statements are the source of truth. Before reporting status,
inspect the actual theorem names, statements, public imports, and build output.

`ROADMAP.md` should stay sparse:

```markdown
# Roadmap

## Public Spine

Accepted AST -> LayerA -> LayerB -> Target interpreter

## Next Layer

- [ ] Interface: syntax, semantics, WF, relation
- [ ] Theorem-truth check and external/resource boundary
- [ ] Complete source-faithful feature set for this layer
- [ ] Lowering function
- [ ] Adjacent same-observation theorem
- [ ] Composed public theorem
- [ ] Boundary checkpoint
```

`PROGRESS_LOG.md` is append-only and flat:

```markdown
- 2026-05-12 18:17:26 - proof - proved `CompilerPreservation.block` and `compile_whole_program_sound_of_run`; command `lake build`; result green.
- 2026-05-12 18:20:00 - architecture-risk - primitive widening proof unfolds full opcode dispatcher; replace with semantic family interface before adding more ops.
```

Use tags such as `proof`, `test`, `audit`, `bottleneck`,
`theorem-boundary`, `architecture-risk`, `shortcut`, `consolidation`,
`deletion`, and `incident`. For risks and shortcuts, name the artifact, why it
is risky, and the generic theorem/interface that should replace it.

Keep logs current, not just append-heavy. When a bottleneck, shortcut, or risk
is resolved or superseded, add a short entry saying so and name the replacing
theorem or interface. Do not leave stale warnings that still read as active.

## Git Preservation

Use git to preserve meaningful theorem-bearing states. Commit only coherent
milestones, preferably green:

- initial Lean package setup;
- first target-reaching theorem;
- new public layer or theorem boundary;
- accepted-language/theorem-boundary change;
- byte encoder or real-machine bridge;
- deletion of obsolete fixture/story routes;
- audited stable proof milestone.

Never revert user changes. Before pausing or finishing substantial work, run
`git status --short` and make the handoff state clear.

## Anti-Patterns

Stop and repair the architecture if any of these appear:

- full high-level language first, proofs later;
- theorem ends at an IR while the claim says end-to-end;
- special theorems for `if` inside `loop` or other combinations;
- fused feature lemmas become public proof routes instead of temporary private
  scaffolding;
- parser helper recognizes a whole story instead of independent constructs;
- semantic classifier or helper interpreter used as if it were the real target
  without an equality/refinement theorem;
- source semantics changed to match a compiler bug;
- broad public imports retain obsolete compiler routes;
- concrete external-world simulation is used where an open protocol is the real
  theorem boundary;
- observed target resources such as gas are patched by replay/future-answer
  oracles instead of source semantics, acceptance rejection, or explicit
  source-facing premises;
- wrapper, adapter, callback, or compatibility-route churn continues without
  reducing public assumptions;
- proof relies on `sorry`, `admit`, new `axiom`, `unsafe`, `partial`, or
  proof-critical external assumptions without excluding them from the claim;
- tests or external review are treated as verification;
- Lean timeout is answered by adding more feature code.

## Completion Gate

Do not call the compiler verified because tests pass, the compiler runs, or a
scaffold theorem exists.

Before reporting a verified milestone:

1. Inspect the accepted compiler path.
2. Name the exact top theorem(s).
3. Run the narrowest meaningful build command, and full build when practical.
4. Run `#print axioms` or the local equivalent on public top theorem(s) when
   practical.
5. Scan for `sorry`, `admit`, `axiom`, `unsafe`, and `partial`.
6. Check public imports for obsolete fixture/story/legacy routes.
7. Check public theorem arguments for compiler-generated certificates or layout
   evidence. They must be discharged by checked constructors, be private helper
   inputs, or be explicitly named as trusted external inputs approved by the
   user. Otherwise keep working.
8. Inspect `Accepted`/`WF` records used by the public theorem. They must not
   smuggle in compiler-output equality, label layout, replay certificates,
   call/return layout, generated-token uniqueness, or semantic preservation
   oracles. They also must not exclude lower-layer capabilities merely because
   the representation or proof is unfinished. If they do, split those fields out
   and discharge them, explicitly narrow the requested source language with the
   user, or keep the milestone incomplete.
9. Check that resource and external-effect premises are source-facing or
   actual-trace-derived, not globally quantified target facts.
10. State remaining assumptions and unsupported features plainly.

The goal is complete only when every source-language feature in the requested
scope has a checked path from trusted input or AST through acceptance,
semantics, compiler/lowering, target interpreter, and theorem. If a fragment was
explicitly requested, say so in the theorem names or surrounding API and audit
the fragment boundary. Otherwise report the current work as a theorem-bearing
milestone and keep working on the missing source semantics.

## References

Load only when useful:

- `references/verified-compiler-patterns.md`: theorem-boundary patterns and
  classic verified-compiler references.
- `references/process-lessons.md`: earlier process failures to avoid.
