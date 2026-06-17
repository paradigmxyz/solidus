# Minimal Horizontal Open-Effects Roadmap

Created: 2026-06-16
Revised: 2026-06-17

## Objective

Prove checked support for:

- `CALL`
- `CALLCODE`
- `DELEGATECALL`
- `STATICCALL`
- `CREATE`
- `CREATE2`

while preserving the horizontal compiler architecture:

```text
Yul
  -> Functions
  -> allocated Locals/Expressions
  -> Structured
  -> TypedCfg
  -> Assembly
  -> bytecode
```

The proof must also preserve the exact order of:

- `gas()`
- `msize()`
- external calls
- contract creation
- ordinary world effects such as logs and storage updates

The migration must not restore a Yul-owned vertical proof corridor, duplicate
control interpreters, observer-specific compilers, replay certificates, or
generic pass-by-pass backward adequacy.

## Architectural Reset

The first draft used:

- an open result tree;
- a relation on open results;
- source and target external-context machines;
- a future-closed context bisimulation with `forth` and `back`;
- per-pass `OpenEffectEquiv` records;
- context plugging and behavior-set semantics.

That is more machinery than compiler correctness needs.

The revised architecture has four shared ideas:

1. The active program is immutable and is not part of mutable world state.
2. Source and target share one code-erased `OpenWorld`.
3. Every observable suspension uses one `Interaction` tree.
4. Every adjacent theorem concludes the same structural
   `Interaction.Rel` directly.

Concrete external worlds are optional interpreters of the tree. They are not
part of the compiler-correctness spine.

## Core State Split

The semantic state is conceptually:

```text
immutable active program
+ immutable transaction/chain context
+ protected execution frame
+ protected machine/control state
+ mutable OpenWorld
```

### Active Program

The active Yul contract is an explicit evaluator parameter. Internal Yul
function calls and dispatcher entry resolve against this parameter.

The active target program or bytecode is likewise an explicit program
parameter or protected frame component.

Neither is looked up from the mutable account map.

This removes the current duplication in which `program.contract` is installed
into both:

- `ExecutionEnv.code`;
- the active owner's `Account.code`.

The existing `codeOverride` path already demonstrates that the evaluator can
carry its active contract independently. The migration makes that path
canonical and removes the account-map lookup from internal Yul calls.

### Static Context

Keep transaction and chain inputs in one immutable shared view:

```lean
structure StaticContext where
  origin : Address
  gasPrice : Nat
  header : BlockHeader
  blockHistory : ProcessedBlocks
  genesisHeader : BlockHeader
  initialAccounts : InitialAccountMap
  blobVersionedHashes : List ByteArray
```

The exact fields should follow the supported primitive set. Source and target
receive the same `StaticContext`.

This context is available to a concrete external strategy, but it cannot be
changed by a CALL/CREATE answer. Target-only gas counters and transaction
receipt construction remain outside compiler state equivalence.

### Protected Frame

The protected frame contains data that an external call cannot rewrite:

- code owner;
- sender and caller/source;
- apparent call value;
- calldata;
- static permission;
- depth;
- active code byte image;
- frame-local call metadata.

The source active Yul AST is separate from the frame's active byte image.
`CODESIZE` and `CODECOPY` read the active byte image. Internal source function
calls read the explicit active Yul program.

### Protected Machine And Control

The external environment cannot directly mutate:

- locals;
- stack;
- memory;
- active memory words;
- return continuation;
- program counter;
- CFG label;
- compiler spill slots;
- compiler return tokens;
- source control mode.

CALL/CREATE response application updates the permitted caller-local fields,
such as return data, output memory, and the result word.

### Code-Erased Open World

External accounts do not need Yul ASTs. Define one common account view:

```lean
structure OpenAccount where
  nonce : Word
  balance : Word
  storage : Storage
  transientStorage : Storage
  codeBytes : ByteArray

structure OpenWorld where
  accounts : AddressMap OpenAccount
  substate : Substate
  createdAccounts : AddressSet
```

The exact representation may reuse existing map and set types. The required
semantics are:

- account existence is represented by map membership;
- empty-account tests use `codeBytes`, nonce, and balance;
- `EXTCODESIZE`, `EXTCODECOPY`, and `EXTCODEHASH` use `codeBytes`;
- logs, refunds, warm accesses, touched accounts, and selfdestruct state remain
  in the shared substate;
- current-contract storage and transient storage are ordinary world fields and
  may change during reentrancy;
- newly created accounts need only an observable byte image, not a Yul AST.

Immutable transaction snapshots, block history, and target-only gas accounting
do not belong in `OpenWorld`.

### Compatibility With Existing State Types

The first migration need not rewrite the imported EvmYul structures.

Provide projections and updates:

```lean
OpenWorld.ofYulState
OpenWorld.installYul
OpenWorld.ofEvmState
OpenWorld.installEvm
```

The source installer may preserve existing Yul AST fields for old accounts and
use an arbitrary default AST for new accounts. Canonical compiler semantics
must never inspect those fields.

Required laws:

- projecting an installed world returns that world;
- installing a world preserves the protected frame;
- installing a world preserves machine and control state;
- source and target world projections are exactly equal in every compiler
  state relation;
- canonical source world observations depend only on `OpenWorld`.

This treats legacy Yul code fields as compatibility ghosts until they can be
removed upstream.

## One Interaction Protocol

### Observable Requests

Use one dependent query family:

```lean
inductive ResourceQuery where
  | gas
  | msize

inductive ExternalRequest where
  | call : CallRequest -> ExternalRequest
  | create : CreateRequest -> ExternalRequest

inductive Query where
  | resource : ResourceQuery -> Query
  | external : OpenWorld -> ExternalRequest -> Query
```

An external query contains the exact pre-interaction `OpenWorld`.

This is necessary because ordinary source steps may change storage, transient
storage, logs, access lists, balances, or other world fields between two
external interactions. Including the pre-world makes those changes visible to
the external strategy and makes ordering part of query equality.

### Observable Answers

```lean
structure CallResponse where
  success : Bool
  returnData : ByteArray
  postWorld : OpenWorld

structure CreateResponse where
  address : Word
  returnData : ByteArray
  postWorld : OpenWorld

def Answer : Query -> Type
  | .resource _ => Word
  | .external _ (.call _) => CallResponse
  | .external _ (.create _) => CreateResponse
```

Answers deliberately exclude:

- effective forwarded gas;
- returned gas;
- child execution traces;
- child-local state;
- source or target machine state;
- compiler allocation artifacts.

The post-world is the committed caller-visible world after the external
interaction. Rolled-back child states are not represented.

### Interaction Tree

```lean
inductive Interaction (Error Result : Type) where
  | done : Except Error Result -> Interaction Error Result
  | request :
      (query : Query) ->
      (Answer query -> Interaction Error Result) ->
      Interaction Error Result
```

Define `pure`, `error`, `bind`, and `map` once.

This one tree records the total order between resource observations and
external interactions. It is finite because every current evaluator is
fuel-bounded.

### Structural Relation

```lean
inductive Interaction.Rel
    (doneRel : Except ErrorS ResultS -> Except ErrorT ResultT -> Prop) :
    Interaction ErrorS ResultS ->
    Interaction ErrorT ResultT ->
    Prop where
  | done :
      doneRel source target ->
      Interaction.Rel doneRel (.done source) (.done target)
  | request :
      (forall answer,
        Interaction.Rel doneRel
          (sourceResume answer)
          (targetResume answer)) ->
      Interaction.Rel doneRel
        (.request query sourceResume)
        (.request query targetResume)
```

The request constructor uses the same exact `query` on both sides. The same
exact answer is supplied to both continuations.

This relation means:

- source and target expose the same effect kind;
- external pre-worlds are equal;
- external requests are equal;
- resource query kinds are equal;
- every possible shared answer preserves the relation;
- terminal outcomes are related.

Required generic theorems:

- `Interaction.Rel.bind`;
- `Interaction.Rel.trans`;
- symmetry when the terminal relation is symmetric;
- exact-query inversion;
- no relation between different query kinds;
- interpretation congruence for a shared strategy.

A small Lean prototype of this carrier, `bind`, `Rel`, `Rel.bind`, and
`Rel.trans` has been checked independently.

## Open-World Meaning

`Interaction.Rel` is the primary open-world semantic theorem.

At every external node it quantifies over every possible response and every
possible committed `OpenWorld`. This directly includes:

- arbitrary reentrant storage changes;
- arbitrary transient-storage changes;
- balance and nonce changes;
- external logs;
- account creation and code-byte installation;
- precompile behavior;
- nondeterministic external responses;
- changes to the currently executing contract's world account.

The protected frame and machine cannot be mutated because they are not part of
the answer type.

### Optional Strategy Corollary

A concrete or abstract external world may be represented as a stateful,
possibly nondeterministic strategy:

```lean
ExternalStrategy.Step :
  StaticContext ->
  ContextState ->
  OpenWorld ->
  ExternalRequest ->
  ExternalResponse ->
  OpenWorld ->
  ContextState ->
  Prop
```

Source and target are interpreted with the same strategy state and the same
static context and choices. Because their external queries are equal, every
strategy transition available to one is available to the other.

The generic theorem is:

```text
Interaction.Rel
  -> interpretation by any one shared strategy
  -> related behavior sets
```

There is no source-context/target-context pair, no context bisimulation, and no
pass-owned context proof.

This strategy layer is optional client infrastructure. Compiler passes prove
only `Interaction.Rel`.

## Request Normalization

### CALL Family

```lean
structure CallRequest where
  kind : CallKind
  requestedGas : Word
  caller : Address
  recipient : Address
  codeAddress : Address
  transferValue : Word
  apparentValue : Word
  calldata : ByteArray
  permission : Bool
```

| Opcode | Recipient | Code address | Transfer value | Apparent value |
|---|---|---|---|---|
| `CALL` | argument | argument | argument | argument |
| `CALLCODE` | current account | argument | argument | argument |
| `DELEGATECALL` | current account | argument | zero | current call value |
| `STATICCALL` | argument | argument | zero | zero |

The requested-gas operand is request data. Effective child gas is not.

Caller-local input and output windows are not part of `CallRequest`. They are
captured privately by the continuation:

```lean
structure CallLocal where
  inputOffset : Word
  inputSize : Word
  outputOffset : Word
  outputSize : Word
```

This prevents the external world from observing caller-local memory offsets.

### CREATE Family

```lean
structure CreateRequest where
  kind : CreateKind
  creator : Address
  value : Word
  initCode : ByteArray
  salt : Option Word
  permission : Bool
```

The init offset and size are private continuation data used to preserve memory
expansion and `msize()` behavior.

The external strategy determines:

- collision failure;
- nonce behavior;
- address derivation;
- initcode execution;
- runtime-code installation;
- committed post-world.

## Ordinary State Effects

Do not turn these into interaction nodes:

- `LOG0` through `LOG4`;
- `SSTORE`;
- `TSTORE`;
- balance and account reads;
- memory writes;
- `SELFDESTRUCT`;
- terminal return or revert.

They remain ordinary state transitions.

Their ordering relative to CALL/CREATE is still proved:

1. A log or storage write changes `OpenWorld`.
2. The next external query contains that exact pre-world.
3. Moving the state effect across the external query changes the query.
4. Different queries cannot be related by `Interaction.Rel`.

Terminal return data, revert data, halt kind, final world, logs, and other
terminal observations belong in the outcome relation used by `done`.

## Gas And Resource Semantics

`gas()` and `msize()` remain abstract resource queries.

Every compiler layer emits:

```lean
.request (.resource .gas) continuation
.request (.resource .msize) continuation
```

The continuation receives the same arbitrary `Word` on source and target.

The compiler theorem therefore proves their placement and downstream use
without inventing a source gas model.

A separate concrete target theorem:

1. runs the gasful bytecode semantics;
2. extracts actual `GAS` and `MSIZE` values;
3. resolves the target interaction tree with those values;
4. resolves the source tree with the same values;
5. preserves the existing exact transcript and terminal-outcome theorem.

CALL/CREATE answers are not replayed from a target trace. They are selected by
the shared external strategy.

### Gas-Sensitive External Worlds

The abstract strategy sees requested gas but not effective forwarded gas.

A concrete EVM-world adapter may assume eventual gas stability:

- below some child-gas threshold, the child may run out of gas;
- above the threshold, caller-visible response and committed post-world are
  stable;
- returned gas and caller gas counters are target-internal.

This assumption belongs only to the concrete-world adapter. It is not a field
of requests, answers, pass theorems, or the public open compiler theorem.

## Static Mode

Intrinsic caller-side failures remain semantic:

- `CREATE` and `CREATE2` fail before an external query in static mode;
- nonzero-value `CALL` fails before an external query in static mode;
- opcode-specific permission and apparent-value rules are normalized in the
  request constructor.

Once an external query is exposed, the generic shared strategy may return any
post-world, even for a static request.

This deliberate over-approximation prevents compiler correctness from relying
on EIP-214 or rollback. A concrete EVM strategy adapter may prove stronger
laws.

## Memory And Spill Safety

CALL/CREATE answers never contain caller memory, stack, locals, or spill state.

The continuation alone performs:

- input or initcode memory expansion;
- return-data-buffer replacement;
- bounded output copying;
- result-word production;
- restoration of the protected continuation.

Source-facing safety must cover:

- nonempty input ranges outside scratch;
- nonempty output ranges outside scratch;
- nonempty initcode ranges outside scratch;
- host byte-array bounds;
- active-word expansion without wrap;
- output copying preserving the memory relation;
- future source reads not observing compiler spill bytes.

Zero-length ranges are inert regardless of offset:

- no host-index obligation;
- no expansion obligation;
- no scratch-disjointness obligation;
- no effect on `msize()`.

`OpenExecutionSafe` must be closed under every possible interaction answer.
The public theorem exposes this source-facing premise, not allocation
artifacts.

## Canonical Semantics

Keep one recursive control evaluator per language.

Refactor its primitive step to return `Interaction`, rather than adding another
open interpreter.

The common shape is:

```lean
PrimitiveSemantics.step :
  Primitive -> State -> Arguments ->
  Interaction Error (State x Results)
```

For Structured and TypedCfg, replace the observer-only `afterInstr` hook with a
primitive/instruction step owned by the canonical evaluator. An after-step hook
is sufficient for `gas()`/`msize()` but cannot honestly intercept CALL/CREATE
before ordinary execution.

Ordinary semantics, current resource replay, and scripted tests become
interpreters or thin specializations of the same evaluator.

During migration, compatibility theorems must preserve the checked ordinary
and resource-observer APIs. A second recursive evaluator is not allowed, even
temporarily as the final architecture.

## Adjacent Theorem Interface

Do not define an `OpenEffectEquiv` wrapper record.

Every adjacent pass exports one theorem whose conclusion is directly:

```lean
Interaction.Rel PassOutcomeRel
  (Source.runOpen ...)
  (Target.runOpen ...)
```

The theorem accepts:

- the ordinary compiler equation;
- related initial states;
- source-facing execution and reservation safety where required.

It does not accept:

- generated compiler evidence;
- allocation certificates beyond the ordinary compiler result;
- a response oracle;
- a replay certificate;
- a target execution;
- a response schedule;
- a context relation;
- generic backward adequacy.

Matching interaction constructors already rule out a target-visible request or
terminal result that the source tree does not match. Local target
determinism/inversion may be used inside a pass proof without becoming a
public backward capability.

Generic `Interaction.Rel.trans` composes adjacent theorems.

## Public Theorem

The target statement is approximately:

```lean
theorem compile_open_correct
    (hAccepted : Accepted sourceProgram)
    (hCompile : compile sourceProgram = some artifact)
    (hInitial :
      InitialStateRel sourceProgram artifact
        sourceInitial targetInitial)
    (hSafe :
      OpenExecutionSafe sourceProgram sourceInitial) :
    Interaction.Rel EndOutcomeRel
      (Yul.runOpen sourceProgram sourceInitial)
      (Bytecode.runOpen artifact.bytes targetInitial)
```

Consequences:

- every external strategy sees identical pre-worlds and requests;
- every possible shared response preserves related continuations;
- resource queries occur in the same order;
- final outcomes are related;
- no target execution or external trace is a compiler premise.

`Yul.EndToEnd` imports only public adjacent composition theorems and contains no
recursive compiler reasoning.

## Migration Order

### Phase 0: Freeze The Simpler Architecture

- [x] Replace the current roadmap with this design.
- [x] Ban new `ExternalContext.Rel`, context-bisimulation, and
  `OpenEffectEquiv` definitions.
- [ ] Ban public response or replay oracles.
- [ ] Ban duplicate recursive evaluators.
- [x] Add one-definition guards for `OpenWorld`, `Query`, `Answer`, and
  `Interaction`.
- [ ] Add a guard preventing canonical Yul semantics from reading account AST
  code.

Exit: architecture checks enforce the intended shape before proof work begins.

### Phase 1: Remove Active Yul Code From Mutable State

- [ ] Make the active Yul program an explicit canonical evaluator parameter.
- [ ] Resolve internal calls and dispatcher entry from that program.
- [ ] Make active `CODESIZE`/`CODECOPY` read a protected code-image parameter.
- [ ] Make external code observations and empty-account tests use code bytes.
- [ ] Stop requiring top-level contract installation for compiler semantics.
- [ ] Prove compatibility with the old installed-state semantics.
- [ ] Preserve the existing checked observer theorem through wrappers.

Exit: changing account AST fields cannot change canonical compiler execution.

### Phase 2: Introduce The Common Open World

- [x] Define `OpenAccount` and `OpenWorld`.
- [x] Define Yul/EVM projections and installers.
- [ ] Prove projection/install and frame-preservation laws.
- [ ] Split active-frame code correctness from world equality.
- [ ] Refactor Yul-to-Functions state relations around exact `OpenWorld`
  equality.
- [ ] Prove existing nonexternal primitives preserve the new relation.

Exit: source and target can consume the same exact external post-world.

### Phase 3: Introduce The Interaction Core

- [x] Define requests, responses, `Query`, and `Answer`.
- [x] Define `Interaction`, `bind`, and `map`.
- [x] Define `Interaction.Rel`.
- [x] Prove bind, transitivity, symmetry, inversion, and strategy
  interpretation.
- [ ] Adapt `ResourceReplay` to resource-query interpretation.

Exit: the shared core builds with no compiler layer changed.

### Phase 4: Migrate Canonical Semantics Bottom-Up

- [ ] Assembly and bytecode.
  - [x] Assembly-owned primitive/instruction suspension for `gas`, `msize`,
    all four CALL-family opcodes, and both CREATE-family opcodes.
  - [x] Exact primitive source/resolved-target
    `Interaction.Rel` seed theorem.
  - [x] One parameterized target control kernel specialized by both ordinary
    bytecode semantics and the shared open interaction semantics.
  - [x] Exact state and outcome-indexed `Interaction.Rel` theorems for every
    emitted Assembly instruction block.
  - [x] One shared fuel-control kernel for target, source, and emitted-block
    execution.
  - [x] Whole-program Assembly source control and emitted target-block
    composition, universally over all interaction answers.
  - [x] Connect emitted-block execution to fetched resolved-target and encoded
    bytecode instruction-count execution.
  - [ ] Migrate the legacy resource-observer runners onto the common kernel.
- [x] TypedCfg.
  - [x] One parameterized control kernel shared by ordinary, resource-observer,
    and open interaction semantics.
  - [x] Exact open preservation for every instruction and recursively composed
    instruction-list body.
  - [x] Assembly-owned control-transfer runner shared by source and compiled
    Assembly execution.
  - [x] Checked direct-terminator theorem for jumps, conditional jumps, halts,
    and invalid execution.
  - [x] Internal-label-aware `returnDispatch`, block, and program theorems.
- [x] Structured.
  - [x] One canonical parameterized control semantics shared by ordinary and
    open execution.
  - [x] Exact open preservation for straight-line code, lexical exits,
    terminals, statement lists, conditionals, and switches.
  - [x] Execution-indexed recursive `for` preservation over the real
    initializer/body/post compiler artifacts, including break, continue,
    leave, halt, and exact transcript order.
  - [x] Internal procedure calls and generated return dispatch.
    - [x] Silent generated call-site entry, optional procedure-entry relabel,
      and token-selected return dispatch.
    - [x] Execution-indexed recursive procedure-body callback and source
      regular/leave/halt call-outcome composition.
    - [x] Pass-owned dynamic activation ancestry, CFG label-shape ownership,
      and stop-policy protection for recursive/self-recursive calls; observer
      modules retain compatibility aliases only.
    - [x] Instantiate the call callback in the mutual whole-statement/block
      owner.
  - [x] One fuel-founded whole-statement/block owner theorem and checked
    generated-main wrapper.
- [ ] Locals/Expressions.
  - [x] One monad-polymorphic Locals expression/control kernel with the legacy
    ordinary and resource-observer APIs as thin specializations.
  - [x] Stable owner-provided constructor equations, so adjacent proofs do not
    depend on the representation depth of those thin specializations.
  - [x] Locals open primitive handler for `gas`, `msize`, all CALL-family
    opcodes, and both CREATE-family opcodes.
  - [x] Stack-free primitive to emitted Structured instruction relation,
    including arbitrary caller-owned stack suffixes.
  - [x] Recursive Locals expression and expression-sequence preservation,
    including initialized named-local lookup, exact result arity, arbitrary
    target runtime control, and ordered open effects.
  - [ ] Recursive source-owned Locals statement, scoped-block, loop,
    terminal, and program preservation. Internal `.call`, `.exprs`,
    `assignTop`, promotion, and explicit cleanup are lower stack-protocol
    constructs owned by the Functions allocation boundary, not by the
    stack-free Locals source semantics.
    - [x] Locals-owned frame/context invariant with exact active-layout stack
      realization over an abstract caller suffix.
    - [x] Checked source assignment preservation through the ordinary emitted
      expression code, `SWAP; POP`, and `bindLocals`, including arbitrary
      ordered open effects in the assigned expression.
    - [x] Compiler-facing zero-result expression, fresh-local, and assignment
      theorems deriving emitted code, stack depth, SWAP selection, and final
      context directly from successful `Stmt.compile`.
    - [x] Exact control-scope suffix invariants plus pass-owned POP cleanup and
      frame-restriction theorems for lexical exits.
    - [x] Stable entry/final-context mode-indexed outcome relation, with
      compiler-facing `break`, `continue`, and `leave` preservation through
      the actual emitted cleanup blocks.
    - [x] Terminal frame theorem plus compiler-facing plain and
      argument-bearing terminal preservation; bare source-owned terminals are
      restricted to zero-argument halt kinds.
    - [x] Fuel-truncated forward interface and checked empty-block base case
      for recursive source-owned block composition.
    - [x] Fuel-lower-bound adapters for every checked straight-line, lexical
      exit, and terminal leaf.
    - [x] Context-stable abrupt outcome relation plus generic regular/abrupt
      sequence kernel over compiler-produced head and tail blocks.
    - [x] Source-owned compiler layout-extension invariant and recursive
      lexical-block preservation through compiler-owned `finishScoped` cleanup.
    - [x] Shared compiled-condition bridge proving Boolean agreement and exact
      target-frame restoration after the condition pop.
    - [x] Shared scoped-child outcome interface and preservation theorem;
      lexical blocks are thin wrappers, and `if`, `switch`, and loop bodies
      reuse the same regular-cleanup and abrupt-bypass proof.
    - [x] Compiler-facing conditional preservation through the shared
      condition and scoped-child interfaces, including both false and every
      regular/abrupt/terminal true-branch outcome.
    - [x] Compiler-facing switch preservation with one structural
      source/compiled selection relation, exact scrutinee-pop frame recovery,
      and shared scoped-child preservation for every selected branch.
    - [x] Independent control-policy refinement for exact break/continue
      frames, with policy-indexed scoped-child and sequence composition; the
      generic outcome interface remains lightweight.
    - [x] Fuel-aligned recursive loop kernel covering false conditions,
      regular body/post recursion, break, continue, leave, halt, and impossible
      post exits with one fixed compiler slack.
    - [x] Whole generated `for` composition through initializer execution,
      recursive loop outcomes, abrupt outer-cleanup bypass, and regular
      compiler-owned outer cleanup.
    - [x] Compiler-facing `for` decomposition deriving initializer, condition,
      post/body blocks, scoped cleanups, outer cleanup, layout extensions, and
      final context from the ordinary pass.
    - [x] Exact source-owned compiler layout equals syntax-level `outEnv` for
      statements and open blocks, eliminating generated tail/condition layout
      premises from the recursive owner.
    - [x] Split policy/control recursion into a dedicated adjacent Locals owner
      before adding the whole compiled `for` wrapper; the current proof module
      is again below the 5K-line architecture soft limit.
    - [x] Add policy-indexed empty-block and bounded sequence composition with
      one additive static target-fuel cost, ready for structural recursion.
    - [x] Prove source control-policy compatibility at every open execution
      leaf and use one shared forward-strengthening law to lift regular source
      leaves without duplicating their compiler proofs.
    - [x] Lift lexical blocks, conditionals, and switches through the shared
      policy-indexed scoped-child theorem; switch recursion is indexed by the
      checked source-selection equation rather than an arbitrary block oracle.
    - [ ] Close the source-owned recursive whole-statement/block owner and
      remove recursive callback premises from the compiler-facing loop theorem.
  - [x] Canonical Expressions open semantics and transparent
    Expressions-to-Structured preservation.
- [ ] Functions.
- [ ] Yul.

At each layer:

- primitive execution returns `Interaction`;
- ordinary semantics is a specialization;
- resource replay is a specialization;
- no control recursion is duplicated;
- focused compatibility tests pass.

Exit: every layer exposes one canonical open computation.

### Phase 5: Prove Adjacent Boundaries Bottom-Up

- [x] Assembly -> bytecode.
  - [x] Per-instruction emitted-block state and outcome preservation.
  - [x] Whole-program emitted-block open execution preservation.
  - [x] Fetched resolved-target and encoded-bytecode open execution bridge.
- [x] TypedCfg -> Assembly.
  - [x] Every lowered instruction, including all six external opcodes.
  - [x] Arbitrary lowered instruction-list bodies.
  - [x] Direct terminators through the Assembly-owned transfer runner.
  - [x] `returnDispatch`, blocks, and whole-program execution.
  - [x] Certified-artifact entry theorem deriving all compiler-selected
    lowering, acceptance, PC-fit, and typing evidence internally.
- [x] Structured -> TypedCfg.
  - [x] Straight-line code, lexical exits, terminals, lists, conditionals, and
    switches.
  - [x] Recursive `for` loops through the adjacent compiler decomposition.
  - [x] Internal procedure calls and generated program wrapper.
    - [x] Generated call-entry, procedure-entry, and return-dispatch routing.
    - [x] Adjacent execution-indexed call theorem parameterized by the
      recursive procedure-body owner.
    - [x] Fuel-founded recursive owner instantiation and successful-generation
      whole-program wrapper.
- [ ] Locals/Expressions -> Structured.
  - [x] Adjacent primitive leaf over the shared ordered interaction tree.
  - [x] Recursive compiler-owned Locals expression composition.
  - [x] Transparent whole-program Expressions-to-Structured open
    preservation, including loops and internal calls.
  - [ ] Recursive compiler-owned source-Locals statement and control
    composition.
    - [x] Source assignment constructor through the ordinary compiler stack
      protocol and canonical Expressions statement semantics.
    - [x] Straight-line source constructors lifted to actual compiled
      singleton target blocks with an explicit adjacent fuel translation.
    - [x] Cleanup compilation packaged as an adjacent frame theorem, ready for
      break/continue/leave and scoped-block composition.
    - [x] `break`, `continue`, and `leave` composed through ordinary compiler
      decomposition facts and the shared mode-indexed outcome relation.
    - [x] Plain and argument-bearing terminals composed through the same
      outcome relation, with arbitrary caller stack suffixes protected.
    - [x] Recursive `ForwardRel` base case distinguishes source fuel
      truncation from checked terminal outcomes.
    - [x] Expressions-owned append execution law, Locals-owned nonempty
      compiler decomposition, and generic adjacent sequence composition.
    - [x] Lexical blocks consume only an adjacent recursive body theorem;
      regular cleanup and abrupt cleanup bypass are both checked generically.
    - [x] Scoped child execution is factored independently of its enclosing
      control constructor, preventing duplicated cleanup reasoning across
      blocks, conditionals, switches, and loops.
    - [x] Ordinary compiled `if` statements preserve ordered interactions and
      mode-indexed outcomes without constructor-specific cleanup reasoning.
    - [x] Ordinary compiled switches preserve no-match and selected-branch
      behavior without importing lower-pass preservation or duplicating a
      switch interpreter.
    - [x] Exact loop-control frames are an orthogonal proof capability rather
      than a stronger global outcome relation or a loop-specific interpreter.
- [ ] Functions -> allocated Locals/Expressions.
  - [ ] Own the emitted internal-call and stack-protocol constructs rather
    than extending stack-free Locals with an operand stack.
- [ ] Yul -> Functions.

Every boundary proves exact query equality and universal continuation
before source fuel truncation. Boundaries whose lowering changes control-step
cost use the shared `Simulation.Interaction.ForwardRel`; its execution theorem
recovers the exact ordered transcript and related outcome for every
non-truncated source run. Fuel-preserving boundaries continue to expose exact
`Simulation.Interaction.Rel`.
preservation.

The allocation boundary additionally proves CALL/CREATE memory and spill
safety.

Exit: every adjacent boundary has a checked `Interaction.Rel` theorem.

### Phase 6: Compose The Public Theorem

- [ ] Add one public composition theorem.
- [ ] Keep `Yul.EndToEnd` short.
- [ ] Add named corollaries for all six opcodes.
- [ ] Add external-strategy contextual corollary.
- [ ] Retain the existing no-external-effects theorem as a specialization.

Exit: universal open-world compiler correctness is checked.

### Phase 7: Reconnect Concrete Resource Execution

- [ ] Relate gasful bytecode execution to open bytecode interaction.
- [ ] Extract exact `gas()`/`msize()` answers.
- [ ] Resolve source and target resource nodes with the same answers.
- [ ] Retain exact terminal outcome and transcript consumption.
- [ ] Keep external answers strategy-driven.

Exit: real target resource observations compose with universal external
correctness.

## Adjacent Ownership

Each pass owns only its boundary:

```text
Yul owner:
  source program and Yul control
  -> Functions program and state relation

Functions allocation owner:
  Functions state
  -> allocated Locals/Expressions plus spill artifact

Locals/Expressions owner:
  stack-free expressions
  -> Structured stack code

Structured owner:
  Structured control
  -> TypedCfg

TypedCfg owner:
  typed CFG
  -> Assembly

Assembly owner:
  Assembly
  -> bytecode
```

No owner imports preservation internals from a nonadjacent lower pass.

## Historical Lessons Retained

Keep:

- the old free open-result idea;
- universal response continuations;
- normalized CALL/CREATE requests;
- table-driven opcode families;
- source-facing scratch safety;
- exact resource replay;
- quantitative source-derived fuel bounds;
- pass-owned outcome relations;
- short end-to-end composition.

Do not restore:

- Yul-specific open runners;
- finite external-event path certificates;
- call or response oracles;
- generated compiler evidence;
- context pairs and context bisimulation in pass proofs;
- generic backward adequacy;
- concrete linked-world recursion;
- the requirement that every account contain compiler-produced code.

The old model's strongest insight was universal continuation quantification.
The revised design keeps that insight and removes the machinery that grew
around it.

## Architecture Guards

Extend `scripts/check_architecture.sh` to enforce:

- one definition of `OpenWorld`;
- one definition of `Interaction` and `bind`;
- no `ExternalContext.Rel`;
- no `OpenEffectEquiv`;
- no external-specific compiler implementation;
- no duplicate recursive `run`, `exec`, `eval`, or `step` in specialization
  modules;
- no canonical Yul account-code lookup for internal calls;
- no canonical Yul empty-account test based on AST equality;
- no public target-run premise in the universal open theorem;
- no response trace, schedule, oracle, certificate, or generated evidence;
- no Yul end-to-end import of lower pass internals;
- all six external opcodes in the verification-root theorem table;
- resource and external effects sharing one `Interaction` carrier.

## Validation

At every completed boundary:

```text
lake env lean <focused module>
lake build EvmCompiler.Verification
scripts/check_architecture.sh
scripts/verify_layer.sh proofs
rg -n "\b(sorry|admit|axiom|unsafe)\b" <changed Lean files>
#print axioms <new public theorems>
git diff --check
```

Also retain:

- real-contract regression tests;
- stack-only and scratch allocation tests;
- zero-length CALL/CREATE memory-window tests;
- log/call interleaving tests;
- reentrant current-contract storage mutation tests;
- static-request arbitrary-world tests;
- external account code-byte tests;
- target resource self-replay tests.

## Definition Of Done

The migration is complete when:

1. Active Yul AST code is no longer semantic mutable state.
2. External accounts are represented only by common observable world data.
3. All effects share one ordered `Interaction` tree.
4. Every adjacent pass has a checked `Interaction.Rel` theorem.
5. CALL/CREATE continuations work for every exact shared response and
   post-world.
6. Scratch-backed allocation is proved safe across external suspension.
7. The public theorem contains no context bisimulation, target run, external
   trace, generated evidence, or backward-adequacy premise.
8. Concrete `gas()`/`msize()` target execution composes separately.
9. `Yul.EndToEnd` is a short composition theorem.
10. Focused builds, full verification, architecture checks, hole scans, axiom
    checks, and diff checks pass.
