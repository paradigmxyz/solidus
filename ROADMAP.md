# Full Resource-Observer Proof Roadmap

External CALL/CREATE support is planned separately in
`EXTERNAL_EFFECTS_ROADMAP.md`. That migration does not turn CALL/CREATE into
another concrete replay transcript. It introduces one ordered open interaction
tree over one code-erased source/target world. External nodes expose the same
pre-world and request and quantify over every exact shared response and
post-world, while resource nodes are resolved from a concrete EVM run only for
`gas()`/`msize()`. The migration preserves adjacent pass ownership and short
end-to-end composition. Concrete linked-world adequacy is not a compiler
completion requirement.

The shared `OpenWorld`/`Interaction` core and the Assembly-owned primitive
semantics for `gas`, `msize`, `CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`,
`CREATE`, and `CREATE2` are now checked. Target bytecode control now uses one
parameterized recursive kernel shared by target, source, and emitted-block
execution. Exact per-instruction and whole-program emitted-block open
preservation are checked. The fetched/encoded-bytecode execution bridge,
legacy observer specialization, and all higher adjacent preservation
boundaries remain active work.

## Open-Effects Migration Status

- [x] Shared ordered `Interaction` semantics and code-erased `OpenWorld`.
- [x] Assembly/bytecode and lower control-pass preservation for all shared
  effects, including CALL-family, CREATE-family, logs, storage, `gas()`, and
  `msize()`.
- [x] Functions allocation relation, primitive families, recursive
  expressions, stack/scratch declaration preservation, and assignment
  preservation in both activation modes.
- [x] Complete Functions statement and program preservation: statement-list
  composition, scoped control, loops, terminal outcomes,
  internal calls, activation setup/cleanup, and whole program.
  - [x] outcome-indexed regular/abrupt result relation and generic real-block
    `nil`/`cons` composition laws;
  - [x] expression, assignment, and stack/scratch declaration leaf adapters;
  - [x] outcome-indexed `break`/`continue` cleanup in both activation modes;
  - [x] ordered return-value emission and frame-cleaning `leave` preservation;
  - [x] plain and argument-bearing terminal preservation under source-facing
    terminal memory safety;
  - [x] canonical compiler-owned root/cursor and exact head/tail decomposition;
  - [x] pass-owned live-slot, stack-order, stack/scratch-location, and sibling
    cursor agreement facts;
  - [x] canonical post-declaration activation context and mode transition for
    stack and scratch placement;
  - [x] shared lexical cursor construction and exact lexical-block/`if`
    decomposition;
  - [x] common and selected-branch `switch` cursor decomposition with exact
    outer-tail retention;
  - [x] exact `for` initializer/condition/post/body/cleanup cursor
    decomposition;
  - [x] recursive interaction base case and generic exact-tail sequencing;
  - [x] arbitrary-fuel expression/assignment/declaration heads and preserved
    compiler-frame capacity;
  - [x] arbitrary-fuel `break`/`continue`/`leave` and terminal cursor heads;
  - [x] observer-free compiler-selected internal-callee artifact constructed
    from canonical lookup and whole-program lowering;
  - [x] compiler-selected callee prelude, stack/scratch body mode, and canonical
    body compiler context constructed without observer proof machinery;
  - [x] compiler-selected callee body packaged as an ordinary pass-owned root
    and recursive cursor;
  - [x] real call-code decomposition and canonical stack/scratch callee-entry
    realization, including parameter spill-store transitions;
  - [x] silent entry-marker execution and one compiler-selected scratch
    parameter lowering/compilation/execution step;
  - [x] recursive all-stack and mixed stack/scratch parameter-prelude
    preservation under the pass-owned compiler context;
  - [x] construct parameter placement, recursive context, and stack/scratch
    execution wrappers from the selected compiler artifact;
  - [x] complete compiler-selected stack/scratch return initialization with
    checked placement/context construction and open execution;
  - [x] compose entry markers and both preludes into the callee body invariant;
  - [x] prefix exact setup to the fuel-decreasing canonical callee-body
    preservation interface;
  - [x] decouple canonical source scope order from compiler live-list order
    through pass-owned extensional cursor and invariant transport;
  - [x] prove canonical non-halting return-stack preservation and complete a
    compiler-selected callee through emitted return values and cleanup;
  - [x] attach the completed callee through the canonical source and target
    call wrappers, including exact return-frame pop and value attachment;
  - [x] define the uniform recursive target budget and checked empty,
    head/tail-composition, expression, assignment, and stack/scratch
    declaration cursor constructors;
  - [x] lift plain/argument terminals and ordered function `leave` into the
    uniform recursive cursor interface;
  - [x] lift `break` and `continue` with compiler-owned loop cleanup into the
    uniform recursive cursor interface;
  - [x] retain entry-to-result frame continuity in the shared control relation
    and compose it through recursive sequencing;
  - [x] prove pass-owned lexical-block cleanup and its recursive cursor lift;
  - [x] prove canonical condition truth/stack restoration plus pass-owned and
    recursive `if` preservation;
  - [x] expose canonical source/target switch equations and prove exact
    one-value scrutinee preservation with incoming-stack restoration;
  - [x] prove pass-owned exact switch selection and recursive selected-branch
    preservation with lexical cleanup and exact tail composition;
  - [x] correct the loop theorem boundary with shared open-world
    `Interaction.Successful` and generic bind inversion, excluding source
    meta-fuel exhaustion without duplicating loop semantics;
  - [x] strengthen caught `break`/`continue` outcomes with destination
    definedness, stack length, mode/live agreement, and frame continuity;
  - [x] exact recursive loop core and compiler-owned `for` wrapper;
  - [x] canonical source/target internal-call equations and compiler-owned
    caller call decomposition;
  - [x] canonical open-world argument-list safety and arbitrary-length
    stack/scratch argument preservation;
  - [x] compiler-selected all-stack callee source initialization, exact target
    split/return-frame entry, and recursive-body entry relation;
  - [x] orthogonal allocator-cell readiness/depth and suspended-prefix effect
    interfaces plus exact canonical scratch-frame acquire execution;
  - [x] canonical scratch-frame acquire resource preservation, including
    machine relation, allocator depth, frame materialization, and protected
    suspended prefixes;
  - [x] compiler-selected scratch-callee entry from exact acquire, canonical
    arguments, allocation artifacts, and an orthogonal argument-resource
    effect;
  - [x] derive the canonical argument-resource effect and check exact
    scratch-frame release for nested calls;
  - [x] pass-owned caller return writeback through the exact emitted
    stack/scratch target code, including deeper-callee bounded effects;
  - [x] strengthen the recursive target budget with a checked whole-program
    procedure-body stride and expose exact caller-chosen selected-callee fuel;
  - [x] expose successful canonical call/body inversion, open argument local
    preservation, and the related suspended caller after argument stack removal;
  - [x] restore outcome-indexed allocator effects across statements, scoped
    blocks, loops, and selected callees, so a halting scratch-backed nested call
    protects caller frames without falsely requiring unreachable frame release;
  - [x] construct identical continuation-ready stack/scratch selected-callee
    invocations from canonical arguments, including suspended caller prefixes,
    exact recursive calls, return writeback, and optional scratch release;
  - [x] orthogonal recursive allocator companion over the same Interaction
    tree, including all statement/control forms, stack/scratch call setup,
    selected-callee recursion, return writeback, scratch release, and exact
    successful-tail composition;
  - [x] compose caller arguments, selected-callee recursion, return writeback,
    scratch release, and the exact successful tail;
  - [x] define an execution-indexed source reservation-safety interface over
    scoped canonical expressions and terminal memory windows;
  - [x] retain successful continuation evidence through generic sequence,
    `if`, `switch`, and loop owners instead of requiring unreachable branches;
  - [x] construct and preserve the source/compiler control-destination
    invariant needed by the recursive statement dispatcher;
  - [x] recursive compiler-cursor statement-list theorem;
    - [x] successful head/tail fixed-point interface and source-derived safety;
    - [x] expression, assignment, declaration, abrupt control, terminal, and
      lexical-block dispatcher cases;
    - [x] replace the false arbitrary-extra target budget with a checked
      nested-code reserve, exact compiled suffixes, and procedure-table bounds;
    - [x] selected-body fixed-point cases for `if` and `switch`;
    - [x] loop capacity, selected internal-call dispatcher, and whole-block
      fixed point.
  - [x] construct the compiler-selected main artifact and check exact scratch
    allocator/frame setup plus recursive main-body preservation.
  - [x] thread the existing resource-mode interface through stack-only
    recursion, then compose source prelude, main body, and cleanup into the
    public adjacent theorem without an allocator premise for stack-only code.
    - [x] exact empty main setup, stack runtime boundary, and target-fuel
      adapter;
    - [x] compiler proof that every selected callee is stack-backed and a
      resource-free function-return epilogue;
    - [x] resource-free internal-call attachment, caller writeback, exact
      successful-tail composition, and compiler-selected all-stack CALL head;
    - [x] successful stack recursion for expression, assignment, declaration,
      abrupt control, terminal, lexical block, conditional, switch, and call
      constructors;
    - [x] stack-only `for` init/body/post recursion and the thirteen-constructor
      source-fuel fixed point.
    - [x] compiler-derived stack-only main setup and recursive main-body
      preservation, with no public all-stack certificate.
    - [x] outcome-indexed top-level cleanup for regular, abrupt, and terminal
      results, with allocation representation erased only after program exit.
    - [x] canonical source append/scoped-append laws, compiler-owned no-variable
      prelude preservation, and flat target setup fuel transport.
    - [x] selected stack/scratch setup, recursive body, and cleanup composition
      with allocator/frame evidence kept internal.
  - [x] public compiler-selected `AllocationInteractionProgram.mainForward`
      from ordinary lowering and source-facing safety/resource premises only.
- [x] Canonical Yul control is one monad-polymorphic evaluator with an explicit
  immutable active contract and a shared open-`Interaction` specialization for
  resources and all CALL/CREATE families.
- [ ] Prove the adjacent Yul -> Functions open-interaction theorem.
  - [x] Exact code-erased state relation and arbitrary post-world transport.
  - [x] GAS/MSIZE plus all CALL/CREATE primitive-family preservation.
  - [ ] Recursive statements, internal calls, and whole program.
    - [x] Source-truncation-aware direct literals, variables, primitive calls,
      and arbitrary argument lists under one compiler-selected capability.
    - [x] Compose independent CALL/CREATE and GAS/MSIZE providers with a
      closed-ordinary-primitive capability; no opcode dispatch occurs inside
      expression recursion.
    - [ ] Discharge the closed ordinary primitive capability over canonical
      code-erased state.
      - [x] Pure binary, unary, and ternary arithmetic/comparison/bitwise
        families through one reusable `PureSpec` forward theorem.
      - [x] Machine families through one reusable `MachineSpec` theorem:
        MSTORE, MSTORE8, MCOPY, MLOAD, KECCAK256, RETURNDATASIZE, and POP.
      - [x] Environment families through one reusable `EnvironmentSpec`
        theorem: active-frame reads and BLOBHASH are related over the shared
        code-erased execution-environment relation.
      - [x] Code-erased world-read interface and immutable reads: COINBASE,
        TIMESTAMP, NUMBER, GASLIMIT, CHAINID, SELFBALANCE, CALLDATALOAD, and
        BLOCKHASH.
      - [x] Repair canonical Yul EXTCODEHASH semantics to decide external
        account emptiness from the executable byte image rather than a
        compatibility Yul AST; prove exact agreement with EVM semantics.
      - [x] World-access transitions through reusable `WorldSpec`: BALANCE,
        EXTCODESIZE, EXTCODEHASH, SLOAD, and TLOAD, including exact account and
        storage warming in the shared open-world substate.
      - [x] World-write transitions through reusable `WorldWriteSpec`: SSTORE
        and TSTORE, including refunds, warm storage, exact account updates,
        and matching static-mode failure.
      - [ ] Copy, log, and invalid families;
        assemble the concrete `ClosedSelected` theorem.
    - [x] Define the code-erased outcome-indexed relation and source-owned
      exact lexical-domain invariant; check direct expression, one-name
      declaration, and one-name assignment statements plus `break`,
      `continue`, and `leave` with exact Functions scope restriction.
- [ ] Compose the short public Yul end-to-end theorem and reconnect the
  source-facing reservation/resource assumptions.
- [ ] Run representative interleaving/reentrancy/static/zero-window tests and
  all completion gates.

## Relation To External Effects

The checked theorem in this file is intentionally asymmetric because EVM
resource values have no intrinsic Yul source meaning.

The external-effects theorem has a different public shape:

- no terminal target run or external-event trace is a premise;
- source and target expose related open computations;
- every exact shared CALL/CREATE response and post-world has a related
  continuation;
- interpreting those computations with any one shared external strategy yields
  equivalent behavior sets;
- the generic strategy may return arbitrary world mutations, including for
  static requests; concrete EVM legality is proved only by a strategy adapter;
- the active Yul program is immutable evaluator input, while arbitrary
  external accounts contain only observable byte images and world state;
- target-to-source reasoning is limited to observable-node reflection and does
  not restore generic pass-by-pass backward adequacy.

## Public Spine

Accepted Yul
-> Functions
-> allocated Locals/Expressions
-> Structured
-> TypedCfg
-> Assembly
-> bytecode observer execution

The primary compiler-correctness result is whole-program forward preservation.
Reverse reasoning is limited to the exact bridge needed to align a concrete
terminal target `gas()`/`msize()` transcript with a canonical source replay.
`Yul.EndToEnd` remains a short composition module.

## Checked Boundaries

- [x] Yul -> Functions whole-program forward preservation.
- [x] Yul -> Functions exact observer replay from source-safe execution,
  forward preservation, semantic uniqueness, and concrete target transcript
  exhaustion.
- [x] Functions -> allocated Expressions whole-main forward preservation for
  compiler-selected stack-only and scratch allocation.
- [x] Functions -> bytecode compiler-selected terminal composition under an
  explicit source-run resource bound.
- [x] Expressions -> Structured transparent forward/backward interface.
- [x] Structured -> TypedCfg terminal backward adequacy.
- [x] TypedCfg -> Assembly terminal backward adequacy.
- [x] Assembly -> bytecode terminal backward adequacy.
- [x] Stack-only end-to-end exact observer replay.
- [x] Compiler-selected lower composition under an explicit Functions resource
  bound.
- [x] Narrow target-to-source transcript bridge through
  `FunctionsObserverTraceAdequacy.compileProgramTraceAdequate`.
- [x] Compiler-selected stack/scratch public theorem with explicit source
  execution and reservation safety.

## Active Proof Work

- [x] Prove pass-owned reservation-capacity lemmas:
  - [x] canonical recipe planning exposes its configured frame bound;
  - [x] validated mixed allocation preserves that frame bound;
  - [x] `(fuel + 1) * frameWords` source reservation capacity implies
    scratch `FuelSafe fuel`;
  - [x] compiler-selected main setup depth is at most one frame.
- [x] Strengthen Yul -> Functions whole-program forward preservation with a
  checked source-derived upper bound on the existential Functions execution
  fuel.
  - [x] canonical Functions open-block composition exposes explicit additive,
    `max + 1`, singleton-wrapper, and unreachable-suffix fuel bounds;
  - [x] Yul expression preparation and scoped open results expose least
    sufficient target fuel with pass-owned composition lemmas;
  - [x] define a dynamic source-fuel amplifier that absorbs up to eight
    strictly smaller recursive budgets plus compiler wrapper overhead;
  - [x] correct the bound with a separate source-derived static expansion
    factor: source fuel alone cannot bound multi-name declarations or wide
    generated argument preambles;
  - [x] carry bounded argument preparation and returned function bodies through
    visible-target calls;
  - [x] reuse the same bounded call execution for fresh declaration targets;
  - [x] prove bounded recursive statement-list composition from a bounded
    statement capability;
  - [x] expose the exact `names.length + 1` target-fuel bound for
    uninitialized declarations and lift it into the corrected execution
    budget;
  - [x] define a source-AST static-expansion measure whose program bound covers
    the dispatcher and every function body reached through canonical lookup;
  - [x] expose exact fuel composition for initialized values, visible
    assignments, and `break`/`continue`/`leave`;
  - [x] lift prepared single-value declarations and assignments into the
    source-static/dynamic bounded forward interface;
  - [x] bound direct and spill-bound expression argument preparation,
    including compiler-selected primitive calls, by exact source-AST cost;
  - [x] bound one-result internal function-call expressions by argument
    runtime cost plus the compiler-selected callee body cost;
  - [x] close recursive expression/value preservation under the call-aware
    runtime cost and derive exact bounded function bodies from bounded lists;
  - [x] identify and repair the nested-call theorem boundary: add a checked
    program-global/local-static two-dimensional budget whose source-fuel step
    absorbs recursive children bounded by the whole program;
  - [x] migrate recursive expression, call, statement, and body capabilities
    to the program-indexed budget;
    - [x] argument preparation and primitive expression evaluation;
    - [x] internal function calls and recursive expression capability;
    - [x] list sequencing and returned-body packaging;
    - [x] leaf statements;
    - [x] compound statements and loops;
    - [x] recursive-family fixed point and dispatcher packaging;
  - [x] retire the provisional one-level call-expanded runtime measure;
  - [x] cover terminal outcomes with the same program-indexed budget;
    - [x] expose least sufficient fuel for terminal statement, function-body,
      and loop results;
    - [x] prove exact quantitative composition for regular prefixes,
      unreachable suffixes, lexical blocks, and loop wrappers;
    - [x] lift recursive terminal statement-list sequencing and function-body
      packaging to the program-indexed budget;
    - [x] bound recursive terminal argument-list evaluation for direct and
      spill-bound unchecked lowering;
    - [x] bound the emitted terminal primitive after a regular, bounded
      argument prelude;
    - [x] lift compiler-selected primitive expression failure into the
      recursive program-indexed terminal family;
    - [x] lift internal-call argument and callee-body failure into the
      recursive program-indexed terminal expression family;
    - [x] lift nonterminal primitive-expression statements, terminal
      primitive statements, and initialized single-value declarations and
      assignments into the recursive program-indexed statement family;
    - [x] lift call-valued declaration, assignment, and expression statements
      into the recursive program-indexed statement family;
    - [x] lift compound terminal control through the recursive
      program-indexed family;
      - [x] lexical blocks, conditionals, and switches;
      - [x] loops;
  - [x] expose the bounded regular whole-program forward theorem;
  - [x] expose the bounded whole-program terminal forward theorem.
- [x] Define an honest source-facing scratch execution/reservation-safety
  interface using that checked bound, without exposing compiler-generated
  evidence.
- [x] Generalize `Yul.EndToEnd.ClosedResourceCorrect`:
  - [x] remove the stack-only field from `ClosedArtifact`;
  - [x] derive the compiler-selected `FuelSafe` fact from the source-facing
    safety premise;
  - [x] compose through
    `Public.ObserverComposition.terminalWithResourceSafety`;
  - [x] retain exact transcript consumption and terminal outcome relation.
- [x] Audit the public theorem for generated artifact evidence, replay
  certificates, call oracles, and cross-pass proof reasoning.

## Retained Local Inversions

These checked backward theorems remain reusable local facts. They are not
completion gates unless the narrow transcript bridge actually needs them.

- [x] compiler-selected primitive families;
- [x] direct and bound expressions;
- [x] internal calls and regular leaf statements;
- [x] recursive statement lists;
- [x] lexical blocks;
- [x] nonterminal `if`;
- [x] nonterminal `switch`.
- [x] terminal primitive replay.
- [x] terminal primitive-expression suffix replay after regular arguments.
- [x] No general terminal call/list/control backward campaign is required.

## Completion Gates

- [x] Every adjacent boundary used by the public spine has checked forward
  preservation owned by that compiler pass.
- [x] Concrete target transcript exhaustion yields an exact source replay
  without reconstructing arbitrary intermediate target executions.
- [x] Public theorem accepts only source validation, related initial states,
  source-facing execution/resource safety, and a concrete terminal target run.
- [x] No observer-specific compiler, duplicate control interpreter, replay
  certificate, call oracle, or vertical Yul-to-bytecode proof corridor.
- [x] Focused Lean builds, full verification root, architecture checks, hole
  scan, axiom audit, proof aggregate, and `git diff --check` pass.
