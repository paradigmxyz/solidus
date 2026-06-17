# Full Resource-Observer Proof Roadmap

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
