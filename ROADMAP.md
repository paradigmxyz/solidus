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
- [x] Honest stack-only public theorem with explicit source execution safety.

## Active Proof Work

- [x] Prove pass-owned reservation-capacity lemmas:
  - [x] canonical recipe planning exposes its configured frame bound;
  - [x] validated mixed allocation preserves that frame bound;
  - [x] `(fuel + 1) * frameWords` source reservation capacity implies
    scratch `FuelSafe fuel`;
  - [x] compiler-selected main setup depth is at most one frame.
- [ ] Strengthen Yul -> Functions whole-program forward preservation with a
  checked source-derived upper bound on the existential Functions execution
  fuel, or an equivalent source-owned execution-depth bound. The current
  theorem proves existence but no numeric relation to the Yul run fuel.
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
  - [ ] prove every remaining compiler construct respects the program static
    measure;
  - [ ] cover remaining leaf/compound statements, loops, and terminal outcomes;
  - [ ] expose the bounded whole-program forward theorem.
- [ ] Define an honest source-facing scratch execution/reservation-safety
  interface using that checked bound, without exposing compiler-generated
  evidence.
- [ ] Generalize `Yul.EndToEnd.ClosedResourceCorrect`:
  - [ ] remove the stack-only field from `ClosedArtifact`;
  - [ ] derive the compiler-selected `FuelSafe` fact from the source-facing
    safety premise;
  - [ ] compose through
    `Public.ObserverComposition.terminalWithResourceSafety`;
  - [ ] retain exact transcript consumption and terminal outcome relation.
- [ ] Audit the public theorem for generated artifact evidence, replay
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
- [ ] No general terminal call/list/control backward campaign is planned.

## Completion Gates

- [x] Every adjacent boundary used by the public spine has checked forward
  preservation owned by that compiler pass.
- [x] Concrete target transcript exhaustion yields an exact source replay
  without reconstructing arbitrary intermediate target executions.
- [ ] Public theorem accepts only source validation, related initial states,
  source-facing execution/resource safety, and a concrete terminal target run.
- [ ] No observer-specific compiler, duplicate control interpreter, replay
  certificate, call oracle, or vertical Yul-to-bytecode proof corridor.
- [ ] Focused Lean builds, full verification root, architecture checks, hole
  scan, axiom audit, proof aggregate, and `git diff --check` pass.
