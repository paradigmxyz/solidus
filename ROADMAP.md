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
Each adjacent owner also exposes the terminal backward adequacy needed to
reconstruct an exact `gas()`/`msize()` source replay from a concrete terminal
target run. `Yul.EndToEnd` remains a short composition module.

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

## Active Proof Work

- [ ] Define an honest source-facing scratch execution/reservation-safety
  interface that supplies the concrete source-run depth bound without exposing
  compiler-generated evidence.
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

These checked Yul-to-Functions inversions are reusable diagnostics and exposed
compiler-bug checks. Completing symmetric backward coverage is not a blocker
for the narrowed public observer-replay theorem.

- [x] compiler-selected primitive families;
- [x] direct and bound expressions;
- [x] internal calls and regular leaf statements;
- [x] recursive statement lists;
- [x] lexical blocks;
- [x] nonterminal `if`;
- [x] nonterminal `switch`.
- [ ] Terminal `if`/`switch`, `for`, and complete generic backward dispatch are
  optional follow-on coverage, not completion prerequisites.

## Completion Gates

- [x] Every adjacent boundary has checked forward preservation; the lower
  terminal boundaries expose only the reverse/trace adequacy needed for the
  concrete terminal target run.
- [ ] Public theorem accepts only source validation, related initial states,
  source-facing execution/resource safety, and a concrete terminal target run.
- [ ] No observer-specific compiler, duplicate control interpreter, replay
  certificate, call oracle, or vertical Yul-to-bytecode proof corridor.
- [ ] Focused Lean builds, full verification root, architecture checks, hole
  scan, axiom audit, proof aggregate, and `git diff --check` pass.
