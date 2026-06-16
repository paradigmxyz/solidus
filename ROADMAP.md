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
- [x] Functions -> allocated Expressions whole-main forward preservation for
  compiler-selected stack-only and scratch allocation.
- [x] Expressions -> Structured transparent forward/backward interface.
- [x] Structured -> TypedCfg terminal backward adequacy.
- [x] TypedCfg -> Assembly terminal backward adequacy.
- [x] Assembly -> bytecode terminal backward adequacy.
- [x] Stack-only end-to-end exact observer replay.
- [x] Compiler-selected lower composition under an explicit Functions resource
  bound.

## Active Proof Work

- [ ] Yul -> Functions exact observer-replay bridge:
  - [x] compiler-selected primitive families;
  - [x] direct and bound expressions;
  - [x] internal calls and regular leaf statements;
  - [x] recursive statement lists;
  - [x] lexical blocks;
  - [x] nonterminal `if`;
  - [x] nonterminal `switch`;
  - [ ] terminal `if` and `switch`, plus `for`;
  - [ ] terminal call statements, complete outcome dispatch, dispatcher, and
    whole program.
- [ ] Functions -> allocated Expressions whole-main backward adequacy:
  construct the canonical Functions run from a concrete terminal allocated
  target run, for stack-only and scratch modes.
- [ ] Replace interpreter-fuel-based scratch budgeting at the public Yul
  boundary with a source-facing execution-depth/reservation invariant, or prove
  a checked source-derived bound for the Functions run constructed by the
  Yul -> Functions pass.
- [ ] Compose compiler-selected stack-only/scratch
  `Yul.EndToEnd.ClosedResourceCorrect` without public compiler-generated
  evidence.

## Completion Gates

- [ ] Every adjacent boundary has checked forward preservation; the boundaries
  used by observer replay expose only the reverse/trace adequacy needed for the
  concrete terminal target run.
- [ ] Public theorem accepts only source validation, related initial states,
  source-facing execution/resource safety, and a concrete terminal target run.
- [ ] No observer-specific compiler, duplicate control interpreter, replay
  certificate, call oracle, or vertical Yul-to-bytecode proof corridor.
- [ ] Focused Lean builds, full verification root, architecture checks, hole
  scan, axiom audit, proof aggregate, and `git diff --check` pass.
