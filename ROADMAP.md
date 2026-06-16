# Narrow Observer Replay Roadmap

## Public Spine

Accepted Yul AST -> ordinary compiler passes -> bytecode target

The primary compiler-correctness result is forward preservation. At the
Yul-to-Functions boundary this is
`Yul.FunctionsObserverPreservation.compileProgramForward`; the lower passes
retain their existing pass-owned forward theorems and whole-program
composition.

## Reverse Trace Bridge

A narrow reverse theorem is still required for `gas()` and `msize()`: a
concrete terminal target observer run determines the exact ordered transcript,
and the source replay must consume that same transcript before forward
preservation and target determinism can identify the terminal outcome.

This is trace adequacy, not general target-to-source adequacy. Arbitrary
intermediate target executions, complete reverse coverage for every syntax
form, and universal `Simulation.ObserverPass.Verified` instances are not
prerequisites. Existing local inversions remain available when they expose a
real semantic fact or compiler bug.

## Honest Safety Boundary

Scratch-backed compilation reserves source memory for compiler spill frames.
Target execution alone does not prove that source execution avoids that
reservation. The public theorem therefore requires source-facing guarded
termination under the program memory contract. This checks reservation
separation, active-memory consistency, host bounds, static-mode permissions,
and terminal reads along the concrete replay without treating compiler
acceptance as proof of source safety. It contains no generated code,
allocation certificate, or semantic call oracle. Exact transcript consumption
is not assumed; it is derived from the concrete target outcome.

## Minimum Obligations

- [x] Yul -> Functions: whole-program forward preservation for regular and
  terminal outcomes.
- [x] Functions -> allocated Locals/Expressions: compiler-selected whole-main
  forward preservation, including stack-only and scratch allocations.
- [x] Lower passes: pass-owned forward preservation through Structured,
  TypedCfg, Assembly, and bytecode.
- [x] Target observer: concrete execution yields an exact self-replay over its
  emitted transcript.
- [x] Source safety owner: define source-facing guarded termination without
  assuming exact transcript consumption.
- [x] Yul -> Functions replay bridge: use forward preservation, cross-fuel
  uniqueness, and target cursor exhaustion to derive exact source replay and
  align terminal outcomes.
- [x] Public target composition: connect a concrete terminal bytecode run to
  the compiler-selected Functions run through pass-owned
  allocation/Structured/TypedCfg/Assembly interfaces.
- [x] `Yul.EndToEnd`: prove stack-only `ClosedResourceCorrect` with explicit
  source validation and guarded source execution premises.
- [x] Final integration: full verification root, architecture guard, hole
  scan, axiom audit, aggregate proof gate, and `git diff --check`.

## Remaining Extensions

The first honest public theorem is complete for compiler-selected stack-only
artifacts with no external effects and explicit terminal EVM halts. General
backward adequacy is not a prerequisite.

- Scratch-backed artifacts need a public source reservation/depth-safety
  premise strong enough to instantiate the existing spill preservation
  theorem for the concrete run.
- The source cursor non-overshoot fact can eventually be derived from guarded
  canonical semantics, simplifying `SourceExecutionSafe`; it is currently an
  explicit source-semantic invariant, not an exact-replay assumption.
- Ordinary Yul fallthrough needs a separate completion boundary because the
  generated CFG currently represents program end with an invalid terminator.

## Architecture Guards

No observer-specific compiler, duplicate control interpreter, public replay
certificate, public call oracle, or direct vertical Yul-to-bytecode proof
corridor. Forward preservation and trace adequacy remain independent
capabilities owned by adjacent modules.
