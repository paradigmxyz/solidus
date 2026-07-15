# Process Lessons From The SolidCore Transcript

This is not SolidCore architecture. It is a process summary to avoid repeating
the same mistakes when starting a new verified compiler.

## What Happened

1. Started with an ambitious Solidity-compatible roadmap: Rust/Solar frontend,
   Lean checker, JSON interop, AST schema, fixtures, and compiler scaffold.
2. Built much of the project surface: Lean syntax/checker/semantics modules,
   ABI/storage metadata, compiler scaffolds, CLI reports, fixtures, and tests.
3. The user repeatedly pushed toward a real end-to-end verified compiler rather
   than a scaffold.
4. The work expanded aggressively: mappings, Keccak assumptions, ABI
   dispatch, events, storage layout, arrays, constructors, fixed bytes, signed
   subwords, parser questions, and RealEVM experiments.
5. The project risked having lots of executable functionality without a crisp
   top-level theorem covering it all.
6. A key zoom-out recognized that the RealEVM model was slowing theorem-shape
   development. RealEVM was archived and a tiny ToyEVM was made the active
   proof playground.
7. The ToyEVM path advanced faster: absolute PCs, conditional jumps, halting,
   expression compiler correctness, statement sequencing, statement `if/else`,
   function-body `STOP` boundary, and a counted backward-jump loop theorem.
8. The top-level active theorem was made honest about what was active and what
   was archived.
9. A small bridge from real AST statements to ToyEVM was added so accepted AST
   fragments could be connected to the PC-level interpreter theorem.
10. CLI/metadata needed repeated honesty fixes so a theorem was not advertised
    for features outside its accepted subset.

## Process Lessons

- Start with the theorem endpoint, not the feature list.
- The first target machine should be small enough that PC and control-flow
  proofs are cheap.
- A realistic backend can be reference material while theorem patterns mature.
- Metadata must be theorem-aware: do not mark every function verified just
  because a generic theorem exists for some smaller subset.
- Completion requires a prompt-to-artifact audit, not a green test suite.
- Parser trust questions are real, but verified parsing can wait until the core
  compiler theorem is stable if Lean checks the AST defensively.
- Long Lean builds change behavior: use narrow module builds, keep working on
  non-overlapping tasks, and avoid broad import graphs.
- External critic review is best for theorem boundaries and architecture traps,
  not for routine syntax.

## Transcript Summary

- Created and evolved a SolidCore roadmap.
- Implemented initial Rust/Lean scaffolding and fixtures.
- Shifted trust toward Lean-only compilation.
- Explored and then archived a heavier RealEVM backend.
- Built ToyEVM as a fast PC-level proof surface.
- Proved forward jumps, explicit else branches, halting boundaries, and counted
  backward loops in ToyEVM.
- Added theorem metadata and CLI reporting.
- Audited with `scripts/check.sh`, `rg` for `sorry/admit/axiom`, and `#print axioms`.
- Identified remaining gap: a true production path must connect accepted source
  programs through verified semantics, real byte emission, and a real target
  interpreter theorem before claiming full end-to-end verification.
