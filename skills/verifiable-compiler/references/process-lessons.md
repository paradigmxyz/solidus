# Process Lessons From An Earlier Verified-Compiler Attempt

These lessons come from an earlier, abandoned attempt at a verified
Solidity-flavored compiler. That project built a large executable surface —
frontend scaffolding, ABI/storage metadata, fixtures, CLI reports — before any
crisp top-level theorem existed, and recovered only by archiving the realistic
backend and moving proof development to a tiny target machine until the
theorem shapes were stable. None of its architecture carried over; the process
lessons did.

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
