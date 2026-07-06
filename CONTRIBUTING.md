# Contributing

There are two ways to contribute to this repository.

## 1. Contest submissions (Solidus Arena)

The arena is a cumulative, machine-checked optimization contest: make the
compiled contracts cheaper (deploy + runtime gas) while the correctness theorem
still proves.

**Read [`CHALLENGE.md`](CHALLENGE.md) first** — it defines the metric, the
record threshold, what is frozen, and how scoring works.

Submission flow:

1. Fork and branch from `arena` (the current record) or any `record-N` tag.
2. Optimize. Iterate locally with the harness:

   ```
   scripts/opt_harness.sh full          # proof gate + gas bench
   ```

   See [`OPTIMIZING.md`](OPTIMIZING.md) for the harness manual.
3. Open a PR **targeting the `arena` branch**. State which record you branched
   from with a `Based-on: record-N` line in the PR body (CI verifies it by git
   ancestry).

### The frozen-file rule

Submissions may **not** modify the frozen specification, the semantic
framework, the toolchain/dependency pins, or the evaluation harness. The exact
list is [`benchmarks/frozen_manifest.txt`](benchmarks/frozen_manifest.txt), and
CI hash-checks it (the private scoring runner re-checks it independently).
Everything else — every compiler pass, every IR, every internal proof — is
yours to rewrite.

### Proof-of-work expectations

Before you submit, your local run should be:

- **Green:** `scripts/opt_harness.sh full` passes — `lake build
  EvmCompiler.Verification` succeeds and `#print axioms` on the public theorems
  is exactly `[propext, Classical.choice, Quot.sound]` (no `sorry`,
  `native_decide`, or smuggled axioms).
- **Deterministic:** the compiler emits byte-identical output on a repeat
  compile of the same input.
- **Complete:** every corpus contract compiles (the compiler fail-closes — no
  output means no score).

Public CI runs the fast-fail versions of these gates on your PR. When it is
green and your public-corpus improvement is plausible, a maintainer requests
private scoring (out of band; the private runner is not in this repo).

## 2. Non-contest contributions

Improvements to the compiler that are not arena submissions — bug fixes,
refactors, new language coverage, tooling — are welcome via PRs targeting
`main`. The same proof gate applies: keep `scripts/opt_harness.sh check` green.
You can delete the arena-specific sections of the PR template for these.
