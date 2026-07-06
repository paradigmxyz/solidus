# The Solidus Optimization Challenge

Solidus is a formally verified Solidity/Yul → EVM bytecode compiler: a
single Lean 4 theorem, `Solidus.compile_correct`, connects the source
program's semantics to the emitted bytes on the pinned EvmYul interpreter.
The challenge: **make the compiled contracts cheaper — deployment plus
runtime gas, as aggressively as you like — while the theorem still
proves.**

Because the correctness claim is a machine-checked theorem over a frozen
specification, there is no "did you break something" review step. If your
compiler builds, the axiom audit is clean, and the frozen spec elaborates
against it, your rewrite is correct by construction. Rewrite any pass, any
IR, any internal proof. The theorem is the only referee.

## The record

- **Metric:** total gas to **deploy and exercise** a private test suite:
  each contract's deployment transaction plus a fixed set of private
  transaction vectors executed against it, on a pinned executor. One
  number. Deployment gas prices bytecode size at the chain's real rate
  (200 gas/byte), so size-vs-runtime tradeoffs are priced by the metric
  itself rather than by a rule; the vector mix (calls per deployment)
  plays the role of solc's `--optimize-runs` and is fixed per season.
- **Record threshold:** a submission takes the record if it improves on the
  current record by **≥ 0.1% (relative)**.
- **Validity:** the compiler must successfully compile *every* contract in
  the suite (fail-closed: no output, no score); every runtime image must
  satisfy **EIP-170 deployability (≤ 24,576 bytes)** and every creation
  image the EIP-3860 initcode cap (≤ 49,152 bytes); every vector
  transaction must produce the same observable result as the reference
  (the correctness theorem guarantees this for the source semantics — the
  vector check is a redundant sanity gate, not the trust anchor); all
  within the per-contract timeout and total wall-clock budget on the
  pinned CI hardware, with the proof gate green.

## What is frozen

Submissions may not modify (CI hash-checks these, and the private scoring
runner independently re-checks from configuration you cannot touch):

- `EvmCompiler/Solidus/Defs.lean` and `EvmCompiler/Correctness.lean` — the
  public entry point `Solidus.compile?` and the correctness theorems;
- the semantic framework the statement is expressed in (the Simulation
  modules, the Yul interaction semantics, the assembly/open interpreter
  semantics modules — see `benchmarks/frozen_manifest.txt`);
- the `EvmYul` dependency pin and `lean-toolchain`;
- the CI workflow files and the evaluation harness (`scripts/opt_harness.sh`
  and what it invokes).

Everything else — every compiler pass, every IR, every internal proof — is
yours to rewrite. Internal proofs are implementation detail: restructure
them, delete them, replace them, as long as the frozen theorems still prove.

## Proof gate

- `lake build EvmCompiler.Verification` must succeed.
- `#print axioms` on `Solidus.compile_correct` and
  `Solidus.compile_correct_creation` must report exactly
  `[propext, Classical.choice, Quot.sound]`. This mechanically excludes
  `sorry`, `native_decide`, and smuggled axioms.
- Run both locally via `scripts/opt_harness.sh check`.

## How to enter

1. Fork the repo; branch from `arena` (the current record) or from any
   `record-NNN` tag — building on older records is allowed and encouraged.
2. Optimize. Iterate locally with `scripts/opt_harness.sh full` against the
   public `examples/` corpus.
3. Open a PR targeting `arena`. State which record you branched from
   (`Based-on: record-NNN`); CI verifies it by git ancestry.
4. Public CI runs the proof gate, the frozen-hash check, and the public
   corpus. When it is green and your public-corpus improvement is
   plausible, a maintainer labels the PR for private scoring.
5. The private runner (sandboxed, offline) verifies the frozen hashes
   independently, re-runs the proof gate, compiles the private suite, and
   reports one number: total bytes.
6. Beat the record by the threshold → your PR is merged to `arena`, tagged
   `record-NNN+1`, and you enter the leaderboard permanently. The
   leaderboard records every holder chronologically, with the lineage of
   which record each one built on.

One private scoring per PR per green public CI. The private suite is
refreshed between seasons, never within one.

## Language coverage note

**Unbounded recursion is not supported, by design.** A function whose
recursion depth depends on runtime input has no static bound on its
operand-stack requirement, and the correctness theorem excludes stack
overflow from the compiled code's possible behaviors — so no
stack-headroom certificate can exist and `Solidus.compile?` fail-closes.
This is a consequence of the guarantee, not a bug: the reference compiler
accepts such code and emits bytecode that can stack-overflow at runtime on
deep inputs — a behavior the source semantics never sanctioned. Solidus
refuses to emit code it cannot prove safe. Write recursive logic as loops.

## Rules of engagement

- Your submission becomes part of the public lineage under this repo's
  license; later records will build on your code. That is the point.
- The compiler must be deterministic: CI compiles the corpus twice and
  requires byte-identical output. Gas is measured on a pinned executor
  version named in the season config; measurements are deterministic given
  the vectors, so record comparisons are exact.
- Search/superoptimization inside the compiler is allowed within the time
  budget. What the proof guarantees, you don't have to justify.
- No tampering with the harness, workflows, or frozen files (CI rejects
  it; the private runner rejects it independently even if public CI is
  somehow fooled).
- The private suite is private. Probing it through submission side-channels
  (e.g., encoding suite-detection into the compiler) is grounds for
  disqualification; it also won't help — per-contract results are never
  reported.

## Why this is interesting

Classical compiler contests bound cleverness by reviewability: a rewrite
nobody can review doesn't ship no matter how much it saves. Here the
reviewer is a proof checker, so the search space is bounded only by what
you can prove — and the current implementation leaves a lot on the table
(it emits several times more bytecode than solc's own backend on the same
input). The leaderboard's lineage graph will show whose ideas survived,
whose were built on, and which abandoned branches turned out to be worth
reviving. It is a public experiment in adversarial, cumulative,
machine-checked engineering.
