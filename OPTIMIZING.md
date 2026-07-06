# The optimization harness

This is the reference manual for `scripts/opt_harness.sh`, the tool you use to
measure emitted bytecode size and to run the correctness gate locally.

For the contest rules — the metric, the record threshold, what is frozen, how to
submit — see **`CHALLENGE.md`** at the repo root. This document only describes
the tool.

## What it does

The harness has two jobs:

1. **Measure size.** It compiles a corpus of Solidity sources through the only
   supported entry, the raw solc Standard JSON path
   (`scripts/solc_lean_standard_json.py` → `evm-compiler-backend raw-image`),
   and reports per-contract and total runtime + creation bytecode sizes.
2. **Gate correctness.** It builds the proof root and checks the axiom footprint
   of the public theorems, so you can confirm a change is still valid before you
   trust a size number.

The harness itself is part of the frozen evaluation machinery (see
`CHALLENGE.md`) — treat it as read-only.

## Subcommands

```
scripts/opt_harness.sh baseline                    # (re)record the reference sizes
scripts/opt_harness.sh check                        # correctness + axiom gate
scripts/opt_harness.sh bench [--fail-on-regression] # measure + diff vs baseline
scripts/opt_harness.sh full  [--fail-on-regression] # check, then bench
```

| subcommand | what it does |
|------------|--------------|
| `baseline` | Compile the corpus and write the reference sizes to `benchmarks/opt_baseline.json`. Your size deltas are measured against this file. |
| `check`    | `lake build EvmCompiler.Verification`, then run `#print axioms` on the pinned public theorems and reject any axiom outside the allowed set. This is what tells you the compiler is still correct. |
| `bench`    | Compile the corpus, diff against the baseline, print a table, and write `benchmarks/opt_last_run.json`. Exits nonzero if any corpus contract fails to compile. |
| `full`     | `check` then `bench`. |

`--fail-on-regression` (on `bench`/`full`) makes the run exit nonzero if total
bytecode grew relative to the baseline.

**A size number only counts once `check` passes.** A compiler that emits smaller
bytecode but no longer proves correct has no score. Use `bench` on its own for
fast size exploration (it does not rebuild the proof root); use `full` — or at
least `check` — before you rely on a result.

### Sample output

```
$ scripts/opt_harness.sh bench

=== BENCH ===
commit 1a2b3c4d5e6f  2026-07-06T02:41:08Z  solc 0.8.26+commit.8a97fa7a...
contracts: 61   corpus wall time: 372.4s

contract                                      runtime  creation    Δrun    Δcre
--------------------------------------------------------------------------------
AbiBox.sol:AbiBox                                2104      2611       0       0
...
Simple.sol:Simple                                1310      1405     -12     -18
--------------------------------------------------------------------------------
TOTAL                                          123456   145678     -12     -18
% vs baseline                                                     -0.01%  -0.01%

wrote benchmarks/opt_last_run.json
```

Negative deltas are smaller bytecode. A `new` marker means a contract appeared
that was not in the baseline; a `MISSING vs baseline` line means a contract that
used to compile no longer does (a compile regression).

## Exit codes

| code | meaning |
|------|---------|
| `0`  | pass |
| `2`  | usage / configuration error |
| `10` | proof build failed (`check`) |
| `11` | axiom-footprint gate failed (`check`) |
| `20` | a corpus contract failed to compile (`bench`) |
| `30` | size regression (`bench --fail-on-regression`) |

## The axiom gate

`check` builds `EvmCompiler.Verification` and then runs `#print axioms` on the
public theorems pinned in
`proof_artifacts/stack_backend_production_smoke.lean`. It fails unless every
pinned theorem depends on **exactly**:

```
[propext, Classical.choice, Quot.sound]
```

Any other axiom — which is how a `sorry`, an `admit`, `native_decide`, or a
hand-written `axiom` would show up — fails the gate. This is the same mechanism
`scripts/verify_layer.sh proofs` uses.

## Output files

All under `benchmarks/`:

- `opt_baseline.json` — the reference sizes (`baseline`).
- `opt_last_run.json` — the most recent `bench` measurement.
- `opt_check.json` — the most recent `check` result (build/axiom status).

Run-record schema:

```json
{
  "commit": "...",
  "date": "2026-07-06T02:41:08Z",
  "solc_version": "0.8.26+commit...",
  "contracts": [
    {"name": "Simple.sol:Simple", "runtime_bytes": 1310,
     "creation_bytes": 1405, "compile_ms": 6100}
  ],
  "excluded": [{"source": "...", "reason": "..."}],
  "empty_sources": ["..."],
  "total_runtime_bytes": 123456,
  "total_creation_bytes": 145678,
  "wall_ms": 372400
}
```

## The corpus

The list of sources compiled each run lives in `benchmarks/corpus.txt` — one
Solidity source path per line, relative to the repo root; blank lines and lines
beginning with `#` are ignored. The manifest is explicit so the measured set is
obvious and reproducible.

Sources are compiled **self-contained**: each file is handed to solc as a
single-file Standard JSON `content` input. Files that need external imports or
import remappings, or that require a newer solc than the pinned one, are omitted
from the manifest; the reasons are recorded at the top of `corpus.txt` and, for
any source that fails at measure time, under `"excluded"` in the run JSON.

Note that the official score is computed over a *private* suite on pinned CI
hardware (see `CHALLENGE.md`); `benchmarks/corpus.txt` is the public,
same-distribution stand-in you iterate against locally.

## What is frozen

The harness gates correctness against a frozen specification and a frozen target
interpreter. The authoritative frozen list is in `CHALLENGE.md`; in short, do
not edit:

- `EvmCompiler/Solidus/Defs.lean`, `EvmCompiler/Correctness.lean`,
  `EvmCompiler/Verification.lean` — the public entry point and the correctness
  theorems;
- the semantic framework the theorems are stated against —
  `EvmCompiler/Simulation/`, the Yul interaction semantics
  (`EvmCompiler/Yul/InteractionSemantics.lean` and the
  `FunctionsInteraction*` modules), and the assembly/open-interpreter semantics
  (`EvmCompiler/Assembly/Semantics.lean`, `PrimSemantics.lean`,
  `InteractionSemantics.lean`);
- the dependency pins: `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`
  (the `EvmYul` pin in particular);
- the evaluation machinery itself: `scripts/opt_harness.sh`,
  `scripts/opt_harness.py`, `benchmarks/corpus.txt`, and
  `proof_artifacts/stack_backend_production_smoke.lean`.

Everything else — every compiler pass, every IR, every internal proof — is fair
game. Internal proofs are implementation detail: restructure, split, merge, or
rewrite them however you like, as long as `check` stays green.

## Timing

`bench` compiles the whole corpus (solc plus two backend invocations per
contract): expect **minutes**. `check` rebuilds the proof root
`EvmCompiler.Verification`, which can take **many minutes** cold and is faster
incrementally. Iterate on `bench` for fast size feedback; run `check`/`full`
when you need to confirm the change is valid.
