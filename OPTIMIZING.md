# The optimization harness

This is the reference manual for `scripts/opt_harness.sh`, the tool you use to
measure emitted **gas** and to run the correctness gate locally.

For the contest rules — the metric, the record threshold, what is frozen, how to
submit — see **`CHALLENGE.md`** at the repo root. This document only describes
the tool.

## The metric: total gas

The contest scores **total gas**, not bytecode size. For every corpus contract:

```
total_gas = deploy_gas + exec_gas
```

* **`deploy_gas`** — the cost of the **deployment transaction**. In the public
  harness it is priced arithmetically from the yellow paper
  (`deploy_gas_model = "computed"`); the private runner measures the real
  `CREATE` gas (constructor execution included). Either way deployment prices
  bytecode **size** at 200 gas/byte, so an oversized contract is penalised by
  the metric — there is no separate size cap:

  ```
  deploy_gas = 21000                       (G_transaction)
             + 32000                       (G_txcreate)
             + calldata_cost(creation)     (4/zero byte, 16/non-zero byte)
             + 2 * ceil(len(creation)/32)  (EIP-3860 initcode word cost)
             + 200 * runtime_bytes         (code-deposit, 200/byte)
  ```

* **`exec_gas`** — the summed gas of a fixed, ordered set of **execution
  vectors** replayed against the compiled image on the pinned executor
  (`exec_gas_model = "measured-callgas+intrinsic"`): the raw `CALL` opcode gas
  is measured with `gasleft()` deltas inside a Foundry EVM, and the per-vector
  transaction intrinsic (`21000 + calldata cost`) is added so each number is a
  faithful EOA→contract transaction cost.

Because deployment is 200 gas/byte of code, **shrinking bytecode still helps** —
it is now one term of the score rather than the whole score. Cheaper hot-path
execution is the other lever.

### Deployability sizes (informational only — no cap)

EIP-170/EIP-3860 deployment-size limits are **no longer validity conditions.**
Deployment gas already prices code size at the chain's real rate (200 gas/byte),
so a size-vs-runtime tradeoff is priced by the metric itself rather than gated by
a rule. The historical sizes are still reported, informationally:

| size | threshold | field |
|-----|-------|-------|
| EIP-170  | runtime image  > 24576 bytes | `eip170_ok` |
| EIP-3860 | creation image > 49152 bytes | `eip3860_ok` |

A contract over a threshold gets `cap_ok = false`, is listed under
`cap_violations`, and is marked `>>` in the table — all purely informational.
`bench` always exits `0` on oversized contracts; only compile failures (and, with
`--fail-on-regression`, a gas regression) fail the run. **`--enforce-caps` is a
deprecated no-op** kept for backward compatibility.

Oversized contracts pay **real measured CREATE gas**: the gas runner raises
forge's in-harness `code_size_limit` (from which foundry derives the EIP-3860
initcode limit) far above any real contract, so every contract — including
>24576-byte runtimes — deploys through the real `CREATE` path with its
constructor executed and immutables set. The `>24576` flag is a deployability
FYI, nothing more.

### Solc-parity sentinel

Every `baseline`/`bench` also compiles each contract with plain solc under the
**same** via-ir + Yul-optimizer settings and records `solc_runtime_bytes` plus
the per-contract ratio `solc_ratio = ours / solc`. The table shows a `solcRT`
column and a `ratio` column, and the totals row carries the overall
ours/solc runtime-byte ratio. Treat a ratio regression as a failure even when
absolute gas improves: it is the early-warning signal that a benchmark-config or
codegen change went the wrong way (a misconfigured benchmark once fed the backend
unoptimized Yul and inflated every number several-fold — a differential ratio
would have caught it immediately).

## What it does

The harness has two jobs:

1. **Measure gas.** It compiles a corpus of Solidity sources through the only
   supported entry, the raw solc Standard JSON path
   (`scripts/solc_lean_standard_json.py` → `evm-compiler-backend raw-image`),
   then computes each contract's `deploy_gas` and measures its `exec_gas` on the
   pinned executor. It reports per-contract and total gas plus the underlying
   runtime/creation byte sizes and the cap flags.
2. **Gate correctness.** It builds the proof root and checks the axiom footprint
   of the public theorems, so you can confirm a change is still valid before you
   trust a gas number.

The harness itself is part of the frozen evaluation machinery (see
`CHALLENGE.md`) — treat it as read-only.

## The executor

The gas runner (`scripts/opt_gas_runner.py`) uses **Foundry `forge test`** — the
same EVM engine the repo's differential execution-compare gates use
(`scripts/compare_contract_call_bytecode.py`). For each contract it renders a
throwaway Forge test that:

* installs the compiled image — a real `CREATE` from the creation bytecode (so
  constructor state and immutables are honoured). The rendered `foundry.toml`
  raises `code_size_limit` far above any real contract, so even a >24576-byte
  runtime deploys through `CREATE`; `vm.etch` of the runtime image is only the
  fallback for a genuinely reverting constructor;
* replays each vector with `vm.prank(sender)` + a low-level `CALL`, measuring
  raw call gas via `gasleft()` deltas;
* writes the per-vector `used,ok` rows out via `vm.writeFile`.

The executor pin is recorded in the output JSON under `executor`
(`forge_version`, `evm_version`, both gas models, the historical size
thresholds). The pinned
versions are **forge 1.5.1-stable** at **evm_version `cancun`**, **solc 0.8.26**.
Determinism: the same compiled input yields the same totals; verify with a
double `bench`.

## Subcommands

```
scripts/opt_harness.sh baseline                    # (re)record the reference sizes
scripts/opt_harness.sh check                        # correctness + axiom gate
scripts/opt_harness.sh bench [--fail-on-regression] # measure + diff vs baseline
scripts/opt_harness.sh full  [--fail-on-regression] # check, then bench
```

| subcommand | what it does |
|------------|--------------|
| `baseline` | Compile the corpus, measure gas, and write the reference to `benchmarks/opt_baseline.json`. Your gas deltas are measured against this file. The prior size-only baseline is preserved once as `benchmarks/opt_baseline_size_only.json`. |
| `check`    | `lake build EvmCompiler.Verification`, then run `#print axioms` on the pinned public theorems and reject any axiom outside the allowed set. This is what tells you the compiler is still correct. |
| `bench`    | Compile the corpus, measure gas, diff against the baseline, print a table, and write `benchmarks/opt_last_run.json`. Exits nonzero if any corpus contract fails to compile. Oversized contracts are reported informationally and never fail the run. |
| `full`     | `check` then `bench`. |

`--fail-on-regression` (on `bench`/`full`) makes the run exit nonzero if total
**gas** grew relative to the baseline. `--enforce-caps` is a **deprecated no-op**
(EIP-170/EIP-3860 sizes are no longer validity conditions).

**A gas number only counts once `check` passes.** A compiler that emits cheaper
bytecode but no longer proves correct has no score. Use `bench` on its own for
fast exploration (it does not rebuild the proof root); use `full` — or at least
`check` — before you rely on a result.

### Sample output

```
$ scripts/opt_harness.sh bench

=== BENCH ===
commit 1a2b3c4d5e6f  2026-07-06T02:41:08Z  solc 0.8.26+commit.8a97fa7a...
executor: foundry-forge-test forge Version: 1.5.1-stable  evm=cancun  deploy=computed
contracts: 48   wall time: 365.0s (compile 340s + gas 25s)

  contract                                   total_gas    deploy    exec runtime  creat  solcRT  ratio
------------------------------------------------------------------------------------------------------
  DynamicStorageSurfaceBox.sol:Dynamic...      3620500   3170600  449900   15853  16012    4231   3.75
  Simple.sol:Simple                             360907    336560   24347    1310   1405     620   2.11
------------------------------------------------------------------------------------------------------
  TOTAL                                        3981407   3507160  474247   17163  17417    4851   3.54

  solc-parity (ours/solc runtime bytes)                                                             3.54

wrote benchmarks/opt_last_run.json
```

A leading `>>` marks a contract over the historical 24,576-byte EIP-170 size
(informational only). The `solcRT`/`ratio` columns show solc's own runtime bytes
on the identical input and the `ours/solc` ratio. A negative `Δtotal` is cheaper
gas. A
`new` marker means a contract appeared that was not in the baseline; a
`MISSING vs baseline` line means a contract that used to compile no longer does.

## Exit codes

| code | meaning |
|------|---------|
| `0`  | pass |
| `2`  | usage / configuration error |
| `10` | proof build failed (`check`) |
| `11` | axiom-footprint gate failed (`check`) |
| `20` | a corpus contract failed to compile (`bench`) |
| `30` | total-gas regression (`bench --fail-on-regression`) |

Exit `40` (EIP-170/EIP-3860 cap enforcement) was **removed**: deployment-size
caps are no longer validity conditions. A compile failure takes precedence over
a gas regression; oversized contracts never fail the run.

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

## Execution vectors

Each corpus contract has an ordered transaction list at
`benchmarks/vectors/<Contract>.vectors.json`. These are the `exec_gas` inputs.

```json
{
  "contract": "Counter.sol:Counter",
  "source": "derived-from-test:scripts/test_solidity_contract_call_compare.sh",
  "deploy": { "constructor_args": "0x", "value": 0 },
  "vectors": [
    { "calldata": "0x3fa4f245", "value": 0,
      "sender": "0x00000000000000000000000000000000000010a0" }
  ],
  "empty_reason": null
}
```

* `source` records provenance: `derived-from-test:<script>` (the calldata was
  taken from an existing differential execution-compare test),
  `auto-abi-zeroargs` (minimal honest vectors built from the contract's ABI —
  each external function called once with zero-valued arguments), or `empty`.
* `deploy.constructor_args` / `deploy.value` seed the real `CREATE` (which every
  contract now takes, regardless of size).
* Each vector is `{calldata, value, sender}`; `sender` is applied with
  `vm.prank`.
* An interface-only or internal-only unit records `"vectors": []` with an
  `empty_reason`; its **deployment gas still counts**.

Regenerate the auto/derived drafts with
`scripts/opt_gas_runner.py gen-vectors [--force]` (does not overwrite existing
files without `--force`).

## Output files

All under `benchmarks/`:

- `opt_baseline.json` — the reference gas measurement, schema v2 (`baseline`).
- `opt_baseline_size_only.json` — the pre-gas (schema v1) baseline, kept for
  history.
- `opt_last_run.json` — the most recent `bench` measurement.
- `opt_check.json` — the most recent `check` result (build/axiom status).
- `vectors/<Contract>.vectors.json` — the execution vectors (see above).

Run-record schema (v2):

```json
{
  "schema_version": 2,
  "commit": "...",
  "date": "2026-07-06T02:41:08Z",
  "solc_version": "0.8.26+commit...",
  "executor": {
    "engine": "foundry-forge-test",
    "forge_version": "forge Version: 1.5.1-stable",
    "evm_version": "cancun",
    "deploy_gas_model": "computed",
    "deploy_gas_formula": "21000 + 32000 + calldata_cost(creation,4/16) + 2*ceil(len(creation)/32) + 200*runtime_bytes",
    "exec_gas_model": "measured-callgas+intrinsic",
    "eip170_runtime_cap": 24576,
    "eip3860_creation_cap": 49152
  },
  "input_epoch": "optimized-yul",
  "solc_parity_ratio": 3.54,
  "contracts": [
    {"name": "Simple.sol:Simple", "runtime_bytes": 1310, "creation_bytes": 1405,
     "deploy_gas": 336560, "exec_gas": 24347, "total_gas": 360907,
     "cap_ok": true, "eip170_ok": true, "eip3860_ok": true,
     "solc_runtime_bytes": 620, "solc_ratio": 2.11,
     "vectors": 1, "vector_source": "derived-from-test:...", "compile_ms": 6100}
  ],
  "excluded": [{"source": "...", "reason": "..."}],
  "empty_sources": ["..."],
  "cap_violations": [
    {"name": "...", "runtime_bytes": 42848, "creation_bytes": 42943,
     "eip170_ok": false, "eip3860_ok": true}
  ],
  "total_runtime_bytes": 123456,
  "total_creation_bytes": 145678,
  "total_deploy_gas": 9711712,
  "total_exec_gas": 317181,
  "total_gas": 10028893,
  "wall_ms": 480000,
  "compile_wall_ms": 360000,
  "gas_wall_ms": 120000
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
  `scripts/opt_harness.py`, `scripts/opt_gas_runner.py`,
  `benchmarks/corpus.txt`, `benchmarks/vectors/`, and
  `proof_artifacts/stack_backend_production_smoke.lean`.

Everything else — every compiler pass, every IR, every internal proof — is fair
game. Internal proofs are implementation detail: restructure, split, merge, or
rewrite them however you like, as long as `check` stays green.

### Freeze-closure checks (import-level and definition-level)

Two checkers guard the freeze cone against an adversary who keeps the frozen
file hashes but redefines something the frozen statements depend on:

- `scripts/check_frozen_closure.py benchmarks/frozen_manifest.txt` — IMPORT-level
  closure: every frozen `.lean` may only `import` another frozen file, a pinned
  package, or an explicitly `#allow`-ed module. Fast, but blind to *which*
  symbols of an allowed import are actually used; the `#allow:` residuals are
  documented promises that the frozen definitions do not touch those modules'
  symbols.

- `lake env lean --run scripts/check_frozen_defs.lean` — DEFINITION-level
  closure, which verifies those promises. It walks the actual definitional cone
  from the two public theorem statements (types only — proofs are mutable) and
  from every declaration in the relocated spec modules (`Solidus.Defs`,
  `.Bridge`, `.SourceRun`, `.Decode`, `.Frontend`, `Correctness`), following
  used-constant references through type *and* value of frozen definitions. It
  PASSES only if every reached constant lives in a frozen-manifest module, an
  `EvmYul.*` module (pinned, treated as terminal), or Lean core. The walk stops
  at an explicit allowlist — the deliberately-mutable `compile?`/`compileUnlinked?`
  entry family (the compiler entries plus the artifact/certificate/image-bytes
  projections the theorems quantify *over*, not over their contents); see the
  allowlist comments in the script for the per-constant justification. On failure
  it prints each escaping constant, its origin module, and the immediate frozen
  parent that referenced it, then exits nonzero. Requires a built
  `EvmCompiler.Correctness` (`lake build EvmCompiler.Correctness`); runtime is
  ~20s once built. This check reads the environment as built, so it reflects the
  current (possibly uncommitted) sources.

  Status: the definition-level check PASSES. The 29 escaping constants that
  failed earlier snapshots were relocated into frozen modules during the freeze
  finalization; the single remaining residual,
  `Assembly.Compact.InteractionSemantics.openRunNResult` (referenced by the
  `Solidus.compile_correct` statement), is accepted because its containment is
  proved outright in `EvmCompiler/Solidus/OpenRunContainment.lean`
  (`openRun_triangulated` et al.). The checker reports it as an accepted
  proved-contained residual, not an allowlist entry (the allowlist is only for
  the `compile?`-entry family).

## Timing

`bench` compiles the whole corpus (solc plus two backend invocations per
contract) and then prices each contract on the Foundry executor: expect
**minutes** (compile dominates; the gas leg adds a shorter tail — one
`forge test` per contract). `check` rebuilds the proof root
`EvmCompiler.Verification`, which can take **many minutes** cold and is faster
incrementally. Iterate on `bench` for fast gas feedback; run `check`/`full`
when you need to confirm the change is valid.
