# Solidus Arena — Season-1 corpus design

This document is the measured rationale for the public optimization corpus
(`benchmarks/corpus.txt` + `examples/*.sol` + `benchmarks/vectors/*.json`). It
records *why* each contract is in the suite, the vector-mix rules that keep the
metric honest, and the known diagnostics gap. It is descriptive, not frozen —
edit it alongside any corpus change.

The scoring metric itself is frozen and unchanged (see `scripts/opt_harness.py`,
`scripts/opt_gas_runner.py`): every contract scores
`total_gas = deploy_gas + exec_gas`, where `deploy_gas` prices the deployment
transaction arithmetically (21000 + 32000 + calldata + initcode-words +
**200·runtime_bytes**) and `exec_gas` is the summed Foundry-measured cost of a
fixed ordered vector set (each vector capped at a 30M block budget). There is no
per-contract deployment-weight knob in the harness; the only corpus levers are
(a) which sources are listed in `corpus.txt` and (b) each contract's vectors.

## Why the redesign (measured observations from the 100-session campaign)

Numbers below are from the pre-redesign baseline (old compiler epoch, commit
`6a65d5c0`, `benchmarks/opt_baseline.json` at that revision) and the peephole
campaign log `EvmCompiler/TypedCfg/PEEPHOLE_PROGRESS.md`.

1. **Single-contract dominance.** Two contracts were ~66% of all corpus gas:
   `CreateLifecycleSurfaceBox` (33.8%) and `ExternalCallBox` (33.0%). Their
   weight came almost entirely from *inherent-burn* execution vectors, not from
   compiler-sensitive code (see §2). Separately, `AdversarialStackPressure` was
   the size-optimization outlier — **90.4% SWAP** opcodes, 8557 runtime bytes,
   15.4× vs solc, and single-handedly ~24% of the optimizer's byte win
   (`PEEPHOLE_PROGRESS.md` §74). Post-`chainCanon` (§94/§95) that contract
   collapsed to **1121 bytes** — the SWAP vein is consumed — so on the current
   optimized compiler it no longer dominates either axis; it is retained purely
   as a stack-pressure stress case.

2. **Inherent burns diluted the compiler signal.** ~65% of the old baseline gas
   was execution any compiler pays *identically*:
   - `ExternalCallBox` vector 5 = `staticcall` to the ecPairing precompile
     `0x08` with malformed input → the precompile OOG-burns **29,553,764 gas**
     (measured; `ok=false`). The other five vectors cost ~24k each.
   - `CreateLifecycleSurfaceBox` `create2Collision` → CREATE2 to an existing
     address is an EIP-684 collision that **consumes all forwarded gas**
     (~29.5M measured).
   These 30M OOG paths are invariant to code quality — they measure the EVM, not
   the compiler — so they drowned the size/gas signal the contest exists to
   reward. (Deployment gas, by contrast, prices code size at 200 gas/byte and
   *is* the primary compiler-sensitive signal.)

3. **Coverage gaps.** No contract exercised a deep internal call graph
   (procedure reuse across many call sites — where the remaining ~1.9× size gap
   vs solc lives, `PEEPHOLE_PROGRESS.md` §99) and none stressed the external
   selector dispatcher with many entry points.

4. **Redundancy.** 48 sources / 56 contracts, with many small `*Box` contracts
   near-identical in post-optimization opcode distribution.

## Design rules (enforced by the numbers, checked at bench time)

- **Dominance cap:** no contract exceeds ~10% of corpus `total_gas`;
  `AdversarialStackPressure` is held to ≤5%.
- **Inherent-burn share < 25%:** OOG/collision/precompile-intrinsic execution is
  kept as *bounded, valid* correctness paths (real precompile calls, real CREATE
  costs — tens of thousands of gas, not 30M OOG floods). Some is retained
  deliberately (it tests correctness), but it no longer sets the metric.
- **One representative per semantic family** (see roster) — storage, memory,
  strings, structs, enums, events, errors, try/catch, proxy, create,
  selfdestruct, precompiles, inline-assembly, modifiers, payable, fallback,
  reentrancy, library-linkage.
- **~40 contracts** (down from 56), each earning its place by exercising
  something distinct. Faster bench = faster CI.
- Frozen invariants kept: deploy+exec total-gas metric, determinism
  double-compile, fail-closed compile-everything validity.

## Roster

### Added (2)

| contract | family / rationale |
|---|---|
| `ProcedureReuseBox` | **Deep call-graph / procedure reuse** (goal 3a). ~11 non-recursive internal helpers (`_clamp`/`_mulDiv`/`_blend`/`_accrue`/`_score`/…) each called from multiple external entry points, so solc emits shared internal Yul functions reused across sites — the structure where the ~1.9× size gap vs solc concentrates (§99). Non-recursive ⟹ passes the stack-headroom cert. |
| `WideDispatchBox` | **Dispatcher-heavy** (goal 3b). 40 external selectors with tiny bodies, stressing solc's selector-sort/dispatch tree while keeping runtime small. |

### Pruned (18 sources retired from `benchmarks/corpus.txt`)

`ConstructorCounter`, `ConstructorAbiBox`, `ForkNeutralBox`, `Opcode44Surface`,
`EnumBytesBox`, `StructBox`, `ArrayBox`, `BytesBox`, `EventCounter`,
`RevertReason`, `InterfaceCase`, `BitwiseBox`, `EffectOrderingSurfaceBox`,
`AbiControlSurfaceBox`, `StorageArrayBox`, `StorageStructBox`, `ImmutableBox`,
`Simple`.

Each is subsumed by a kept representative of the same family (e.g.
`EnumBytesBox`/`StructBox`/`StorageStructBox` → `PackedStorageBox` covers
enum+struct+packed storage; `EventCounter` → `EventMatrix`; `RevertReason` →
`ErrorPanicBox`; `BitwiseBox` → `ArithmeticBox`; `ArrayBox`/`StorageArrayBox` →
`DynamicStorageSurfaceBox` + `LoopBox`; `EffectOrderingSurfaceBox`/
`AbiControlSurfaceBox` → `SemanticSurfaceBox` + `InlineAssemblyBox` +
`ModifierBox`).

**Note:** pruned `.sol` files are *retained on disk* — they remain fixtures for
non-scored differential/smoke scripts (`scripts/test_solidity_contract_call_compare.sh`,
etc.) and CI sentinels (`Simple.sol`/`Counter.sol` are the determinism-check
sentinels). Pruning removes them only from the *scored* corpus and deletes their
`benchmarks/vectors/*.json`. This avoids red states in the wider (non-frozen)
test suite while achieving the faster-bench / better-signal goal.

### Kept (30 sources → 38 contracts), by family

- **storage:** `Counter`, `MappingCounter`, `PackedStorageBox`,
  `DynamicStorageSurfaceBox` (the deliberate large storage/nested-ABI stress)
- **arithmetic:** `ArithmeticBox`
- **memory / strings:** `StringBox`, `AbiBox`
- **loops:** `LoopBox`
- **events:** `EventMatrix`
- **errors:** `ErrorPanicBox`
- **try/catch + reentrancy:** `TryCatchBox` (+`TryCatchTarget`),
  `ReentrantTryCatchSurfaceBox`
- **proxy:** `ProxyLifecycleSurfaceBox` (+`ProxyLifecycleLogicV1`/`V2`)
- **create / factory:** `FactoryBox` (+`ChildBox`), `CreateLifecycleSurfaceBox`
  (+`CreateLifecycleChild`) — *burn vectors retuned*
- **selfdestruct:** `SelfDestructBox`
- **fallback:** `FallbackBox`
- **modifiers / inheritance:** `ModifierBox` (+`ModifierBase`)
- **payable / context:** `PayableVault`, `EnvBox`
- **inline assembly / low-level:** `InlineAssemblyBox`, `CancunOpcodeSurface`
  (transient storage TLOAD/TSTORE + MCOPY), `SemanticSurfaceBox`
- **precompiles / external calls:** `PostCancunPrecompileBoundary`,
  `ExternalCallBox` — *burn vector retuned*
- **library linkage:** `MathLib`, `ExternalMathLib` (+`ExternalMathBox`)
- **token:** `MiniToken`
- **advanced types:** `AdvancedTypeSurfaceBox` (+`PriceMath`, user-defined value
  types + interface + abstract)
- **adversarial stress:** `AdversarialStackPressure` (SWAP stress; collapsed by
  `chainCanon`, retained as a stress case, held ≤5%)

## Vector retunes (burn taming — vector-only, no source rewrite)

- **`ExternalCallBox`:** the ecPairing-`0x08`-invalid OOG vector (calldata
  `0xad258fff…0008…`) is replaced with a *valid* precompile call
  (identity/SHA-256/valid-ecPairing empty input). External-call coverage
  (call/staticcall/delegatecall + returndata assembly) is preserved; exec drops
  from 29.67M → ~0.1M.
- **`CreateLifecycleSurfaceBox`:** the `create2Collision` (`0x1410fe88`) OOG
  vector is dropped. `createSuccess`, `createFailure` (constructor-revert
  rollback) and `parentBalance` remain, so the CREATE lifecycle + revert-data +
  balance-retention paths are still exercised at real, bounded cost.

The remaining inherent burns (valid precompile intrinsics in
`PostCancunPrecompileBoundary`/`ExternalCallBox`, real CREATE costs in
`FactoryBox`/`CreateLifecycleSurfaceBox`, SSTORE in the storage contracts) are
kept — they are correctness paths — but bounded so their combined share is
< 25% of total.

## Diagnostics path (creation objects)

Creation objects that reference child `datasize` / `dataoffset` need the
verified object-image planner's layout. The stack-diagnostics / stack-analysis
CLI now takes the Functions program from that same planner artifact, so
`CreateLifecycleSurfaceBox`, `FactoryBox`, and `ProxyLifecycleSurfaceBox` are
introspectable (previously the probe used an empty `ObjectLayout` and failed
at `resolveObjectBuiltinsIn?` even though `raw-image` succeeded).

## Baseline (new season, optimized compiler)

Regenerated with the promoted chain-canon compiler on the new corpus via
`scripts/opt_harness.sh bench`/`baseline`. See the "New-baseline validation"
section below for the measured totals, per-contract share extremes, and
inherent-burn share.

<!-- BASELINE_TOTALS -->
Measured `benchmarks/opt_baseline.json` (optimized chain-canon compiler, new
corpus; forge 1.5.1 / cancun, solc 0.8.26):

| metric | value |
|---|---|
| contracts | **40** (32 sources), 0 compile failures, 0 empty |
| total_gas | **24,986,512** = deploy 16,198,298 (65%) + exec 8,788,214 (35%) |
| runtime bytes | 65,126 (was 103,211 pre-redesign) |
| solc-parity (ours/solc runtime bytes) | **2.03** (was 2.86 pre-redesign) |

Constraint validation:

| rule | target | measured | verdict |
|---|---|---|---|
| max single-contract share | ≤ ~10% | **9.38%** (`DynamicStorageSurfaceBox`, deploy-bound at 9565 B) | PASS |
| `AdversarialStackPressure` share | ≤ 5% | **1.55%** (runtime collapsed 8557→1121 B via chainCanon) | PASS |
| inherent-burn share (precompile + CREATE exec) | < 25% | **4.1%** | PASS |
| compile everything (fail-closed) | 100% | 40/40 | PASS |
| determinism double-compile (sample) | byte-identical | 4/4 (ProcedureReuseBox, WideDispatchBox, Counter, DynamicStorageSurfaceBox) | PASS |

Share extremes: top = `DynamicStorageSurfaceBox` 9.38%; then `WideDispatchBox`
6.75%, `LoopBox` 6.64%, `ProcedureReuseBox` 6.05%; smallest scored contracts
`MathLib`/`PriceMath` at 0.27% each (deploy-only libraries). Deploy gas (priced
at 200 gas/byte) is the majority (65%) and is the primary compiler-sensitive
signal; the remaining exec is spread across real workloads (loops, SSTORE, deep
call graph, dispatch, bounded precompile/CREATE correctness paths).

The two 30M-OOG inherent-burn vectors that were ~66% of the *pre-redesign* total
are gone: `ExternalCallBox` fell 33.0% → 2.9% and `CreateLifecycleSurfaceBox`
33.8% → 3.9%.
<!-- /BASELINE_TOTALS -->
