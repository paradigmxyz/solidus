# Adjacent-inverse peephole — progress & continuation notes

Goal: cancel redundant instruction pairs (`push v ; pop`, then `swap n ; swap n`,
`dup n ; pop`) in generated code to shrink bytecode (⇒ deploy gas) while keeping
`Solidus.compile_correct` green. Diagnosis established that runtime/exec gas on
the hot contracts is dominated by *inherent* precompile / CREATE gas sinks
(identical to solc, unwinnable); the winnable lever is bytecode size, where we
emit ~2.86× solc and ~49% of ops are stack shuffles (61 literal `SWAP1;SWAP1`
no-ops on ExternalCallBox alone).

## Landed (green, axiom-clean) on branch `arena-opt`

- **(a)** `EvmCompiler/TypedCfg/PeepholeKernel.lean` —
  `pop_after_push_sameRuntimeData`: popping a just-pushed value restores the
  stack and perturbs only pc (`SameRuntimeData`).
- **(b)** `EvmCompiler/TypedCfg/Peephole.lean` — `peepholeBody`
  (tail-first `push v ; pop → ε`, structural recursion, collapses cascades) +
  `peepholeBody_length_le`.
- **(c-core)** `EvmCompiler/TypedCfg/PeepholeSemantics.lean` —
  - `runState_map_erase` / `runPops_map_erase`: closed `runState` is a
    `SameRuntimeData` congruence on peephole-safe instructions
    (`Instr.peepholeSafe`: ordinary stack/data ops; excludes `PC` and
    call/create/terminal). Reuses `Assembly.PrimOp.step_map_eraseRuntimeControl`.
  - `runBody_map_erase`: congruence lifted to whole straight-line bodies
    (equal output shape + `SameRuntimeData` final state).
  - `peepholeBody_runBody_erase`: **the preservation theorem** for the closed
    straight-line case.

## Remaining to a live, validated gas delta

1. **Open-interaction analogue.** The public theorem routes *every* block
   (call-free and call-bearing alike) through
   `TypedCfg.InteractionPreservation.OpenBlock.RunSimulates`, which is built on
   top of the closed `Preservation.Outcome.Simulates`. So the closed c-core is
   on the reuse path but must be lifted: prove the peephole preserves the OPEN
   step relation. The needed congruence already exists —
   `Assembly.InteractionPreservation.openStep_runtimeRel_of_ne_pc` (single-step
   `SameRuntimeData` congruence with `.pc` as the sole exception, and
   call/create handled by `callStep_runtimeRel`/`createStep_runtimeRel`). This
   removes the `Instr.peepholeSafe` call/create restriction at the open level.

2. **Global `.pc` guard.** Removing instructions shifts all subsequent label
   positions, so any `PC` opcode anywhere becomes observ­ably different. Guard
   the whole transform to identity if the program contains `.prim .pc`
   (decidable; `.pc` is essentially never emitted, so the peephole still fires
   corpus-wide). Alternatively thread `BodySafe`/no-pc as a certificate side
   condition.

3. **Wiring into `Block.lower?`.** Fold `peepholeBody` into the body before
   lowering so `certified.target = cfg.lower?` holds by definition. The
   `ProgramCert` certificate is derived from cfg blocks and is peephole-invariant
   (labels untouched, `maxAdditionalStack` only shrinks); `compileCertified?`
   stays valid. Re-prove, in order:
   - `EvmCompiler/TypedCfg/Lower.lean`: `lower?_starts_with_label`,
     `definedLabel_instr_mem_of_lower?`, `target_instr_mem_of_lower?` — these
     inspect only the label/terminator, so updates are mechanical (body is
     opaque to them).
   - `EvmCompiler/TypedCfg/Preservation.lean`: `lowerBodyFrom?_source_runNResult`
     and `lower?_eventually` — bridge canonical-code execution (existing) to
     peepholed via `peepholeBody_runBody_erase` + `runBody_map_erase`; the
     terminator step must accept a `SameRuntimeData`-equivalent body-end state
     (SameRuntimeData machinery already exists and is PC-insensitive).
   - `EvmCompiler/TypedCfg/InteractionPreservation.lean` +
     `InteractionPrefixPreservation.lean`: lift as in (1).
   - PCFits/byteLength: peephole only shrinks, so `PCFitsFrom` is preserved;
     re-derive the `pcAfter` arithmetic.

4. **Validate.** `scripts/opt_harness.sh full` (proof gate + axiom check +
   bench). Determinism holds automatically (peephole is a pure function of
   input). Expected: ~122 bytes on ExternalCallBox (61 pairs × 2), ~24.4k deploy
   gas there; corpus-wide, once `swap n ; swap n` is added (the dominant
   pattern), closing a meaningful fraction of the 67k-byte gap to solc.

### Blocker note

The wiring in (3) recompiles essentially the whole downstream tower
(compiler + RawAst + Verification) per iteration, which combined with the
open-interaction lift (1) exceeds a single working session. The three landed
milestones are the reusable, validated foundation; (1)→(4) is the remaining,
well-scoped continuation. `swap n ; swap n` (higher payoff than push;pop) needs
only an additional involution kernel lemma
(`EvmYul.swap n (EvmYul.swap n s) = .ok s` under stack depth ≥ n+1) plus one
more `peepholeBody` match arm; it reuses all of the c-core congruence machinery.
