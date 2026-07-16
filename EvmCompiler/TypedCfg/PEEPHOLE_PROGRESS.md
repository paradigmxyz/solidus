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

## Session-2 update (2026-07-16): reuse path found, c-block landed, wiring plan sharpened

Landed one more green, axiom-clean milestone and mapped a substantially cheaper
route than the original plan (3). Read this before continuing; it supersedes the
tactical detail (not the goal) of the numbered list below.

### (c-block) landed — `EvmCompiler/TypedCfg/PeepholeBlock.lean` (commit 43403cf)
`Peephole.Block.run_peephole_runtimeRel`: peepholing a peephole-safe body
preserves the CLOSED `Block.run` up to `InteractionCongruence.Block.
RuntimeOutcomeRel` (= `ExceptRel (=) Outcome.RuntimeRel`: equal control
label / equal halt kind / `SameRuntimeData` carried state), from the *same*
input state. Proof = `peepholeBody_runBody_erase` (c-core) composed with the
EXISTING terminator congruence, plus `runBody_erase_cases` (a helper turning the
`map eraseFst` equality into the error/error ∨ ok/ok+SameRuntimeData split).
Axioms: `[propext, Classical.choice, Quot.sound]`.

### KEY DISCOVERY: the RuntimeRel congruence tower already exists
The original notes pointed only at the single-step
`Assembly.InteractionPreservation.openStep_runtimeRel_of_ne_pc`. In fact
`EvmCompiler/TypedCfg/InteractionCongruence.lean` already builds the whole
block/program congruence over `SameRuntimeData`, all pass-agnostic:
- `Outcome.RuntimeRel` (inductive; identical to what c-block needed — do NOT
  redefine it), with `refl`/`symm`/`trans`.
- `Block.runTerm_runtimeRel`, `Block.runTermChecked_runtimeRel` (CLOSED
  terminator congruences — reused by c-block).
- `Block.openRunBody_runtimeRel`, `Block.openRun_runtimeRel`,
  `Program.openStep_runtimeRel` — OPEN congruences: same program, two
  `SameRuntimeData` states ⇒ `Simulation.Interaction.Rel RuntimeOutcomeRel`.
- `InteractionPreservation.OpenOutcome.Simulates` handles the halt case with an
  EXISTENTIAL simulant (`∃ simulated, SameRuntimeData simulated state ∧ target =
  stepInstrResult (prim kind.toPrimOp) simulated`), and
  `OpenOutcome.Simulates.runtime_left : RuntimeRel left middle → Simulates
  program middle target → Simulates program left target`.

### The halt-PC "blocker" is NOT a blocker
`Block.Halt` records the full pc-bearing state, so `Preservation.Outcome.
Simulates`'s halt arm is literal equality incl. pc — a naive local congruence
fails there. BUT it is reconciled two layers up: (a) `OpenOutcome.Simulates`
uses the existential simulant above, and (b) the frozen top relation
`EvmCompiler/Solidus/Bridge.lean::DoneRel` compares a halt via `OpenSameData`
(control/gas erased) and existentially binds `haltKind`; `output` for
return/revert is `state.toMachineState.H_return` (memory, i.e. runtime data,
`SameRuntimeData`-stable). So the peephole's byte/pc shift at a halt is absorbed;
no "global .pc guard" for halts is required. (A `.pc`-opcode guard is still
needed — `Instr.peepholeSafe` already excludes `.prim .pc`, and `BodySafe`
carries it.)

### Recommended architecture (cheaper than re-threading `lower?_eventually`)
Instead of manually re-proving `Preservation.lower?_eventually` with pc/
SameRuntimeData threaded through the terminator, model the peephole as a
`Program → Program` transform and reuse the existing generic preservation +
`runtime_left`:
1. `peepholeProgram P := { P with blocks := P.blocks.map (fun b =>
   { b with body := peepholeBody b.body }) }` (a valid `Program`; labels/terms
   untouched).
2. Prove `peepholeProgram` preserves `WellTyped` and
   `ProgramCounterIndependent` (peephole drops safe non-pc ops; `bodyType?`
   preserved because a `push;pop` pair is shape-neutral — this needs a
   `peepholeBody_bodyType?` lemma paralleling the shape bookkeeping in
   `peepholeBody_runBody_erase`).
3. **The one genuinely-new lemma**: the OPEN peephole body congruence
   `Rel RuntimeOutcomeRel (openRun (peepholeBlock b) state) (openRun b state)`
   — analogue of c-block but on `InteractionSemantics.Block.openRun`. ENABLER:
   `push`/`pop` are NOT `.prim`, so `openRunState` on them is `.done (runState
   …)` (`InteractionSemantics.openRunAt_eq_done_of_not_prim`); a cancelled
   `push;pop` pair therefore reduces to closed `.done` steps and the cancellation
   reuses `PeepholeKernel.pop_after_push_sameRuntimeData` directly, threaded
   through `Simulation.Interaction.Rel.bind`. Kept (possibly `.prim`)
   instructions ride `Instr.openRunAt_runtimeRel` + `Rel.bind` exactly as
   `openRunBody_runtimeRel` does. Structure the induction like
   `peepholeBody_runBody_erase` (tail-first, `peepholeBody_cons` split).
4. Insert `peepholeProgram` into the compile spine so `compileCertified?`
   lowers the peepholed program. Two options:
   - (a) fold into `Block.lower?` (original plan): `certificate?`/`certified.
     target` unchanged by definition, but every `lower?`-unfolding lemma sees the
     peepholed body; OR
   - (b) compose at the `Program` level: `compileCertified? (peepholeProgram P)`
     with the frontend still yielding `P`. Cleaner for reuse: the existing
     preservation applies verbatim to `peepholeProgram P` (a valid program), and
     the source↔`openRun P` bridge is untouched; glue = `openRun (peepholeProgram
     P) RuntimeRel openRun P` (from step 3, lifted program-wide) fed to
     `runtime_left`. Check where the frozen spine pins `certified.target` /
     `compileCertified?_target` to decide (a) vs (b); (b) may need a thin
     `compileCertified?_target`-style lemma for the composed entry.
5. Validate: `scripts/opt_harness.sh full`.

### Build-cost note
Steps 2–4 recompile `InteractionPreservation.lean` (165k) + downstream per
iteration. Kick narrow module builds (`lake build EvmCompiler.TypedCfg.<mod>`)
while iterating; only run the full `EvmCompiler.Verification` + harness at the
end. `swap n ; swap n` (step 4 of the original list) still layers cleanly on top
once push;pop is wired: add one `peepholeBody` arm + the involution kernel lemma;
all c-core/c-block/open machinery is reused unchanged.

## Remaining to a live, validated gas delta (original plan — tactics partly superseded above)

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

## Session-3 update (2026-07-16): open congruence + Program transform + WellTyped, all green

Landed the entire semantic core of the wiring plan (steps 1–2 of the session-3
directive) as four green, axiom-clean commits. What remains is purely the
mechanical spine splice plus ONE lowering-length lemma (details + exact recipe
below). Axioms on every new theorem: `[propext, Classical.choice, Quot.sound]`
(the two shape/label-only lemmas need only `[propext, Quot.sound]`).

### Landed commits (branch `arena-opt`)
- **(d) `EvmCompiler/TypedCfg/PeepholeOpen.lean`** (commit c062ab44) — THE
  genuinely-new lemma. `openRunBody_peephole_congr`: peepholed body from
  `state1` `Simulation.Interaction.Rel`-relates (`Instr.RuntimeAtRel`, i.e.
  `SameRuntimeData` up to pc/execLength) to the original body from any
  `SameRuntimeData` `state2`. Needs only `ProgramCounterIndependent` (NO
  call/create exclusion — CALL/CREATE ride `Instr.openRunAt_runtimeRel`;
  cancelled push/pop are non-prim `.done` steps reusing
  `pop_after_push_sameRuntimeData`). Lifts through the terminator via the
  existing `runTermChecked_runtimeRel` to `Block.openRun_peephole_runtimeRel`.
  Also `peepholeBody_bodyType?` (shape neutrality), `peepholeBlock` + proj simps,
  `openRunBody_nonprim_cons` / `openRunBody_push_cons` reductions.
- **(e) `EvmCompiler/TypedCfg/PeepholeProgram.lean`** (commit c2f7c552) —
  `peepholeProgram : Program → Program` (blocks.map peepholeBlock; CFG untouched);
  `findBlock?_peepholeProgram`, `peepholeProgram_programCounterIndependent`, and
  the WHOLE-PROGRAM open congruence `openStep_/openRunN_/openRunNPrefix_peephole_congr`
  relating the ORIGINAL program from `state1` to the PEEPHOLED program from any
  `SameRuntimeData` `state2` (original on the LEFT), up to
  `Block.RuntimeOutcomeRel`. Plus `runtimeOutcomeRel_symm/_trans`,
  `rel_runtimeOutcomeRel_symm`.
- **(f) `EvmCompiler/TypedCfg/PeepholeSpine.lean`** (commit 58ed8314) —
  `peepholeProgram_wellTyped` (via `labelShape?_peepholeProgram` invariance ⇒
  `terminator_type?_peepholeProgram`; `block_wellTyped_peepholeProgram`;
  `emittedLabels_/labelsUnique_peepholeProgram`). Ensures
  `(peepholeProgram cfg).compileCertified?` succeeds whenever cfg's does.

### Exact wiring the spine map established (session-2/3 recon, verified)
Public spine (all NON-frozen; frozen public theorems never name `fuelBudget`, so
the change is absorbed at their `∃ openFuel`):
- `Compiler/StackArtifact.lean:33 compile?` builds `cfg := generated.cfg`, then
  `certified ← cfg.compileCertified?` (line 59), `target ← compileExecutable?
  certified.target` (60). `compile?_parts` (72) exposes `hGenerate` (source),
  `cfg.WellTyped`, `cfg.ProgramCounterIndependent`, `cfg.compileCertified? = some
  certified` (assembly).
- `Compiler/OpenInteractionComposition.lean:808 yulToNormalizedStackAssemblyPrefixForward`
  couples BOTH ends to the SAME `cfg`: `hGenerate`/`hWellTyped` feed the source
  bridge `yulToNormalizedStackTypedCfgPrefixForward` (→ `openRunNPrefix cfg`);
  `hCompile : cfg.compileCertified? = some artifact` + `hIndependent` feed the
  assembly bridge `InteractionPrefixPreservation.Program.
  compileCertified?_entry_openRunNPrefix_assembly_follows` / `_branch` (lines
  896/914). Conclusion assembly fuel = `blockBudget… * fuelBudget cfg`.
- `compiledVerifiedStackCodeToRawBytecodeForward` (OIC:2018) supplies those from
  `StackArtifact.compile?_parts` and passes `codeArtifact.compiled.certified.target`
  (= `cfg.lower?`) as the emitted bytes. Fuel `fuelBudget cfg` is LITERAL up
  through ~8 theorems (×2 suffix variants: EndToEnd.lean, RawAstSourcePreservation,
  RawAstEndToEnd, RawAstTotal) and only becomes `∃ openFuel` at frozen
  `Correctness.lean` compile_correct / compile_correct_creation.

### Remaining: the splice (option b, keep-original-budget-and-pad)
Chosen so NO downstream statement changes (only hypotheses/proofs):
1. `StackArtifact.compile?`: `let certified ← (peepholeProgram cfg).compileCertified?`
   (keep `cfg := generated.cfg`). `compile?_parts`: change the certified field to
   `(peepholeProgram artifact.cfg).compileCertified? = some artifact.certified`;
   KEEP `artifact.cfg.WellTyped` / `.ProgramCounterIndependent` / `hGenerate`
   (about original cfg). `certified.target = (peepholeProgram cfg).lower?` now,
   i.e. the smaller peepholed bytes — the whole gas win. All other `compile?_*`
   corollaries use `certified.target` opaquely (unchanged). Downstream callers
   (`compiledVerifiedStackCodeToRawBytecodeForward`) now get
   `hCertified : (peepholeProgram cfg).compileCertified? = some certified`.
2. `yulToNormalizedStackAssemblyPrefixForward`: change hyp
   `hCompile : cfg.compileCertified? = some artifact` →
   `(peepholeProgram cfg).compileCertified? = some artifact`. KEEP conclusion
   budget `… * fuelBudget cfg`. Internally:
   - `hIndepPeep := peepholeProgram_programCounterIndependent hIndependent`.
   - Transfer source `Follows`/`Executes` on `openRunNPrefix cfg …` to
     `openRunNPrefix (peepholeProgram cfg) …` via `openRunNPrefix_peephole_congr`
     (cfg=left, peephole=right, `SameRuntimeData.refl`) + `Rel.executes`
     (Interaction.lean:1871) for the done branch, and
     `exists_executes_extension` + `Rel.executes` + `Follows.prefix_of_append`
     for the truncated branch (mirror `assembly_follows` at
     InteractionPrefixPreservation.lean:90-95).
   - Feed peephole preservation `…assembly_follows`/`…assembly_branch hCompile
     hIndepPeep …` (budget `… * fuelBudget (peepholeProgram cfg)`).
   - Pad `… * fuelBudget (peepholeProgram cfg)` up to `… * fuelBudget cfg` with
     `Source.openRunNResult_follows_of_le_follows` (Follows) /
     `openRunNResult_halted_add_executes` (Executes) — REQUIRES the ONE missing
     lemma `fuelBudget (peepholeProgram cfg) ≤ fuelBudget cfg` (see below).
   - Convert the branch's `RunSimulates target peepDone targetDone` +
     `RuntimeOutcomeRel cfgDone peepDone` back to `RunSimulates target cfgDone
     targetDone` via `InteractionPreservation.OpenBlock.runtime_left`
     (InteractionPreservation.lean:144). The final `YulStackAssemblyPrefixDoneRel`
     binds cfgDone existentially, so the source-supplied cfgDone stays on the
     source leg untouched.
   - Need `PrefixAssemblySafe cfgDone → RuntimeOutcomeRel cfgDone peepDone →
     PrefixAssemblySafe peepDone` (SafeAt is `SameRuntimeData`-stable: it reads
     only memory/stack; prove a small transfer lemma).

### The ONE remaining lowering lemma (blocker for the pad)
`fuelBudget (peepholeProgram cfg) ≤ fuelBudget cfg`
(`InteractionSemantics.CompiledProgram.fuelBudget`). Reduce to per-block
`CompiledBlock.fuelBudget (peepholeBlock b) ≤ CompiledBlock.fuelBudget b`
(sum over `blocks.map` monotone). Per-block: when the peephole side lowers to a
positive budget `1 + bodyCode'.length + termCode.length`, the orig side lowers to
`1 + bodyCode.length + termCode.length` with `bodyCode'.length ≤ bodyCode.length`
and SAME `output`/`termCode` (term/output untouched). This is a
`lowerBodyFrom?`-length analogue of `peepholeBody_runBody_erase`
(`Lower.lean:def lowerBodyFrom?` is a simple `head ++ tail` fold; push;pop
cancellation returns the shape to `input` so the tail lowers identically and only
`head_push ++ head_pop` bytes are removed). ~80-120 lines mirroring
`peepholeBody_bodyType?`, tail-first with the `peepholeBody_cons` split. Once this
lands the pad + splice compiles with no downstream statement churn.

### Build/validation note
Steps 1/2/f build in seconds (narrow modules). The splice (step 3) recompiles
`InteractionPreservation` (165k) + RawAst tower + Verification + harness — budget
for 2–3 full rebuilds. Run `scripts/opt_harness.sh full` only at the end;
`#print axioms Solidus.compile_correct` must stay
`[propext, Classical.choice, Quot.sound]`.
