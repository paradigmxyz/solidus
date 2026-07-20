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

## Session-3 addendum: fuelBudget monotonicity landed; splice blast radius verified

Two more green, axiom-clean commits closed every self-contained obligation the
splice needs:
- **(g) `EvmCompiler/TypedCfg/PeepholeFuel.lean`** (commit ea7ed24e) —
  `fuelBudget_peepholeProgram_le : fuelBudget (peepholeProgram cfg) ≤ fuelBudget
  cfg`, via `lowerBodyFrom?_peephole_le` (peepholed body lowers to the SAME output
  shape with ≥ bytes; push;pop removes exactly the 1-byte `[.push v]`/`[.prim
  .pop]` fragments) → `compiledBlock_fuelBudget_peephole_le`. This is the exact
  fact that lets the splice KEEP its conclusion budget at `fuelBudget cfg` and
  pad the (smaller) peepholed assembly run up with the existing
  `openRunNResult_*_add_executes` / `_follows_of_le_follows` — so NO downstream
  statement changes.
- **(f) `PeepholeSpine.lean`** already gives `peepholeProgram_wellTyped`.

### Blast radius of the splice — verified CONTAINED (all non-frozen)
`StackArtifact.compile?_parts` is consumed at EXACTLY three sites, all in
`EvmCompiler/Compiler/OpenInteractionComposition.lean` (2084 = the Forward/prefix
path → `compile_correct`; 2447 + 2538 = the terminal/gasful path →
`RunRefinesOpenTotal` in the total theorem), plus a `#check` in Verification.lean.
The `compile?_parts` appearing in FROZEN `Correctness.lean:136/195` is the
UNRELATED `Solidus.compile?_parts` (SolidusInstall.lean:29), decomposing the
public JSON entry — NOT StackArtifact's. So the frozen surface is untouched.

### The splice, now fully unblocked (mechanical)
1. `StackArtifact.compile?`: `let certified ← (peepholeProgram cfg).compileCertified?`
   (keep `cfg := generated.cfg`). In `compile?_parts`, change ONLY the 11th
   tuple field from `artifact.cfg.compileCertified? = some artifact.certified` to
   `(peepholeProgram artifact.cfg).compileCertified? = some artifact.certified`
   (proof: rename `cases hCertified : generated.cfg.compileCertified?` →
   `(peepholeProgram generated.cfg).compileCertified?`). Positions/count of the
   tuple unchanged, so the `_`-discarded uses in the sibling corollaries
   (`compile?_assembly` etc., which use `hTarget`) keep elaborating.
2. Each of the three OIC consumer theorems (2018 Forward, and the two terminal
   ones feeding 2447/2538): after `compile?_parts`, `hCertified` is now about
   `peepholeProgram cfg`; derive `hIndepPeep := peepholeProgram_programCounterIndependent
   hIndependent`; transfer the source-side `openRunNPrefix cfg …` Follows/Executes
   to `openRunNPrefix (peepholeProgram cfg) …` via `openRunNPrefix_peephole_congr`
   + `Simulation.Interaction.Rel.executes` (Interaction.lean:1871) /
   `exists_executes_extension`; feed the peephole preservation
   (`InteractionPrefixPreservation`/`InteractionPreservation` entry theorems with
   `hCertified`,`hIndepPeep`, budget `… * fuelBudget (peepholeProgram cfg)`); pad
   up to `… * fuelBudget cfg` with `fuelBudget_peepholeProgram_le` +
   `Source.openRunNResult_follows_of_le_follows` / `_halted_add_executes`; convert
   the resulting `OpenBlock.RunSimulates target peepDone targetDone` +
   `RuntimeOutcomeRel cfgDone peepDone` back to `… cfgDone …` via
   `OpenBlock.runtime_left` (InteractionPreservation.lean:144). The final DoneRels
   bind cfgDone existentially, so the source leg is untouched and the CONCLUSIONS
   are byte-identical (still `fuelBudget cfg`).
3. Two tiny transfer lemmas still to write for the terminal path:
   `PrefixAssemblySafe cfgDone → RuntimeOutcomeRel cfgDone peepDone →
   PrefixAssemblySafe peepDone` and the gasful `AssemblySafeHalted` analogue
   (`Terminal.SafeAt` reads only memory/stack, `SameRuntimeData`-stable).
4. `scripts/opt_harness.sh full`: expect `#print axioms Solidus.compile_correct`
   / `compile_correct_creation` still `[propext, Classical.choice, Quot.sound]`,
   all 56 corpus contracts compiling (guaranteed to still COMPILE by
   `peepholeProgram_wellTyped` + PCFits-shrinks + accepted), and a bytes/deploy-gas
   reduction concentrated on the 61 `SWAP1;SWAP1`/`push;pop` no-ops (ExternalCallBox
   ≈122 bytes / ≈24.4k deploy gas; corpus-wide grows once `swap n; swap n` is
   added — one extra `peepholeBody` arm + an involution kernel lemma, reusing all
   of (a)–(g) unchanged).

### Status: the semantic tower is COMPLETE and green
Commits deda555f (a), 16e38b0c (b), 9728d205 (c-core), 43403cfc (c-block),
c062ab44 (d open-block), c2f7c552 (e program+whole-program congruence),
58ed8314 (f WellTyped), ea7ed24e (g fuelBudget). Remaining = only the mechanical
spine rewrite in steps 1–3 above + one full `EvmCompiler.Verification` rebuild.

## Session-4 update (2026-07-16): splice LANDED, green, axiom-clean — but push;pop delta is ZERO

The mechanical spine splice is done and validated. `EvmCompiler.Verification`
builds green; `#print axioms` on `Solidus.compile_correct` /
`compile_correct_creation` = exactly `[propext, Classical.choice, Quot.sound]`
(all 43 public theorems contained). All 56 corpus contracts still compile.

### What landed
- **`Compiler/StackArtifact.lean`**: `compile?` now certifies
  `(peepholeProgram cfg).compileCertified?`; `compile?_parts`' 11th field is the
  peephole certificate. `certified.target = (peepholeProgram cfg).lower?`.
- **`TypedCfg/PeepholeTransfer.lean`** (new, axiom-clean): the
  `RuntimeOutcomeRel`-stability transfer lemmas
  (`prefixAssemblySafe_of_runtimeRel`, `assemblySafeHalted_of_runtimeRel`,
  `assemblySafeFinished_of_runtimeRel`, `runtimeOutcomeRel_eq_error_right`,
  `assemblySafeFinished_of_prefixAssemblySafe`) + the generic target-fuel padding
  lemma `rel_openRunNResult_finished_pad` (finished assembly `Rel` lifts to any
  larger budget via `Rel.of_executes` + `openRunNResult_*_add_executes`).
- **`Compiler/OpenInteractionComposition.lean`**: the consuming theorems now take
  `hCompile : (peepholeProgram cfg).compileCertified?` + an explicit
  `hWellTyped : cfg.WellTyped` (the source bridge still needs the ORIGINAL cfg's
  WellTyped, no longer derivable from the peephole certificate). Prefix path
  (`yulToNormalizedStackAssemblyPrefixForward`) transfers source-side
  `openRunNPrefix cfg` Follows/Executes to `peepholeProgram cfg` via
  `openRunNPrefix_peephole_congr` + `Rel.executes`, pads with
  `fuelBudget_peepholeProgram_le`, reconciles via `OpenBlock.runtime_left`.
  Terminal paths (`structuredToAssemblySource[Finished]`,
  `structuredToEncodedBytecode`, and their yul wrappers) bridge `openRunN cfg` →
  `openRunN (peepholeProgram cfg)` via `openRunN_peephole_congr`, transfer the
  `AssemblySafe*` side-condition, pad the finished target `Rel`, collapse via
  `runtime_left`. `hWellTyped` is threaded from `compile?_parts` at the two
  terminal consumers. Blast radius was exactly the theorems carrying
  `cfg.compileCertified?` (incl. the dead `structuredToEncodedBytecode` /
  `yulStackToEncodedBytecode` / `yulStackToAssemblySource` cluster — reworked for
  consistency). No frozen file touched.

### MEASURED RESULT: zero delta (push;pop has no targets)
`scripts/opt_harness.sh` check = OK; bench (solc 0.8.26, matching the baseline —
NOTE the env's default solc 0.8.35 gates `irOptimizedAst` behind
`settings.experimental` and cannot drive the pipeline) = **+0.00% total_gas, 0
bytes on every contract** incl. ExternalCallBox (runtime 2791 bytes, unchanged).
The reason: our generated code essentially never emits a literal adjacent
`push v ; pop` pair, so `peepholeProgram` is the identity corpus-wide. The
verified wiring is correct and inert.

### The real lever is `swap n ; swap n` (step 3), NOT push;pop
The 61 cancellable no-ops on ExternalCallBox are `SWAP1;SWAP1`, not `push;pop`.
Delivering a nonzero delta requires the involution arm: one extra `peepholeBody`
match arm (`swap n :: swap n :: rest → rest` when the two `n` agree) + an
involution kernel lemma (`swap n (swap n s) = s` under stack depth ≥ n+1 from the
depth-typing invariant) + threading it through the (b)–(g) structural inductions
(each pattern-matches on `peepholeBody`, so the new arm must be discharged in
`peepholeBody_length_le`, `peepholeBody_bodyType?`, `runBody_erase`,
`lowerBodyFrom?_peephole_le`, etc.). This is the outstanding work for a live
byte/gas win; the push;pop tower + splice is the reusable, validated substrate.

## Session-5 update (2026-07-16): swap involution kernel LANDED; tower blocker precisely located

### (a-swap) landed — `EvmCompiler/TypedCfg/PeepholeSwapKernel.lean`
`swap_swap_sameRuntimeData` (green, axiom-clean `[propext, Classical.choice,
Quot.sound]`; wired into `EvmCompiler.Verification` so CI checks it):
```
theorem swap_swap_sameRuntimeData (s : EVMState) (n : Nat)
    (hn : 1 ≤ n) (hDepth : n + 1 ≤ s.stack.length) :
    ∃ s1 s2, EvmYul.swap n s = .ok s1 ∧ EvmYul.swap n s1 = .ok s2 ∧
      SameRuntimeData s2 s
```
Uniform in `n` (no 16-way split), phrased at the `EvmYul.swap` transformer level.
Proof = `exists_swap_decomp` (a length-≥`n+1` list splits as
`top :: front ++ [last] ++ suffix`) + two applications of the pre-existing
`Assembly.StackShuffle.swap_snoc` characterization (first swap exchanges
`top`/`last`; second exchanges them back, restoring `s.stack`; only pc advances).
The kernel is deliberately standalone: the landed green `push v ; pop` tower and
`peepholeBody` are UNTOUCHED. Note `Instr.swap depth` runs `EvmYul.swap (depth+1)`
so the `hn : 1 ≤ n` guard is always met at the instruction level, and
`hDepth : depth+2 ≤ stack.length` is exactly what `Instr.type? (.swap depth)`
demands of the SHAPE — see the blocker below for the missing shape⇒stack step.

### WHY the swap arm is NOT a drop-in like push;pop — the exact blocker
`push v ; pop` cancellation is sound UNCONDITIONALLY (pop after push always sees
a non-empty stack), so its kernel needs no side condition and the (b)–(g)
inductions are stated as unconditional equalities/`Rel`s over ARBITRARY states.
`swap n ; swap n` cancellation is sound ONLY when the runtime stack is ≥ `n+1`
deep. On a shallower stack the first `swap n` errors (`StackUnderflow`) where the
cancelled `ε` succeeds, so the OPEN congruence `openRunBody_peephole_congr`
(and hence `Block.openRun_peephole_runtimeRel`, `openStep_peephole_congr`,
`openRunN_peephole_congr`) is literally FALSE for such states. These lemmas are
proved for arbitrary `state1 state2` with only `SameRuntimeData` between them and
`bodyType? body input = some output`; `bodyType?` bounds the SHAPE length
(`depth+2 ≤ shape.length`) but the semantic layer has NO invariant tying
`shape.length ≤ state.stack.length`. So the swap arm needs a runtime stack-depth
precondition threaded through the whole open tower.

Scoping of the threading (from a full read of the tower):
- **Body level (bounded, provable now):** add hyp `input.length ≤ state.stack.length`
  to `openRunBody_peephole_congr` (and the closed `peepholeBody_runBody_erase`).
  Swap arm discharges via `swap_swap_sameRuntimeData` (shape depth ⇒ stack depth)
  + a shape-level `type?(swap)(type?(swap) s) = s` involution + `runBody_map_erase`
  to carry the pc-shift through the tail. The keep/cancel recursion re-establishes
  the invariant one step down using the per-instruction stack-length facts already
  in `Preservation.lean` (`PrimOp.step_stack_length_of_stackArity`,
  `runPops_stack_length`). Shape involution and the invariant-preservation step
  are new but self-contained (~150 lines).
- **THE DEEP BLOCKER — program level:** `openRunN_peephole_congr` steps between
  blocks through arbitrary jump targets with only `SameRuntimeData`. To discharge
  the body-level `block.input.length ≤ state.stack.length` at EVERY block entry it
  must maintain, as an execution invariant of `openRunN`, that the runtime stack
  realizes the current block's input shape. Establishing this requires a
  per-terminator stack-effect argument (fallthrough/jump/jumpi-pops-1/
  returnDispatch-erases-1/halt) composed with the CFG's row-compatibility
  (`Shape.compatible`, incl. opaque `caller` tails) so that the state handed to
  the next block is ≥ that block's `input.length` deep. This invariant does not
  exist anywhere in the current TypedCfg semantic layer (grep-confirmed: only
  isolated `runPops_stack_length` / `step_stack_length` facts, no
  "stack-realizes-shape" relation on `openRunN`). It is a genuine multi-hundred-
  line addition touching subtle row typing.

Because adding the `swap` arm to `peepholeBody` immediately forces the unhandled
arm into EVERY lemma that `split`s on `peepholeBody_cons` — reddening the frozen-
adjacent green tower — the arm must NOT be added until the whole open tower
(including the program-level invariant) is proved. Landing it partially is not
green-preservable. Hence this session lands the kernel (the requested first
milestone) and the invariant is deferred.

### Exact next-session recipe
1. Write `swap_type_involution` : `type?(swap d) s = some s' → type?(swap d) s' = some s`
   (pure typing; ~40 lines, mirrors `length_of_type?_swap`).
2. Write `StackRealizes shape state := shape.length ≤ state.stack.length`; prove
   `runAt`-step preservation from the per-instruction length facts.
3. Add the depth hyp to `peepholeBody_runBody_erase` + `openRunBody_peephole_congr`
   + prove the swap arm with (1)(2) + `swap_swap_sameRuntimeData`.
4. The hard part: prove `openRunN`/`openStep` maintain `StackRealizes (labelShape? label) state`
   across terminators (per-terminator + row-compat), feed it to the block congruence.
5. Only THEN add the `swap n :: swap n → ε` arm to `peepholeBody`; re-green (b)–(g)
   swap arms (length_le/mem/bodyType?/lowerBodyFrom?_le are syntactic — trivial;
   the semantic ones consume steps 1–4).
6. `scripts/opt_harness.sh full`; expect ExternalCallBox ≈122 bytes / ≈24.4k deploy
   gas, corpus-wide delta from the SWAP-heavy AdversarialStackPressure contract.

Landed this session: commit for `PeepholeSwapKernel.lean` + `Verification.lean`
import. `#print axioms swap_swap_sameRuntimeData` =
`[propext, Classical.choice, Quot.sound]`. Public spine unchanged (push;pop splice
from session 4 intact; measured delta still 0 until the swap arm ships).

## Session-6 update (2026-07-16): steps (1)–(3) landed; step (4) obstruction pinned to caller-tail frames

Three more green, axiom-clean commits. Steps (1)+(2)+(3) of the session-5 recipe
are done as standalone modules (the landed push;pop tower and `peepholeBody`
remain untouched, so the frozen-adjacent tower stays green). Step (4) is analysed
below and found to require the procedure-calling-convention model — genuinely the
deferred multi-hundred-line addition, with the precise obstruction now located.

### (1)+(2) landed — `EvmCompiler/TypedCfg/PeepholeStackRealizes.lean`
- **`Instr.swap_type_involution`** (`[propext, Quot.sound]`): `type? (.swap d)`
  is its own inverse on shapes (`type?(swap d)(type?(swap d) s) = s`). Pure
  typing; the shape-level companion of the runtime kernel. Proof via the
  `getElem?`/`set` characterization of `type? (.swap d)` + `List.set_set` +
  `set_getElem_self`.
- **`StackRealizes shape state := shape.length ≤ state.stack.length`** with
  preservation (`[propext, Classical.choice, Quot.sound]`):
  - `runState_stackRealizes` — per-instruction: from `StackRealizes input state`
    + `type? instr input = some output` + `runState instr input state = .ok state'`
    conclude `StackRealizes output state'`. All 10 `Instr` cases; dup/swap use
    `interval_cases` + `step_stack_length_of_stackArity` with the δ/α arity
    reduced uniformly via `norm_num [EvmYul.EVM.δ, EvmYul.EVM.α, PrimOp.toEVM]`
    (the generic lemma leaves the arity symbolic; norm_num forces it concrete so
    it matches the concrete `length_of_type?_*` bound); unwind uses
    `Preservation.runPops_stack_length`.
  - `runAt_stackRealizes` (single `runAt`) and `runBody_stackRealizes`
    (whole straight-line body, by induction) wrappers.

### (3) landed — `EvmCompiler/TypedCfg/PeepholeSwapOpen.lean`
- **`openRunBody_swap_swap_congr`** (`[propext, Classical.choice, Quot.sound]`):
  the depth-guarded OPEN-body swap-arm reduction — the swap analogue of the
  `push v ; pop` cancel branch inside `openRunBody_peephole_congr`, isolated so
  the green tower stays green. From `(type? (.swap d) input).isSome`,
  `bodyType? rest input = some output`, `rest` PC-independent,
  `StackRealizes input state2`, and `SameRuntimeData state1 state2`, it derives
  `Rel (Instr.RuntimeAtRel output) (openRunBody rest input state1)
  (openRunBody (.swap d :: .swap d :: rest) input state2)`.
  Proof: `length_of_type?_swap` (⇒ `d+2 ≤ input.length`) + `StackRealizes`
  (⇒ `d+2 ≤ state2.stack.length`) feeds `swap_swap_sameRuntimeData`; the two
  swaps reduce via `runState_swap_eq` (`runState (.swap d) = EvmYul.swap (d+1)`,
  `interval_cases <;> rfl`) + `openRunBody_swap_cons_ok`; `swap_type_involution`
  supplies the second-swap typing back to `input`; the shared tail rides the
  pre-existing `InteractionCongruence.Block.openRunBody_runtimeRel`. This lemma
  is exactly what step 5's new `openRunBody_peephole_congr` swap arm will invoke.

Commits: `93ec0755` (1+2), plus the (3) commit; both wired into
`EvmCompiler.Verification` (imports) — full `EvmCompiler.Verification` rebuilds
green, `compile_correct` / `compile_correct_creation` axioms unchanged
`[propext, Classical.choice, Quot.sound]`.

### THE STEP-(4) OBSTRUCTION, precisely located: caller-tail hidden frames
Step (4) wants `StackRealizes (labelShape? label) state` maintained as an
execution invariant of `openRunN`/`openStep`, i.e. **at every block entry the
runtime stack realizes that block's `input` shape**. The within-block half is
done (`runBody_stackRealizes`). The cross-block half does NOT follow from
`WellTyped`, and here is why:

A terminator is well-typed via `Shape.compatible output target.input`
(`Typing.lean:typeWith?`). But `Shape.compatible left right`
(`Syntax.lean:111`) explicitly PERMITS `left.length < right.length` — precisely
when `left.tail = .caller`. So a well-typed `jump`/`jumpi`/`returnDispatch` may
hand control to a target block whose `input.length` is STRICTLY GREATER than the
jumping block's `output.length`. Since `output.length ≤ state.stack.length` is
all `runBody_stackRealizes` gives, `target.input.length ≤ state.stack.length`
(the realization the target needs at entry) is simply NOT DERIVABLE at the pure
CFG level. The missing slots live in the opaque `caller` suffix of the runtime
stack: a caller-tailed shape describes only a PREFIX of the stack, and how deep
the hidden caller portion actually is (whether it supplies the extra
`target.input.length − output.length` slots) is a **runtime call-convention
property**, established by the real CALL that entered the procedure, not by the
CFG typing. `tail_of_type?` shows the tail is invariant through a body, so a
block that can jump "wider" is itself caller-tailed — confirming the extra depth
must come from a caller frame that the CFG type deliberately hides.

Consequently `StackRealizes` as defined (`shape.length ≤ stack.length`) is
maintainable only for the **closed-tail** fragment (entry/deploy/dispatch blocks
with `tail = .closed`, where `compatible` forces equal lengths and realization
holds with equality). For caller-tailed procedure bodies — where essentially all
the SWAP-heavy code lives — the correct invariant must additionally assert that
the runtime stack carries a VALID CALLER FRAME beneath the shape prefix, i.e. an
inductive relation of the form `state.stack = shape.slots' ++ frame` with `frame`
recursively realizing the caller's continuation shape. That relation is the
procedure-calling-convention model; it does not exist in the current TypedCfg
semantic layer and is the genuine multi-hundred-line addition (grep-confirmed
absent, consistent with the session-5 diagnosis, now with the exact mechanism).

### Refined next-session recipe (step 4 → 5 → 6)
4a. Define `FrameRealizes : Shape → EVMState → Prop` inductively: for a
    `.closed` shape, `shape.length = state.stack.length` (or `≤` if trailing
    scratch is permitted — check `runTerm`/dispatch); for a `.caller` shape,
    `∃ frameLen, shape.length + frameLen ≤ state.stack.length` where `frameLen`
    is pinned by the caller's continuation (thread the caller shape as an index,
    or carry the return-frame layout the `returnDispatch`/`unwind` terminators
    consume). Reconcile with how `returnToken`/`returnPC` slots and
    `Shape.returnTokenDepth?` mark the frame boundary.
4b. Prove `openStep` preserves `FrameRealizes` per terminator: fallthrough/jump
    (row-compat + frame carried), jumpi (pops the 1 condition slot — realization
    of `{shape with slots := rest}` at both targets), returnDispatch (erases the
    token slot, `Shape.erase`, and the selected `site.target` is realized because
    the dispatched frame supplied it), halt/invalid (terminal). Compose with
    `runBody_stackRealizes` for the body leg. Feed the result into `openRunN`
    by fuel induction.
4c. Restate `openRunBody_peephole_congr` (and the closed `peepholeBody_runBody_erase`)
    with the `StackRealizes input state`/`FrameRealizes` hypothesis; discharge the
    swap arm via `openRunBody_swap_swap_congr` (landed); discharge the entry
    hypothesis at each block from 4b.
5.  Add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`; re-green the
    syntactic (b)-family lemmas (`peepholeBody_length_le`, `mem_peepholeBody`,
    `peepholeBody_bodyType?`, `lowerBodyFrom?_peephole_le` — all trivial extra
    match arm) and the semantic ones (consume 4c).
6.  `scripts/opt_harness.sh full` (solc 0.8.26 via solc-select, restore 0.8.35
    after). Expect ExternalCallBox ≈122 bytes / ≈24.4k deploy gas; corpus-wide
    delta dominated by the SWAP-heavy AdversarialStackPressure contract.

Landed this session: `PeepholeStackRealizes.lean` (1+2), `PeepholeSwapOpen.lean`
(3), `Verification.lean` imports. All axiom-clean, all green,
`compile_correct` unchanged, `peepholeBody`/public spine untouched (measured
delta still 0 until step 5 ships the arm).

### KEY DISCOVERY for step 4: the caller-frame entry-depth invariant ALREADY EXISTS (reuse, don't rebuild)
A fan-out search of the whole tower found that the "at each block entry the
runtime stack realizes the shape" invariant — including the caller-frame
hidden-suffix — is ALREADY defined and ALREADY maintained across open multi-block
execution, in the Structured→TypedCfg simulation layer. Do NOT rebuild it from
scratch (the 4a `FrameRealizes` sketch above is subsumed). The reusable pieces:

- **`EvmCompiler/Structured/TypedCfgCompiler.lean:186`**
  `def SourceFrameFits (shape : Shape) (stackLength : Nat) : Prop :=
   shape.sourceLength ≤ stackLength ∧
   ∀ depth, shape.returnTokenDepth? = some depth → stackLength = depth`
  — EXACTLY the block-entry depth invariant needed (`sourceLength :=
  shape.sourceView.length`, the visible slots below the return token; exact
  depth at a return-token frame). `TypedCfgCompilerFacts.lean:76`
  `returnTokenDepth?_lt_length` bounds the token slot.
- **`EvmCompiler/Structured/TypedCfgPreservation/Core.lean`** — the concrete
  hidden-suffix decomposition: `realizeStack : Stack → List ReturnDest →
  List Word → Option Stack` (17) appends each ghost return frame BENEATH the
  visible stack; `StateRel source tokens target` (51) = runtime stack decomposes
  as source stack with all caller frames realized beneath; `ActivationExtension`
  (285, inductive, with `trans`/`realize_length_lt`) tracks nested frames.
- **`EvmCompiler/Structured/InteractionPreservation.lean`** — the invariant is
  THREADED across open steps/blocks: `StateRel.hiddenSuffix` (16) gives
  `stack = visible ++ hidden`; `openStepEVM_sourceFrameFits` (200) preserves
  `SourceFrameFits` across one open step; `openRun_toCfg` (457, documented at
  454 as "carries the source-frame invariant needed by the next block").
  `InteractionTruncationOwnerPreservation.lean` (e.g. 611) threads
  `SourceFrameFits input source.evm.stack.length` as the block-entry invariant
  across `Block.openRun` / `openRunNResultWithStop`.

**Two caveats that define the remaining work (still nontrivial, but NOT a
from-scratch frame model):**
1. It is parameterized by the STRUCTURED SOURCE's ghost return frames
   (`RunState.returns : List ReturnDest`) and the shape's
   `sourceLength`/`returnTokenDepth?` — NOT directly by `Shape.tail = .caller`.
   `Shape.compatible`/`hasPrefix`/`unwindTo` remain pure boolean predicates with
   no proven runtime-suffix bridge; the runtime tie-in goes exclusively through
   `sourceView`/`returnTokenDepth?`/`SourceFrameFits`.
2. There is NO standalone theorem "for an arbitrary well-typed TypedCfg
   `Program`, `openRunN` maintains `block.input.length ≤ state.stack.length` at
   every entry" independent of a Structured source.

**Therefore the correct step-4 route (revised):** couple the peephole congruence
to the SAME Structured source witness the public spine already carries. The
splice point (`Compiler/OpenInteractionComposition.lean`,
`yulToNormalizedStackAssemblyPrefixForward` and the terminal theorems) already
has both ends on `cfg` = `generated.cfg` AND the source bridge
`yulToNormalizedStackTypedCfgPrefixForward` in scope — so `SourceFrameFits` /
`StateRel` for the running state is available there. Rather than adding a raw
`StackRealizes` hypothesis to `openRunBody_peephole_congr` (unprovable
standalone for caller tails, per the obstruction above), thread the EXISTING
`SourceFrameFits input state` (already established at each block entry by the
source simulation) into a `SourceFrameFits`-guarded peephole congruence, and
derive the swap arm's runtime guard `depth+2 ≤ state.stack.length` from
`SourceFrameFits` + `sourceLength`/`length` bounds (`returnTokenDepth?_lt_length`
et al.). The landed `openRunBody_swap_swap_congr` (step 3) already takes a
`StackRealizes input state2` = `input.length ≤ state2.stack.length` guard; the
remaining glue is `SourceFrameFits input n → input.length ≤ n` (or the
`sourceLength`-adjusted variant) at the swap position, plus re-stating the body
congruence over `SourceFrameFits`. This is the concrete, reuse-based unblock for
a future session; it is bounded by the Structured-source coupling, not by a new
frame model.

## Session-7 update (2026-07-16): the SourceFrameFits reuse path does NOT close — corrected, with the exact wrong-side/wrong-magnitude proof

Session 7 executed the step-4 recipe as written (couple the swap depth guard to
the already-threaded `SourceFrameFits` invariant at the OIC splice) and, after a
full trace of the Structured→TypedCfg preservation layer, found that the
session-6 "reuse job" framing is **over-optimistic**: `SourceFrameFits` is the
*wrong side and the wrong magnitude* for the swap guard. No swap arm was added
(it would redden the tower ungreenably, per session 5); the tower stays green,
axioms exactly `[propext, Classical.choice, Quot.sound]`, and the measured
corpus delta is still **+0 bytes / +0.00% gas on all 56 contracts** (bench,
solc 0.8.26; TOTAL 103211 our runtime bytes vs 36115 solc = 2.86×; ExternalCallBox
6 vec, +0). This section replaces the step-4 route above with the accurate
obstruction and the two genuine routes forward.

### The precise obstruction (definitions, not intuition)
The swap arm's landed reduction `openRunBody_swap_swap_congr` (step 3) requires
`StackRealizes input state2` = `input.length ≤ state2.stack.length`, where
`state2` is the **TARGET (cfg) EVM state** the *original* body runs from (the
peephole congruence's right leg). Via `runBody_stackRealizes` (landed) this only
has to hold at each **block entry**; the within-body evolution carries it.

`SourceFrameFits input n := sourceLength input ≤ n ∧ (returnTokenDepth? = some d → n = d)`
(`Structured/TypedCfgCompiler.lean:186`), and it is threaded everywhere as
`SourceFrameFits input source.evm.stack.length` — i.e. about the **SOURCE**
stack. Two facts make it unusable directly:

1. **Wrong side / wrong magnitude.** `sourceLength input ≤ input.length`
   (`TypedCfgCompilerFacts.lean:161 sourceLength_le_length`), and whenever a
   return token is present the second `SourceFrameFits` conjunct *pins*
   `source.evm.stack.length = returnTokenDepth = sourceLength < input.length`
   (`returnTokenDepth?_lt_length`, `sourceLength_eq_of_returnTokenDepth?_eq_some`).
   So on the source stack `input.length` provably does **NOT** fit — the source
   stack is strictly shallower than `input.length` exactly for the caller-tailed
   procedure bodies where the SWAP-heavy code lives. `SourceFrameFits` cannot give
   `StackRealizes` for the target.

2. **The target bound exists but needs a missing correspondence.** The correct
   target-stack fact is `ActivationFrameMatches` (`TypedCfgPreservation/Core.lean:469`):
   for a token shape at depth `d`, `target.stack.length = d + hidden.length`
   where `hidden = realizeStack [] returns tokens` is the realized ghost
   caller-frame suffix (`Core.lean:17`). Deriving `input.length ≤ target.stack.length`
   thus reduces to `input.length - d ≤ hidden.length`, i.e. *the shape's slots at
   and below the return token are covered by the realized caller-frame suffix*.
   This is NOT implied by `SourceFrameFits`/`StateRel`: `returnTokenDepth?`
   (`Typing.lean:286`) explicitly permits slots below the token, and nothing in
   `SourceFrameFits` bounds them by `hidden.length`. It is a genuine shape↔frame
   layout invariant, and in the current tower it is established only *distributed*
   through the procedure-CALL convention proof, threaded as the bare hypothesis
   `input.length ≤ state.stack.length` (`Core.lean:749 step_stack_bound_of_type`,
   `:1180 exists_step_of_type_bound_append`, `:1223`), never exposed as a
   standalone "`openRunN` maintains `block.input.length ≤ state.stack.length` at
   every entry" theorem (grep-confirmed absent, consistent with sessions 5/6).

### (jump to session-10 for the definitive interleave scoping)

### Consequence: step 4 is a re-architecture, not a glue lemma
There are exactly two honest routes, both real work (multi-hundred-line,
plausibly multi-session):

- **Route A — standalone target-stack invariant.** Prove the missing
  correspondence `input.length - returnTokenDepth? ≤ (realizeStack [] returns tokens).length`
  as a program-level invariant of `openRunN` under the block typing, using
  `ActivationFrameMatches` as the hook. This needs a new "below-token shape slots
  are caller-frame slots" fact tying the CFG shape to the realized frames —
  precisely the calling-convention layout invariant the current tower proves only
  incrementally inside the CALL handler, not as a reusable `openRunN` invariant.

- **Route B — interleave the peephole with the source simulation.** Do NOT prove
  a standalone `openRunN_peephole_congr` carrying the invariant. Instead thread
  the peephole congruence *through* the whole-program Structured→cfg simulation
  (`Structured/InteractionTruncationOwnerPreservation.lean`, ~2000 lines, which
  already maintains `SourceFrameFits`/`StateRel`/`ActivationFrameMatches` per
  block-entry across `openRunNResultWithStop`), converting each maintained
  target-stack bound (`ActivationFrameMatches ⇒ target.stack.length = d + hidden.length`)
  into the swap depth guard `d_swap + 2 ≤ state2.stack.length` at each straight-line
  body. This is a triple (source, cfg, peephole-cfg) simulation and touches the
  subtle terminator/CALL cases.

Route B reuses the most and is the intended spirit, but it is NOT the "add a
`SourceFrameFits input n → input.length ≤ n` glue lemma at the splice" that the
session-6 note implied — that glue lemma is *false* (fact 1 above).

### Smaller win considered and rejected
Restricting the swap peephole to **closed-tail** blocks (`returnTokenDepth? = none`),
where `SourceFrameFits` with empty ghost frames *does* give `StackRealizes`
(`hidden = []`, `sourceLength = length`, target.stack = source.stack), was
weighed. Rejected: (a) it still needs the source coupling to obtain
`SourceFrameFits` at entry, (b) it needs per-block closed-tail classification
threaded through the congruence tower, and (c) the payoff is limited to
dispatch/entry shuffles — almost all SWAP1;SWAP1 no-ops on ExternalCallBox /
AdversarialStackPressure live in caller-tailed procedure bodies. Net expected
delta small-to-zero for real complexity; not landed.

### No unconditional alternative exists
Every adjacent-inverse stack rewrite that would actually fire needs the same
runtime depth guard: `swap n; swap n` and `dup n; pop` both diverge from `ε` on
a shallow stack (original underflows, cancelled succeeds). The one *unconditional*
rewrite, `push v; pop`, has zero corpus targets (measured, sessions 4 & 7). So
there is no depth-free lever; the swap arm genuinely requires Route A or B.

### Status handed to session 8
Landed foundation is UNCHANGED and green: kernel `swap_swap_sameRuntimeData`,
`swap_type_involution` + `StackRealizes` + runBody preservation,
`openRunBody_swap_swap_congr` (the depth-guarded body reduction, ready to be
invoked by the new arm). The single remaining blocker is the block-entry
target-stack bound (Route A or B). Sessions 5, 6, and 7 have each independently
converged on this being the deferred hard part; session 7's contribution is the
definitional proof that the `SourceFrameFits`-glue shortcut is unsound and the
correct hook is `ActivationFrameMatches` + the missing shape↔frame length fact.

## Session-8 update (2026-07-16): Route A reduced to its minimal residual + closed-tail half proved outright; the "deep" below-token layout invariant collapses for compiler shapes

Session 8 executed Route A. The full standalone `openRunN` invariant is confirmed
*not* provable over arbitrary well-typed programs (a caller-tailed block may be
jumped to "wider" than the jumping block's output — the extra depth is a runtime
call-convention property, not CFG typing; session 7's `A→B jump` obstruction is
correct). But Route A's *reusable core* — the lemma that turns the maintained
source invariants into the target-stack realization the swap arm needs — is now
landed green and axiom-clean, and the residual it leaves is far smaller than
sessions 6/7 feared.

### (h) landed — `EvmCompiler/Structured/TypedCfgPreservation/StackRealizesEntry.lean`
Green, axiom-clean `[propext, Classical.choice, Quot.sound]`, wired into
`EvmCompiler.Verification`. Full `Verification` rebuilds green; `compile_correct` /
`compile_correct_creation` axioms unchanged. Public spine / `peepholeBody`
UNTOUCHED (measured delta still +0 — no arm shipped; compiled output byte-identical
to session 7, so `peepholeProgram` stays identity corpus-wide by construction).

- **`stackRealizes_of_stateRel`** — THE Route A reduction. From the invariants the
  whole-program Structured→cfg simulation *already* maintains at every block entry
  (`StateRel source tokens target` + `SourceFrameFits shape source.evm.stack.length`)
  plus ONE crisp residual hypothesis
  `hBelow : returnTokenDepth? = some depth → realizeStack [] source.returns tokens = some hidden → shape.length - depth ≤ hidden.length`,
  it concludes `TypedCfg.StackRealizes shape target` (= `shape.length ≤ target.stack.length`).
  Proof: `StateRel` ⇒ `target.stack = source.evm.stack ++ hidden` (via
  `realizeStack_append_prefix`, mirroring `ActivationFrameMatches.of_stateRel`) so
  `target.stack.length = source.evm.stack.length + hidden.length`; the token case
  pins `source.evm.stack.length = depth` (`SourceFrameFits.2`) and closes by
  `hBelow` + `returnTokenDepth?_lt_length`; the no-token case needs no residual.
- **`stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none`** — the closed /
  token-free half closes UNCONDITIONALLY (no residual): with no token
  `sourceLength = length`, and `StateRel` only appends frames beneath the source
  stack, so `input.length = sourceLength ≤ source.stack.length ≤ target.stack.length`.
  This fully covers entry/deploy/dispatch closed-tail blocks — genuine new ground.
- **`stackRealizes_of_stateRel_of_token_last`** — discharges `hBelow` for the
  procedure-entry shapes the compiler actually emits, via the KEY FINDING below.
- Supporting: `realizeStack_seed_le` (realizeStack only appends),
  `realizeStack_length_pos_of_returns_ne_nil` (a live frame realizes ≥ 1 slot).

### KEY FINDING: the "below-token slots are caller-frame slots" blocker collapses
Sessions 6/7 flagged `shape.length - depth ≤ hidden.length` as a full
calling-convention *layout* invariant (feared multi-hundred-line). But
`TypedCfgCompiler` places `.returnToken` as the **LAST** slot of every procedure
input shape (`TypedCfgCompiler.lean:147, 153, 160, 935` — `replicate argc .word ++
[.returnToken]`, etc.). So for procedure-entry shapes `depth = length - 1` and
`shape.length - depth = 1`; there are ZERO slots strictly below the token, and the
"deep layout" fact reduces to `1 ≤ hidden.length`, i.e. the realized caller frame
is non-empty — which follows from `source.returns ≠ []` (being inside a live
procedure activation). `stackRealizes_of_stateRel_of_token_last` proves exactly this.

### The genuine remaining work (materially smaller than sessions 5–7 estimated)
To ship the swap arm, discharge, at each block entry, the two hypotheses of
`stackRealizes_of_stateRel_of_token_last` / `_of_returnTokenDepth?_eq_none`:
1. **Shape structural fact (open risk, must verify first):** every reachable block
   **input** shape has `returnTokenDepth? = none` OR `= some (length - 1)` (token
   at bottom). CAVEAT: `Instr.returnToken` pushes a `.returnPC` slot on TOP
   (`Typing.lean:15`), so token-not-at-bottom shapes DO occur mid-body during call
   setup. Whether any block-**boundary** input shape inherits such a top-`returnPC`
   layout is unverified — this is the one thing to check before committing to the
   token-last route. If some block inputs are token-not-at-bottom with slots below,
   those specific blocks fall back to the general `stackRealizes_of_stateRel` +
   the full `hBelow` (still the deep fact, but now scoped to only those blocks; the
   swap arm could alternatively be guarded to fire only on token-at-bottom/none
   blocks, which covers the SWAP-heavy procedure bodies).
2. **Source coupling:** `returnTokenDepth? = some _ → source.returns ≠ []` at block
   entry (in-a-procedure ⟺ live frame). Almost certainly already available near the
   `StateRel`/`ActivationFrameMatches` threading in
   `Structured/InteractionPreservation.lean` /
   `InteractionTruncationOwnerPreservation.lean` — locate and reuse.

Then (Route-B-style, but per-entry obligation is now a PROVED lemma, not an open
goal): thread `stackRealizes_of_stateRel_of_{token_last,returnTokenDepth?_eq_none}`
into a `StackRealizes`-guarded peephole congruence at the OIC splice (both source
bridge and cfg are on the same `generated.cfg` there, so `StateRel`/`SourceFrameFits`
are in scope); consume `openRunBody_swap_swap_congr` (landed session 6); finally add
the `swap d :: swap d :: rest → rest` arm to `peepholeBody` and re-green (b)–(g)
(syntactic arms trivial; semantic ones consume the guarded congruence).

Commit this session: `StackRealizesEntry.lean` + `Verification.lean` import. Foundation
from sessions 1–7 unchanged and green.

## Session-9 update (2026-07-16): token audit RESOLVED (no guard needed); source coupling reduced to the runtime tokens witness; the genuine remaining blocker re-confirmed as the interleaved (triple) simulation at the OIC

Session 9 executed the two open pre-conditions from session 8 (token-position
audit + source coupling) and pinned, with definitions, why the arm still cannot
ship green in one session. Foundation from sessions 1–8 UNCHANGED and green;
`peepholeBody`/public spine UNTOUCHED, so the measured corpus delta is still
**+0 bytes / +0.00% gas on all 56 contracts** (no arm shipped — by construction
`peepholeProgram` stays identity corpus-wide). One new green, axiom-clean lemma
landed (below).

### (1) TOKEN AUDIT — RESOLVED by code inspection: every block INPUT is token-at-bottom or none
Session 8 flagged "does any block-**boundary** input inherit the top-`returnPC`
layout?" as the one open risk gating the token-last route. Answer: **NO.** The
complete inventory of block-input shapes (`Block.input` = the `input`/`valueShape`
argument at every `mkBlock?` site + the fixed entry/dispatch/end blocks) is:
- `main`/entry block — `input = TypedCfg.Shape.caller` = `{slots := [], tail := .caller}`
  → `returnTokenDepth? = none`. (`TypedCfgCompiler.lean:722/724`)
- `endBlock` — `input = main.fallthrough?.getD caller`, a top-level source-visible
  shape → **none**. (`:731-737`)
- procedure entry blocks — `input = Shape.procEntry proc = replicate argc .word ++
  [.returnToken]` → token LAST (`depth = length-1`). (`:671`, `:145-148`)
- dispatch blocks — `input = Shape.procExit proc = replicate retc .word ++
  [.returnToken]` → token LAST. (`:706`, `:158-161`)
- all `compileBlock?`-emitted blocks (if/switch/loop joins, call block, terminal,
  break/continue/leave) — `input` is the **threaded current shape**, which starts
  at `procEntry`/`procExit`/`caller` and evolves only by source ops that act on the
  `sourceView` ABOVE the return token (`Shape.sourceView` takes `slots.take depth`),
  so the token stays at the bottom throughout a procedure body. Switch case blocks
  take `valueShape` = scrutinee pushed on TOP of the current shape (`[.pop]` body) →
  token still at bottom.
- The ONE `returnPC`-on-top layout in the whole compiler is the call-setup **body**
  `.returnToken token :: sinkTopUnder proc.argc` (`:542`), which `Instr.returnToken`
  types by pushing `.returnPC` on top (`Typing.lean:15`). This is strictly
  **mid-body** inside the single call block; that block's terminator is
  `.jump (ProcLabel.entry name)`, and the callee's INPUT is the fresh `procEntry`
  (token at bottom). The returnPC-not-at-bottom shape is a block OUTPUT consumed
  only by the jump-compatibility check, never a block INPUT.

**Consequence:** the swap arm needs NO token-position guard — every reachable block
entry is covered by `stackRealizes_of_stateRel_of_token_last` (token-last) or
`stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none` (none), both landed
session 8. (A fully formal Lean proof of this inventory would be a structural
induction over `compileBlock?`/`lowerProcBodiesWithShapes?` — a bounded sub-project,
but NOT required for a guarded arm and NOT on the critical path: the guard can be a
decidable per-block `returnTokenDepth? ∈ {none, some (length-1)}` check that fires
on 100% of emitted blocks anyway.)

### (2) SOURCE COUPLING — the `returns ≠ []` obligation reduces to a non-empty runtime tokens list
`stackRealizes_of_stateRel_of_token_last` needs `source.returns ≠ []`. The existing
`StateRel.returns_cons_of_tokens_cons` (`Core.lean:74`) already gives
`StateRel source (token :: tokens) target → source.returns = frame :: returns`.
So the frame-nonemptiness obligation is discharged by a *non-empty* realized token
list — exactly what the whole-program simulation carries at a token-bearing block
entry. Landed this session:

- **`stackRealizes_of_stateRel_of_token_last_of_tokens_cons`** in
  `StackRealizesEntry.lean` (green, axiom-clean `[propext, Classical.choice,
  Quot.sound]`): same conclusion as `_of_token_last`, but takes
  `StateRel source (token :: tokens) target` instead of `source.returns ≠ []`.
  A future spine wiring now only has to supply the token-list *shape* at each
  token block entry (non-empty because the input shape owns a return token), not a
  separate frame fact.

The residual gap in (2): the fully-static `returnTokenDepth? = some _ → tokens ≠ []`
still needs the shape↔tokens-count correspondence (that a token-bearing input shape
forces a non-empty maintained `tokens` list). That correspondence is threaded inside
the whole-program sim (`InteractionTruncationOwnerPreservation`), not exposed
standalone — and this is the SAME threading the deep blocker below requires, so it
is not separately blocking.

### THE DEEP BLOCKER, re-confirmed with the exact call site
The per-entry realization is now a PROVED lemma, but CONNECTING it to the peephole
congruence still requires the source witness at the program level, and that witness
is **not present** where the congruence is invoked. At the OIC splice
(`OpenInteractionComposition.lean:909-916`, `:942-947`, and the three terminal
consumers at `:1415/1561/1688`), `openRunNPrefix_peephole_congr` /
`openRunN_peephole_congr` are called as:
```
TypedCfg.Peephole.openRunNPrefix_peephole_congr hWellTyped hIndependent
  budget cfg.entry expressionsState.evm expressionsState.evm
  (Assembly.SameRuntimeData.refl _)
```
i.e. with only `WellTyped`/`ProgramCounterIndependent` and `SameRuntimeData.refl` —
**no source witness**. It works today only because push;pop is UNCONDITIONAL. The
swap arm makes the congruence FALSE on shallow stacks, so it needs
`StackRealizes block.input state` at EVERY block entry the internal `openRunN` fuel
induction steps through — which is NOT derivable standalone (sessions 5–8: a
caller-tailed block can be jumped-to "wider"; the extra depth is a runtime
call-convention property). The `hUpper` source coupling from
`yulToNormalizedStackTypedCfgPrefixForward` IS in scope at the splice, but only as a
whole-prefix `ForwardRel`; the per-entry `StateRel`/`SourceFrameFits`/
`ActivationFrameMatches` invariants live INSIDE the ~2000-line
`InteractionTruncationOwnerPreservation` proof, not at the OIC. Therefore shipping
the arm requires re-proving `openRunNPrefix_peephole_congr` as an **interleaved
(triple: source × cfg × peephole-cfg) simulation** that carries the source
invariant — the Route-B re-architecture. This is genuinely multi-session and is why
the arm is not added here (adding it to `peepholeBody` without the guarded congruence
reddens the whole (b)–(g) tower ungreenably; session 5).

### Exact next-session recipe (unchanged in spirit, now fully de-risked on (1)+(2))
1. Prove a source-carrying program congruence
   `openRunNPrefix_peephole_congr_of_source` that threads the Structured→cfg
   invariants (`StateRel`/`SourceFrameFits` at each entry) alongside the fuel
   induction — reuse `InteractionTruncationOwnerPreservation`'s per-block-entry
   invariant maintenance rather than re-deriving it; at each straight-line body
   discharge `StackRealizes input state` via
   `stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,returnTokenDepth?_eq_none}`
   (landed) — NO token guard needed (audit (1)) — and feed
   `openRunBody_swap_swap_congr` (landed session 6) for the swap arm.
2. Swap the OIC calls to the source-carrying variant (the `hUpper`/`generated`
   witness is already in scope at all four consumers).
3. Add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`; re-green the
   syntactic (b)-family (`peepholeBody_length_le`, `mem_peepholeBody`,
   `peepholeBody_bodyType?`, `lowerBodyFrom?_peephole_le` — trivial extra arm) and
   the semantic congruences (consume step 1).
4. `scripts/opt_harness.sh full`; expect ExternalCallBox ≈122 bytes / ≈24.4k deploy
   gas, corpus-wide delta from the SWAP-heavy AdversarialStackPressure contract.

Commit this session: `StackRealizesEntry.lean` (+`stackRealizes_of_stateRel_of_token_last_of_tokens_cons`)
+ this note. `#print axioms` on the new lemma and on
`compile_correct`/`compile_correct_creation` unchanged
`[propext, Classical.choice, Quot.sound]`.

## Session-10 update (2026-07-16): the interleaved congruence traced to the theorem level — it is a genuine 4-file / ~16.7k-line re-architecture of the source→cfg sim; NO reusable per-entry hook exists (grep- AND structurally-confirmed). Tower green, axioms clean, delta still +0 (no arm shipped).

Session 10 attempted step (1) of the session-9 recipe — the source-carrying
program congruence `openRunNPrefix_peephole_congr_of_source`. After an
independent, theorem-level trace of the entire Structured→cfg preservation
stack it is confirmed that this cannot be landed green in one session, for a
reason now pinned MORE precisely than sessions 5–9: the per-block-entry
`StateRel` witness the swap guard needs is **not exposed anywhere** — the single
whole-program forward theorem exposes only the *final-outcome* relation, and the
per-entry invariant is threaded internally across four files totalling ~16.7k
lines. No arm was added (adding it reddens the whole (b)–(g) tower ungreenably;
session 5). Inherited tower UNCHANGED and green: `scripts/opt_harness.sh check`
= OK, 43 public theorems, axioms `[propext, Classical.choice, Quot.sound]` incl.
`compile_correct` / `compile_correct_creation`. `peepholeProgram` stays identity
corpus-wide (no swap arm; push;pop has zero targets, measured sessions 4/7), so
the compiled output is byte-identical to session 9 and the measured corpus delta
is definitionally **+0 bytes / +0.00% gas on all 56 contracts** (TOTAL 103211
our runtime bytes vs 36115 solc = 2.86×, per the session-9 committed baseline;
no spine/peepholeBody change this session ⇒ no re-bench needed).

### What was verified this session (new, concrete, saves the next session the trace)
1. **The only source→cfg forward theorem exposes just the final outcome.**
   `InteractionTruncationOwnerPreservation.GeneratedProgram.main_prefix_forward`
   (`:4833`) yields `ForwardRel Truncated (PrefixDoneRel generated) (source
   openRun) (cfg openRunNPrefix)`. `PrefixDoneRel` (`:4613`) = `ExceptRel
   StructuralErrorRel (PrefixOutcomeRel generated)` — it relates ONLY the
   terminal `sourceDone`/`targetDone`. There is **no** per-entry `StateRel`
   carried in the conclusion. Confirmed by reading the statement AND by
   `grep -rn "openRunN.*StateRel|entry.*StateRel"` over `Structured/*.lean`
   returning **nothing**.
2. **The per-entry `StateRel` lives inside the recursion, across four files.**
   `main_prefix_forward` → `main_forward` (`:4561`) →
   `InteractionBoundedOwnerPreservation` (3490 L) →
   `InteractionControlPreservation` (6212 L) →
   `InteractionOwnerPreservation` (2116 L). The actual per-construct threading of
   `StateRel source tokens target` + `SourceFrameFits input source.evm.stack.length`
   is the family `code_exec` / `if_exec` / `switch_exec` / `for_exec` /
   `call_exec` / `brk|cont|leave|terminal_exec` / `exec_succ` / `block_owner`
   (`InteractionOwnerPreservation.lean:555–1615`) plus the truncation-bounded
   mirrors in `InteractionTruncationOwnerPreservation.lean` (`Call`/`Loop`/
   `Switch`/`Block`/`Stmt` namespaces). Each is a source-structural induction; a
   peephole (third) leg must be threaded through EVERY one.

### Why no black-box reuse of `main_prefix_forward` closes it
The splice consumes the congruence as `Rel.executes hCongr hCfgExec`
(`OpenInteractionComposition.lean:916/947`) — applied to ONE concrete cfg
execution `hCfgExec` that itself came from the source via `hUpper`. So the
natural fix is an **execution-indexed** transfer, not a universal `Rel`:
`openRunNPrefix_peephole_execTransfer : Executes (openRunNPrefix cfg …)
transcript cfgDone → «this-execution-is-source-realizing» → ∃ peepDone, Executes
(openRunNPrefix (peepholeProgram cfg) …) transcript peepDone ∧ RuntimeOutcomeRel
cfgDone peepDone`. Its fuel/execution induction needs `StackRealizes block.input
state` at each entry, dischargeable (landed sessions 8/9:
`stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,returnTokenDepth?_eq_none}`,
NO token guard needed — audit session 9) ONLY from a per-entry `StateRel` — which
`main_prefix_forward` does not hand out. Hence the "source-realizing witness"
premise is exactly the missing exposure, and supplying it = strengthening the
giant sim. No shortcut around re-threading.

### The concrete, minimal re-architecture (recommended shape for the next session)
Rather than a fresh triple simulation, **strengthen the existing recursion's
carried relation** so it exposes the per-entry invariant, then compose:
- **Step A (the bulk).** Add to `InteractionOwnerPreservation` /
  `…BoundedOwnerPreservation` / `…TruncationOwnerPreservation` an *entry
  invariant* alongside the existing threading: prove a forward theorem
  `main_prefix_forward_realizing` whose target-done relation additionally records
  that every block entry visited by the cfg `openRunNPrefix` satisfies
  `∃ source tokens, StateRel source tokens state ∧ SourceFrameFits input
  source.evm.stack.length` (equivalently, expose an `openRunNResultWithStop`
  invariant "each `openStep` is entered in a `StateRel`-realized state"). Because
  the per-construct lemmas ALREADY carry precisely these witnesses at entry and
  exit (see `openRun_toCfg` in `InteractionPreservation.lean:457`, and the
  `hStateRel`/`hFits` parameters threaded through `*_exec`), this is a
  *bookkeeping strengthening* of the conclusion, not new mathematics — but it
  touches every `*_exec` case and both mirror files.
- **Step B (small, mostly landed).** Given the per-entry witness from Step A,
  prove `openRunNPrefix_peephole_congr_of_source` by the SAME fuel induction as
  the current `openRunNPrefix_peephole_congr` (`PeepholeProgram.lean:174`), but at
  each `openStep` discharge `StackRealizes input state` via the session-8/9
  entry lemmas and feed the (new) swap arm through `openRunBody_swap_swap_congr`
  (landed session 6). The push;pop cases are unchanged.
- **Step C.** Swap the four OIC call sites
  (`OpenInteractionComposition.lean:909/942` prefix path; `:1415/1561/1688`
  terminal paths) from `openRunNPrefix_peephole_congr` /
  `openRunN_peephole_congr` to the `_of_source` variants; the source witness
  (`hUpper` / `generated`) is already in scope at all four.
- **Step D.** Add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`;
  re-green the syntactic (b)-family (trivial extra arm) and semantic congruences
  (consume Step B). Validate `scripts/opt_harness.sh full`.

**Effort estimate:** Step A is the multi-hundred-line (plausibly multi-session)
item — it is a conclusion-strengthening pass over ~16.7k lines of already-green
source-structural induction. Steps B–D are the bounded, de-risked remainder
(session 9 proved (1)+(2) of the recipe; the entry-discharge lemmas are landed).
The honest scope: this is NOT a glue lemma at the splice; it is a strengthening
of the Structured→cfg simulation's carried invariant. Sessions 5–9 and 10 have
each independently converged on exactly this, now pinned to the four files and
the specific `*_exec` case family that must gain the entry-invariant bookkeeping.

Landed this session: this note. Foundation from sessions 1–9 unchanged and green;
`peepholeBody`/public spine UNTOUCHED; measured delta +0.

## Session-11 update (2026-07-17): Step A scoped to the exact shared carried relations; in-place strengthening quantitatively shown ungreenable in one session (490 `ExecPreservesUnder` sites / 13 files); the green-preserving route is an ADDITIVE parallel "realizing" relation family. No code landed (greenness protected); baseline re-verified green.

Session 11 took the session-10 directive (Step A: expose a per-entry `StateRel`/
`SourceFrameFits` invariant from the source→cfg simulation so `main_prefix_forward`
hands out `main_prefix_forward_realizing`). After a full read of the carrying
relations I confirm — now with a **quantitative blast-radius measurement and the
interaction-monad subtlety pinned** — that Step A is NOT a localized bookkeeping
pass and cannot start-and-finish green in one session. The inherited tower is
UNCHANGED and green: `scripts/opt_harness.sh check` = OK (43 public theorems,
axioms `[propext, Classical.choice, Quot.sound]` incl. `compile_correct` /
`compile_correct_creation`). `peepholeBody`/public spine UNTOUCHED ⇒ measured
corpus delta definitionally **+0 bytes / +0.00%** (no re-bench needed).

### Finding 1 (NEW, decisive): the per-entry invariant is carried by SHARED abbrevs threaded through all 13 Structured files — in-place strengthening reddens ~17k lines at once
Session 10 called Step A "a bookkeeping strengthening of the conclusion … but it
touches every `*_exec` case and both mirror files." The stronger, measured truth:
the conclusion is not a bespoke relation per theorem — it is a **shared relation
abbrev** reused pervasively, so strengthening it *in place* is not 4 files, it is
the whole preservation stack.
- `ExecPreservesUnder result cfg entry ctx regular source tokens sourceRun policy`
  (`InteractionControlPreservation.lean:1043`, actually the `Exec…`/`Forward…`
  family) unfolds to `∀ target, StateRel source tokens target → ForwardRel
  Truncated (SegmentDoneRel …) sourceRun (openRunNResultWithStop policy cfg …)`.
  **`ExecPreservesUnder` occurs 490 times across 13 files** (`InteractionControl-
  Preservation` 116, `InteractionTruncationOwnerPreservation` 100, `Bounded-
  BlockPreservation` 18, `BoundedLoopPreservation` 47, `BoundedSwitchPreservation`
  49, `BoundedOwnerPreservation` 52, `CallPreservation` 26, `LoopPreservation` 34,
  `SwitchPreservation` 24, `OwnerPreservation` 16, `BranchPreservation`/`Bounded-
  BranchPreservation`/`TerminalPreservation`/`BoundedBranchPreservation` the
  remainder). `SegmentDoneRel` (`:552`, `= ExceptRel _ (SegmentRunRel …)`) occurs
  ~30×; `ForwardPreservesUnder` (`:1122`), `PrefixDoneRel` (`Truncation…:4613`,
  `= ExceptRel StructuralErrorRel (PrefixOutcomeRel)`), `PrefixOutcomeRel`
  (`:4594`) are the whole-program endpoints.
- Adding an entry-accumulator FIELD to `ExecPreservesUnder`/`SegmentDoneRel`
  changes the type at all 490 sites; each of the ~200 theorems producing/consuming
  it (the `*_exec` family + `if/switch/for/call/bounded_*` recursors + `block_owner`
  + both `*OwnerPreservation` mirrors) must be re-proved to establish/relay the new
  field. This reddens the entire tower simultaneously and is unre-greenable inside
  one session's build budget. (This is the concrete reason sessions 5–10 each
  deferred it; session 11 measures it.)

### Finding 2 (NEW): even the SOURCE-FREE half of the strengthened conclusion is a real interaction-tree induction, not plain plumbing
"Every block entry visited by the cfg `openRunNPrefix`" is a statement about
`openRunNResultWithStop policy cfg fuel entry target` (`InteractionSemantics.lean:772`
→ `Control.Program.runNWithStopAs`, `Control.lean:70`), which is an **interaction
tree** in `M = Simulation.Interaction EVMException`, not a linear trace: each
`openStep program label state` (`:759`) is itself an interaction tree whose
`.jump next state'` leaves depend on the environment's responses. So "visited
entry" is only well-defined **along an `Executes`/`Follows` branch** (or as a
step-indexed openStep invariant), never as a plain fuel fold over states. The
target-side accumulator must therefore be phrased as
`AllEntriesRealized cfg policy entry target := ∀ label state,
  «(entry,target) reaches an openStep at (label,state) before stopping» →
  ∃ source tokens block, cfg.findBlock? label = some block ∧
  StateRel source tokens state ∧ SourceFrameFits block.input state.evm.stack.length`
with a new step-indexed "reaches an openStep at" predicate over
`openRunNResultWithStop_succ` (`:863`). This is genuine interaction-tree
machinery — session 10's "expose an `openRunNResultWithStop` invariant" one-liner
hides a real sub-development.

### Recommended architecture (revised): ADDITIVE parallel "realizing" family, NOT in-place strengthening
To keep the tower green at every intermediate commit (the hard constraint), do
NOT edit `ExecPreservesUnder`/`SegmentDoneRel`/`ForwardPreservesUnder` in place.
Instead, in a NEW file (`Structured/InteractionEntryRealized.lean` or under
`TypedCfgPreservation/`), define a PARALLEL family that CONJOINS the existing
relation with the entry accumulator, and prove parallel `*_exec_realizing`
theorems that REUSE the existing (green, unchanged) `*_exec` for the outcome leg
and only ADD the accumulator leg:
- `RealizingForwardPreservesUnder … := ForwardPreservesUnder … ∧
   (∀ target, StateRel source tokens target → AllEntriesRealized cfg policy entry target)`
  (or fold the invariant into a `RealizingSegmentDoneRel = SegmentDoneRel ∧
  AllEntriesRealized-at-the-run-that-produced-this-done`).
- `code_exec_realizing`/`if_exec_realizing`/…/`block_owner_realizing` each take the
  same `FragmentContract` (whose `fits`/`activation` fields at `OwnerPreservation.
  lean:38,46` ALREADY supply the entry `SourceFrameFits`/`ActivationInput`, and the
  `StateRel` arrives as the `ExecPreservesUnder` hypothesis) and discharge the new
  accumulator by relaying the per-recursive-call entry witnesses. Because the
  existing `*_exec` stays byte-identical and green, the additive layer can be
  landed and committed **one file at a time, bottom-up**
  (`InteractionOwnerPreservation` → `block_owner` → `InteractionBoundedOwner-
  Preservation` mirror → `InteractionTruncationOwnerPreservation` mirror →
  `main_prefix_forward_realizing`), so partial progress is bankable green — unlike
  the in-place edit which is all-or-nothing red.

This is still the full recursion (every `*_exec` case + both mirrors + the
target-side interaction-tree invariant), i.e. genuinely multi-session, but it is
green-preserving at each step, which the in-place strengthening is not.

### Exact next-session recipe (green-preserving, bankable)
1. NEW file: define `ReachesOpenStepAt cfg policy entry target label state` (step-
   indexed over `openRunNResultWithStop_succ`) and `AllEntriesRealized` as above;
   prove the two structural facts: (i) the START entry `(entry,target)` is reached;
   (ii) reached-entries are closed under one non-stopping `openStep .jump` leaf.
   Prove `AllEntriesRealized` at fuel 0 / at a stop, trivially. [target-side only,
   NO source — self-contained green.]
2. NEW file: `RealizingForwardPreservesUnder` + `code_exec_realizing` (leaf; the
   straight-line `openRun_toCfg` at `InteractionPreservation.lean:457` already
   emits `StateRel`+`SourceFrameFits` at exit — relay them as the single-block
   entry witness). Commit green.
3. Thread the accumulator through `if/switch/for/call/brk/cont/leave/terminal_exec`
   → `exec_succ_realizing` → `block_owner_realizing`, REUSING each existing `*_exec`
   for the outcome. Commit per construct where the mutual recursion allows (likely
   one commit at `block_owner_realizing` since the recursion is mutual).
4. Mirror in `InteractionBoundedOwnerPreservation` then
   `InteractionTruncationOwnerPreservation`; produce `main_prefix_forward_realizing`.
5. Step B: `openRunNPrefix_peephole_congr_of_source` consumes `main_prefix_forward_
   realizing`'s `AllEntriesRealized`; at each openStep discharge `StackRealizes
   input state` via `stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,
   returnTokenDepth?_eq_none}` (landed sessions 8/9, NO token guard — audit
   session 9) and feed `openRunBody_swap_swap_congr` (landed session 6).
6. Step C: swap the four OIC call sites (`OpenInteractionComposition.lean:909/942`
   prefix; `:1415/1561/1688` terminal) to the `_of_source` variants.
7. Step D: add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`; re-green
   the syntactic (b)-family + semantic congruences; `scripts/opt_harness.sh full`.

### Status handed to session 12
Foundation from sessions 1–10 UNCHANGED and green. Landed this session: this note
+ the quantitative ripple measurement (490 `ExecPreservesUnder` sites / 13 files)
and the interaction-tree phrasing of the target-side invariant, which redefine
Step A from "in-place conclusion bookkeeping" (all-or-nothing red) to an ADDITIVE
parallel realizing family (bankable green, still multi-session). No `peepholeBody`/
public-spine/shared-definition change ⇒ `compile_correct` / `compile_correct_creation`
axioms unchanged `[propext, Classical.choice, Quot.sound]`, measured delta +0.

## Session-12 update (2026-07-17): FIRST CODE IN 7 SESSIONS — Step A item 1 (the target-side realizing substrate) LANDED green, axiom-clean, in 2 commits; leaf-discharge rule proved; the exec-vs-forward fuel-coupling design pinned for item 2

Sessions 5–11 ended with scoping notes and zero Lean. Session 12 executed the
session-11 recipe's **item 1** (the self-contained, source-free, target-side
machinery) and landed it as two green, axiom-clean commits. `scripts/opt_harness.sh
check` = OK (43 public theorems, axioms `[propext, Classical.choice, Quot.sound]`
incl. `compile_correct` / `compile_correct_creation`). `peepholeBody`/public spine
UNTOUCHED ⇒ measured corpus delta still definitionally **+0** (no arm shipped).

### Landed commits (branch `arena-opt`)
- **`7a0c6df8`** — NEW file `EvmCompiler/TypedCfg/InteractionEntryRealized.lean`
  (wired into `EvmCompiler.Verification`). The step-indexed block-entry
  reachability substrate the recipe's item 1 designates, phrased per session-11
  Finding 2 (openStep is an interaction tree, so a `.jump` leaf is only defined
  along a concrete `Executes` branch):
  - `ReachesOpenStepAt program stopJump fuel entry target rLabel rState`
    (`:60`, inductive) — `start` (reflexive) + `step` (one non-stopping openStep
    `.jump` leaf along an `Executes` transcript extends reachability).
  - `AllEntriesRealized program stopJump fuel entry target realized` (`:111`) —
    quantifies an ABSTRACT `realized : Label → EVMState → Prop` over every reached
    entry. Left abstract on purpose so this layer is source-free/green; item 2
    instantiates it with `fun label state => ∃ source tokens block,
    cfg.findBlock? label = some block ∧ StateRel source tokens state ∧
    SourceFrameFits block.input state.evm.stack.length`.
  - Structural facts: `reaches_start` (i, `:82`), `eq_of_zero` inversion (`:90`),
    `AllEntriesRealized.realized_start` (`:123`), `.of_zero` (`:132`),
    `.of_succ` (ii, the successor-introduction rule the recursion relays, `:150`).
- **`5bb770ff`** — same file, `AllEntriesRealized.of_first_jump_stops` (`:179`):
  the **leaf-discharge rule**. If every concrete first-step jump out of the entry
  lands on a STOPPING target, the run visits no entry beyond the start, so
  `AllEntriesRealized (fuel+1)` reduces to the single fact `realized entry target`.
  This is exactly what the leaf `*_exec_realizing` cases (`code`/`terminal`/`brk`/
  `cont`/`leave`) invoke: those fragments each compile to ONE block ending in a
  `.jump` that the fragment's stop policy halts on (VERIFIED via
  `InteractionControlPreservation.openRun_nil_under_of_compileStmtListFuel?` /
  `openRun_code_of_compileStmtFuel?`: `.code` → single block, body = lowered code,
  term = `.jump regular`, targetFuel = 1, `regular` a policy stop boundary).

All new lemmas `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### The design decision item 2 must make FIRST (pinned this session — saves the trace)
The recipe's `RealizingForwardPreservesUnder := ForwardPreservesUnder ∧
(∀ target, StateRel → AllEntriesRealized cfg policy entry target)` attaches the
accumulator at the **FORWARD** level, which carries a SINGLE `targetFuel` budget
(`InteractionControlPreservation.lean:1122 ForwardPreservesUnder`, one `targetFuel`
arg). But the leaf theorem the recipe names is `code_exec_realizing`, and
`code_exec` produces `ExecPreservesUnder` (`InteractionControlPreservation.lean:936`),
whose `targetFuel` is **existential per (transcript, sourceOutcome)**. You cannot
cleanly conjoin `AllEntriesRealized cfg policy <fuel> …` to `ExecPreservesUnder`
because there is no single `<fuel>` to name. RESOLUTION (recommended): attach the
realizing accumulator at the level where the budget is a single value:
- Define `RealizingForwardPreservesUnder result cfg entry ctx regular regularExit
  source tokens sourceRun targetFuel policy realized := ForwardPreservesUnder …
  targetFuel … ∧ (∀ target, StateRel source tokens target → AllEntriesRealized
  cfg policy targetFuel entry target realized)` — SAME `targetFuel`, so both legs
  refer to one run. (Analogously add `Realizing` variants of `BoundedExec…`/
  `BoundedForward…` where the accumulator is `∀ tf ≤ budget, AllEntriesRealized …
  tf …`; note more fuel visits a SUPERSET of entries, but the extra entries are
  past the policy stop, so for a fragment they never appear — prove a monotone
  `AllEntriesRealized_of_le` if the bounded level needs it.)
- Name the leaf `code_forward_realizing` (built on the existing `ForwardPreservesUnder`
  leaf, not the `Exec` one) OR keep `_exec` naming but state it at the uniform-fuel
  `UniformDoneExecPreservesUnder` level (`:1098`, single `targetFuel`) which `code`
  already satisfies at `targetFuel = 1`. The `Exec`→`Forward` glue in the existing
  tower (`PreservesUnder.exec`, the bounded/forward combinators) shows where the
  single budget is chosen; mirror it for the realizing leg.

### Exact next-session recipe (items landed struck through)
1. ~~target-side `ReachesOpenStepAt`/`AllEntriesRealized` + structural facts~~ **DONE (session 12)**.
   The leaf-discharge `of_first_jump_stops` is **also DONE** — leaf `*_exec_realizing`
   cases consume it directly.
2. NEW file (e.g. `Structured/InteractionEntryRealizedForward.lean`): define
   `RealizingForwardPreservesUnder` (single-`targetFuel` form above) and prove the
   LEAF `code_forward_realizing` / `terminal_forward_realizing`: reuse the existing
   green `code`/`terminal` forward leaf for the `ForwardPreservesUnder` conjunct;
   discharge the `AllEntriesRealized` conjunct with `AllEntriesRealized.of_first_jump_stops`
   (landed) — supplying `realized entry target` from the `StmtContract`'s
   `fits`/`activation` + the `StateRel target` hypothesis and `cfg.findBlock? entry`,
   and the "first jump stops" hypothesis from the fragment's `stops`/boundary
   (`TargetStoppedBy policy`). Commit green.
3. Thread the accumulator through `if/switch/for/call/brk/cont/leave` →
   `exec_succ_realizing` → `block_owner_realizing`, REUSING each existing `*_exec`/
   `*_forward` for the outcome leg and relaying per-recursive-call `AllEntriesRealized`
   via `of_succ` (composite fragments: the accumulator over the whole run is the
   start entry realized + the recursive sub-runs' accumulators, glued at each
   openStep jump). Commit at `block_owner_realizing` (mutual recursion).
4. Mirror in `InteractionBoundedOwnerPreservation` then
   `InteractionTruncationOwnerPreservation`; produce `main_prefix_forward_realizing`
   exposing `AllEntriesRealized cfg policy targetFuel cfg.entry target realizedSrc`.
5. Step B: `openRunNPrefix_peephole_congr_of_source` consumes
   `main_prefix_forward_realizing`'s `AllEntriesRealized`; at each openStep discharge
   `StackRealizes input state` via `stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,
   returnTokenDepth?_eq_none}` (landed 8/9) + feed `openRunBody_swap_swap_congr`
   (landed 6). NO token guard (audit 9).
6. Step C: swap the four OIC call sites (`OpenInteractionComposition.lean:909/942`
   prefix; `:1415/1561/1688` terminal) to the `_of_source` variants.
7. Step D: add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`; re-green
   the syntactic (b)-family + semantic congruences; `scripts/opt_harness.sh full`.

### Status handed to session 13
Foundation from sessions 1–11 UNCHANGED and green. NEW this session: the entire
target-side realizing substrate (`InteractionEntryRealized.lean`, 8 defs/lemmas)
+ the leaf-discharge rule — i.e. item 1 of the session-11 recipe is CLOSED and
banked green, and the leaf `*_exec_realizing` obligation is now a one-lemma
application away. Remaining = items 2–7 (the realizing forward family + the
per-construct threading + both mirrors + Steps B–D). The exec-vs-forward
fuel-coupling — the one design ambiguity in the session-11 recipe — is resolved
above (attach at the single-`targetFuel` FORWARD/uniform level, not the
existential-fuel `ExecPreservesUnder` level). `compile_correct` /
`compile_correct_creation` axioms unchanged `[propext, Classical.choice,
Quot.sound]`; measured delta +0.

## Session-13 update (2026-07-17): item 2 CLOSED — the `RealizingForwardPreservesUnder` family + the backward simulation bridge + ALL FIVE single-block leaf realizing lemmas landed green in 3 commits. The exec-vs-forward fuel-coupling limits the leaf pattern to single-block (`targetFuel = 1`) fragments; the composite cases (if/switch/for/call) genuinely need the bounded/forward budget-selection layer (the deferred Step-A bulk), precisely re-scoped below.

Session 13 executed the session-11/12 recipe's **item 2** and the leaf half of
**item 3**, landing three green, axiom-clean commits. Foundation from sessions
1–12 UNCHANGED and green; `peepholeBody`/public spine UNTOUCHED ⇒ measured corpus
delta still definitionally **+0** (no arm shipped). All new lemmas
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (`Rel.executes_right`
needs only `[propext, Quot.sound]`).

### Landed commits (branch `arena-opt`)
- **`19ca2221`** (item 2a) — NEW file
  `EvmCompiler/Structured/InteractionEntryRealizedForward.lean` (wired into
  `EvmCompiler.Verification`). Three things, all ADDITIVE (no existing abbrev or
  lemma statement touched):
  - `Simulation.Interaction.Rel.executes_right` (`:56`) — the **backward companion
    of the package's `Rel.executes`**: `Rel doneRel left right` +
    `Executes right transcript rightOutcome` → `∃ leftOutcome, Executes left
    transcript leftOutcome ∧ doneRel leftOutcome rightOutcome`. Mirror induction
    on the RIGHT execution (the interaction-tree `Rel.request` aligns queries, so
    the same transcript replays on the left). This is the bridge that turns an
    `openStep` execution into the source-side `Rel` the fragment contract's `stops`
    field constrains. `[propext, Quot.sound]`.
  - `RealizingForwardPreservesUnder result cfg entry ctx regular regularExit
    source tokens sourceRun targetFuel policy realized` (`:100`) — the parallel
    family: `ForwardPreservesUnder … targetFuel policy ∧ (∀ target, StateRel →
    AllEntriesRealized cfg policy targetFuel entry target realized)`, at the SAME
    single `targetFuel`. Projections `.forward` / `.allEntriesRealized`.
  - `RealizingForwardPreservesUnder.of_forward_first_jump_stops` (`:186`) — the
    **generic single-block leaf constructor** at budget `fuel + 1`: given the
    forward outcome leg, the start-entry realization `hRealized`, and that every
    first-step jump out of the entry lands on a policy-stopping target `hStops`
    (∀ target/StateRel, ∀ transcript/next/state', `Executes (openStep cfg entry
    target) transcript (.ok (jump next state'))` → `policy next state' = true`),
    it produces the family by discharging `AllEntriesRealized` through the landed
    `of_first_jump_stops`. This is the reusable heart; each leaf proves its own
    `hStops`/`hRealized`.
- **`32970a18`** (item 2b) — NEW file
  `EvmCompiler/Structured/InteractionOwnerRealized.lean` (wired into Verification).
  The two leaves the recipe names:
  - `code_forward_realizing` (`:44`) / `terminal_forward_realizing` (`:104`)
    (namespace `Structured.InteractionOwnerPreservation.OpenOutcome`). Each is one
    application of `of_forward_first_jump_stops`:
    - forward leg = the EXISTING single-`targetFuel` leaf `PreservesUnder … 1
      policy` (`openRun_{code,terminal}_under_of_compileStmtFuel?`) weakened via
      `Simulation.Interaction.ForwardRel.ofRel`;
    - `hStops` = the fragment's single `openStep` relation
      (`openStep_{code,terminal}_of_compileStmtFuel?` : `Rel (OutcomeDoneRel …)
      sourceRun (openStep cfg entry target)`) backward-simulated by
      `Rel.executes_right`; the resulting `Rel result … srcOut (jump next state')`
      is fed to `contract.stops`, whose `TargetStoppedBy policy (jump next state')`
      is **defeq** `policy next state' = true`.
  - The start-entry realization `realized entry target` is taken as the hypothesis
    `hEntry : ∀ target, StateRel source tokens target → realized entry target`,
    keeping `realized` ABSTRACT at this layer (the concrete source-witness
    instantiation is a spine-level concern; sessions 7/8 showed the
    `SourceFrameFits`-on-target shortcut is unsound, so `realized` will be the
    `∃ src tks blk, findBlock? label = blk ∧ StateRel src tks state ∧
    SourceFrameFits blk.input src.evm.stack.length` witness, discharged at each
    entry by `stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,
    returnTokenDepth?_eq_none}`).
- **`05db85a4`** (item 2c) — same file, the other three single-block leaves
  `brk_forward_realizing` (`:181`) / `cont_forward_realizing` /
  `leave_forward_realizing`. Identical `of_forward_first_jump_stops` shape, with
  the break/continue/leave exit label obtained from `ContextSupports` (and leave's
  live-frame witness `hSourceReturns`) exactly as `brk_exec`/`cont_exec`/`leave_exec`.

**All five single-block leaf constructs now have realizing forward lemmas.** The
existing `code_exec`/`terminal_exec`/`brk_exec`/`cont_exec`/`leave_exec`
(producing `ExecPreservesUnder`) are UNTOUCHED and sit beside these.

### The exec-vs-forward fuel-coupling, re-confirmed at the composite boundary
The leaf pattern works because a single-block fragment lowers at a FIXED
`targetFuel = 1` (`of_openStep` gives `PreservesUnder … 1`), so `AllEntriesRealized
cfg policy 1 …` names one concrete run and `of_first_jump_stops` (fuel `0 + 1`)
applies. The composite recursors `if_exec`/`switch_exec`/`for_exec`/`call_exec`
(`InteractionOwnerPreservation.lean`) produce `ExecPreservesUnder` — whose
`targetFuel` is **existential per (transcript, sourceOutcome)** — NOT a single-fuel
`PreservesUnder`. So `RealizingForwardPreservesUnder` (which fixes ONE `targetFuel`)
cannot be conjoined to a composite `*_exec` directly; there is no single `<fuel>`
to name for its `AllEntriesRealized` conjunct. This is exactly the design tension
session 12 pinned, and it stops cleanly at the leaf boundary: the leaves are the
fragments with a canonical single target budget.

### Exact next-session recipe (leaves landed struck through)
1. ~~target-side `ReachesOpenStepAt`/`AllEntriesRealized` + `of_first_jump_stops`~~
   **DONE (session 12)**.
2. ~~`RealizingForwardPreservesUnder` family + generic constructor + the five
   single-block leaf `*_forward_realizing` lemmas~~ **DONE (session 13)**.
3. **Composite threading (the Step-A bulk — genuinely multi-session).** The
   composite cases cannot reuse `of_forward_first_jump_stops` (existential fuel,
   above). Two sub-routes, in dependency order:
   - **3a. Bounded realizing family.** Define `RealizingBoundedForwardPreservesUnder`
     (or `…BoundedExec…`) conjoining the existing bounded exec/forward leg with
     `∀ tf ≤ budget, AllEntriesRealized cfg policy tf entry target realized`
     (`AllEntriesRealized` is MONOTONE in fuel only up to the policy stop — more
     fuel past a stop visits no new entries; prove `AllEntriesRealized_of_le` or,
     better, note the composite's own stop policy bounds the reachable set). The
     accumulator over the WHOLE composite run is the start entry realized + the
     recursive sub-runs' accumulators, glued at each `openStep` jump via
     `AllEntriesRealized.of_succ` (landed session 12): each `ReachesOpenStepAt`
     `.step` leaf out of the composite entry lands in a sub-fragment whose
     realizing lemma supplies the residual `AllEntriesRealized`.
   - **3b. Per-construct realizing recursors.** `if_forward_realizing` /
     `switch_forward_realizing` / `for_forward_realizing` / `call_forward_realizing`
     → `exec_succ_realizing` → `block_owner_realizing`, each REUSING the existing
     (green, unchanged) `*_exec` for the outcome leg and relaying per-recursive-call
     `AllEntriesRealized` via `of_succ`. The mutual recursion likely forces one
     commit at `block_owner_realizing`. The key new obligation per construct: relate
     `ReachesOpenStepAt` of the composite `openStep`/`openRunNResultWithStop` to the
     sub-fragments' reachability (the composite's first `openStep` jumps into a
     child block; `of_succ`'s `hNext` is discharged by the child's realizing lemma).
4. Mirror in `InteractionBoundedOwnerPreservation` then
   `InteractionTruncationOwnerPreservation`; produce `main_prefix_forward_realizing`
   exposing `AllEntriesRealized cfg policy targetFuel cfg.entry target realizedSrc`.
5. Step B: `openRunNPrefix_peephole_congr_of_source` consumes
   `main_prefix_forward_realizing`'s `AllEntriesRealized`; at each openStep discharge
   `StackRealizes input state` via `stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,
   returnTokenDepth?_eq_none}` (landed 8/9) + feed `openRunBody_swap_swap_congr`
   (landed 6). NO token guard (audit 9). Here the abstract `realized` is instantiated
   to the source witness and `hEntry` at each leaf is discharged from the threaded
   `StateRel`/`SourceFrameFits`.
6. Step C: swap the four OIC call sites (`OpenInteractionComposition.lean:909/942`
   prefix; `:1415/1561/1688` terminal) to the `_of_source` variants.
7. Step D: add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`; re-green
   the syntactic (b)-family + semantic congruences; `scripts/opt_harness.sh full`.

### Files/lemmas landed this session (all absolute-buildable, wired into Verification)
- `EvmCompiler/Structured/InteractionEntryRealizedForward.lean` — `Rel.executes_right`,
  `RealizingForwardPreservesUnder` (+ `.forward` / `.allEntriesRealized` /
  `.of_forward_first_jump_stops`).
- `EvmCompiler/Structured/InteractionOwnerRealized.lean` — `code_forward_realizing`,
  `terminal_forward_realizing`, `brk_forward_realizing`, `cont_forward_realizing`,
  `leave_forward_realizing`.

### Status handed to session 14
Item 2 (the realizing forward family) and ALL FIVE single-block leaves are CLOSED
and banked green. Remaining = item 3's composite cases (the genuine Step-A bulk:
bounded realizing family + `if`/`switch`/`for`/`call`/`exec_succ`/`block_owner`
realizing recursors + both mirrors → `main_prefix_forward_realizing`) then Steps
B–D. The composite cases require the bounded/forward budget-selection layer (they
cannot reuse the single-`targetFuel` leaf constructor), re-scoped precisely above.
`compile_correct` / `compile_correct_creation` axioms unchanged
`[propext, Classical.choice, Quot.sound]`; measured delta +0.

## Session-14 update (2026-07-17): item 3a (the bounded realizing family) LANDED + fuel monotonicity + the KEY composite unblock — the per-block `openStep_*_of_compileStmtFuel?` relations ALREADY expose the child-entry `StateRel`, so the composites do NOT need the 16.7k-line giant-sim re-threading sessions 10/11 feared. Three green, axiom-clean commits; the `if` child-`StateRel` extraction landed and validated. The remaining composite recursors are now a bounded, de-risked build (recipe rewritten below), not an open-ended re-threading.

Session 14 executed item 3a of the session-13 recipe and, in the course of it,
found that the composite obstruction sessions 5–13 had scoped as "requires
strengthening the giant Structured→cfg simulation to expose a per-entry
`StateRel`" is **already discharged by existing per-block machinery**.  Three
commits, all green; `scripts/opt_harness.sh check` = OK (43 public theorems,
axioms `[propext, Classical.choice, Quot.sound]` incl. `compile_correct` /
`compile_correct_creation`).  `peepholeBody`/public spine UNTOUCHED ⇒ measured
delta still definitionally **+0**.

### Landed commits (branch `arena-opt`)
- **`1c5dc20d`** — target-side fuel monotonicity, additive in
  `EvmCompiler/TypedCfg/InteractionEntryRealized.lean`:
  - `ReachesOpenStepAt.of_le` (`:105`) — reachable block-entry set is **monotone**
    in fuel (`m ≤ n → reaches m → reaches n`; induction on the derivation, each
    `.step` re-applies one level higher, `.start` holds at any fuel).
  - `AllEntriesRealized.of_le` (`:223`) — realization is **antitone** in fuel
    (`m ≤ n → AllEntriesRealized n → AllEntriesRealized m`).  This is the fact the
    bounded family's `∀ tf ≤ budget` quantifier rests on: it is *equivalent* to the
    single `AllEntriesRealized … budget …`, so a budget-level realization spreads
    to every shorter run the existential-fuel composite might actually take.
  Axioms `[propext, Classical.choice, Quot.sound]`.
- **`73539c93`** — **item 3a**, NEW file
  `EvmCompiler/Structured/InteractionEntryRealizedBounded.lean` (wired into
  `EvmCompiler.Verification`).  `RealizingBoundedExecPreservesUnder` (`:62`): the
  additive parallel family conjoining the existing (unchanged)
  `BoundedExecPreservesUnder` outcome leg with
  `∀ tf ≤ targetBudget, AllEntriesRealized cfg policy tf entry target realized`.
  This is the vehicle the composites need — unlike the single-`targetFuel`
  `RealizingForwardPreservesUnder` (session 13, leaves only), the bounded budget +
  `∀tf≤budget` accommodates the **existential** `targetFuel` a composite
  `ExecPreservesUnder`/`BoundedExecPreservesUnder` selects.  Projections
  `.bounded` (`:91`) / `.exec` (`:103`, forgets to plain `ExecPreservesUnder` via
  `BoundedExecPreservesUnder.exec`) / `.allEntriesRealized` (`:113`); builder
  `.mk` (`:132`, budget-level accumulator ⇒ `∀tf≤` via `AllEntriesRealized.of_le`);
  `.mono_budget` (`:155`, note: the accumulator is genuinely STRONGER at a larger
  budget, so it is supplied afresh — there is deliberately no upward-monotone
  accumulator lemma).  Axioms `[propext, Classical.choice, Quot.sound]`.
- **`6ebe2ceb`** — the composite UNBLOCK, NEW file
  `EvmCompiler/Structured/InteractionBranchEntryRealized.lean` (wired into
  Verification).  `jump_state_rel_of_rel` (`:55`, namespace
  `Structured.InteractionBranchPreservation.Condition`): from the `if`-entry
  block's branch relation `Rel (DoneRel trueLabel falseLabel tokens restShape)
  srcRun targetRun` and a concrete target first-step jump
  `Executes targetRun transcript (.ok (.jump next state'))`, extract
  `next = (if cond then trueLabel else falseLabel)`,
  `StateRel srcState tokens state'`, and
  `SourceFrameFits restShape state'.evm.stack.length`.  Axioms `[propext, Quot.sound]`.

### THE KEY DISCOVERY (rewrites the composite scoping): child `StateRel` is already exposed
Sessions 10/11 concluded the composite accumulator was blocked because
`main_prefix_forward` / `ExecPreservesUnder` collapse intermediate block-entry
jumps and expose no per-entry `StateRel`, so they framed step 4/A as a
multi-session strengthening of the whole ~16.7k-line source→cfg simulation.  That
framing is **too pessimistic at the owner-preservation layer**.  The composite
recursors do not go through `main_prefix_forward`; they go through the per-block
`openStep_*_of_compileStmtFuel?` relations, and those **already carry the child
`StateRel`**:
- `InteractionBranchPreservation.Condition.openStep_if_of_compileStmtFuel?`
  (`InteractionBranchPreservation.lean:278`) returns
  `Rel (DoneRel trueLabel falseLabel tokens bodyInput) (openRunCondition cond
  source) (openStep cfg entry target)`, where `DoneRel = ExceptRel _ (ResultRel …)`
  and `ResultRel` (`:95`) is literally
  `∃ targetState, target = .jump (if cond then trueLabel else falseLabel)
  targetState ∧ StateRel source.1 tokens targetState ∧ SourceFrameFits restShape
  source.1.evm.stack.length`.
- So a composite's non-stopping **first** openStep jump, backward-simulated by
  `Rel.executes_right` (landed session 13), yields the source `StateRel` +
  `SourceFrameFits` for the jumped-to child state directly (this is exactly
  `jump_state_rel_of_rel`, landed).  The child fragment's realizing lemma then
  supplies the residual `AllEntriesRealized`, glued by `AllEntriesRealized.of_succ`
  (landed session 12).  **No giant-sim re-threading is required.**

Consequence for the `realized` abstraction: at the composite level `realized`
must be **instantiated to (or side-conditioned as derivable-from) the source
witness** `fun label state => ∃ src tks blk, cfg.findBlock? label = some blk ∧
StateRel src tks state ∧ SourceFrameFits blk.input state.evm.stack.length`,
because the child entry's `hEntry` is discharged from the extracted `StateRel`
(the abstract-`realized` pass-through only works at the leaves, where the first
jump stops).  Equivalently, add a uniform side hypothesis
`hRealizedOfStateRel : ∀ label state src tks blk, cfg.findBlock? label = some blk →
StateRel src tks state → SourceFrameFits blk.input state.evm.stack.length →
realized label state` to the composite recursors; the leaves already satisfy it
vacuously via `hEntry`.

### Exact next-session recipe (item 3b — now bounded and de-risked)
Leaves (item 2) + item 3a bounded family + fuel monotonicity + the `if`
child-`StateRel` extraction are DONE and banked green.  Remaining:
1. **Realizing block owner.**  Define `RealizingBlockOwnerAt` mirroring
   `BlockOwnerAt` (`InteractionOwnerPreservation.lean:155`) but yielding
   `RealizingBoundedExecPreservesUnder` (with the source-witness `realized`).
   Prove `block_owner_realizing` by the SAME `Nat.strong_induction_on sourceFuel`
   as `block_owner` (`:1502`), feeding each recursive call the strictly-smaller-fuel
   realizing owner.  This is the mutual-recursion anchor; the per-construct cases
   are its body.
2. **Per-construct realizing recursors**, each REUSING the existing (green)
   `*_exec` for the outcome leg (`.bounded` conjunct via
   `BoundedExecPreservesUnder`, obtained from the existing owner-preservation
   `openRun_*_exec_under` at its bounded budget) and discharging the accumulator by:
   `AllEntriesRealized.of_succ` on the composite entry's first jump →
   `jump_state_rel_of_rel` (for `if`; write the `switch`/`for`/`call` analogues —
   `switch` selects one of N case labels, `for` enters the cond/body/post cycle,
   `call` pushes a frame — each has its own `openStep_*` relation exposing the child
   `StateRel`, mirror `openStep_if`) → the child's realizing lemma from
   `RealizingBlockOwnerAt` at the extracted `StateRel`.  Rule out the non-body
   branch (e.g. `if` false → `regular`) under `hStop` via `contract`'s boundary
   stop fact (`policy regular _ = true` contradicts `hStop = false`).  Order:
   `if` → `switch` → `for` → `call` (dependency = none between them; do `if` first
   as the template).  Commit per construct where the mutual recursion allows
   (likely one commit at `block_owner_realizing`).
3. `exec_succ_realizing` (dispatch over `Stmt`, mirroring `exec_succ` `:1370`) then
   the mirrors in `InteractionBoundedOwnerPreservation` /
   `InteractionTruncationOwnerPreservation` → `main_prefix_forward_realizing`.
4. Steps B–D (unchanged): `openRunNPrefix_peephole_congr_of_source` consumes
   `main_prefix_forward_realizing`'s `AllEntriesRealized`, discharges
   `StackRealizes` via `stackRealizes_of_stateRel_of_*` (landed 8/9) + feeds
   `openRunBody_swap_swap_congr` (landed 6); swap the four OIC call sites
   (`OpenInteractionComposition.lean:909/942` prefix; `:1415/1561/1688` terminal) to
   `_of_source`; add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`;
   re-green the syntactic (b)-family + semantic congruences; `scripts/opt_harness.sh full`.

### Status handed to session 15
Item 3a (bounded realizing family) + fuel monotonicity + the `if` child-`StateRel`
extraction are CLOSED and banked green.  The composite obstruction is **downgraded
from "re-thread the 16.7k-line giant sim" (sessions 10/11) to "build a realizing
block owner + four per-construct recursors that read the child `StateRel` off the
existing `openStep_*` relations"** — a bounded, mechanical build with the `if`
template already landed.  `compile_correct` / `compile_correct_creation` axioms
unchanged `[propext, Classical.choice, Quot.sound]`; measured delta +0 (no arm
shipped).

## Session-15 update (2026-07-17): the `call` child-`StateRel` extraction LANDED, and the KEY finding that ALL FOUR composite extraction lemmas collapse to exactly TWO reusable lemmas — the entire item-3b *extraction* layer is now closed. The realizing recursors + `block_owner_realizing` mutual recursion (item 3b *threading*) remain the genuine multi-session bulk; the bounded owner layer is confirmed as the exact mirror target and the source-witness form is pinned. One green, axiom-clean commit; peepholeBody/public spine UNTOUCHED ⇒ measured delta still definitionally **+0**.

### Landed commit (branch `arena-opt`)
- **`56f06ce3`** — NEW file
  `EvmCompiler/Structured/InteractionCallEntryRealized.lean` (wired into
  `EvmCompiler.Verification`).  `jump_state_rel_of_pure` (`:63`, namespace
  `Structured.InteractionCallPreservation.Call`): the **`call` analogue of the
  session-14 `if` template `jump_state_rel_of_rel`**.  From a concrete pure-jump
  characterization `openStep cfg entry target = pure (.jump childLabel childState)`
  (exactly what `InteractionCallPreservation.Call.openStep_entry_of_compileStmtFuel?`
  at `InteractionCallPreservation.lean:264` establishes for the *silent* call-site
  block, with `childLabel = ProcLabel.entry name` and a child `StateRel` for
  `childState`), plus a child `StateRel childSource childTokens childState`, plus a
  concrete `Executes … transcript (.ok (.jump next state'))`, it extracts
  `next = childLabel ∧ StateRel childSource childTokens state'`.  Proof: `pure x =
  .done (.ok x)`, so `cases` on the `Executes` of the `.done` leaf pins
  `transcript = []` and `next = childLabel`, `state' = childState` by injection — no
  backward simulation needed (unlike the `if`/jumpi case).  Axioms `[propext,
  Classical.choice, Quot.sound]`.

### THE KEY FINDING: four constructs, two extraction lemmas (extraction layer CLOSED)
A per-construct read of every composite's first-`openStep` exposure shows the item-3b
"write the `openStep` child-`StateRel` extraction lemma for each" obligation collapses
to the two lemmas now landed — no new extraction lemmas for `switch`/`for` are needed:

- **`if`** — entry block is a `jumpi` to `body`/`regular`, related to the source
  condition run by `InteractionBranchPreservation.Condition.DoneRel trueLabel
  falseLabel tokens restShape` (an interaction `Rel`).  Extraction =
  **`jump_state_rel_of_rel`** (landed session 14).
- **`for`** — the loop condition block is *also* a `jumpi`, and
  `InteractionLoopPreservation.Loop.openStep_condition`
  (`InteractionLoopPreservation.lean:76`) states its relation over the **same**
  `InteractionBranchPreservation.Condition.DoneRel bodyLabel endLabel tokens {…}`
  (verified at `:98-104`).  So `for`'s extraction is **`jump_state_rel_of_rel`
  reused verbatim** (generic over `trueLabel`/`falseLabel`/`tokens`/`restShape`);
  no `for`-specific lemma is required.
- **`switch`** — the entry block (`[.pop]` then `jump` to the first test) and every
  test block (`[.dup 0, .push cv, .prim .eq]` then `jumpi`) are **silent**:
  `InteractionSwitchPreservation.Switch.openStep_pop_jump`
  (`InteractionSwitchPreservation.lean:19`) and `.openStep_test` (`:95`) both prove
  `openStep … = .done (.ok (.jump L targetFinal))` = a concrete `pure` jump, with
  `StateRel` in hand.  So `switch`'s extraction is **`jump_state_rel_of_pure`
  reused** (`.done (.ok x) = pure x`); no `switch`-specific lemma is required.
- **`call`** — silent call-site block, `pure` jump to `ProcLabel.entry name`.
  Extraction = **`jump_state_rel_of_pure`** (landed this session).

**Net: `jump_state_rel_of_rel` (jumpi-branch `Rel` form; if + for) and
`jump_state_rel_of_pure` (pure-jump form; switch + call) together discharge the
child-`StateRel` extraction for every composite.**  Item 3b's extraction sub-task
(the "write the `openStep_*` child-`StateRel` extraction lemmas for each" in the
session-14 recipe) is CLOSED.

### The recursor + mutual-recursion bulk (item 3b *threading*) — still the remaining work, now fully de-risked
The outstanding piece is the accumulator *threading*: the `*_bounded_realizing`
recursors + `bounded_succ_realizing` + `block_owner_realizing` + `main_bounded_realizing`.
Recon this session pinned the exact mirror target and the design crux:

- **Mirror target = the BOUNDED owner layer** (`InteractionBoundedOwnerPreservation.lean`),
  NOT the plain `InteractionOwnerPreservation.lean` `*_exec` layer.  The bounded layer
  already has the full spine at the `BoundedExecPreservesUnder` budget
  `InteractionStaticCost.blockBudget program blockSourceFuel block`, which is the
  single concrete `targetBudget` the realizing family
  (`RealizingBoundedExecPreservesUnder`, landed session 14) needs:
  `code_bounded` (`:152`), `if_bounded` (`:205`), `switch_bounded` (`:387`),
  `for_bounded` (`:609`), `call_bounded` (`:1385`), `brk/cont/leave/terminal_bounded`
  (`:1803`/`:1870`/`:1937`/`:2014`), `bounded_succ` (`:2069`), the fuel-founded
  `block_owner` (`:2335`, `Nat.strong_induction_on sourceFuel`), `main_bounded`
  (`:3121`), `main_uniform` (`:3229`).  The realizing layer mirrors each with a
  `_realizing` suffix: `.bounded` conjunct = the existing bounded theorem verbatim;
  `.allEntriesRealized` conjunct = the accumulator threaded via `of_succ`.
- **`StopPolicy = Assembly.Label → EVMState → Bool`** (`InteractionControlPreservation.lean:108`),
  i.e. `policy` IS the `stopJump` that `AllEntriesRealized` takes as its second
  argument — no coercion.  So the composite's `regular`/boundary branch (`if` false,
  `for` end, `switch` default-fallthrough) is ruled out inside `of_succ`'s `hNext`
  by `policy regular _ = true` (the contract's `boundary`/`stops` fact) contradicting
  the supplied `hStop : policy next state' = false`.  The `body`/`case`/`proc-entry`
  branch is non-stopping and recurses into the child's realizing owner at the
  extracted `StateRel`.
- **The source-witness `realized` is pinned** (validated against BOTH the extraction
  outputs AND the session-8/9 discharge lemmas):
  ```
  realized label state :=
    ∃ (source : RunState) (tokens : List Word) (block : TypedCfg.Block),
      cfg.findBlock? label = some block ∧
      TypedCfgPreservation.StateRel source tokens state ∧
      TypedCfgCompiler.Shape.SourceFrameFits block.input source.evm.stack.length
  ```
  Note `SourceFrameFits` reads the **SOURCE** stack length (`source.evm.stack.length`),
  exactly as `jump_state_rel_of_rel` returns it (`SourceFrameFits restShape
  srcState.evm.stack.length`) and exactly as `stackRealizes_of_stateRel_of_{returnTokenDepth?_eq_none,
  token_last_of_tokens_cons}` (`StackRealizesEntry.lean:166`/`:214`) consume it to
  produce the runtime `TypedCfg.StackRealizes block.input state` the swap arm needs.
  `state` is the runtime/target state at the entry.  This is the concrete instantiation
  the composite recursors require (per session-14: `realized` must be the source
  witness at composites, since the child `hEntry` is discharged from the extracted
  `StateRel`; abstract pass-through only survives at the leaves).

### Exact next-session recipe (item 3b threading — extraction closed, mirror + witness pinned)
1. **`RealizingBlockOwnerAt`** — mirror `InteractionBoundedOwnerPreservation.BlockOwnerAt`
   (`:42`) but yield `RealizingBoundedExecPreservesUnder … (blockBudget …) policy
   (realizedWitness cfg)` (define `realizedWitness cfg` as the pinned predicate above).
   Prove `.owner`/`.mono` projections (the `.bounded`/`.exec`/`.allEntriesRealized`
   projections on the family itself are already landed session 14).
2. **Per-construct `*_bounded_realizing`** (order `if`→`for`→`switch`→`call`; `if`/`for`
   share `jump_state_rel_of_rel`, `switch`/`call` share `jump_state_rel_of_pure`):
   `.bounded` = the existing `*_bounded`; `.allEntriesRealized` = `AllEntriesRealized.of_succ`
   with `hHere` from the entry's `realizedWitness` (supplies `StateRel` + `SourceFrameFits
   input` ⇒ feeds `openStep_*`/the extraction lemma), and `hNext` per first jump:
   extraction lemma ⇒ (`next`, child `StateRel`, child `SourceFrameFits`) ⇒ the
   child's realizing owner (`hBlockOwner : RealizingBlockOwnerAt`) at that `StateRel`
   gives the residual `AllEntriesRealized`; the boundary branch is killed by
   `policy regular _ = true` vs `hStop`.  Discharging `openStep_*`'s own hypotheses
   (`hBlocks`, `hFits`, `StateRel target`) at the composite entry comes from the
   entry's `realizedWitness` + the compile facts already in the `*_bounded` proofs.
3. **`bounded_succ_realizing`** (dispatch over `Stmt`, mirror `bounded_succ` `:2069`)
   → **`block_owner_realizing`** (same `Nat.strong_induction_on`, mirror `:2335`;
   likely one commit for the mutual anchor) → **`main_bounded_realizing`**
   (mirror `:3121`) exposing `AllEntriesRealized cfg policy (blockBudget …) cfg.entry
   target (realizedWitness cfg)`.
4. Mirror into `InteractionTruncationOwnerPreservation` → `main_prefix_forward_realizing`;
   then Steps B–D unchanged (`openRunNPrefix_peephole_congr_of_source` consumes the
   `AllEntriesRealized`, discharges `StackRealizes` via
   `stackRealizes_of_stateRel_of_*` + `openRunBody_swap_swap_congr`; swap the four OIC
   call sites `OpenInteractionComposition.lean:909/942`/`:1415/1561/1688`; add the
   `swap d :: swap d :: rest → rest` arm to `peepholeBody`; re-green the syntactic
   (b)-family + semantic congruences; `scripts/opt_harness.sh full`).

### Status handed to session 16
The item-3b **extraction** layer is CLOSED (two reusable lemmas cover all four
composites; both landed).  Remaining = the item-3b **threading** bulk: the
`*_bounded_realizing` recursors + `block_owner_realizing` mutual recursion +
`main_bounded_realizing`, mirroring `InteractionBoundedOwnerPreservation.lean`
theorem-for-theorem with the accumulator conjunct, then the truncation mirror and
Steps B–D.  Mirror target, `StopPolicy=stopJump` identity, and the source-witness
`realized` form are all pinned above.  `compile_correct` / `compile_correct_creation`
axioms unchanged `[propext, Classical.choice, Quot.sound]`; measured delta +0
(no arm shipped).

## Session-16 update (2026-07-17): item-3b threading — ALL FIVE leaf `*_bounded_realizing` + the mutual-recursion anchor (`realizedWitness` + `RealizingBlockOwnerAt`) + BOTH accumulator-threading step helpers (`allEntriesRealized_branch_step` / `_pure_step`) LANDED green, axiom-clean, in three commits. The composite `*_bounded_realizing` recursors + `block_owner_realizing` mutual recursion remain — but the accumulator core they turn on is now landed and the remaining gap is precisely the child-`FragmentContract` reconstruction + entry-witness construction (located below).

Session 16 executed the item-3b **threading** mandate at the bounded owner layer.
Everything landed in ONE new file `EvmCompiler/Structured/InteractionBoundedOwnerRealized.lean`
(wired into `EvmCompiler.Verification`), all **additive** — `peepholeBody`/public
spine UNTOUCHED ⇒ measured delta still definitionally **+0**.  `scripts/opt_harness.sh
check` = OK (43 public theorems, axioms `[propext, Classical.choice, Quot.sound]`
incl. `compile_correct` / `compile_correct_creation`, unchanged).

### Landed commits (branch `arena-opt`)
- **`96f54027`** — the FIVE leaf `*_bounded_realizing` lemmas
  (`code`/`terminal`/`brk`/`cont`/`leave`) in namespace
  `InteractionBoundedOwnerPreservation.OpenOutcome.Stmt`.  Each mirrors the existing
  green leaf `*_bounded` (its `.bounded` outcome conjunct is that theorem verbatim)
  and produces `RealizingBoundedExecPreservesUnder … (stmtBudget …) policy realized`.
  The `.allEntriesRealized` conjunct is discharged by the new helper
  `allEntriesRealized_of_first_jump_stops` (`:65`, folds `AllEntriesRealized.of_zero`
  + `.of_first_jump_stops` into `∀ fuel`) via `RealizingBoundedExecPreservesUnder.mk`,
  reusing the EXACT backward-simulation stops argument from the forward leaves in
  `InteractionOwnerRealized.lean` (`Rel.executes_right` on
  `openStep_{code,terminal,brk,cont,leave}_of_compileStmtFuel?` → `contract.stops`).
  `realized` is kept ABSTRACT with `hEntry : ∀ target, StateRel source tokens target →
  realized entry target`, exactly as the forward leaves — the composites instantiate
  it to `realizedWitness` and discharge `hEntry` from the extracted child `StateRel`.
- **`05ffa7ee`** — the mutual-recursion anchor definitions:
  - `realizedWitness cfg : Label → EVMState → Prop` (`:~285`) — the session-15 pinned
    source witness `∃ source tokens block, cfg.findBlock? label = some block ∧
    StateRel source tokens state ∧ SourceFrameFits block.input source.evm.stack.length`.
  - `RealizingBlockOwnerAt sourceFuel program entryShapes cfg generated` — the
    realizing counterpart of the bounded `BlockOwnerAt` (hypotheses identical),
    yielding `RealizingBoundedExecPreservesUnder … (blockBudget program
    blockSourceFuel block) policy (realizedWitness cfg)`.  Projections
    `.owner` (forgets the accumulator to the existing `BlockOwnerAt` via
    `RealizingBoundedExecPreservesUnder.bounded`) and `.mono`.
- **`cb9ee6d4`** — the two accumulator-threading step helpers (the CORE the composite
  recursors turn on), both `AllEntriesRealized.of_succ` packagers:
  - `allEntriesRealized_branch_step` (`:~430`) — `jumpi`-branch composites (`if`, and
    `for`'s loop-condition block, sharing `Condition.DoneRel`).  Consumes `hHere`, the
    branch `Rel` (from `openStep_if_of_compileStmtFuel?` / `openStep_condition`),
    `hRegularStops : ∀ state', policy falseLabel state' = true` (rules out the
    non-body branch under the non-stopping `hStop`), and `hBody` (the body branch's
    child `AllEntriesRealized` from the extracted `StateRel`/`SourceFrameFits`).
    Residual budget = `bodyBudget`, EXACTLY matching `stmtBudget_if_succ = 1 +
    blockBudget body`, so **no upward-monotone accumulator step is needed** (the
    session-14 concern is void at this budget).  Turns on `jump_state_rel_of_rel`.
  - `allEntriesRealized_pure_step` (`:~475`) — `pure`-jump composites (`switch`
    pop/test, `call`).  Turns on `jump_state_rel_of_pure`; single non-stopping jump,
    no branch to rule out.

### The remaining gap for `if_bounded_realizing` (and the other composites), precisely located
The composite `*_bounded_realizing` recursors are `RealizingBoundedExecPreservesUnder.mk
(if_bounded … (hBlockOwner.owner) …) (accumulator)` where the accumulator is
`allEntriesRealized_branch_step`/`_pure_step`.  Two obligations remain per composite
(both mechanical but non-trivial; each needs the construct-specific compiler facts):
1. **Entry witness `hHere : realizedWitness cfg entry target`.**  Needs
   `cfg.findBlock? entry = some block ∧ block.input = input` for the composite's
   OWN entry block, then `realizedWitness = ⟨source, tokens, block, hFind, hStateRel,
   contract.fits⟩` (`contract.fits : SourceFrameFits input source.evm.stack.length`,
   and `block.input = input`).  There is **no general** entry-block lemma — each
   construct builds its entry block inside its `components_of_compileStmtFuel?_X`
   (`if`: `openStep_if_of_compileStmtFuel?`'s internal `hFind` on `generated` with
   `input := input`, `InteractionBranchPreservation.lean:326`; NOT exposed by the
   lemma conclusion, so re-derive from `components_of_compileStmtFuel?_if` +
   `BlocksInProgram`).  Alternatively keep `hHere` a hypothesis `hEntry` (as the
   leaves do) and construct it once, centrally, in `block_owner_realizing` when it
   dispatches each block — likely the cleaner factoring (write a single
   `realizedWitness_of_entry` per construct, or a `BlocksInProgram`-based entry-block
   extractor).
2. **Body branch `hBody`.**  Inside `allEntriesRealized_branch_step`'s `hBody`
   (given `srcState state'`, `StateRel srcState tokens state'`, `SourceFrameFits
   bodyInput srcState.evm.stack.length`), invoke the child owner
   `(hBlockOwner : RealizingBlockOwnerAt sourceFuel …) (Nat.le_refl sourceFuel)
   hBodyCompile hBodyBlocks hBodyCalls hBodyWF hBodySafe hBodyCallsResolved hSupports
   hProcs hReturns' bodyContract` and project `.allEntriesRealized hStateRel
   (le_refl)`.  The `bodyContract : FragmentContract cfg bodyResult ctx (supply+1)
   (LabelSupply.label supply 0) regular bodyInput srcState tokens policy` and the
   compile facts (`hBodyCompile`, `hBodyBlocks`, `hBodyCalls`, `hReturns'`) are
   **exactly** the record `if_bounded` builds internally at
   `InteractionBoundedOwnerPreservation.lean:270-294` — but there they are threaded
   through `openRun_if_bounded_under_of_compileStmtFuel?`'s callback; in the separate
   `mk` accumulator they must be re-derived from `openStep_if_of_compileStmtFuel?`'s
   outputs (`bodyResult`, `hBody`-compile, `hRequire`, `hResult`, the branch `Rel`)
   plus `contract`/`hWF`/`hFrameSafe`/`hCalls` cases.  This is the ~90-line
   contract-reconstruction bulk, done once for `if` (template) then adapted for
   `switch`/`for`/`call`.
   - `hRegularStops` for the `if`/`for` false branch = `contract.boundary.fresh`
     (`RecursiveBoundary.fresh : ActivationFreshExcept cfg returns tokens policy
     supply regular`, `InteractionBoundaryPreservation.lean:533`) — the regular label
     is freshly allocated and policy-stopping, exactly the existing preservation's
     regular-fallthrough discharge.

### Exact next-session recipe (item 3b threading — leaves + anchor + accumulator core landed)
1. Write the entry-witness extractor (per construct, or a `BlocksInProgram`-based
   `realizedWitness_of_entry`), and factor whether `hHere` is reconstructed in each
   composite or centrally in `block_owner_realizing`.
2. `if_bounded_realizing`: `.bounded` = `if_bounded … hBlockOwner.owner …`;
   `.allEntriesRealized` via `mk` + `allEntriesRealized_branch_step` (rewrite
   `stmtBudget_if_succ` to `blockBudget body + 1`), reconstructing `bodyContract` +
   compile facts as `if_bounded` does (`:270-294`) and invoking the child
   `RealizingBlockOwnerAt.allEntriesRealized`.  `hRegularStops` from
   `contract.boundary.fresh`.  Commit.
3. `for_bounded_realizing` (reuse `allEntriesRealized_branch_step` on
   `openStep_condition`'s `Condition.DoneRel`; note the loop cycle re-enters — the
   `for` residual budget uses `loopBudget_succ`, check the `of_succ`/`of_le` glue for
   the cond→body→post→cond re-entry, likely needs the child owner at each phase),
   then `switch_bounded_realizing` / `call_bounded_realizing` (both
   `allEntriesRealized_pure_step` on `openStep_pop_jump`/`openStep_test` /
   `openStep_entry_of_compileStmtFuel?`).  Bank each green.
4. `bounded_succ_realizing` (dispatch over `Stmt`, mirror `bounded_succ` `:2069`) →
   `block_owner_realizing` (same `Nat.strong_induction_on sourceFuel`, mirror `:2335`;
   the mutual anchor — feeds each recursive call the strictly-smaller-fuel
   `RealizingBlockOwnerAt`) → `main_bounded_realizing` (mirror `:3121`).
5. Truncation mirror → `main_prefix_forward_realizing`; then Steps B–D unchanged.

### Status handed to session 17
Item-3b threading leaves + the mutual-recursion anchor + the accumulator-threading
core are CLOSED and banked green (3 commits).  Remaining = the composite
`*_bounded_realizing` recursors (each = `mk` of the existing `*_bounded` + the landed
step helper, gated on the per-construct child-`FragmentContract` reconstruction and
entry-witness extraction located above) → `bounded_succ_realizing` →
`block_owner_realizing` (mutual anchor) → `main_bounded_realizing`, then the
truncation mirror and Steps B–D.  `compile_correct` / `compile_correct_creation`
axioms unchanged `[propext, Classical.choice, Quot.sound]`; measured delta +0
(no arm shipped).

## Session-17 update (2026-07-17): the `if` composite recursor `if_bounded_realizing` LANDED green + a CORRECTED, reusable `allEntriesRealized_branch_step` (session-16's had an undischargeable unconditional false-branch stop). This is the composite TEMPLATE — it solves every core problem the other constructs share (returns threading, false-branch stopping, entry witness, body-`FragmentContract` reconstruction). Two green, axiom-clean commits; `switch`/`call`/`for` remain (each a distinct large reconstruction, `for` coupled to the mutual anchor). `scripts/opt_harness.sh check` = OK; `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still definitionally **+0**.

Session 17 executed the item-3b MANDATE (composite `*_bounded_realizing` recursors,
`if` first).  It landed the `if` composite and, in doing so, corrected the
accumulator step helper and pinned the exact obstruction for the other three
constructs.  All additive in `InteractionBoundedOwnerRealized.lean`.

### Landed commits (branch `arena-opt`)
- **`1876993e`** — `if_bounded_realizing`
  (`InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.if_bounded_realizing`).
  `.bounded` conjunct = the existing green `if_bounded` fed `hBlockOwner.owner`
  (the realizing owner's forgetful projection).  `.allEntriesRealized` conjunct =
  `AllEntriesRealized.of_succ` over the `if`-head's single `openStep`, with the
  body-`FragmentContract` reconstructed EXACTLY as `if_bounded` does internally
  (`InteractionBoundedOwnerPreservation.lean:270-294`) and the false/regular branch
  ruled out via the reconstructed regular-exit `Rel` + `contract.stops`
  (mirroring `openRun_if_under`'s false arm, `InteractionBranchPreservation.lean:499-519`).
  Budget `stmtBudget program (sourceFuel+1) (.if_ cond body) = 1 + blockBudget program
  sourceFuel body` (`stmtBudget_if_succ`), so the residual `of_succ` budget is exactly
  `blockBudget program sourceFuel body` and the child owner is invoked at
  `Nat.le_refl sourceFuel` — no monotone step.  Axioms `[propext, Classical.choice,
  Quot.sound]`.
- **`1813be7b`** — corrected reusable `allEntriesRealized_branch_step` +
  `if_bounded_realizing` refactored to call it.

### KEY FINDING: session-16's `allEntriesRealized_branch_step` was UNUSABLE (flaw + fix)
Session 16 landed `allEntriesRealized_branch_step` with an **unconditional**
false-branch stop obligation `hRegularStops : ∀ state', policy falseLabel state' = true`.
This is **not dischargeable**: the fragment's stop policy `policy` is arbitrary (a
theorem variable), and it halts at `regular` ONLY for frame-matching states — the
mechanism is `contract.stops` applied to a reconstructed `Rel result ctx regular
source.returns tokens (.regular afterCond) (.jump regular state')`
(`TargetStoppedBy` def: a `.jump` stops iff `policy label state = true`, established
only through that `Rel`, `InteractionControlPreservation.lean:1186`).  The corrected
helper therefore:
1. takes the branch relation **strengthened with returns** — `Rel (fun l r =>
   Condition.DoneRel … l r ∧ ConditionReturnsEq sourceReturns l)` (built via
   `Simulation.Interaction.Rel.strengthen_left hHeadRel (openRunCondition_returns
   cond source)`, exactly as `openRun_if_under` does) so BOTH branches recover
   `afterCond.returns = sourceReturns` (the fact the body contract's
   `boundary`/`stops`/`nonregular` fields require — they read `source.returns`);
2. takes a **conditional** false-stop obligation `hFalseStops : ∀ afterCond state',
   afterCond.returns = sourceReturns → StateRel afterCond tokens state' →
   SourceFrameFits restShape afterCond.evm.stack.length → policy falseLabel state' =
   true` (discharged from the extracted child StateRel/returns/fits);
3. takes `hBody` in the same extracted form.
The extraction (`Rel.executes_right` on the strengthened relation → `ExceptRel.ok` →
`ResultRel` destructure + `ConditionReturnsEq`) is inlined in the helper (it does NOT
reuse `jump_state_rel_of_rel`, which discards returns).  `for`'s loop-condition block
reuses `Condition.DoneRel`, so this helper is the shared jumpi-branch step for
`for_bounded_realizing`.

### The `if` reconstruction, reusable pattern for the other constructs
Every composite `*_bounded_realizing` is `RealizingBoundedExecPreservesUnder.mk
(<existing *_bounded> … hBlockOwner.owner …) (accumulator)`.  The accumulator's two
non-trivial pieces (both mechanical once the pattern is known, ~inlined in `if`):
1. **Entry witness `hHere : realizedWitness cfg entry target`.**  For `if`:
   `components_of_compileStmtFuel?_if hCompile` → build the entry `jumpi` block
   `entryBlock` (input := input) → `hFind : cfg.findBlock? entry = some entryBlock`
   via `hBlocks entryBlock (by simp [entryBlock, hResult])` → witness
   `⟨source, tokens, entryBlock, hFind, hStateRel, contract.fits⟩` (`entryBlock.input
   = input`, so `SourceFrameFits entryBlock.input _ = contract.fits`).
2. **Body `FragmentContract` + child owner.**  Reconstruct the `if_bounded`
   `:270-294` record with `hReturns := afterCond.returns = source.returns` (from the
   strengthened relation), then invoke `(hBlockOwner (Nat.le_refl sourceFuel)
   hBodyCompile hBodyBlocks hBodyCalls hBodyWF hBodySafe hBodyCallsResolved hSupports
   hProcs hBodyReturns bodyContract).allEntriesRealized hAfterCondRel (Nat.le_refl _)`.
   `hBodyBlocks`/`hBodyCalls` derived from `hResult` (the `components_…` result
   structure) + `hBlocks`/`hResultCalls`; `hBodyWF`/`hBodySafe`/`hBodyCallsResolved`
   via `cases hWF/hFrameSafe/hCalls` inside `have`s (so the whole hyps survive for the
   `if_bounded` call in the `.bounded` conjunct).

### Remaining (recipe for session 18)
- **`for_bounded_realizing`** — loop-condition block is a `jumpi` over the SAME
  `Condition.DoneRel bodyLabel endLabel tokens {…}` (`openStep_condition`,
  `InteractionLoopPreservation.lean:76`), so it reuses the corrected
  `allEntriesRealized_branch_step` for the FIRST jump.  BUT the `for` fragment's open
  run re-enters cond→body→post→cond across iterations (`loopBudget_succ = 1 +
  blockBudget body + blockBudget post + loopBudget …`), so `of_succ` on the entry
  covers only the first body-entry; the post block and re-entered cond are reachable
  too.  Realizing ALL of them needs the loop-level fuel recursion — i.e. `for` is
  coupled to `block_owner_realizing` (the child owner must realize body, then post
  re-enters the loop owner at smaller fuel).  Do `for` AS PART OF the mutual anchor,
  not standalone.
- **`switch_bounded_realizing` / `call_bounded_realizing`** — pure-jump composites
  (use `allEntriesRealized_pure_step`, landed session 16, which is fine — no false
  branch).  Obstruction is the ENTRY-WITNESS + child extraction for their specific
  block shapes, and for `call` the child is a PROCEDURE BODY: `openStep_entry_of_compileStmtFuel?`
  (`InteractionCallPreservation.lean:264`) needs `hSplit : splitArgs? proc.argc
  source.evm.stack = some (args, callerStack)` (invert from the deterministic pure
  jump) and the child owner must be invoked on the proc body with the pushed call
  frame — i.e. re-deriving `call_bounded`'s ~150-line ownership-callback machinery
  (`InteractionBoundedOwnerPreservation.lean:1385-1560+`).  `switch` threads through
  the entry `pop;jump` then N `jumpi` test blocks (a multi-step reachability to the
  matching case, not a single `of_succ`).  Both are larger than `if`; do them after
  (or alongside) the mutual anchor.
- Then `bounded_succ_realizing` (mirror `bounded_succ` `:2069`) →
  `block_owner_realizing` (`Nat.strong_induction_on sourceFuel`, mirror `:2335`) →
  `main_bounded_realizing` (`:3121`); truncation mirror → `main_prefix_forward_realizing`;
  Steps B–D.

### Status handed to session 18
The `if` composite recursor is CLOSED and banked green, and the shared jumpi-branch
step helper is corrected and reusable (fixes the session-16 flaw).  `if_bounded_realizing`
is the working TEMPLATE: entry-witness construction, returns threading, false-branch
stopping, and body-`FragmentContract` reconstruction are all demonstrated and reusable.
Remaining = `switch`/`call` (pure-jump, larger construct-specific reconstructions) and
`for` (coupled to the mutual anchor via loop re-entry) → `bounded_succ_realizing` →
`block_owner_realizing` → `main_bounded_realizing`, then truncation mirror + Steps B–D.
`compile_correct` / `compile_correct_creation` axioms unchanged `[propext,
Classical.choice, Quot.sound]`; measured delta +0 (no arm shipped).

## Session-18 update (2026-07-17): the `switch`/`call` composites do NOT close via the standalone `allEntriesRealized_pure_step` route — the obstruction is a strict BUDGET SLACK requiring an UPWARD-monotone accumulator step. Landed the exact missing lever green + axiom-clean (`ReachesOpenStepAt.of_runCompletes` / `AllEntriesRealized.of_runCompletes`, `EvmCompiler/TypedCfg/InteractionReachesCap.lean`, commit `e6702dee`), which the whole tower had deliberately left open. `switch`/`call` themselves remain: their `RunCompletes` discharge is coupled to the child fragment's bounded stopping (the mutual anchor), and `call` additionally has a stop-policy-refinement gap. `scripts/opt_harness.sh check` = OK (43 theorems, axioms unchanged); `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still **+0**.

Session 18 executed the item-3b MANDATE (`switch_bounded_realizing`,
`call_bounded_realizing` via `allEntriesRealized_pure_step`).  A full budget audit
of both constructs found the session-17 remaining-recipe for `switch`/`call`
**over-optimistic in the same way** session-17 found session-16's
`allEntriesRealized_branch_step` unusable: the `pure_step` route only closes when
the composite budget matches the child budget *exactly* (the `if` case).  It does
NOT for `switch`/`call`, and the reason — and its fix — is now landed and pinned
below.

### KEY FINDING: the `pure_step` route fails on strict budget slack (why `if` ≠ `switch`/`call`)
`if_bounded_realizing` (session 17) closes because
`stmtBudget (.if_ cond body) = 1 + blockBudget body` (`stmtBudget_if_succ`), the
head is exactly one `openStep`, so the `of_succ` residual budget is *precisely*
`blockBudget body` — the budget the child owner (`RealizingBlockOwnerAt` at
`Nat.le_refl sourceFuel`) provides.  Exact match ⇒ `allEntriesRealized_branch_step`
lands the accumulator with no fuel arithmetic.

`switch`/`call` carry **strict slack** (`InteractionStaticCost.lean`):
* `stmtBudget_switch_succ` `:138` = `1 + (switchBodyBudget + cases.length + 1)`,
  and `switchBodyBudget` `:70` is a `max` over case bodies.  The matched case is
  reached after the entry `pop;jump` (`InteractionSwitchPreservation.openStep_pop_jump`
  `:19`) plus `k` test blocks (`openStep_test` `:95`, each a single
  `.done (.ok (.jump …))` with a retained-scrutinee `StateRel`); the `of_succ`
  residual at the matched body is `switchBodyBudget + cases.length − k`, which is
  `≥ blockBudget matchedBody` with the inequality generally **strict**.
* `stmtBudget_call_succ` `:149` = `3 + procBodyBudget`, `procBodyBudget` `:82` a
  `max` over procs.  The proc body (`fragment.entry = ProcLabel.body name`) is
  reached after TWO pure jumps — the call-site block
  (`InteractionCallPreservation.openStep_entry_of_compileStmtFuel?` `:264`, whose
  `hSplit` is derivable from `contract.fits` + `argc ≤ sourceLength input`, cf.
  `InteractionTruncationOwnerPreservation.lean:457-466`) and the proc-entry adapter
  (`openStep_procEntry_of_adapter` `:336`) — leaving residual `1 + procBodyBudget`
  at `fragment.entry`, `≥ blockBudget proc.body`, generally **strict**.

Because `AllEntriesRealized` is *antitone* in fuel (`AllEntriesRealized.of_le`), a
larger-fuel realization is strictly STRONGER and cannot be recovered from the
child owner's `blockBudget`-level fact.  `RealizingBoundedExecPreservesUnder.mk`
requires the accumulator at *exactly* `stmtBudget` (the slack-containing budget),
so the composite MUST bridge the gap upward.  This is precisely the direction
`RealizingBoundedExecPreservesUnder.mono_budget`'s docstring flags as
"deliberately absent … exactly the extra reachability the composite threading must
establish."

### LANDED (green, axiom-clean): the upward lever — `EvmCompiler/TypedCfg/InteractionReachesCap.lean` (commit `e6702dee`)
The gap closes because the fragment run genuinely *completes* (stops at its
recursive boundary) within the child budget along every branch; past the stop,
extra fuel reaches NO new block entries.  Made precise, target-side and
`StateRel`-free:
* **`RunCompletes program stopJump B label state`** — the fuel-`B` whole-program
  runner (`openRunNResultWithStop`) reaches a proper `.stopped` result (never
  `.exhausted`, never an interaction error) on EVERY concrete answer branch.
* **`ReachesOpenStepAt.of_runCompletes`** — if the `B`-run completes, every block
  entry reached at ANY fuel `n` is already reached at fuel `B`.  Proof: induction
  on the fuel-`n` reach derivation, generalizing `B` + the completion hypothesis;
  `.start` trivial; at a `.step` non-stopping jump, completion forces `B ≥ 1`
  (fuel-0 = `.exhausted` ≠ `.stopped`), then `Simulation.Interaction.Executes.bind_ok`
  (`.lake/packages/evm-interaction/…/Interaction.lean:1140`) composes the head jump
  with any residual run to restrict whole-run completion to residual completion,
  and the IH caps the residual reachability.
* **`AllEntriesRealized.of_runCompletes`** — promotes a `B`-budget per-entry
  realization to any larger budget given `RunCompletes … B`.  This is the exact
  upward-monotone accumulator step `switch`/`call`/`for` need.
Axioms `[propext, Classical.choice, Quot.sound]`; wired into `EvmCompiler.Verification`.

### The remaining obstruction for `switch`/`call` (precisely located)
With the cap lemma in hand, `switch_bounded_realizing` reduces to: walk the entry
`pop;jump` + test chain with `allEntriesRealized_pure_step` (each hop realized via
`jump_state_rel_of_pure` + the test/`pop` block's retained `StateRel`), then at the
matched-case leaf promote the child owner's `blockBudget`-accumulator up to the
residual `stmtBudget` slack via `AllEntriesRealized.of_runCompletes`.  The ONE piece
that is NOT standalone is **discharging `RunCompletes` at each leaf**:
* `RunCompletes` demands the target run stops on EVERY branch.  The child
  fragment's `BoundedExecPreservesUnder` (available as `switch_bounded`/`call_bounded`'s
  `.bounded` conjunct) proves stopping only for branches matching a *successful
  source outcome*; the ERROR/divergent source branches are covered by the SEPARATE
  `RuntimeErrorBlockOwnerAt` + truncation owners.  Assembling `RunCompletes` from
  all three is exactly the coupled analysis that lives at the mutual anchor
  (`block_owner_realizing`, `bounded_succ`-style dispatch `:2069`/`:2335`).  So the
  `RunCompletes` discharge — and therefore `switch`/`call` — must be done AS PART
  of the mutual anchor, not standalone.  (This is the same coupling session-17
  flagged for `for`; the budget audit shows it applies to `switch`/`call` too.)
* **`call` additionally** has a stop-policy-refinement gap: its proc body runs
  under `InteractionCallPreservation.Call.bodyStopPolicy` (stops at `ProcLabel.exit`),
  whereas the composite's `AllEntriesRealized` uses the OUTER `policy` (does not stop
  at the exit — the run continues into the return-dispatch block and back to
  `regular`).  So `call`'s reachable-entry SET differs from the child owner's, and a
  policy-refinement reachability bridge (the `AllEntriesRealized` analogue of
  `ExecPreservesUnder.close_refined_follows`, `InteractionControlPreservation.lean`)
  is needed on top of the cap.  `switch`'s case bodies run under the SAME outer
  `policy` (stop at `regular`, like `if` — `switch_bounded` `:472-496`), so `switch`
  has NO policy gap; `switch` is strictly closer than `call`.

### Exact next-session recipe (session 19)
1. Prove a `RunCompletes` discharge at the mutual anchor: `RealizingBlockOwnerAt`
   (or a sibling) should additionally yield `RunCompletes cfg policy (blockBudget …)
   entry target` for every `StateRel`-related `target`, assembled from the bounded
   owner's stopping (success branches) + `RuntimeErrorBlockOwnerAt`/truncation
   (error branches).  This is the genuine coupled obligation.
2. `switch_bounded_realizing`: `.bounded` = existing `switch_bounded` fed
   `hBlockOwner.owner`; `.allEntriesRealized` = pop;jump + `cases.length` test-chain
   `allEntriesRealized_pure_step` hops (entry witnesses from `openStep_pop_jump`/
   `openStep_test` block shapes), then the matched-case leaf via the child owner's
   `blockBudget`-accumulator promoted through `AllEntriesRealized.of_runCompletes`
   (discharge `RunCompletes` from step 1).  Same outer `policy`, no refinement.
3. `call_bounded_realizing`: two `allEntriesRealized_pure_step` hops (call-site +
   adapter, `hSplit` from `contract.fits`), then the proc body — but FIRST bridge
   `bodyStopPolicy`-reachability to `policy`-reachability (the missing
   `AllEntriesRealized` refinement lemma), THEN promote via
   `AllEntriesRealized.of_runCompletes`.
4. `for_bounded_realizing` (loop re-entry) → `bounded_succ_realizing` →
   `block_owner_realizing` (mutual anchor, where step 1's `RunCompletes` discharge
   is produced by the same `Nat.strong_induction_on sourceFuel`) →
   `main_bounded_realizing`; truncation mirror → `main_prefix_forward_realizing`;
   Steps B–D.

### Status handed to session 19
The upward-monotone accumulator lever — the tower's long-standing "deliberately
absent" step — is CLOSED and banked green (`InteractionReachesCap.lean`, commit
`e6702dee`).  No `*_bounded_realizing` composite landed this session: the audit
showed `switch`/`call` are NOT standalone (their `RunCompletes` discharge couples to
the mutual anchor's success+error+truncation stopping analysis, and `call` also
needs a stop-policy-refinement reachability bridge), correcting session-17's
`pure_step`-suffices recipe.  `compile_correct` / `compile_correct_creation` axioms
unchanged `[propext, Classical.choice, Quot.sound]`; `scripts/opt_harness.sh check`
= OK (43 theorems); measured delta +0 (no arm shipped).

## Session-19 update (2026-07-17): the ENTIRE target-side substrate for the `RunCompletes` discharge (session-18 recipe step 1) + the `call` policy-refinement bridge (step 3) LANDED green + axiom-clean, in three commits (all additive to `EvmCompiler/TypedCfg/InteractionReachesCap.lean`, the cheap ~2 s module). What remains is exactly and only the SOURCE-COUPLED mutual anchor `block_owner_realizing` (which discharges these target-side lemmas' hypotheses from the fragment owners). `scripts/opt_harness.sh check` = OK (43 theorems, `compile_correct`/`compile_correct_creation` axioms unchanged `[propext, Classical.choice, Quot.sound]`); `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still **+0**.

Session 19 executed the item-3b MANDATE at the mutual anchor. A design pass found
that the recipe's step-1 (`RunCompletes` discharge) and step-3 (`call` policy
refinement) each decompose into (a) a fully **target-side, `StateRel`-free**
reusable lemma — landable NOW and cheaply — plus (b) a source-coupled discharge
that genuinely lives at `block_owner_realizing`.  This session closed **all** of
the (a) parts.  With them, `switch`/`call`/`for` composite recursors become
mechanical once the anchor supplies the coupled facts; the anchor is now the sole
remaining obstruction (as sessions 15–18 progressively localized).

### Landed commits (branch `arena-opt`, all in `InteractionReachesCap.lean`)
- **`8f5d29aa`** — `RunCompletes.succ` + `RunCompletes.of_head_stops`.  The
  branch-by-branch **assembler** for `RunCompletes` (recipe step 1).
  `RunCompletes.succ` reduces `RunCompletes … (fuel+1) label state` to
  (i) `hNoError`: the head `openStep` never raises an interaction error on any
  answer branch, and (ii) `hStops`: after any head jump to a *non-stopping*
  `(next,state')`, `RunCompletes … fuel next state'`.  Every other head outcome
  (stopping jump / fallthrough / returnDispatch / halt / invalid) settles the run
  immediately via `afterOpenStepResultWithStop`'s `pure (.stopped …)` leaf, so it
  needs no hypothesis.  Proof = `openRunNResultWithStop_succ_eq_bind` +
  `Executes.bind_cases`.  `of_head_stops` is the single-block leaf shape (all jumps
  stop).  **Discharge of `hNoError`/`hStops` is the coupled work at the anchor.**
- **`30a1f772`** — `RunCompletes.add_right` + `RunCompletes.of_le`.  `RunCompletes`
  is monotone UPWARD in fuel (via `openRunNResultWithStop_add`: the firstFuel run
  is `.stopped` on every branch, so the continuation is the trivial pure-stopped
  leaf).  Absorbs the strict `switch`/`call` **budget slack** for `RunCompletes`
  exactly as `AllEntriesRealized.of_runCompletes` (session 18) does for the
  accumulator: the anchor supplies each child's `RunCompletes` at that child's own
  budget; these promote it to the composite's larger residual before feeding
  `RunCompletes.succ`.
- **`a69acd53`** — `ReachesOpenStepAt.refined_decomp` + `AllEntriesRealized.of_refined`.
  The **`call` policy-refinement bridge** (recipe step 3 / the session-18 `call`
  gap).  `refined_decomp`: reachability under a looser policy `outer` factors
  through a tighter `inner` — every `outer`-reached entry is either `inner`-reached
  at the same fuel, OR reached only after CROSSING an `inner`-boundary that `outer`
  steps through (a jump out of an `inner`-reachable `(crossLabel,crossState)` into
  `(next,state')` with `inner next state' = true ∧ outer next state' = false`, then
  `outer`-reachable from `(next,state')`).  No `outer`/`inner` relationship needed;
  pure structural induction on the `outer` derivation.  `of_refined` promotes a
  tighter-policy realization to the looser one given each crossing continuation is
  realized.  For `call`: `inner = bodyStopPolicy = pushStopJump … policy` (stops at
  `ProcLabel.exit`), `outer = policy`; the ONLY `inner`-reachable crossing is the
  exit, so the `hTail` obligation is confined to the return-dispatch continuation.

All three: axioms `[propext, Classical.choice, Quot.sound]`; wired via the existing
`InteractionReachesCap` import in `EvmCompiler.Verification`.  Together with
session-18's `of_runCompletes`, the target-side toolkit for the RunCompletes
discharge + switch/call/for composite promotion is now COMPLETE.

### The sole remaining obstruction: the source-coupled discharge at `block_owner_realizing`
Every landed lemma above reduces the composites to hypotheses that are ALL
discharged at the mutual anchor from the existing fragment owners:
1. **`hNoError` (openStep never errors at a realized block entry).**  The fragment
   at a block reached under a `StateRel`/`SourceFrameFits` witness (`realizedWitness`)
   executes its block cleanly on every answer branch — i.e. `openStep cfg label
   state` never `Executes … (.error e)`.  This is NOT a standalone target fact
   (an arbitrary block can error); it is the *forward totality* of a realized
   block, and must be produced from the source coupling.  Candidate sources: the
   forward preservation `ForwardPreservesUnder`/`ForwardRel Truncated` already in the
   tower, and/or the block-execution facts feeding `BoundedExecPreservesUnder`.
   The precise obligation: at each entry reached along the composite run,
   reconstruct the child `StateRel` (already done in `if_bounded_realizing`'s
   accumulator via `jump_state_rel_of_pure`/`_of_rel`) and use it to rule out the
   error branch of `Executes.bind_cases` on `openStep`.
2. **Child `RunCompletes` at the leaf** (`RunCompletes.succ`'s recursive premise).
   Assembled from the child fragment's `.bounded` stopping (success branches,
   `BoundedExecPreservesUnder`) + `RuntimeErrorBlockOwnerAt` (error branches) +
   truncation, proving the child target run reaches `.stopped` on EVERY branch.
   This is the "success+error+truncation stopping" coupling session 18 flagged; it
   is the genuine multi-branch analysis at the anchor.  `RunCompletes.add_right`
   then lifts it across the composite's budget slack; `of_runCompletes` promotes the
   child's `blockBudget`-accumulator to `stmtBudget`.
3. **`hTail` for `call`** (`of_refined`'s crossing hypothesis).  The return-dispatch
   continuation from `ProcLabel.exit` back to `regular` is realized — supplied by
   the OUTER fragment's `block_owner_realizing` on the post-return block sequence.

### Exact next-session recipe (session 20)
1. **Anchor a `RunCompletes` discharge**: strengthen `RealizingBlockOwnerAt` (or add
   a sibling `CompletingBlockOwnerAt`) to additionally yield, for every
   `StateRel`-related `target`, `RunCompletes cfg policy (blockBudget …) entry
   target`.  Produce it by the SAME `Nat.strong_induction_on sourceFuel` as
   `block_owner` (`:2335`), branch-by-branch via the landed `RunCompletes.succ`:
   discharge `hNoError` from the realized block's forward totality (obligation 1
   above — locate/extract the cleanest source: check
   `InteractionPreservation`/`ForwardPreservesUnder` and the block-run facts behind
   `BoundedExecPreservesUnder`), and the recursive child premise from
   `switch_bounded`/`call_bounded`'s `.bounded` + `RuntimeErrorBlockOwnerAt`
   (`runtime_error_bounded_succ` `:2141` is the mirror) + truncation, then
   `add_right` for the slack.
2. `switch_bounded_realizing`: `.bounded` = existing `switch_bounded` fed
   `hBlockOwner.owner`; `.allEntriesRealized` = the pop;jump + `cases.length` test
   chain via the LANDED `allEntriesRealized_pure_step` (session 16) hops, then at the
   matched-case leaf promote the child owner's `blockBudget`-accumulator through
   `AllEntriesRealized.of_runCompletes` (discharge `RunCompletes` from step 1).  Same
   outer `policy`, NO refinement.  Entry witnesses from `openStep_pop_jump`/
   `openStep_test` block shapes (`InteractionSwitchPreservation.lean:19/95`).
3. `call_bounded_realizing`: two `allEntriesRealized_pure_step` hops (call-site +
   proc-entry adapter, `hSplit` from `contract.fits`,
   `InteractionCallPreservation.lean:264/336`), then the proc body under
   `bodyStopPolicy`; bridge to outer `policy` with the LANDED
   `AllEntriesRealized.of_refined` (`hTail` = outer owner on the return-dispatch
   tail, obligation 3), and promote via `of_runCompletes`.
4. `for_bounded_realizing` (loop re-entry; reuse the corrected
   `allEntriesRealized_branch_step` on `openStep_condition`'s `Condition.DoneRel`,
   `InteractionLoopPreservation.lean:76`; loop body/post re-enter the loop owner at
   smaller fuel — do inside the anchor) → `bounded_succ_realizing` (dispatch over
   `Stmt`, mirror `bounded_succ` `:2069`) → `block_owner_realizing`
   (`Nat.strong_induction_on sourceFuel`, mirror `block_owner` `:2335`; the mutual
   anchor — feeds each recursive call the strictly-smaller-fuel
   `RealizingBlockOwnerAt` AND the step-1 `RunCompletes` discharge) →
   `main_bounded_realizing` (mirror `:3121`); truncation mirror →
   `main_prefix_forward_realizing`; then Steps B–D (add the swap arm to
   `peepholeBody`, re-green the syntactic (b)-family, ship the measured delta).

### Status handed to session 20
The complete target-side substrate for the `RunCompletes` discharge (`succ` /
`of_head_stops` / `add_right` / `of_le`, atop session-18's `of_runCompletes`) AND
the `call` policy-refinement bridge (`refined_decomp` / `of_refined`) are CLOSED
and banked green (3 commits: `8f5d29aa`, `30a1f772`, `a69acd53`).  These reduce
`switch`/`call`/`for` and the anchor to THREE source-coupled discharges (openStep
forward totality `hNoError`; child multi-branch `RunCompletes`; `call`'s
return-dispatch `hTail`), all produced by the same
`Nat.strong_induction_on sourceFuel` as `block_owner`.  Building the mutual anchor
`block_owner_realizing` (with the RunCompletes discharge threaded through it) is the
sole remaining obstruction — a large but now fully-scoped construction with every
target-side tool it needs in hand.  `compile_correct` / `compile_correct_creation`
axioms unchanged `[propext, Classical.choice, Quot.sound]`; measured delta +0
(no arm shipped).

## Session-20 update (2026-07-17): the anchor's fuel-0 base case + the uniform entry-witness supplier LANDED green + axiom-clean; the `hNoError` obligation (1) precisely re-scoped as a source-block *interpreter-totality* theorem (the real remaining bulk)

Session 20 attacked the mutual anchor `block_owner_realizing` per the session-19
recipe.  Two green, axiom-clean lemmas landed (one commit, `489fe72b`, additive to
`EvmCompiler/Structured/InteractionBoundedOwnerRealized.lean`); a full-tower design
pass pinned down exactly where the remaining knot lives, and corrected an
over-optimistic reading of the session-19 `RunCompletes` obligations.
`scripts/opt_harness.sh check` = OK (43 public theorems; `compile_correct` /
`compile_correct_creation` axioms unchanged `[propext, Classical.choice,
Quot.sound]`); `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still **+0**.

### Landed commit (`489fe72b`, both in `InteractionBoundedOwnerRealized.lean`)
- **`realizedWitness_of_stateRel`** (`[propext, Quot.sound]`) — the **uniform
  entry-witness supplier**.  From a fragment's `LabelShape cfg entry input` (the
  ambient cfg block at `entry` expects `input`) + `StateRel source tokens target` +
  the contract's `SourceFrameFits input source.evm.stack.length`, produces
  `realizedWitness cfg entry target`.  `LabelShape` is obtained generically from any
  compile fact via `TypedCfgPreservation.LabelShape.of_compileStmtFuel?`, so this is
  the reusable `hHere`/`hEntry` supplier at every leaf, composite head, and the
  anchor base case — it packages, once and uniformly for every `Stmt` shape, the
  hand-built `⟨source, tokens, entryBlock, hFind, hStateRel, contract.fits⟩` term
  that `if_bounded_realizing` (session 17) reconstructs inline.  (Additive; the
  existing `if_bounded_realizing` was NOT modified — frozen-adjacent green tower
  stays green.)
- **`Stmt.bounded_zero_realizing`** (`[propext, Classical.choice, Quot.sound]`) —
  the **fuel-0 base arm of the mutual anchor** (mirrors `bounded_zero`
  `InteractionBoundedOwnerPreservation.lean:2228`, the arm `block_owner` dispatches
  to when its inner block fuel bottoms out, `:2481`).  KEY simplification found: at
  source level 0, every *composite* statement carries
  `stmtBudget program 0 (.if_/.switch/.for_/.call) = 0`
  (`levelCost program 0 |>.stmt` sends all four composites to `0`,
  `InteractionStaticCost.lean:24`), so the target-side accumulator collapses via
  `AllEntriesRealized.of_zero` to the single entry witness — discharged uniformly by
  `realizedWitness_of_stateRel` — while the `.bounded` leg is the existing green
  `bounded_zero` (whose source run is empty at fuel 0).  The five *leaf* statements
  carry budget 1 and are handled by the already-landed leaf `*_bounded_realizing`
  recursors (uniform in `sourceFuel`), fed the same uniform entry witness.  So the
  base case needs **no** RunCompletes and **no** source-coupled totality — it is
  fully closed.

### The corrected frontier: obligation (1) `hNoError` IS the bulk, and it is a *source-block interpreter-totality* theorem (not a relation-vacuity lemma)
A full read of the head relations settles what obligations (1)/(2) actually require,
and corrects the session-19 phrasings:

- The leaf/head relation `openStep_code_of_compileStmtFuel?`
  (`InteractionControlPreservation.lean:5127`, and the `if`/`switch`/`call` analogues)
  relates the source run to `openStep` under a `doneRel` that maps **target
  `.error` ↔ source `.error`** *bijectively* (lines 5192–5203: `sourceError`/
  `targetError` ↦ `ExceptRel.error`; mixed ok/error ↦ `cases hOriginal`, impossible).
  Therefore `hNoError` (`RunCompletes.succ`/`of_head_stops`, target head `openStep`
  never `Executes … (.error e)`) is **equivalent** to the *source* block/code run
  never raising an interaction `.error` on that answer branch.  It is NOT a
  vacuously-dischargeable "the relation never allows a target error" fact.
- Consequently `hNoError` reduces to: **a realized (well-typed, frame-fitting)
  compiled block's `openStep` produces an `.ok` `Outcome` on every answer branch**
  (a genuine EVM `revert`/`invalid` is an `.ok (.halt …)`/`.ok (.invalid …)`
  *outcome*, settled by `afterOpenStepResultWithStop` as `.ok (.stopped …)` — NOT an
  interaction `.error`; the interaction `.error` is reserved for `Instr.openRunState`
  raising an `EVMException`, i.e. stack underflow / structural failure, which
  `SourceFrameFits` + `WellTyped` rule out).  This is an *interpreter-totality*
  theorem about `Instr.openRunState` over a well-typed block under the realizing
  witness — the real multi-hundred-line source-coupled content.  Grep-confirmed
  there is no standalone "well-typed block openStep never errors under `StateRel`"
  lemma in the tower today; `openStep_code_of_compileStmtFuel?` gives the *relation*
  but leaves the source no-error side open.
- This resolves the apparent contradiction in session-19 obligation (2): the child
  `RunCompletes` (strict: every branch reaches `.ok (.stopped …)`) IS true precisely
  because, once `hNoError` holds at every realized entry, the only `.ok` outcomes are
  `jump`/`fallthrough`/`returnDispatch`/`halt`/`invalid`, all of which
  `afterOpenStepResultWithStop` settles to `.ok (.stopped …)` (a `revert` halts to
  `.stopped`, it does not error).  So obligations (1) and (2) collapse to the SAME
  interpreter-totality fact plus the child owner's stopping — there is no separate
  "error-branch stopping" to prove.

### Exact next-session recipe (session 21)
1. **Land the interpreter-totality lemma (obligation 1, the bulk).** State and prove
   `openStep_ok_of_stateRel` (working name): for a compiled block `generated` in
   `cfg` with `WellTyped`/`SourceFrameFits input source.evm.stack.length` and
   `StateRel source tokens target`, every `Executes (openStep cfg entry target)
   transcript r` has `r = .ok outcome` (never `.error`).  Route: it is the totality
   half of `openStep_code_of_compileStmtFuel?`'s `Rel` — prove the source
   `Code.openRun`/`Block.openRun` never raises an interaction `.error` under the
   frame-fit (stack ops don't underflow; reverts are `.halt` outcomes), then transfer
   across the `Rel` via the error↔error bijection.  Check
   `InteractionPreservation.Code.openRun_toCfg` / the block-run facts behind
   `BoundedExecPreservesUnder`, and `runState`/`runPops` length facts in
   `Preservation.lean` for the underflow-freeness.
2. With (1): `RunCompletes` at every realized leaf via `RunCompletes.of_head_stops`
   (`hNoError` from (1); `hAllStop` = the SAME first-jump-stops fact the landed leaf
   `*_bounded_realizing` already prove, `InteractionBoundedOwnerRealized.lean:105`).
3. `switch_bounded_realizing` / `call_bounded_realizing` / `for_bounded_realizing`:
   mechanical per the session-19 recipe — child accumulator at `blockBudget` from
   `hBlockOwner`, child `RunCompletes` at `blockBudget` from (2), promote to
   `stmtBudget` via `AllEntriesRealized.of_runCompletes` (`InteractionReachesCap.lean:322`);
   `call` bridges the stop-policy refinement via `AllEntriesRealized.of_refined`
   (`:411`), `hTail` from the outer owner on the return-dispatch tail; entry witnesses
   now via the landed `realizedWitness_of_stateRel`.
4. `bounded_succ_realizing` (dispatch over `Stmt`, mirror `bounded_succ` `:2069`) —
   now total: leaves + `if` (landed) + switch/call/for (step 3) + the fuel-0 arm is
   `bounded_zero_realizing` (LANDED).
5. `block_owner_realizing` (`Nat.strong_induction_on sourceFuel`, mirror `block_owner`
   `:2335`; feed each recursive call the smaller-fuel `RealizingBlockOwnerAt` and the
   step-1 totality) → `main_bounded_realizing` (mirror `:3121`) → truncation mirror →
   `main_prefix_forward_realizing`; then Steps B–D (add the swap arm to `peepholeBody`,
   re-green the syntactic (b)-family, ship the measured delta).

### Status handed to session 21
The anchor's fuel-0 base case (`bounded_zero_realizing`) and the uniform
entry-witness supplier (`realizedWitness_of_stateRel`) are CLOSED and banked green
(commit `489fe72b`).  The `succ`-fuel arm reduces — via the corrected analysis above
— to ONE genuinely new source-coupled theorem: **`openStep` interpreter-totality at
a realized entry** (obligation 1), which subsumes obligation 2 (child `RunCompletes`
is then immediate) and is orthogonal to obligation 3 (`call` `hTail`, already served
by the landed `of_refined`).  Everything downstream of that lemma is mechanical
composition with tools already in hand.  `compile_correct` /
`compile_correct_creation` axioms unchanged `[propext, Classical.choice,
Quot.sound]`; measured delta +0 (no arm shipped).

## Session-21 update (2026-07-17): session-20's "real remaining bulk" (`hNoError` / `openStep` interpreter-totality) is ELIMINATED from the promotion path by weakening `RunCompletes`→`RunSettles`; the lever landed green + axiom-clean

Session 21 attacked the session-20 mandate (prove `openStep_ok_of_stateRel`, the
`hNoError` interpreter-totality theorem).  A close reading of exactly *how* the
completion witness is consumed found that theorem is **not needed at all** for the
composite budget-slack promotion — it was an over-specification introduced by
session 18's `RunCompletes`.  The genuinely-needed fact is strictly weaker and
carries no source coupling.  Landed as `EvmCompiler/TypedCfg/InteractionSettlesCap.lean`
(commit `18c45ef2`, additive sibling of `InteractionReachesCap.lean`, ~2 s module).
`scripts/opt_harness.sh check` = OK; `peepholeBody`/public spine UNTOUCHED ⇒ measured
delta still **+0**.

### KEY FINDING: the upward cap only ever uses "never `.exhausted`", never "reaches `.stopped`"/"no error"
The sole consumer of the completion witness is `ReachesOpenStepAt.of_runCompletes`
(→ `AllEntriesRealized.of_runCompletes`), the upward-monotone accumulator promotion
that `switch`/`call`/`for` need for their budget slack.  Reading its proof
(`InteractionReachesCap.lean:268`): the witness `RunCompletes … B` is used in
exactly two spots, **both to rule out `.exhausted`**:
* the `B = 0` case derives a contradiction from the fuel-`0` runner yielding
  `.ok (.exhausted …)`;
* the `.step` case restricts whole-run completion to residual-run completion — and
  only needs the residual not to exhaust.

The `.stopped`-shape / no-`.error` strength of `RunCompletes` is **dead weight**.
Session-18's `RunCompletes` (`reaches .ok (.stopped …)` on every branch, hence
never `.error`) is therefore strictly stronger than the cap requires, and its
`.succ` constructor's `hNoError` premise — session-20's "real remaining bulk",
the `openStep` interpreter-totality obligation — exists only to serve that unused
strength.

### THE UNSOUNDNESS `hNoError` WOULD HAVE HIT (why the weaker witness is also the *correct* one)
`hNoError` ("a realized block's `openStep` never `Executes … (.error e)`") is in fact
**false in general**: `Assembly.InteractionSemantics.callStep`/`createStep`
(`EvmCompiler/Assembly/InteractionSemantics.lean:203-235`) raise
`.done (.error .StaticModeViolation)` for a state-modifying CALL/CREATE issued in
static mode, and `.done (.error .StackUnderflow)` — genuine interaction errors that
`WellTyped` + `SourceFrameFits` do **not** rule out (static-mode violation is a
*runtime* condition, not a shape condition).  A block that CALLs with value while
in static mode has an answer branch on which `openStep` errors.  So the session-20
plan to prove `openStep_ok_of_stateRel` outright would not have closed — the target
genuinely can error.  (This is consistent with the error↔error bijection in
`openStep_code_of_compileStmtFuel?`'s `doneRel`, `InteractionControlPreservation.lean:5192-5203`:
on those branches the SOURCE errors identically, so peephole preservation still
holds — both sides error.)  A branch that errors reaches *fewer* block entries, so
it never threatens the per-entry realization accumulator; demanding it not error was
the wrong requirement.

### LANDED (green, axiom-clean `[propext, Classical.choice, Quot.sound]`): `EvmCompiler/TypedCfg/InteractionSettlesCap.lean` (commit `18c45ef2`)
* **`RunSettles program stopJump fuel label state`** — the fuel-bounded whole-program
  runner never yields `.ok (.exhausted …)` on any answer branch (an interaction
  `.error` is *allowed*).  Strictly weaker than `RunCompletes`.
* **`RunSettles.succ`** — the recursion constructor, **with NO `hNoError`**: only
  `hStops` (after any non-stopping head jump, the residual `fuel`-run settles).  An
  erroring head branch makes the whole run `.error`, trivially not `.exhausted`; every
  stopping/non-jump head outcome settles at `.ok (.stopped …)`.  This is the exact
  spot where session-20's obligation evaporates.
* **`RunSettles.of_head_stops`** — leaf constructor, only `hAllStop` (every jump lands
  on a stopping boundary — the same fact the leaf `*_bounded_realizing` already prove
  via `contract.stops`).  No `hNoError`.
* **`RunSettles.add_right` / `.of_le`** — upward fuel monotonicity (absorbs the
  `switch`/`call` budget slack; `RunResult` is `exhausted | stopped`, so
  never-exhausted ⇒ stopped ⇒ the continuation is the pure `.stopped (…+restFuel)` leaf).
* **`RunSettles.of_runCompletes`** — any already-discharged `RunCompletes` (e.g. an
  `if`-leaf) feeds the `RunSettles` cap unchanged.
* **`ReachesOpenStepAt.of_runSettles`** — the upward reachability cap, verbatim the
  `of_runCompletes` proof with the `.exhausted` obstructions discharged from
  `RunSettles`.
* **`AllEntriesRealized.of_runSettles`** — the `hNoError`-free replacement for
  `AllEntriesRealized.of_runCompletes`: promote the child owner's `blockBudget`-level
  accumulator up to the composite's `stmtBudget` using only that the child run does
  not *exhaust* its budget.

### The corrected frontier (materially weaker than session 20's)
`block_owner_realizing` (the mutual anchor) still has to *supply* the composites'
`RunSettles blockBudget childLabel childState` — but this is now a **non-exhaustion**
(fuel-sufficiency) fact, NOT the interpreter-totality no-error theorem:
* **Success branches** (source `Executes` to `.ok sourceOutcome`): the child
  `BoundedExecPreservesUnder` (`InteractionControlPreservation.lean:1140`, the
  `.bounded` conjunct of `RealizingBoundedExecPreservesUnder`) already gives a target
  `Executes … (.ok (.stopped remaining targetOutcome))` at some `targetFuel ≤ budget`;
  promote to non-exhaustion at exactly `budget` via `RunSettles.of_le`-style
  monotonicity.  (Needs the per-transcript `.stopped` fact re-quantified into the
  `RunSettles` ∀-form — a mechanical repackaging.)
* **Error branches** (source `Executes` to `.error`): via the error↔error bijection
  in the head `doneRel`, the target `openStep` errors too, so the whole target run is
  `.error` — trivially not `.exhausted`.  No totality needed.
The remaining anchor work is thus the same success+error branch split sessions 18/19
flagged, but discharging **non-exhaustion** instead of **no-error** — qualitatively
easier, and with the unsound `hNoError` obligation removed.

### Exact next-session recipe (session 22)
1. **Bridge lemma** (self-contained, landable before the anchor):
   `RunSettles cfg policy budget entry target` from
   `BoundedExecPreservesUnder result cfg entry ctx regular source tokens sourceRun budget policy`
   + the head forward `Rel` (`openStep_*_of_compileStmtFuel?`) at the entry, for every
   `StateRel`-related `target`.  Success branches: `BoundedExec` → `.stopped ≤ budget`
   → `of_le`.  Error branches: `Rel.executes_right` + the error↔error `doneRel` ⇒
   target result is `.error` (not `.exhausted`).  Requires care to cover EVERY target
   `Executes` branch (not just those arising from a source execution) — use the source
   fuel-safety `InteractionFuelSafety.Code.openRun` (`AllDone NotOutOfFuel`) +
   `Rel.executes_right` to get a source execution for each target transcript, then the
   `doneRel` classification.
2. With (1) and `AllEntriesRealized.of_runSettles`, `switch_bounded_realizing` /
   `call_bounded_realizing` / `for_bounded_realizing` are mechanical per the
   session-19/20 recipe — child accumulator at `blockBudget` from `hBlockOwner`, child
   `RunSettles` at `blockBudget` from (1), promote to `stmtBudget` via
   `AllEntriesRealized.of_runSettles`; `call` bridges the stop-policy refinement via
   the LANDED `AllEntriesRealized.of_refined`; entry witnesses via the LANDED
   `realizedWitness_of_stateRel`.
3. `bounded_succ_realizing` (dispatch over `Stmt`, mirror `bounded_succ` `:2069`;
   now total: leaves + `if` (landed) + switch/call/for (step 2) + fuel-0 arm is the
   LANDED `bounded_zero_realizing`) → `block_owner_realizing`
   (`Nat.strong_induction_on sourceFuel`, mirror `block_owner` `:2335`) →
   `main_bounded_realizing` (`:3121`) → truncation mirror →
   `main_prefix_forward_realizing`; then Steps B–D (add the swap arm to `peepholeBody`,
   re-green the syntactic (b)-family, ship the measured delta).

### Status handed to session 22
The single obstruction session 20 identified as the sole remaining source-coupled
bulk (`openStep` interpreter-totality / `hNoError`) is **removed** — it was serving an
unused strength of `RunCompletes`, and is moreover *false in general*
(`StaticModeViolation`).  The `hNoError`-free promotion lever `RunSettles` (+ cap +
accumulator promotion) is CLOSED and banked green (commit `18c45ef2`).  The composites
now need only child-run **non-exhaustion** at budget, dischargeable from the existing
`BoundedExecPreservesUnder` (success) + head error-bijection (error) — the step-1
bridge lemma.  `compile_correct` / `compile_correct_creation` axioms unchanged
`[propext, Classical.choice, Quot.sound]`; measured delta +0 (no arm shipped).

## Session-22 update (2026-07-17): `RunSettles` bridge CORE landed green (`of_cover` + upward stop/error stability); the composite discharge is BLOCKED by a genuine source-truncation obstruction — `RunSettles`/`AllEntriesRealized` at the slack-bearing residual budget is FALSE on `OutOfFuel` branches

Session 22 executed the session-21 step-1 recipe (the `RunSettles` bridge lemma).
The reusable, `StateRel`-free target-side CORE landed green + axiom-clean; a full
trace of the discharge then found that the session-21 success+error branch analysis
is **incomplete** — it silently omits the SOURCE-TRUNCATION (`.error OutOfFuel`)
branches, on which the target run genuinely reaches `.ok (.exhausted …)` and the
composite's residual-budget accumulator is genuinely FALSE.  No composite arm was
added (it would be red/sorry).  `scripts/opt_harness.sh check` = **OK (43 public
theorems, axioms ⊆ [propext, Classical.choice, Quot.sound])**; `compile_correct` /
`compile_correct_creation` unchanged; `peepholeBody`/public spine UNTOUCHED ⇒
measured delta still **+0**.

### LANDED (green, axiom-clean `[propext, Classical.choice, Quot.sound]`): `EvmCompiler/TypedCfg/InteractionSettlesBridge.lean` (commit `316f22d5`, wired into `EvmCompiler.Verification`)
The target-side, `StateRel`-free core that turns a per-branch classification of a
fuel-bounded run into `RunSettles`:
* **`executes_stopped_add_right`** / **`executes_stopped_of_le`** — a `.ok (.stopped
  remaining outcome)` leaf reached at fuel `m` persists (padded remaining) at every
  `n ≥ m` along the SAME transcript.  Proof: `openRunNResultWithStop_add` +
  `Executes.bind_ok` + the `continueOpenRunNResultWithStop … (.stopped …)` pure leaf.
* **`executes_error_add_right`** / **`executes_error_of_le`** — an interaction
  `.error err` leaf reached at fuel `m` persists verbatim at every `n ≥ m` (a
  `.done (.error …)` is absorbing under `bind`; `Executes.bind_error`).
* **`RunSettles.of_cover`** — *the reduction*: `RunSettles program stopJump budget
  label state` from the hypothesis that EVERY terminal branch `(transcript, result)`
  of the `budget`-run is *covered* — its exact transcript executes, at some `m ≤
  budget`, to either a `.ok (.stopped …)` or a `.error …`.  Each budget-branch's
  covering smaller-fuel leaf is promoted to `budget` (the two stability lemmas) and
  pinned against the budget-branch's `result` by the FROZEN determinism lemma
  `Solidus.OpenRunContainment.executes_unique` (unique terminal outcome per fixed
  transcript).  A `.stopped`/`.error` result is not `.ok (.exhausted …)`.

`of_cover` is exactly the right shape: the child `BoundedExecPreservesUnder`
(success) supplies the `.stopped` cover, `BoundedRuntimeErrorExecPreservesUnder`
(runtime error) supplies the `.error` cover.  It is correct and unconditional.

### THE OBSTRUCTION session 21 missed: `of_cover`'s hypothesis is UNDISCHARGEABLE on `OutOfFuel` branches — and there it is not just hard but FALSE
Discharging `hCover` quantifies over TARGET branches `(transcript, result)` of the
`budget`-run and must classify each.  Two independent problems, both centered on the
source-truncation (`.error OutOfFuel`, `Structured/InteractionControlPreservation.lean:1032`)
branches that `BoundedTruncationExecPreservesUnder` (`:1035`) handles with `Follows`
(a prefix), NOT a `.done`:

1. **No backward classifier exists.**  `hCover` is stated per TARGET transcript;
   `BoundedExec`/`BoundedRuntimeError` are FORWARD (indexed by SOURCE `Executes`).
   Turning a target branch into a source branch needs `Rel.executes_right`
   (`InteractionEntryRealizedForward.lean:58`), which requires a FULL
   `Simulation.Interaction.Rel doneRel sourceRun (openRunNResultWithStop … budget …)`.
   The fragments establish only a `ForwardRel Truncated …` (`ForwardPreservesUnder`,
   `:1122`) — a full `Rel` does NOT hold precisely because a source `OutOfFuel`
   branch leaves the target still running (`Follows`, not `.done`).  Grep-confirmed:
   there is no whole-fragment full `Rel` between `sourceRun` and
   `openRunNResultWithStop` anywhere in the tower (only single-`openStep` head
   `Rel`s, e.g. `openStep_code_of_compileStmtFuel?`).

2. **`RunSettles` at the child budget is itself FALSE on truncation branches, and so
   is the promoted accumulator.**  `blockBudget`/`stmtBudget`
   (`InteractionStaticCost.lean`) are *fuel-indexed* over-approximations: `levelCost
   program F` bounds the target block-entries for a source run of ≤ `F` steps (the
   `.loop`/`.for_` cost scales linearly in `F`).  So on a branch where the child
   source run OUT-OF-FUELS at `blockSourceFuel` (an adversary CALL-return can drive a
   `for`-loop past any fixed `F`), the target `blockBudget`-run keeps executing past
   `blockBudget` entries and reaches `.ok (.exhausted …)` (`openRunNResultWithStop … 0
   … = .done (.ok (.exhausted …))`, `InteractionSemantics.lean:857`).  Hence
   `RunSettles cfg policy (blockBudget program F body) childLabel childState` is
   **false in general** — `of_cover`'s stopped/error cover cannot exist on that
   branch.  Session 21's "success ⇒ `.stopped ≤ budget`; error ⇒ `.error`" dichotomy
   is not exhaustive: it omits `OutOfFuel`.

3. **Worse — the composite's *residual-budget* accumulator is FALSE too, so
   `of_runSettles` cannot help even granting `RunSettles`.**  `AllEntriesRealized` is
   ANTITONE in fuel (`ReachesOpenStepAt.of_le` is monotone UP —
   `InteractionEntryRealized.lean:105`).  `switch`/`call`/`for` carry STRICT residual
   slack over the matched child's `blockBudget` (session-18 finding: `residual =
   switchBodyBudget + cases.length + 1 − k > blockBudget(matchedBody)`; the slack is
   the dispatch overhead + the `max` over the OTHER, possibly larger, cases).  On a
   truncation branch the matched body does NOT stop, so the residual run reaches
   entries at target-depth `(blockBudget, residual]`.  By the contrapositive of the
   over-approximation (`source ≤ F ⇒ target-depth ≤ blockBudget`), those entries sit
   at source-depth `> blockSourceFuel` — i.e. PAST where the source witness has
   out-of-fueled, so **no `StateRel` witness exists for them** and `realizedWitness
   cfg` is FALSE there.  The child owner's accumulator only covers `≤ blockBudget`;
   promoting to `residual` crosses into witnessless territory.  So
   `AllEntriesRealized cfg policy residual childLabel childState (realizedWitness cfg)`
   is genuinely FALSE on truncation branches — regardless of the promotion mechanism.

This is NOT unsoundness of `compile_correct` (already axiom-clean; the public spine
handles `OutOfFuel` via `Follows`/`ForwardRel`, never claiming the target settles).
It is the caller-frame / fuel-decoupling obstruction of **sessions 5–7 resurfacing
one layer up**: the swap-guard realization is fundamentally tied to the SOURCE
frame, which only exists up to the matched source fuel; the composite's extra
budget reaches past it.

### Corrected frontier / next-session options
The upward-promotion lever (`RunCompletes`→`RunSettles` + `of_runCompletes`/
`of_runSettles`, sessions 18–22) is the WRONG tool for the slack-bearing composites:
it presupposes the run settles within the child budget, which fails on truncation.
Two viable directions:
* **(A) Eliminate the slack (budget domination, not settling).**  Realize the
  composite accumulator at a budget with NO strict slack over the child's — i.e.
  invoke the child owner at a fuel `F'` with `blockBudget program F' matchedBody ≥
  residual`, so no witnessless entry is ever reached.  Requires a `blockBudget`
  MONOTONICITY-in-fuel lemma and a way to raise the child's `RealizingBlockOwnerAt`
  ceiling above `sourceFuel` (the current `switch`/`call` recursion fixes it AT
  `sourceFuel`; the residual can exceed `blockBudget(sourceFuel, matchedBody)` via the
  `max`-over-cases + `cases.length+1`, so this may need re-deriving the static cost so
  the matched-case residual never exceeds that case's own `blockBudget` at a
  reachable fuel).
* **(B) A fuel-DECOUPLED target-side stack-realization invariant** (the deferred
  procedure-calling-convention model, sessions 5–7 §4a/4b): maintain "the runtime
  stack realizes the current block's shape (incl. the hidden caller frame)" as an
  invariant of `openRunN` itself, so the swap depth guard is dischargeable at EVERY
  reached entry WITHOUT a source witness — removing the dependence on `SourceFrameFits`
  and hence on source fuel entirely.  This is the multi-hundred-line addition every
  prior session has punted; the session-22 analysis shows it (or (A)) is unavoidable
  — the accumulator route cannot be completed for `switch`/`call`/`for` as designed.

The landed `of_cover` + stability lemmas remain the correct, reusable reduction: any
route that establishes per-branch coverage feeds them directly.  What must change is
the SUPPLIER of that coverage on `OutOfFuel` branches, per (A)/(B).

### Status handed to session 23
Green banked: `InteractionSettlesBridge.lean` (`of_cover` + 4 stability lemmas,
commit `316f22d5`), harness `check` OK, axioms unchanged.  Blocker precisely located:
the `of_runSettles` upward promotion is provably insufficient for the slack-bearing
composites — `RunSettles`/`AllEntriesRealized` at the residual budget is false on
source-`OutOfFuel` branches (extra reachable entries lack a `StateRel` witness).
Recommend pivoting to (A) budget-domination or (B) the fuel-decoupled stack-realization
invariant before adding any `switch`/`call`/`for` realizing arm.  Do NOT attempt
`switch_bounded_realizing` via `of_runSettles`/`of_cover` alone — it cannot close green.

## Session-23 update (2026-07-17): ROUTE DECISION — obstruction 3 is an artifact of STATIC-BUDGET indexing; the fix is the per-outcome EXISTENTIAL-FUEL realizing family (route C, corrected). Decision written with file:line evidence; first substrate commit attempted below.

Session 23's mandate was a rigorous route decision between (A) budget-domination,
(B) the fuel-decoupled target-side stack-realization invariant, and any justified
third route, then execution.  A full trace of the preservation family definitions
(`InteractionControlPreservation.lean`) against the session-22 obstruction shows
that **(A) is dead, (B) is the deferred multi-hundred-line frame model, and there
is a THIRD route that dissolves obstruction 3 by REUSING the entire sessions 12-22
investment** — changing only the *fuel index* at which the accumulator is attached.

### Why (A) budget-domination is DEAD (not just hard)
(A) proposes realizing the composite accumulator at a budget with no strict slack
over the matched child, so no witnessless entry is reached.  But the composite's
`openRunNResultWithStop` runs at the *static* `stmtBudget` fuel
(`InteractionStaticCost.lean`, `stmtBudget_switch_succ`/`_call_succ`), and the
accumulator must cover the fuel the run actually uses.  On a source-`OutOfFuel`
(truncation) branch the matched body does NOT stop
(`BoundedTruncationExecPreservesUnder`, `InteractionControlPreservation.lean:1035`,
uses `Follows`, not `.stopped`), so the residual run keeps stepping past
`blockBudget(matchedBody)` and reaches entries with no `StateRel` witness.
"Raising the child owner's ceiling above `sourceFuel`" (session-22 (A) sketch)
requires a source run of MORE than `sourceFuel` steps, which does not exist on a
truncation branch — the source out-of-fuels AT `sourceFuel`.  So (A) cannot
eliminate the witnessless entries.  Confirmed dead for the same reason obstruction
3 bites.

### Why (B) is the honest-but-enormous route
(B) maintains "the runtime stack realizes the current block's shape" as a
target-side invariant of `openRunN` itself, discharging the swap depth guard at
every reached entry WITHOUT a source witness.  Sessions 8-9 already PROVED the
per-entry reduction collapses for compiler shapes — the return token sits at the
bottom of every procedure input shape
(`TypedCfgCompiler.lean:147/153/160/935`; audit in session-9 §(1)), so
`stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,returnTokenDepth?_eq_none}`
(`Structured/TypedCfgPreservation/StackRealizesEntry.lean`) discharges the guard
from the SOURCE `StateRel`/`SourceFrameFits`.  What (B) still lacks is a
source-FREE version of that invariant maintained across `openStep` — and
sessions 5-7 proved it is NOT derivable from CFG typing (`Shape.compatible`
permits `left.length < right.length` for caller tails; the missing depth is a
runtime call-convention property).  A genuinely source-free frame model is the
multi-hundred-line addition every session has punted.  (B) remains viable but is
strictly larger than (C) and does not reuse the sessions 12-22 owner-recursor
tower.

### THE DECISION — route (C), corrected: attach `AllEntriesRealized` at the per-outcome EXISTENTIAL settling fuel, not the static budget
The mandate's third-route hint ("index by the concrete `Executes` branch rather
than all branches ≤ budget; truncated branches may be irrelevant to the single
spliced execution") is CORRECT, and the exact mechanism is now pinned:

`ExecPreservesUnder` (`InteractionControlPreservation.lean:936`) is stated
per `(transcript, sourceOutcome)` and binds
`∃ targetFuel remaining targetOutcome, Executes (openRunNResultWithStop policy cfg
targetFuel entry target) transcript (.ok (.stopped remaining targetOutcome)) ∧ Rel …`.
That existential `targetFuel` is the run's ACTUAL SETTLING fuel — the run at it
produces `.stopped`, never `.exhausted`.  Sessions 12-22 instead moved to
`RealizingBoundedExecPreservesUnder`
(`Structured/InteractionEntryRealizedBounded.lean:62`), which conjoins
`∀ tf ≤ targetBudget, AllEntriesRealized cfg policy tf entry target realized` at
the STATIC `targetBudget = stmtBudget`.  That static budget is a fuel-indexed
over-approximation (`InteractionStaticCost.lean`, linear in `F` for loops), so on
truncation branches `AllEntriesRealized … targetBudget …` quantifies over entries
the actual run never settles into — precisely the witnessless entries of
obstruction 3.  **The slack is entirely an artifact of the static-budget index.**

Route (C) defines the parallel family at the EXEC (existential-fuel) level:
```
def RealizingExecPreservesUnder … realized :=
  ∀ target, StateRel source tokens target →
    ∀ transcript sourceOutcome, Executes sourceRun transcript (.ok sourceOutcome) →
      ∃ targetFuel remaining targetOutcome,
        Executes (openRunNResultWithStop policy cfg targetFuel entry target)
          transcript (.ok (.stopped remaining targetOutcome)) ∧
        Rel result ctx regular source.returns tokens sourceOutcome targetOutcome ∧
        AllEntriesRealized cfg policy targetFuel entry target realized     -- SAME existential targetFuel
```
The accumulator rides the SAME `targetFuel` the outcome leg produces.  At a
SETTLING fuel the run visits only entries of the settled run, all of which the
source simulation covers (each backward-simulates via `Rel.executes_right`,
`InteractionEntryRealizedForward.lean:56`, to a source step with a `StateRel`
witness).  There is no static over-approximation, hence NO witnessless entry, hence
obstruction 3 does not arise.

Session 13's objection ("`ExecPreservesUnder`'s `targetFuel` is existential
per-outcome, so there is no single fuel to name for the `AllEntriesRealized`
conjunct", `InteractionOwnerRealized` docstring / session-13 note) is ANSWERED:
put `AllEntriesRealized` UNDER the same per-outcome existential.  The reason
session 13 could not do this was that the flat `RealizingBounded…` hypothesis was
meant to feed a whole-program peephole congruence running at the static budget.
Route (C) also restates the CONSUMER per-outcome (a swap peephole `Executes`/
`Follows` transfer that consumes `AllEntriesRealized cfg policy targetFuel …` at
the outcome's own fuel — an induction on the `openRunNResultWithStop targetFuel`
recursion mirroring `Rel.executes`, `Interaction.lean:1871`, discharging the swap
guard per block-entry from the accumulator), so the flat static-budget hypothesis
is never needed.

### Why (C) dissolves the composite slack that killed sessions 16-22
`if_bounded_realizing` closed (session 17) because `stmtBudget (.if_ …) = 1 +
blockBudget body` (exact match, no slack).  `switch`/`call`/`for` failed
(sessions 18-22) because `stmtBudget` carries strict slack over the matched
child's `blockBudget` and `AllEntriesRealized` is antitone in fuel, so the slack
cannot be bridged upward.  Under (C) the composite's `targetFuel` is the ACTUAL
run fuel = dispatch-steps + child's actual settling fuel (the `Executes.bind_ok`,
`Interaction.lean:1144`, decomposition inherent in `if_exec`/`switch_exec`/
`call_exec`/`for_exec`, `InteractionOwnerPreservation.lean:580/674/1078/…`).
Gluing the accumulator is `AllEntriesRealized.of_succ` (`InteractionEntryRealized.
lean:173`) chained across the dispatch jumps, landing each child's accumulator at
its own actual fuel — NO budget arithmetic, NO `max`-over-cases slack, because
there is no static budget in the index at all.  The child-entry `StateRel` needed
at each `of_succ` step is already exposed by the per-block
`openStep_*_of_compileStmtFuel?` relations (session-14 KEY finding), so the
composites do not need the 16.7k-line giant-sim re-threading.

### Route (C) plan (dependency order)
1. **[substrate, self-contained]** Define `RealizingExecPreservesUnder` + projections
   (`.exec`, `.allEntriesRealized`) + the generic single-block constructor
   `of_exec_first_jump_stops` (exec leg + start realization + "first jump stops"
   ⇒ family, discharging the accumulator at the existential `targetFuel` via
   `AllEntriesRealized.of_first_jump_stops`; `targetFuel ≥ 1` from `.stopped ≠
   .exhausted`).  Then the FIVE exec leaves (`code`/`terminal`/`brk`/`cont`/`leave`
   `_exec_realizing`) mirroring `InteractionOwnerRealized.lean` but on `*_exec`.
2. Composite realizing recursors `if`/`switch`/`call`/`for` `_exec_realizing`
   reusing the existing `*_exec` outcome leg and gluing the accumulator via
   `of_succ` at the actual per-outcome fuels + the child-entry `StateRel` from the
   `openStep_*_of_compileStmtFuel?` extraction lemmas (sessions 14-15).  →
   `block_owner_exec_realizing` mutual recursion.
3. Mirror to `main_prefix_exec_realizing` / the prefix + truncation owners
   (`BoundedTruncationExecPreservesUnder` gets a `Follows`-indexed realizing
   sibling at its own `targetFuel`; on truncation the accumulator covers only the
   `Follows`-prefix entries, all source-covered).
4. **Consumer:** a per-outcome swap peephole transfer
   (`openRunNResultWithStop`-level `Executes`/`Follows` congruence guarded by
   `AllEntriesRealized cfg policy targetFuel …`), replacing the flat full-`Rel`
   consumer for the swap arm.  Discharge the swap guard per entry via
   `stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,returnTokenDepth?_eq_none}`
   (landed 8/9) — the accumulator's per-entry `realized` IS the source witness.
5. Wire at the four OIC call sites; add the `swap d :: swap d :: rest → rest` arm
   to `peepholeBody`; re-green the syntactic (b)-family; `scripts/opt_harness.sh full`.

The landed `of_cover` + stability lemmas (session 22) and the ENTIRE sessions 12-22
owner tower remain valid and reused; only the accumulator's FUEL INDEX changes
(static budget → per-outcome existential settling fuel).  `RealizingBounded…`
stays as-is for the leaf/if path already closed; the exec family is additive.

### LANDED (green, axiom-clean `[propext, Classical.choice, Quot.sound]`): `EvmCompiler/Structured/InteractionOwnerExecRealized.lean` (commit `fbe40999`, wired into `EvmCompiler.Verification`)
Route (C)'s substrate — the plan step-1 family + all five single-block leaves:
* **`RealizingExecPreservesUnder`** (`:60`) — the per-outcome existential-fuel
  realizing family (body = `ExecPreservesUnder`'s per-`(transcript, sourceOutcome)`
  `∃ targetFuel remaining targetOutcome, Executes … (.stopped …) ∧ Rel …` with the
  added conjunct `AllEntriesRealized cfg policy targetFuel entry target realized`
  UNDER the same existential `targetFuel`).
* **`RealizingExecPreservesUnder.exec`** (`:99`) — projection to the unchanged
  `ExecPreservesUnder` (feeds the spine).
* **`RealizingExecPreservesUnder.of_exec_first_jump_stops`** (`:127`) — the generic
  single-block constructor: `ExecPreservesUnder` leg + start realization + "every
  first jump stops" ⇒ the family.  Discharges the accumulator at the existential
  `targetFuel` via `AllEntriesRealized.of_first_jump_stops`; `targetFuel ≥ 1` is
  forced from the `.stopped ≠ .exhausted` result (`openRunNResultWithStop_zero`,
  `InteractionSemantics.lean:857`).
* **`code_exec_realizing`** / **`terminal_exec_realizing`** / **`brk_exec_realizing`**
  / **`cont_exec_realizing`** / **`leave_exec_realizing`** — the five leaves, each
  one `of_exec_first_jump_stops` application reusing the existing `*_exec`
  (`InteractionOwnerPreservation.OpenOutcome.Stmt.*_exec`) for the outcome leg and
  the `openStep_*_of_compileStmtFuel?` relation + `Rel.executes_right` + `contract.stops`
  for the "first jump stops" fact (identical structure to session 13's
  `*_forward_realizing`, but on the existential-fuel `*_exec` leg).

`scripts/opt_harness.sh check` = **OK (43 public theorems, axioms contained in
[propext, Classical.choice, Quot.sound])**; `compile_correct` /
`compile_correct_creation` unchanged.  `peepholeBody`/public spine UNTOUCHED ⇒
measured delta still **+0** (no arm shipped).

### Remaining frontier (route C, plan steps 2-5)
The leaves are landed on the correct index; the OPEN work is the composites and
the consumer:
1. **Composite exec recursors** `if`/`switch`/`call`/`for` `_exec_realizing`
   → `block_owner_exec_realizing` (mutual recursion).  Each reuses the existing
   `*_exec` outcome leg (`InteractionOwnerPreservation.OpenOutcome.Stmt.*_exec`,
   `:580/674/1078/…`) and glues the accumulator via `AllEntriesRealized.of_succ`
   (`InteractionEntryRealized.lean:173`) across the composite's dispatch jumps at
   the ACTUAL per-outcome fuels.  The child-entry `StateRel` each `of_succ` step
   needs is exposed by the per-block `openStep_*_of_compileStmtFuel?` extraction
   lemmas (sessions 14-15; the `if`/`call` extractions collapse to two reusable
   lemmas, session 15).  KEY: because the index is the actual run fuel
   (dispatch-steps + child settling fuel, from the `Executes.bind_ok` decomposition
   inside `*_exec`), there is NO static-budget slack — the `switch`/`call`/`for`
   wall of sessions 18-22 does not recur.  The one genuine obligation per construct:
   relate `ReachesOpenStepAt` of the composite's first `openStep` to the child's
   reachability (the `of_succ` `hNext`), discharged by the child's own
   `*_exec_realizing`.
2. **Mirrors** to `main_prefix_exec_realizing` + the truncation owner: give
   `BoundedTruncationExecPreservesUnder` (`InteractionControlPreservation.lean:1035`)
   a `Follows`-indexed realizing sibling at its own `targetFuel` (on truncation the
   accumulator covers only the `Follows`-prefix entries, all source-covered).
3. **Consumer:** a per-outcome swap peephole transfer at the
   `openRunNResultWithStop`-level — an induction mirroring `Rel.executes`
   (`Interaction.lean:1871`) that transfers the source-established `Executes`/
   `Follows` to the peepholed program, consuming `AllEntriesRealized cfg policy
   targetFuel …` at the outcome's own fuel and discharging the swap guard per
   block-entry via `stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,
   returnTokenDepth?_eq_none}` (landed 8/9) — the accumulator's per-entry `realized`
   is instantiated to the source witness there.  This replaces the flat full-`Rel`
   consumer for the swap arm (avoids needing realization at all branches ≤ budget).
4. Wire the four OIC sites to the `_of_source` variants; add the `swap d :: swap d
   :: rest → rest` arm to `peepholeBody`; re-green the syntactic (b)-family;
   `scripts/opt_harness.sh full`.

### Next-session recipe (start here)
Build `if_exec_realizing` first (the `if` composite has exact single-openStep
dispatch, cf. `if_bounded_realizing` session 17): reuse `if_exec` for the leg;
for the accumulator, `of_succ` at the composite entry — the single dispatch
`openStep` jumps to the chosen branch's child, whose `*_exec_realizing` supplies
the residual `AllEntriesRealized` at the child's actual fuel.  Then `switch`
(the pop;jump + k test blocks chain — `of_succ` k+1 times, each test block realized
via its retained-scrutinee `StateRel`), then `call`/`for`.  The exec index removes
the budget arithmetic that blocked these; the extraction lemmas (sessions 14-15)
supply every child-entry `StateRel`.  Do NOT reintroduce a static `targetBudget`
into the accumulator — that is exactly what obstruction 3 punishes.

## Session-24 update (2026-07-17): `if_exec_realizing` LANDED green + the generic `of_bounded` lift; the switch/call/for composites' exact obstruction pinned (the exec leg's opaque existential fuel), with the concrete threaded-re-derivation recipe

Session 24's mandate was the composite exec recursors (route-C frontier item 1):
`if_exec_realizing` first, then `switch`/`for`/`call`, then the mutual glue.  One
green, axiom-clean commit landed (`if`); the other three are shown to require a
genuinely larger threaded re-derivation and the exact obstruction + recipe are
pinned below.  `scripts/opt_harness.sh check` = **OK** (43 theorems, axioms
contained in `[propext, Classical.choice, Quot.sound]`); `compile_correct` /
`compile_correct_creation` unchanged; `peepholeBody`/public spine UNTOUCHED ⇒
measured delta still **+0**.

### LANDED (green, axiom-clean, commit `aaccb2aa`): `EvmCompiler/Structured/InteractionOwnerExecRealized.lean`
* **`RealizingExecPreservesUnder.of_bounded`** (`:134`) — the generic bounded→exec
  lift.  Whenever a fragment's *bounded* realizing family closes at a static budget
  (`RealizingBoundedExecPreservesUnder … targetBudget …`,
  `InteractionEntryRealizedBounded.lean:62`), its exec-level realizing family
  follows with NO extra reachability argument: the bounded outcome leg
  (`BoundedExecPreservesUnder`, `InteractionControlPreservation.lean:1140`) hands
  back a settling `targetFuel ≤ targetBudget`, and the bounded accumulator
  `.allEntriesRealized`, specialized to that very `targetFuel`, supplies
  `AllEntriesRealized cfg policy targetFuel …` — exactly the conjunct the exec
  family attaches under its existential `targetFuel`.  (Proof = destructure
  `h.bounded`; the `targetFuel ≤ targetBudget` witness feeds `h.allEntriesRealized`
  directly; no `of_le`, no `of_runCompletes`.)
* **`if_exec_realizing`** (`:473`) — the `if` composite exec recursor, = `of_bounded
  (InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.if_bounded_realizing …)`.
  `if`'s bounded realizing already closed (session 17) because `stmtBudget (.if_ cond
  body) = 1 + blockBudget body` is an EXACT child match (no slack), so the exec
  family is a one-liner over it.  Same hypotheses as `if_bounded_realizing`
  (incl. the mutual anchor `RealizingBlockOwnerAt` and `StmtContract`); concludes
  `RealizingExecPreservesUnder … (openRun program (sourceFuel+1) (.if_ cond body)
  source) policy (realizedWitness cfg)`.

Module builds ~6.5 s; import added: `EvmCompiler.Structured.InteractionBoundedOwnerRealized`.
`#print axioms if_exec_realizing` / `of_bounded` = `[propext, Classical.choice,
Quot.sound]`.

### WHY `switch`/`call`/`for` do NOT land via `of_bounded` — and the exact obstruction to the direct exec route
`of_bounded` needs the *bounded* realizing family (accumulator at a static budget).
For `switch`/`call`/`for` that family **does not close** (grep-confirmed: the only
composite realizing theorems in `InteractionBoundedOwnerRealized.lean` are
`if_bounded_realizing` + the five leaf `*_bounded_realizing` + `bounded_zero_realizing`;
there is no `switch_/call_/for_bounded_realizing` and no `block_owner_realizing`).
This is exactly obstruction 3 (sessions 18–22): their static `stmtBudget` carries
strict slack over the matched child's `blockBudget`, so the accumulator at the
static budget quantifies over witnessless truncation-branch entries.  Route C's
whole purpose is to attach the accumulator at the *settling* fuel instead — but the
direct exec construction of the composite recursor hits a concrete fuel-bridging
wall:

To build `switch_exec_realizing` at the exec family's existential `targetFuel` one
would reuse `switch_exec` (`InteractionOwnerPreservation.lean:674`) for the outcome
leg and glue the accumulator with `AllEntriesRealized.of_succ` across the dispatch
jumps.  `of_succ` at `targetFuel = f+1` needs the residual
`AllEntriesRealized cfg policy (f − dispatchSteps) matchedLabel matchedState realized`.
The child's `*_exec_realizing` supplies `AllEntriesRealized … childFuel …` at the
child's OWN settling fuel `childFuel`.  Bridging `f − dispatchSteps` to `childFuel`
fails both ways:
* `AllEntriesRealized.of_le` needs `f − dispatchSteps ≤ childFuel` — NOT derivable:
  `switch_exec`'s `targetFuel` and the child's `childFuel` are *independent*
  existentials (the composite leg is reused as a black box, so its internal
  `Executes.bind_ok` fuel decomposition is not exposed).
* `AllEntriesRealized.of_runCompletes` (`InteractionReachesCap.lean:322`) needs
  `RunCompletes cfg policy childFuel matchedLabel matchedState` — settling on ALL
  branches at that fixed `childFuel`.  A per-outcome `childFuel` does not give
  uniform completion; constructing `RunCompletes`/`RunSettles` was the sessions
  18–22 interpreter-totality wall (`hNoError` / `openStep` no-error), NOT dissolved
  by route C.

So the ONLY sound route is to re-derive the exec leg **fuel-matched**:
`targetFuel := dispatchSteps + childFuel` via the internal `Executes.bind_ok`, so
`of_succ`'s residual lands the child accumulator at exactly `childFuel`.  Concretely
this means building **realizing siblings** of the underlying exec-under lemmas that
thread the accumulator through the child callback:
* `InteractionBranchPreservation.lean:573 openRun_if_exec_under_of_compileStmtFuel?`
  (the `if` case — its `hBody` callback provides child `ExecPreservesUnder`; the
  realizing sibling takes a child `RealizingExecPreservesUnder` and returns a
  composite `RealizingExecPreservesUnder`),
* `InteractionSwitchPreservation.lean:2425 openRun_switch_exec_under_of_compileStmtFuel?`,
* `InteractionCallPreservation.lean:1888 openRun_call_exec_under_of_compileStmtFuel?`,
* `InteractionLoopPreservation.lean:1309 openRun_for_exec_under_of_compileStmtFuel?`.
These live in the large preservation files (Call is 1888+ lines) and the accumulator
threading must ride the SAME internal `bind_ok` witness that fixes the fuel — a new
additive sibling module cannot reconstruct it without re-proving the source
decomposition those lemmas encapsulate.  This is the genuine multi-hundred-line
bulk; the `if` case escaped it ONLY because `if_bounded_realizing` had already
closed, letting `of_bounded` shortcut the whole thing.

### Remaining frontier (route C)
1. **`switch`/`call`/`for` `_exec_realizing`** via the threaded re-derivation above,
   → `block_owner_exec_realizing` (mutual recursion at the exec layer, mirroring
   `block_owner` but producing `RealizingExecPreservesUnder`/attaching the
   accumulator at the matched fuel).  For `call` also thread the landed
   `AllEntriesRealized.of_refined` (`InteractionReachesCap.lean:411`) for the
   proc-body stop-policy refinement.  Child-entry `StateRel` at each `of_succ`/bind
   step is already exposed by `jump_state_rel_of_rel`
   (`InteractionBranchEntryRealized.lean:55`) / `jump_state_rel_of_pure`
   (`InteractionCallEntryRealized.lean:61`).
2. **Mirrors** to `main_prefix_exec_realizing` + the truncation owner
   (`BoundedTruncationExecPreservesUnder`, `InteractionControlPreservation.lean:1035`)
   at its own `Follows`-indexed settling fuel.
3. **Consumer** (plan step 4) + wiring (step 5) — unchanged from session 23.

### Next-session recipe (start here)
Build `openRun_if_exec_realizing_under` first as the TEMPLATE (even though
`if_exec_realizing` is already done via `of_bounded`): additively, in
`InteractionBranchPreservation` or a sibling that can see its internals, mirror
`openRun_if_exec_under_of_compileStmtFuel?` (`:573`) but (a) take `hBody` supplying
the child `RealizingExecPreservesUnder`, and (b) at the internal `Executes.bind_ok`
composition, in addition to the outcome leg, assemble the composite accumulator via
`AllEntriesRealized.of_succ` (`InteractionEntryRealized.lean:173`) with `hHere` from
`realizedWitness_of_stateRel` and the residual = the child callback's accumulator at
the SAME `childFuel` the bind picks.  Then `switch`/`call`/`for` follow the identical
pattern over their (pop;jump + k test blocks) / (two pure jumps) / (loop-condition
`jumpi`) heads.  Do NOT reuse the plain `*_exec` as a black box for the accumulator
leg — its existential `targetFuel` is opaque and cannot feed `of_succ`.  `of_bounded`
is the correct tool ONLY where the bounded realizing family closes (`if` and the
leaves); it is definitionally unavailable to `switch`/`call`/`for`.

## Session-25 update (2026-07-17): the session-24 exec-recursor recipe is REFUTED for the oracle-branching heads; `realizedWitness` is existential-per-state, so the true (and only) blocker is route B (target-side decodability preservation), NOT static-budget slack. NO Lean lemma landed — this is a corrected diagnosis, not a frontier advance. Baseline reconfirmed green.

Session 25's mandate was to build `openRun_if_exec_realizing_under` as the fuel-matched
threaded template, then the `switch`/`call`/`for` analogues.  A full trace of the
underlying definitions (`realizedWitness`, `AllEntriesRealized`, `of_succ`,
`allEntriesRealized_branch_step`/`_pure_step`, and the four `openRun_*_exec_under_of_compileStmtFuel?`
lemmas) shows the session-24 recipe **cannot close for the oracle-branching heads
(`if`, `for`)** and that the reason is a target-side decodability obligation (route B)
that route C does **not** avoid — contradicting route C's founding premise.  No new
lemma was committed (committing red/false Lean is forbidden; no unsoundness was found —
`compile_correct`/`compile_correct_creation` remain axiom-clean, harness `check` = **OK,
43 theorems**, and `peepholeBody`/public spine are UNTOUCHED ⇒ measured delta still **+0**).

### THE DECISIVE FACT session 22/24 misread: `realizedWitness` is EXISTENTIAL PER STATE, not tied to the actual source run
`realizedWitness cfg label state` (`InteractionBoundedOwnerRealized.lean:313`) is
```
∃ source tokens block, cfg.findBlock? label = some block ∧
  StateRel source tokens state ∧ SourceFrameFits block.input source.evm.stack.length
```
— i.e. "`state` DECODES to *some* source frame at `label`'s cfg block".  It is a purely
LOCAL, per-state well-formedness/decodability predicate; it does **not** say the
*actual* source run reached `(label, state)` at the run's fuel.  Session-22 obstruction 3
("those entries sit at source-depth > `blockSourceFuel`, so no `StateRel` witness exists
and `realizedWitness` is FALSE there") is therefore **imprecise**: a post-truncation
target entry is not automatically witnessless — it is witnessless only if NO source frame
decodes it, which is a genuine (hard) question, not a free consequence of the source run
having out-of-fueled.  The static-budget accumulator is thus not FALSE on truncation
branches; it is UNPROVEN — provable exactly when every entry the fuel-bounded run reaches
is decodable.  "Every reached entry is decodable" is **route B** (the fuel-decoupled
target-side stack-realization invariant, sessions 5-7/22 §4a/4b).

### Why route C's exec recursor still needs route B for the oracle-branching heads (`if`, `for`) — precise mechanism
Building `AllEntriesRealized cfg policy targetFuel entry target (realizedWitness cfg)` at
the composite's settling `targetFuel` via `AllEntriesRealized.of_succ`
(`InteractionEntryRealized.lean:173`) forces the `hNext` obligation: for EVERY concrete
first-step jump `openStep cfg entry target ⟶ .jump next state'` that does not stop,
supply `AllEntriesRealized cfg policy (targetFuel-1) next state' realized`.

* For `if`/`for` the head is the **condition block**, whose `openStep` is a genuine
  interaction tree branching on the condition CODE's oracle reads (`Condition.DoneRel`,
  `InteractionBranchPreservation.lean`).  So `of_succ`'s `hNext` quantifies over MULTIPLE
  condition-eval transcripts — one per oracle answer — each yielding a different
  `afterCond''`/`state''` and a body-entry jump.  The child `RealizingExecPreservesUnder`
  (uniform over `afterCond` as a recursor hypothesis) can only produce an accumulator for
  a branch on which a full body source run `Executes (bodyRun afterCond'') _ (.ok _)` is in
  hand — but `of_succ`'s `hNext` supplies only the HEAD transcript (up to the jump), never
  a body outcome.  For any non-settling condition branch (and a fortiori a truncating one),
  no body outcome is available ⇒ no child accumulator ⇒ the entry's realization can ONLY
  come from route B (decodability of that branch's reachable entries, source-free).  This
  is a hard refutation of the session-24 claim that the residual is "the child callback's
  accumulator at the SAME `childFuel`" — that works for the SINGLE settling branch, but
  `of_succ`/`allEntriesRealized_branch_step` demand ALL non-stopping first branches, and
  the branch-step's `hBody` is **uniform** (`∀ afterCond state'`, fixed residual fuel).
  A per-outcome exec child cannot feed a uniform, fixed-fuel `hBody`.  (Confirmed against
  `allEntriesRealized_branch_step`, `InteractionBoundedOwnerRealized.lean:464`, whose
  `hBody` is `∀ afterCond state', … → AllEntriesRealized cfg policy bodyBudget trueLabel
  state' realized` — exactly the uniform form `if_bounded_realizing` supplies from the
  BOUNDED owner and the per-outcome exec child cannot.)

* `if` escapes ONLY because `if_exec_realizing` = `of_bounded if_bounded_realizing`
  (session 24): the bounded owner already discharged the uniform coverage at the exact
  budget `stmtBudget (.if_) = 1 + blockBudget body` (no slack).  `for` has NO closing
  bounded realizing family (grep-confirmed absent; its `stmtBudget` scales linearly in
  fuel — real static slack, `InteractionStaticCost`), so `of_bounded` is unavailable and
  the direct exec route hits the route-B wall above.  **`for` is the fundamental blocker.**

* `switch`/`call` heads are **deterministic dispatch** (`openStep_pop_jump`/`openStep_test`
  — `dup;push;eq;jumpi`, resolved purely by the already-computed scrutinee, no oracle;
  call's silent call-site).  There `of_succ`'s `hNext` has a SINGLE first branch, so the
  per-outcome child suffices and route B is NOT needed at the switch/call dispatch level
  (the child's own internals are handled by the child recursor).  So the switch/call exec
  recursors ARE constructible in principle — but (i) each requires a realizing sibling of
  the ENTIRE dispatch recursion re-derived fuel-matched (switch delegates the pop;jump + k
  test-block chain to `openRun_cases_*_exec_under_of_compileCasesFuel?`, an inductive
  family over the case list — see the `routeFuel + 1` bind at
  `InteractionSwitchPreservation.lean:2822`; a `openRun_cases_*_realizing` sibling is a
  multi-hundred-line inductive addition, not one lemma), and (ii) they are still blocked in
  the mutual `block_owner_exec_realizing` because a switch/call CHILD may be a `for`.

### Net: route C cannot close the endgame; it is blocked at `for` by the very route-B obligation it claimed to sidestep
The mutual anchor is unbuilt: neither `block_owner_realizing` (bounded) nor
`block_owner_exec_realizing` (exec) exists (grep-confirmed — only referenced as future in
`InteractionBoundedOwnerRealized.lean:355/772`); `switch/call/for _exec_realizing` and
`*_exec_realizing_under` do not exist.  What exists: the five leaf `*_exec_realizing`, the
generic `of_exec_first_jump_stops`/`of_bounded`, and `if_exec_realizing` (all sessions
23-24, all with the UNFULFILLED hypothesis `RealizingBlockOwnerAt`, which requires the
never-built mutual anchor).  Because `RealizingBlockOwnerAt` is never inhabited, even
`if_exec_realizing` is presently a vacuous implication.

The route-C premise — "attach the accumulator at the per-outcome settling fuel and the
static-budget slack (obstruction 3) dissolves" — is only HALF right: it dissolves the
slack for pure-dispatch composites, but the underlying accumulator obligation for the
oracle-branching composites (`if`/`for`) was never about slack; it is the target-side
DECODABILITY of non-settling condition branches, i.e. route B, which route C does not
touch.  `if` hid this behind `of_bounded`; `for` cannot, so it surfaces there.

### Corrected recipe for the NEXT session — route B is the master key, and it discharges EVERYTHING at once
Stop building per-construct exec recursors.  Prove the single target-side invariant:
```
theorem openStep_preserves_realizedWitness :
    cfg.WellTyped →                       -- (or the concrete GeneratedContext)
    realizedWitness cfg entry target →
    Executes (openStep cfg entry target) transcript (.ok (.jump next state')) →
    realizedWitness cfg next state'
```
i.e. `realizedWitness cfg` is an `openStep`-jump invariant.  From it,
`AllEntriesRealized cfg policy fuel entry target (realizedWitness cfg)` follows at ANY
fuel from `hHere = realizedWitness_of_stateRel …` by a trivial `ReachesOpenStepAt`
induction (each `.step` reuses the invariant) — dissolving the accumulator conjunct of
EVERY family (leaf / `if` / `switch` / `call` / `for`, bounded AND exec) UNIFORMLY, with
no `of_succ` branch analysis, no fuel matching, no per-construct recursor, and no
dependence on the source run's fuel.  The proof obligation splits by terminator on the
`entry` block (from the decoded `block`):
  * fallthrough / `jump` / `jumpi` (NON-widening: `target.input.length ≤ output.length`,
    `Shape.compatible` with equal or shrinking length): the jump carries the block-body
    end-state decode forward; reuse the existing per-block `StateRel` step machinery
    (`Preservation`/`InteractionPreservation` block-step lemmas) to rebuild
    `StateRel`+`SourceFrameFits` at `next` from the `entry` decode.  Likely the bulk of
    the tractable part.
  * `returnDispatch` / proc-entry (WIDENING: `Shape.compatible` permits
    `output.length < target.input.length` for a `.caller` tail, `Syntax.lean:111`): the
    extra depth is the hidden caller frame — decode it via the calling-convention frame
    (`Structured/TypedCfgPreservation/Core.lean` `realizeStack`/`StateRel`/
    `ActivationExtension`; `SourceFrameFits`/`returnTokenDepth?` in
    `TypedCfgCompiler.lean:186`, `TypedCfgCompilerFacts.lean:76`).  This is the
    multi-hundred-line frame-model step every session 5-24 has punted; it is UNAVOIDABLE
    and is the real remaining cost of the whole peephole swap arm.
This is route (B) as scoped in sessions 5-7 §4a/4b and reaffirmed in sessions 22-23 as
"strictly larger than (C) but honest"; session 25's contribution is proving (C) does NOT
avoid it (the oracle-branch `hNext` obligation IS route B), so (B) is not merely the
larger option — it is the ONLY one that closes.  A partial win banks
`openStep_preserves_realizedWitness` for the non-widening terminators first (a genuine
green additive lemma), then the widening/caller-frame case.

### Status handed to session 26
No Lean lemma landed (per the mandate's own criterion this is a non-advancing session on
lemma count — but committing red/false code or a vacuously-hypothesised recursor would be
worse, and no unsoundness exists to report).  Baseline reconfirmed: harness `check` = OK,
43 public theorems, `compile_correct`/`compile_correct_creation` = `[propext,
Classical.choice, Quot.sound]`, `peepholeBody`/public spine untouched, delta +0.  The
banked substrate (sessions 23-24: leaf `*_exec_realizing`, `of_exec_first_jump_stops`,
`of_bounded`, `if_exec_realizing`) remains valid and reusable AFTER route B inhabits
`RealizingBlockOwnerAt`.  Do NOT attempt `switch`/`call`/`for` `_exec_realizing_under` or
the mutual `block_owner_exec_realizing` before landing `openStep_preserves_realizedWitness`
— they cannot close without it (for `for`) and are redundant with it (for all).

## Session-26 update (2026-07-17): the route-B MASTER LEVER landed green + axiom-clean (the uniform accumulator discharge); the invariant `openStep_preserves_realizedWitness` shown to REQUIRE per-block source provenance (NOT extractable from `realizedWitness` alone — even for the non-widening terminators), with the exact mechanism + the corrected route

Session 26's mandate was `openStep_preserves_realizedWitness`, split non-widening
first then widening.  Result: **one green, axiom-clean commit** landing the trivial
`ReachesOpenStepAt`-induction plumbing that the whole route B turns on (mandate
deliverable item 3 / "the uniform accumulator discharge lemma"), plus a precise,
evidence-based correction: the invariant is **not** provable from `realizedWitness`
standalone for ANY terminator (widening or not), because reconstructing `StateRel`
at the jump target requires the jumped-from block's **source-construct compile-fact**,
which `realizedWitness` (`findBlock?` + `StateRel` + `SourceFrameFits`) does not carry.
`scripts/opt_harness.sh check` = **OK (43 public theorems, axioms contained in
`[propext, Classical.choice, Quot.sound]`)**; `compile_correct`/`compile_correct_creation`
unchanged; `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still **+0**.

### LANDED (green, axiom-clean, commit `a2f32bc6`): `EvmCompiler/TypedCfg/InteractionEntryRealized.lean`
* **`AllEntriesRealized.realized_of_reaches_of_invariant`** (`:250`) and
  **`AllEntriesRealized.of_openStep_invariant`** (`:271`) — the route-B master lever,
  fully target-side over an ABSTRACT `realized : Label → EVMState → Prop`.  Given
  `hInv : ∀ e t transcript n s, realized e t → Executes (openStep program e t) transcript
  (.ok (.jump n s)) → realized n s` (an `openStep`-jump invariant) and a seed
  `realized entry target`, it produces `AllEntriesRealized program stopJump fuel entry
  target realized` at **any** fuel.  Proof = the trivial `ReachesOpenStepAt` induction
  the session-25 recipe called for (`.start` returns the seed; each `.step` reuses `hInv`
  on its concrete first jump, then relays the IH on the residual run — NO fuel matching,
  NO `of_succ` branch analysis, NO per-construct recursor).  `#print axioms` on both =
  `[propext, Classical.choice, Quot.sound]`.  This is exactly what makes route B pay off
  the moment the invariant lands: ONE `hInv` (instantiated `realized := realizedWitness cfg`,
  with `cfg.WellTyped`/`GeneratedContext` closed over) discharges the accumulator conjunct
  of EVERY family (leaf / `if` / `switch` / `call` / `for`, bounded AND exec) uniformly.

### THE DECISIVE FINDING: the invariant needs per-block source provenance the `realizedWitness` existential does not carry (all terminators, not just widening)
Session-25's split assumed the NON-widening cases (fallthrough/jump/jumpi) are "tractable,
green-able first" by "reusing the existing per-block `StateRel` step machinery."  A full
trace shows this understates the coupling.  `openStep cfg entry target` (= `Control.Program.step
Instr.openRunState`, `Control.lean:57`) with `findBlock? entry = some block` runs
`Block.run block target` = `runBody block.body block.input target` → `(state'', block.output)`,
then `runTermChecked block.output block.term state''`.  A `.jump next state'` outcome fixes
`(next, state')` from `state''` per terminator (`Semantics.lean:112 runTerm`; the target-side
`next`-existence is already `Semantics.lean:299 findBlock?_exists_of_type?_runTerm_jump`,
covering fallthrough/jump/jumpi/returnDispatch — reuse it).  The obstruction is **not** the
`next` label; it is rebuilding `realizedWitness cfg next state'`, i.e. a NEW source witness
`∃ source' tokens' block', findBlock? next = some block' ∧ StateRel source' tokens' state' ∧
SourceFrameFits block'.input source'.evm.stack.length`:

* To get `StateRel source' … state'` you must know what SOURCE step the block performed on
  the visible stack prefix (the body mutates `target.stack` above the hidden return-frame
  suffix; `realizeStack`, `Core.lean:17`).  For an ARBITRARY `block.body` (list of
  `TypedCfg.Instr`) there is no canonical source' — `StateRel` is preserved only because the
  body is a *compiled `Code` fragment* and `openRun_toCfg` (`InteractionPreservation.lean:457`)
  steps source and target *together*.  That theorem needs `Code.type? code block.input =
  some block.output` for the ACTUAL source `code` the block came from.
* The per-jump `StateRel` extraction lemmas already in the tower — `jump_state_rel_of_rel`
  (`InteractionBranchEntryRealized.lean:55`), `jump_state_rel_of_pure`
  (`InteractionCallEntryRealized.lean:61`) — ALL consume a source-coupled
  `Rel (DoneRel …) srcRun (openStep …)`, produced only by the per-construct compile-fact
  `openStep_*_of_compileStmtFuel?`.  `realizedWitness` carries `StateRel`/`SourceFrameFits`
  but NOT that `Rel`, and not the construct identity that yields it.
* `GeneratedContext` (`Core.lean:3387`) fixes `cfg.blocks = main.blocks ++ procBlocks ++
  dispatchBlocks … ++ [programEnd]`; recovering, for a given `findBlock? label = some block`,
  which category/source-construct it is (and thus its compile-fact) is a decomposition over
  those lists — precisely the `block_owner` mutual recursion (the never-inhabited anchor
  `RealizingBlockOwnerAt`/`block_owner_realizing`, `InteractionBoundedOwnerRealized.lean:358/355/772`).
  There is NO standalone `findBlock? → construct `Rel`` hook (grep-confirmed, consistent with
  sessions 10/11).

**Net:** route B does not avoid the source coupling any more than route C did — it relocates
it into the invariant's proof, where the block's source construct must be recovered from
`GeneratedContext`.  That recovery IS the `block_owner` giant coupling.  This is NOT a claim
the invariant is false (it is TRUE — it is compiler soundness restricted to one block step);
it is a claim it is not GREEN-provable standalone from `realizedWitness` in a session, for the
non-widening terminators any more than the widening one.  The widening (`returnDispatch`,
`Semantics.lean:137`, erases the token slot and dispatches to a `.caller`-tail target) adds,
on top, the caller-frame depth reconstruction (`SourceFrameFits` at the wider `block'.input`)
— the frame-model step every session 5–25 punted — but even fallthrough/jump/jumpi are gated
by the same provenance recovery.

### The corrected route (what actually closes)
The invariant must be proved as a corollary of the block-owner mutual recursion, indexed by
`GeneratedContext`, NOT standalone from `realizedWitness`.  Two equivalent framings:
1. **Provenance-indexed invariant.**  Prove, by the same `Nat.strong_induction_on sourceFuel`
   as `block_owner`, that at every reachable block entry the target state carries a *source
   witness PLUS its construct compile-fact*; the jump then feeds `jump_state_rel_of_rel`/
   `_of_pure` to land the child witness+fact at `next`.  This inhabits `RealizingBlockOwnerAt`
   (session-25's item-3 note that `if_exec_realizing` is presently VACUOUS because
   `RealizingBlockOwnerAt` is never inhabited stands — inhabiting it is the same work).
2. **Whole-run realization theorem.**  Prove directly, inside the OIC splice where the source
   bridge `yulToNormalizedStackTypedCfgPrefixForward` is already in scope (so the running
   `cfg = generated.cfg` HAS a `GeneratedContext` and a source `StateRel` at the entry),
   `AllEntriesRealized cfg policy fuel cfg.entry initialState (realizedWitness cfg)` — feeding
   `of_openStep_invariant` (LANDED this session) an `hInv` whose proof at each jump recovers
   the construct via the source simulation already threaded there.  This is the cheaper wiring
   because it never needs a construct-recovery hook divorced from the source run; the source
   run supplies the construct at each entry it visits.

Framing 2 is recommended: `of_openStep_invariant` reduces the ENTIRE remaining endgame to
"produce `hInv` for `realizedWitness cfg` **with the source run in scope**", which is a
single source-coupled preservation step (one block ⟶ one jump), not the full per-construct
exec-recursor tower sessions 16–25 built toward.  The banked substrate (leaf `*_exec_realizing`,
`of_bounded`, `if_exec_realizing`, `if_bounded_realizing`, the accumulator step helpers) remains
valid and is what `hInv`'s block-step proof will reuse per construct.

### Status handed to session 27
Landed: `a2f32bc6` (`realized_of_reaches_of_invariant` + `of_openStep_invariant`,
`InteractionEntryRealized.lean:250/271`), green, axiom-clean, wired into the tree the harness
checks.  Frontier: the single obligation is now `hInv : realizedWitness cfg` is an
`openStep`-jump invariant, provable ONLY with the block's source construct in scope — recover
it via `GeneratedContext`/`block_owner` (framing 1) or, cheaper, at the OIC splice with the
source run threaded (framing 2).  Start with framing 2: state the whole-run
`AllEntriesRealized … (realizedWitness cfg)` at `cfg.entry` and discharge its `hInv` from the
already-threaded source simulation, block by block; the non-widening terminators
(fallthrough/jump/jumpi) reuse `runBody_stackRealizes` (session 6) + `openRun_toCfg` for the
body leg and `findBlock?_exists_of_type?_runTerm_jump` for the target; the widening
`returnDispatch` reuses `realizeStack`/`StateRel`/`ActivationExtension` (`Core.lean`) +
`SourceFrameFits`/`returnTokenDepth?` for the caller-frame depth.  Do NOT re-attempt the
standalone-from-`realizedWitness` proof — it is provably underdetermined (no source' without
the construct).  `compile_correct`/`compile_correct_creation` axioms unchanged; delta +0.

## Session-27 update (2026-07-17): the two NON-widening `realizedWitness` successor legs (branch/if + call/pure) LANDED green + axiom-clean as direct compositions; the sole remaining hInv frontier isolated to (a) per-entry source-construct provenance recovery and (b) the widening `returnDispatch` caller-frame extraction (no green-able returnDispatch child-`StateRel` lemma exists yet)

Session 27's mandate was framing 2: state and prove, at the OIC splice, the
`openStep`-jump invariant `hInv` for `realized := realizedWitness cfg`, then feed
`AllEntriesRealized.of_openStep_invariant` (landed session 26,
`InteractionEntryRealized.lean:271`).  Result: **one green, axiom-clean commit**
(`e93600d1`) banking the two per-jump *successor legs* the invariant's proof invokes
at every `if`/branch and `call` entry — the non-widening, non-provenance part of
`hInv`, isolated so the remaining frontier is exactly two named obligations.  The
full `hInv` did NOT close (it cannot in one session — see frontier below); no red
code, no sorries, `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still **+0**.

### LANDED (green, axiom-clean, commit `e93600d1`): `EvmCompiler/Structured/InteractionRealizedWitnessSuccessor.lean`
Both `#print axioms` = `[propext, Classical.choice, Quot.sound]`; wired into
`EvmCompiler.Verification` (import after `InteractionBoundedOwnerRealized`).
* **`realizedWitness_of_branch_jump`** (`:62`) — the **branch/`if` leg** of the
  invariant.  From the source-coupling `Rel (InteractionBranchPreservation.Condition.DoneRel
  trueLabel falseLabel tokens restShape) srcRun (openStep cfg entry target)`, a concrete
  non-stopping `Executes … (.ok (.jump next state'))`, and the target `LabelShape cfg
  next restShape`, concludes `realizedWitness cfg next state'`.  Proof = the existing
  child-`StateRel` extraction `InteractionBranchPreservation.Condition.jump_state_rel_of_rel`
  (`InteractionBranchEntryRealized.lean:55`) ∘ the uniform entry-witness supplier
  `realizedWitness_of_stateRel` (`InteractionBoundedOwnerRealized.lean:334`).
* **`realizedWitness_of_pure_jump`** (`:100`) — the **`call` leg**.  From the silent
  call-site `openStep cfg entry target = pure (.jump childLabel childState)`, the child
  `StateRel childSource childTokens childState`, a concrete `Executes … (.ok (.jump next
  state'))`, the target `LabelShape cfg childLabel childInput`, and `SourceFrameFits
  childInput childSource.evm.stack.length`, concludes `realizedWitness cfg next state'`.
  Proof = `InteractionCallPreservation.Call.jump_state_rel_of_pure`
  (`InteractionCallEntryRealized.lean:61`) ∘ `realizedWitness_of_stateRel`.

These are the exact per-jump discharges framing 2's `hInv` proof runs at each
`if`/branch and `call` entry: they consume precisely the source-coupling
(`DoneRel` `Rel` / silent `pure`-jump equation) + the target `LabelShape`, and emit the
child `realizedWitness`.  They confirm the non-widening successor step is a clean
green composition once the coupling is in hand.

### THE FRONTIER, now isolated to exactly two named obligations
`of_openStep_invariant` needs a GLOBAL `hInv : ∀ e t transcript n s, realizedWitness
cfg e t → Executes (openStep cfg e t) transcript (.ok (.jump n s)) → realizedWitness cfg
n s`.  The successor legs above discharge the *conclusion* GIVEN the source coupling at
`e`; what remains is:

1. **Per-entry source-construct provenance recovery (the session-26 obstruction, unmoved).**
   To invoke `realizedWitness_of_branch_jump`/`_of_pure_jump` at an ARBITRARY reached
   `(e, t)` with only `realizedWitness cfg e t` in hand, one must first PRODUCE the
   source coupling at `e` — the `Rel (DoneRel …)` (branch) or the `openStep = pure …`
   equation (call) — which requires knowing `e`'s source construct.  `realizedWitness`
   carries `StateRel`/`SourceFrameFits` but NOT the coupling nor the construct identity.
   Recovering it from `GeneratedContext` (`Core.lean:3387`, `cfg.blocks = main ++ procs ++
   dispatch ++ [programEnd]`) is the `block_owner` decomposition — the never-inhabited
   `RealizingBlockOwnerAt`/`block_owner_realizing` anchor
   (`InteractionBoundedOwnerRealized.lean:358`).  Framing 2's intended fix: at the OIC
   splice, do NOT prove a global `hInv` from `realizedWitness` alone; instead STRENGTHEN
   the carried predicate to bundle the construct compile-fact (so `hInv` becomes
   self-contained), OR couple the `AllEntriesRealized` proof to the actual source run
   `yulToNormalizedStackTypedCfgPrefixForward` so the construct is supplied at each entry
   it visits.  Both routes inhabit the same `block_owner`-indexed provenance; the
   successor legs landed here are what that proof calls once provenance is in hand.
2. **The widening `returnDispatch` caller-frame leg (deferred since session 5, still absent).**
   There is NO `returnDispatch` analogue of `jump_state_rel_of_rel`/`_of_pure` — grep-confirmed:
   the only child-`StateRel` extractions are the branch and call ones.  `returnDispatch`
   (`Semantics.lean:137`, erases the token slot, dispatches to a `.caller`-tail target
   whose `input.length` may EXCEED the pre-jump `output.length`) needs the hidden
   caller-frame depth reconstructed via `realizeStack`/`StateRel`/`ActivationExtension`
   (`Structured/TypedCfgPreservation/Core.lean:17/51/285`) + `SourceFrameFits`/
   `returnTokenDepth?` (`TypedCfgCompiler.lean:186`, `TypedCfgCompilerFacts.lean:76`).
   Writing that `returnDispatch` extraction is the genuine multi-hundred-line frame-model
   step; it is a prerequisite for a `realizedWitness_of_dispatch_jump` sibling of the two
   legs banked this session.

### Next-session recipe
* First bank the **`returnDispatch` child-`StateRel` extraction** (obligation 2) as a new
  `jump_state_rel_of_dispatch`-style lemma in the `Structured/Interaction*EntryRealized`
  family, mirroring `jump_state_rel_of_rel` but reading the caller frame off
  `realizeStack`/`ActivationExtension`; then a `realizedWitness_of_dispatch_jump` leg is a
  one-line composition with `realizedWitness_of_stateRel` (as the two landed legs are).
  This closes the *successor* half of `hInv` for ALL terminators.
* Then attack obligation 1 (provenance) at the OIC splice: state
  `AllEntriesRealized cfg policy fuel cfg.entry initialState (realizedWitness cfg)` where
  the source bridge is in scope; build the global `hInv` by the `block_owner`
  `Nat.strong_induction_on sourceFuel`, feeding each terminator's landed successor leg
  (`realizedWitness_of_{branch,pure,dispatch}_jump`) with the construct recovered from
  `GeneratedContext`.  Feed the result to `of_openStep_invariant`; proceed to Step B.
* Do NOT add the swap arm to `peepholeBody` until the whole invariant is green (adding it
  reddens every `peepholeBody_cons` split, per session 5).

### Status handed to session 28
Landed: `e93600d1` (`realizedWitness_of_branch_jump` + `realizedWitness_of_pure_jump`,
`InteractionRealizedWitnessSuccessor.lean:62/100`), green, axiom-clean, wired into
`EvmCompiler.Verification`.  `scripts/opt_harness.sh check` = PASS (43 public theorems,
axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/
`compile_correct_creation` unchanged; delta +0.  Frontier = (1) per-entry provenance
recovery (`block_owner`, framing 2 at the OIC splice) + (2) the widening `returnDispatch`
caller-frame extraction (write `jump_state_rel_of_dispatch` first).  The two successor
legs banked here are the reusable per-jump discharges those two obligations feed into.


## Session-28 update (2026-07-17): the widening `returnDispatch` caller-frame leg LANDED green + axiom-clean — obligation (2) of session 27 CLOSED; the `hInv` successor half is now complete for ALL terminators (branch, call, returnDispatch). Sole remaining frontier = obligation (1), per-entry source-construct provenance at the OIC splice

Session 28's mandate was obligation (2) from §Session-27: the widening
`returnDispatch` caller-frame extraction — deferred since session 5 as "the genuine
multi-hundred-line frame-model step". **Result: two green, axiom-clean commits**
(`ddc6360c`, `3cb8716b`). The key finding is that the frame-model work was ALREADY
proved inside `InteractionCallPreservation`, so the leg is a clean composition — NOT
a from-scratch frame model. No red code, no sorries, `peepholeBody`/public spine
UNTOUCHED ⇒ measured delta still **+0**.

### KEY FINDING: the CFG-level return dispatch is a SILENT `pure` jump, and its frame model is already discharged
The session-5→27 framing called this "the widening `returnDispatch` caller-frame
extraction … genuinely a multi-hundred-line frame-model step". The obstruction was
over-scoped. Two facts collapse it:

1. **The `Terminator.returnDispatch` produces a `.jump` Outcome, not a residual.**
   `Semantics.lean:112 runTerm` on `.returnDispatch returnCount sites` reads
   `shape.returnTokenDepth? = some depth`, checks `depth = returnCount`, reads the
   token `state.stack[depth]?`, `ReturnSite.findTarget? token sites` selects the
   caller continuation `target`, and yields
   `.jump target { state with stack := state.stack.eraseIdx depth }` (the token slot
   erased). (The `Outcome.returnDispatch` CONSTRUCTOR — a residual that STOPS the
   runner, Control.lean:90/150/182/206 — is a DIFFERENT thing; the exit block's
   terminator never emits it.) So at the CFG `Program.openStep` level the exit block
   is a **silent `pure` jump to the caller**, structurally identical to the `call`
   leg — NOT a widening `jumpi` branch.

2. **The caller-frame peel + caller `StateRel` is already proved:**
   `InteractionCallPreservation.Call.openStep_dispatch`
   (`InteractionCallPreservation.lean:747`) concludes exactly
   `∃ targetFinal, Program.openStep cfg (ProcLabel.exit proc.name) target =
   pure (.jump site.returnLabel targetFinal) ∧ StateRel (returned.withEVM …) tokens
   targetFinal`, via `TypedCfgPreservation.CallStack.eraseReturnToken_preserves`
   (`Structured/TypedCfgPreservation/Core.lean:1761`) — i.e. the
   `realizeStack`/`StateRel`/`ActivationExtension` machinery peels one activation
   frame off the runtime stack and restores the caller state. This is the frame
   model the session-5 diagnosis wanted; it exists, is green, and hands back the
   caller `StateRel`. It is consumed internally at `openRun_call_exec_under`
   (`InteractionCallPreservation.lean:1024/1136`) — the "ownership callback" the
   mandate pointed at.

Because `openStep_dispatch`'s conclusion is the abstract `pure`-jump shape that the
generic `jump_state_rel_of_pure` (`InteractionCallEntryRealized.lean:61`) already
consumes, the `returnDispatch` extraction is a direct composition — no backward
simulation, no re-derivation of the frame model.

### LANDED (green, axiom-clean)
* **`ddc6360c` — `EvmCompiler/Structured/InteractionDispatchEntryRealized.lean`:**
  `InteractionCallPreservation.Call.jump_state_rel_of_dispatch` (`:74`) — the
  `returnDispatch` analogue of `jump_state_rel_of_rel`/`_of_pure`. From the
  `openStep_dispatch` hypotheses (`context`, `hLookup`, `hSiteProc`, `hSiteMem`,
  `hRel : StateRel bodyState (site.token :: tokens) target`, `hPop`, `hAttach`,
  `hRetc`) + a concrete `hExec : Executes (openStep cfg (ProcLabel.exit proc.name)
  target) transcript (.ok (.jump next state'))`, concludes
  `next = site.returnLabel ∧ StateRel (returned.withEVM { bodyState.evm with stack
  := stack }) tokens state'`. Proof = `openStep_dispatch` (frame model) ∘
  `jump_state_rel_of_pure` (pure-jump leaf). Wired into `EvmCompiler.Verification`.
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
* **`3cb8716b` — `EvmCompiler/Structured/InteractionRealizedWitnessSuccessor.lean`:**
  `realizedWitness_of_dispatch_jump` (`:149`) — the return-dispatch **successor leg**
  of `hInv`, the widening sibling of `realizedWitness_of_branch_jump`/`_of_pure_jump`.
  Given the dispatch hypotheses + `hExec` + `hLabelShape : LabelShape cfg
  site.returnLabel callerInput` + `hFits : SourceFrameFits callerInput (returned.withEVM
  …).evm.stack.length`, concludes `realizedWitness cfg next state'`. Proof =
  `jump_state_rel_of_dispatch` ∘ (`subst`) ∘ `realizedWitness_of_stateRel`. One-line
  composition exactly as the two session-27 legs. `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`.

### THE SUCCESSOR HALF OF `hInv` IS NOW COMPLETE FOR ALL TERMINATORS
`of_openStep_invariant` (`InteractionEntryRealized.lean:271`) needs the global
`hInv : realizedWitness cfg e t → Executes (openStep cfg e t) transcript
(.ok (.jump n s)) → realizedWitness cfg n s`. The per-terminator successor
discharges — GIVEN the source coupling at `e` — are now all banked:
`realizedWitness_of_branch_jump` (if/branch), `realizedWitness_of_pure_jump`
(call), `realizedWitness_of_dispatch_jump` (returnDispatch). Fallthrough/halt/
invalid do not emit `.jump` successors (fallthrough is a whole-program-level
residual; halt/invalid are terminal), so no further successor legs are needed.

### THE SOLE REMAINING FRONTIER: obligation (1), per-entry source-construct provenance
Unchanged from §Session-27 obligation (1), now the ONLY hole. To invoke a successor
leg at an ARBITRARY reached `(e, t)` with only `realizedWitness cfg e t` in hand, the
`hInv` proof must first PRODUCE the source coupling at `e` — the branch `Rel (DoneRel …)`,
the call `openStep = pure …` equation, OR (new this session) the return-dispatch
`openStep_dispatch` hypotheses (`hLookup`/`hSiteMem`/`hRel`/`hPop`/`hAttach`/`hRetc`)
plus the caller `LabelShape`/`SourceFrameFits` — which requires knowing `e`'s source
construct. `realizedWitness` carries `StateRel`/`SourceFrameFits` but NOT the coupling
nor the construct identity. Recovering it is the `block_owner` decomposition over
`GeneratedContext` (`Core.lean:3387`, `cfg.blocks = main ++ procs ++ dispatch ++
[programEnd]`) — the never-inhabited `RealizingBlockOwnerAt`/`block_owner_realizing`
anchor (`InteractionBoundedOwnerRealized.lean:358`). Framing 2's fix: at the OIC
splice, do NOT prove a global `hInv` from `realizedWitness` alone; instead couple the
`AllEntriesRealized` proof to the in-scope source run
`yulToNormalizedStackTypedCfgPrefixForward` so the construct (and hence the coupling)
is supplied at each entry it visits. The three successor legs are what that proof
calls once provenance is in hand.

Note for the dispatch entry specifically: provenance recovery there must additionally
supply the frame-boundary facts `hPop`/`hAttach`/`hRetc` — these come from the source
run's `RunState.returns`/`popReturn?` at the procedure-exit point, exactly as
`openRun_call_exec_under` supplies them internally (via `Rel.regular_elim_of_required_fallthrough`,
`InteractionControlPreservation.lean:694`, feeding the body `StateRel` into
`openStep_dispatch`). So the same source-run coupling that supplies the branch/call
constructs supplies the dispatch ones — obligation (1) is genuinely a single unified
provenance problem, not three.

### Next-session recipe
* Attack obligation (1) at the OIC splice. State `AllEntriesRealized cfg policy fuel
  cfg.entry initialState (realizedWitness cfg)` where the source bridge
  `yulToNormalizedStackTypedCfgPrefixForward` is in scope; build the global `hInv` by
  the `block_owner` `Nat.strong_induction_on sourceFuel`, feeding each terminator's
  landed successor leg (`realizedWitness_of_{branch,pure,dispatch}_jump`) with the
  construct — and, for dispatch, the `openStep_dispatch` frame-boundary hypotheses —
  recovered from `GeneratedContext`/the source run. Feed the result to
  `of_openStep_invariant`; proceed to Step B.
* Do NOT add the swap arm to `peepholeBody` until the whole invariant is green (adding
  it reddens every `peepholeBody_cons` split, per session 5).

### Status handed to session 29
Landed: `ddc6360c` (`jump_state_rel_of_dispatch`,
`InteractionDispatchEntryRealized.lean:74`) + `3cb8716b`
(`realizedWitness_of_dispatch_jump`, `InteractionRealizedWitnessSuccessor.lean:149`),
green, axiom-clean, wired into `EvmCompiler.Verification`. `scripts/opt_harness.sh
check` = PASS (43 public theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` unchanged; delta +0. Frontier reduced to
the SINGLE obligation (1): per-entry source-construct provenance recovery
(`block_owner`, framing 2 at the OIC splice). The `hInv` SUCCESSOR half is now complete
for all terminators (branch/call/returnDispatch); provenance is the only remaining gate
before `of_openStep_invariant` → Step B.

## Session-29 update (2026-07-17): the per-entry block-provenance SUBSTRATE landed green + axiom-clean (reverse `findBlock?` classification + the programEnd `hInv` arm discharged unconditionally); obligation (1) reduced from four categories to three (the compiled-construct ones still gated on the source-run coupling)

Session 29's mandate was obligation (1): per-entry source-construct provenance at
the OIC splice — build the coupled `hInv` (or its pieces) so
`AllEntriesRealized.of_openStep_invariant` (landed session 26) can fire.  Result:
**one green, axiom-clean commit** landing the *reverse-classification substrate* of
the `block_owner` provenance recovery — the first, unavoidable move of `hInv`'s
per-entry case split, absent from the tower until now (every prior `GeneratedContext`
`findBlock?` lemma is *forward*, category ⟶ block) — PLUS the clean unconditional
discharge of the programEnd arm.  The full `hInv` did NOT close (it cannot in one
session; the three compiled-construct arms remain gated on the source-run coupling —
see frontier).  No red code, no sorries, `peepholeBody`/public spine UNTOUCHED ⇒
measured delta still **+0**.

### LANDED (green, axiom-clean): `EvmCompiler/Structured/InteractionBlockProvenance.lean`
All three `#print axioms` = `[propext, Classical.choice, Quot.sound]`; wired into
`EvmCompiler.Verification` (import after `InteractionRealizedWitnessSuccessor`).
Namespace `EvmCompiler.Structured.TypedCfgPreservation.Program.GeneratedContext`.
* **`block_category`** (`:79`) — **reverse block classification under a
  `GeneratedContext`.**  From `cfg.findBlock? label = some block`, concludes the
  four-way disjunction
  `block ∈ context.main.blocks ∨ block ∈ context.procBlocks ∨
   block ∈ dispatchBlocks source.procs (main.calls ++ procCalls) ∨
   block = context.programEndBlockOf`.
  Proof = `List.mem_of_find?_eq_some` + `cfgEq` rewrite + `List.mem_append` split.
  This is what tells the `hInv` proof *which* compile fact governs the jumped-from
  block at an arbitrary reached entry `e` — the entry point of any provenance
  recovery.
* **`programEnd_openStep_eq`** (`:108`) — `openStep cfg ProcLabel.programEnd t =
  .done (.ok (.halt .stop t))` (empty body, `.halt .stop` terminator; reduces via
  `context.programEndBlock` + `Control.Block.run`/`runBody` + `bind_done_ok` +
  `if_pos rfl`).
* **`programEnd_openStep_no_jump`** (`:138`) — **the programEnd arm of `hInv`,
  discharged UNCONDITIONALLY.**  Any `Executes (openStep cfg ProcLabel.programEnd t)
  transcript (.ok (.jump next state'))` is impossible (the outcome is a completed
  `.halt`), so the programEnd entry needs NO source coupling.  Proof = rewrite by
  `programEnd_openStep_eq` then `cases` the `.done` `Executes` (indices `.halt` vs
  `.jump` fail to unify).
* **`programEndBlockOf`** (`:55`) — the explicit programEnd block (as pinned by
  `cfgEq`), the classification's fourth disjunct.

### Where this leaves obligation (1): three arms, all gated on the source-run coupling
`of_openStep_invariant` needs the global `hInv : realizedWitness cfg e t →
Executes (openStep cfg e t) … (.jump n s) → realizedWitness cfg n s`.  With
`block_category`, `hInv`'s proof splits the entry `e` (via its `findBlock?` witness
inside `realizedWitness`) into the four categories; this session closes ONE:
* **programEnd** — `programEnd_openStep_no_jump`: vacuous, done. ✓
* **main body block** (`∈ main.blocks`) — needs the branch/pure source coupling
  (`Rel (DoneRel …)` / `openStep = pure …`) to feed `realizedWitness_of_branch_jump`
  / `_of_pure_jump` (session 27).  NOT recoverable from `realizedWitness` alone.
* **proc body block** (`∈ procBlocks`) — same as main.
* **dispatch block** (`∈ dispatchBlocks …`) — needs the `openStep_dispatch`
  frame-boundary facts (`hLookup`/`hSiteMem`/`hRel`/`hPop`/`hAttach`/`hRetc`) to feed
  `realizedWitness_of_dispatch_jump` (session 28).  The `hPop`/`hAttach`/`hRetc`
  come from the source run's `RunState.returns`/`popReturn?` — NOT recoverable from
  `realizedWitness` alone.

So `block_category` performs the case split but the three compiled-construct arms
still require the *source construct* at `e`, which `realizedWitness`
(`findBlock?` + `StateRel` + `SourceFrameFits`) provably does not carry (session 26
obstruction, unmoved for those arms).  Recovering it is the deeper `block_owner`
decomposition INSIDE each category — for `main.blocks`, *which statement* compiled
to `block` (not merely that it is a main block); this is the source-run coupling
`openRun_toCfg` (`InteractionPreservation.lean:457`) provides only when the source
`Code` fragment is in scope.  `block_category` is necessary-but-not-sufficient: it is
the outer case split; the inner per-statement coupling is the residual bulk.

### THE FRONTIER (unchanged in essence; the outer split is now banked)
The genuine remaining work is to supply, at each reached entry, the source construct
+ coupling for the three compiled-construct arms.  Two routes, both multi-session:
1. **`block_owner`-indexed provenance** — inhabit `RealizingBlockOwnerAt` /
   `block_owner_realizing` (`InteractionBoundedOwnerRealized.lean:358`) by the same
   `Nat.strong_induction_on sourceFuel` as `block_owner`
   (`InteractionOwnerPreservation.lean:1502`), threading `realizedWitness cfg` through
   the whole recursion.  Blocked since session 24 at `switch_exec_realizing` /
   `call_exec_realizing` / `for_exec_realizing` (the oracle-branching heads' opaque
   exec fuel).
2. **Source-run coupling at the OIC splice** — thread the in-scope source bridge
   `yulToNormalizedStackTypedCfgPrefixForward`
   (`Compiler/OpenInteractionComposition.lean:695`) so each reached entry's construct
   (and, for dispatch, its `RunState.returns`/`popReturn?` frame facts) is supplied
   directly, feeding `block_category` ⟶ the matching session-27/28 successor leg.
   The remaining glue is exactly the per-construct coupling `openRun_toCfg` /
   `Rel.regular_elim_of_required_fallthrough`
   (`InteractionControlPreservation.lean:694`) restricted to one block step.

### Next-session recipe
* Start route 2.  In `hInv`'s proof, split `e` with `block_category`; discharge the
  programEnd arm with `programEnd_openStep_no_jump` (landed).  For the three
  compiled-construct arms, do NOT try to recover the construct from `realizedWitness`
  standalone (provably underdetermined) — instead couple to the source run threaded
  at the OIC splice and produce the branch/pure/dispatch coupling one block step at a
  time, feeding `realizedWitness_of_{branch,pure,dispatch}_jump`.  Feed the resulting
  `hInv` to `of_openStep_invariant`; proceed to Step B.
* Do NOT add the swap arm to `peepholeBody` until the whole invariant is green.

### Status handed to session 30
Landed: `InteractionBlockProvenance.lean` (`block_category` :79,
`programEnd_openStep_eq` :108, `programEnd_openStep_no_jump` :138,
`programEndBlockOf` :55), green, axiom-clean, wired into `EvmCompiler.Verification`.
`scripts/opt_harness.sh check` = OK (43 public theorems, axioms ⊆ `[propext,
Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation`
unchanged; delta +0.  Obligation (1)'s outer case split (`block_category`) + the
programEnd arm are now banked; the three compiled-construct arms remain the frontier,
gated on the per-block source-run coupling (route 2 above).

## Session-30 update (2026-07-17): the per-construct coupling SUPPLIERS for the `if` and `call` main-body/proc-body arms landed green + axiom-clean (producer ∘ successor-leg collapse); the two remaining route-2 gates precisely isolated (the `.code` regular-jump successor leg + the provenance quantifier)

Session 30's mandate was route 2: the source-run coupling for the three
compiled-construct arms of `hInv` — supply, at each reached compiled-construct
entry, the source coupling the session-27/28 successor legs consume, feeding
`block_category` (session 29) ⟶ the matching leg.  **Result: one green,
axiom-clean commit** banking the *per-construct coupling suppliers* for the `if`
and `call` arms — the exact single-lemma form `hInv`'s per-construct case invokes
once provenance hands it the block's compile fact.  The full `hInv` did NOT close
(the provenance quantifier + one missing successor leg remain — see frontier); no
red code, no sorries, `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still
**+0**.

### KEY FINDING: the per-construct couplings are already produced by `openStep_*_of_compileStmtFuel?` — the arm is a two-line collapse
A fan-out of the coupling substrate confirmed that each successor leg's *input*
coupling is produced, from the construct's **compile fact** + the entry
`StateRel`/`SourceFrameFits`, by an existing per-block lemma:
* `if`/branch — `InteractionBranchPreservation.Condition.openStep_if_of_compileStmtFuel?`
  (`InteractionBranchPreservation.lean:278`) yields
  `Rel (Condition.DoneRel (label supply 0) regular tokens bodyInput) (openRunCondition cond source) (openStep cfg entry target)`
  and pins `result.fallthrough? = some bodyInput` — exactly what
  `realizedWitness_of_branch_jump` consumes.
* `call`/pure — `InteractionCallPreservation.Call.openStep_entry_of_compileStmtFuel?`
  (`InteractionCallPreservation.lean:264`) reduces the call-site `openStep` to the
  silent `pure (.jump (ProcLabel.entry name) targetFinal)` and hands back the child
  `StateRel` — exactly what `realizedWitness_of_pure_jump` consumes.
* `returnDispatch` — `openStep_dispatch` (`InteractionCallPreservation.lean:747`);
  its supplier (`realizedWitness_of_dispatch_jump`,
  `InteractionRealizedWitnessSuccessor.lean:149`) *already* takes the frame-boundary
  facts directly, so the dispatch arm was already at this level (session 28).
So the `if`/`call` arms are each a two-line composition producer ∘ successor-leg;
no new frame model, no backward simulation.

### LANDED (green, axiom-clean): `EvmCompiler/Structured/InteractionConstructCoupling.lean`
Both `#print axioms` = `[propext, Classical.choice, Quot.sound]`; wired into
`EvmCompiler.Verification` (import after `InteractionBlockProvenance`).  Namespace
`EvmCompiler.Structured.InteractionConstructCoupling`.
* **`realizedWitness_of_if_compile`** (`:70`) — the compiled-`if` main-body/proc-body
  arm.  From the `if` compile fact `compileStmtFuel? (n+1) (.if_ cond body) … = some
  result`, `BlocksInProgram result cfg`, the entry `SourceFrameFits input …` +
  `StateRel source tokens target`, a concrete first jump `(next, state')`, and the
  target `LabelShape` at `result.fallthrough?` (the branch residual body shape),
  concludes `realizedWitness cfg next state'`.  Proof =
  `openStep_if_of_compileStmtFuel?` ∘ `realizedWitness_of_branch_jump`.
* **`realizedWitness_of_call_compile`** (`:135`) — the compiled-`call` arm.  From the
  callee lookup + the `.call name` compile fact + entry `StateRel` + arg split +
  `proc.WF`, a concrete first jump, the target `LabelShape` at `ProcLabel.entry name`,
  and the pushed child-frame `SourceFrameFits`, concludes `realizedWitness cfg next
  state'`.  Proof = `openStep_entry_of_compileStmtFuel?` ∘ `realizedWitness_of_pure_jump`.

These are precisely the per-construct discharges `hInv`'s proof runs at each reached
`if`/`call` main-body or proc-body entry: they consume the *compile fact*
(what provenance recovers at `e`) + the `realizedWitness` ingredients (`StateRel`/
`SourceFrameFits`, carried at the entry) + the target `LabelShape`, and emit the
child `realizedWitness`.  Together with `realizedWitness_of_dispatch_jump` (session 28,
already compile-fact-adjacent) and `programEnd_openStep_no_jump` (session 29,
vacuous), the per-entry ARM DISCHARGES of `block_category`'s case split are now
banked for `if`/`call`/dispatch/programEnd.

### THE FRONTIER: exactly two gates remain before `hInv` closes
1. **The `.code` (straight-line) arm's successor leg is NOT yet banked.**  A compiled
   `.code` statement lowers to a block with terminator `.jump regular`
   (`openStep_code_of_compileStmtFuel?`, `InteractionControlPreservation.lean:5127`,
   yields `Rel (OpenOutcome.OutcomeDoneRel result ctx regular source.returns tokens) …`).
   Under the WHOLE-PROGRAM `hInv` that `.jump regular` is the *sequential
   continuation* (not a fragment stop — the leaf `code_exec_realizing` collapses it
   via `contract.stops`, which is a fragment-local policy, NOT valid globally), so
   `hInv` must produce `realizedWitness cfg regular state'`.  There is currently NO
   `realizedWitness_of_regular_jump` sibling of the branch/pure/dispatch legs, and NO
   `jump_state_rel`-style extraction off `OutcomeDoneRel` for the regular outcome.
   The building block exists — `Rel.regular_elim_of_required_fallthrough`
   (`InteractionControlPreservation.lean:694`) gives, from an eliminated `OpenOutcome.Rel`
   on a `regular` outcome, `target = .jump regular targetState ∧ StateRel source
   tokens targetState ∧ SourceFrameFits expected …` — but it needs the `OutcomeDoneRel`
   first pushed through `Rel.executes_right` to a concrete `regular`/`.jump` outcome,
   i.e. a small `jump_state_rel_of_outcome` extraction (mirroring
   `Condition.jump_state_rel_of_rel`) then a one-line `realizedWitness_of_regular_jump`
   supplier.  CAVEAT for that extraction: `OpenOutcome.Rel` maps break/continue/leave
   source outcomes to `.jump` too, so the `.jump next state'` target does NOT by itself
   force a `regular` source outcome — the extraction must case on the source outcome and
   discharge the break/continue/leave arms as VACUOUS (a straight-line `.code` run only
   ever yields `Outcome.regular`/error — establish this from the code run's outcome
   shape, e.g. the `OutcomeDoneRel`/`openRunCondition_returns`-family facts), leaving the
   regular arm to `Rel.regular_elim_of_required_fallthrough`.  NEXT-SESSION FIRST STEP —
   bank these two (self-contained, no frame model): the `.code` arm is the last missing
   successor discharge.
2. **The provenance quantifier (the deep, unmoved gate).**  `of_openStep_invariant`
   needs the coupling suppliers invoked at an ARBITRARY reached `(e,t)` with only
   `realizedWitness cfg e t` in hand — i.e. the compile fact
   (`compileStmtFuel? … = some result` with `entry = e`) must be PRODUCED at each
   reached entry.  `block_category` gives the outer category; recovering *which
   statement* compiled to the block (its compile fact) is the `block_owner`
   decomposition — route 1's `RealizingBlockOwnerAt`/`block_owner_realizing`
   (`InteractionBoundedOwnerRealized.lean:358`), blocked since session 24 at the
   oracle-branching heads — or route 2's OIC-splice source-run coupling
   (`yulToNormalizedStackTypedCfgPrefixForward`,
   `OpenInteractionComposition.lean:695`), threading the source construct at each
   entry the run visits.  The coupling suppliers landed this session are what EITHER
   route feeds once the compile fact is in hand; they reduce the residual bulk to
   pure provenance (no more per-construct coupling glue for `if`/`call`, and, after
   gate 1, none for `.code` either).

### Next-session recipe
* First close gate 1: bank `jump_state_rel_of_outcome` (extract `StateRel`/`.jump
  regular` from `Rel (OutcomeDoneRel …) srcRun (openStep …)` + `Executes … (.jump)`,
  via `Rel.executes_right` + `Rel.regular_elim_of_required_fallthrough`) then
  `realizedWitness_of_regular_jump` (∘ `realizedWitness_of_stateRel`) then the
  `.code` supplier `realizedWitness_of_code_compile` (∘ `openStep_code_of_compileStmtFuel?`),
  mirroring this session's two suppliers.  Then the per-entry ARM discharges are
  complete for ALL compiled-construct categories.
* Then attack gate 2 (provenance) at the OIC splice per route 2: thread
  `yulToNormalizedStackTypedCfgPrefixForward` so each reached entry's compile fact is
  supplied, feeding `block_category` ⟶ the matching landed supplier
  (`realizedWitness_of_{if,call,code}_compile` / `realizedWitness_of_dispatch_jump`).
  Feed the resulting `hInv` to `of_openStep_invariant`; proceed to Step B.
* Do NOT add the swap arm to `peepholeBody` until the whole invariant is green.

### Status handed to session 31
Landed: `InteractionConstructCoupling.lean` (`realizedWitness_of_if_compile` :70,
`realizedWitness_of_call_compile` :135), green, axiom-clean, wired into
`EvmCompiler.Verification`.  `scripts/opt_harness.sh check` = OK (43 public theorems,
axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/
`compile_correct_creation` unchanged; delta +0.  The `hInv` per-entry ARM discharges
are now banked for `if`/`call`/dispatch/programEnd; frontier = (1) the `.code`
regular-jump successor leg (first, self-contained, recipe above) + (2) the deep
provenance quantifier (routes 1/2 unchanged).

## Session-31 update (2026-07-17): gate 1 CLOSED — the `.code` regular-jump leg trio landed green + axiom-clean (ALL per-arm suppliers now complete); gate 2 route DECIDED (static-provenance map) with evidence + first ROOT lemma banked

Session 31's mandate: (1) close gate 1 (the `.code` leg trio per §Session-30), then
(2) evaluate the two gate-2 provenance routes, write the choice + evidence, and land
what is cleanly greenable.  **Result: four green, axiom-clean commits closing gate 1
(`.code` extraction / successor / supplier + the source-regular helper), plus the
gate-2 route decision and its first green ROOT lemma.**  Gate 1 is DONE — the per-entry
ARM discharges of `block_category`'s case split are banked for ALL compiled-construct
categories.  Gate 2 (the deep provenance quantifier) remains the sole frontier before
`of_openStep_invariant` fires; its engine (the statement-list drill) is the next-session
bulk.  No red code, no sorries, `peepholeBody`/public spine UNTOUCHED ⇒ measured delta
still **+0**.

### GATE 1 CLOSED (green, axiom-clean): `EvmCompiler/Structured/InteractionCodeConstructCoupling.lean`
All `#print axioms` = `[propext, Classical.choice, Quot.sound]`; wired into
`EvmCompiler.Verification` (import after `InteractionConstructCoupling`).  Three
progressive commits (one per lemma) per the mandate:
* **`0dee8c29` — `jump_state_rel_of_outcome`** (`:64`, namespace
  `InteractionControlPreservation.OpenOutcome`) — the `.code`/regular extraction off
  the outcome-indexed `Rel (OutcomeDoneRel result ctx regular returns tokens) srcRun
  targetRun`.  Proof = `Rel.executes_right` → `cases`-`ok` →
  `Rel.regular_elim_of_required_fallthrough`.  CAVEAT discharged as designed: the
  break/continue/leave source outcomes also map to `.jump` under `OpenOutcome.Rel`,
  so the extraction takes `hSrcRegular : ∀ t o, Executes srcRun t (.ok o) → ∃ final,
  o = Outcome.regular final` (a straight-line `.code` run is regular-or-error) and the
  non-regular arms are vacuous.  The `.code`/regular sibling of
  `Condition.jump_state_rel_of_rel`.
* **`edd64915` — `realizedWitness_of_regular_jump`** (`:119`, namespace
  `InteractionRealizedWitnessSuccessor`) — the `.code` **successor leg**, sibling of
  `realizedWitness_of_{branch,pure,dispatch}_jump`.  Proof =
  `jump_state_rel_of_outcome` ∘ `realizedWitness_of_stateRel`.
* **`47e12553` — `realizedWitness_of_code_compile`** (`:205`, namespace
  `InteractionConstructCoupling`) + helper **`stmt_openRun_code_only_regular`**
  (`:162`) — the `.code` **supplier**, sibling of `realizedWitness_of_{if,call}_compile`.
  Proof = `Stmt.openStep_code_of_compileStmtFuel?`
  (`InteractionControlPreservation.lean:5127`) ∘ `realizedWitness_of_regular_jump`,
  discharging `requireFallthrough?` from the `.code` compile fact
  (`components_of_compileStmtFuel?_code` ⟶ `fallthrough? = some output`, then
  `requireFallthrough?_eq_some_iff.mpr`) and `hSrcRegular` from the helper.  The
  helper proves any `.ok` outcome of `Stmt.openRun … (.code code)` is `Outcome.regular`
  (`Stmt.openRun` unfolds to `bind (Code.openRun code source) (fun final => pure
  (.regular final))`; `Executes.bind_cases` + the `pure`-done leaf).

**The per-entry ARM discharges of `block_category`'s case split are now complete for
ALL categories:** `realizedWitness_of_if_compile` / `_call_compile` / `_code_compile`
(main-body / proc-body compiled constructs), `realizedWitness_of_dispatch_jump`
(dispatch), `programEnd_openStep_no_jump` (programEnd, vacuous).  Every arm now
consumes ONLY the block's *compile fact* (+ the `realizedWitness` `StateRel`/
`SourceFrameFits` carried at the entry + the successor `LabelShape`).

### GATE 2 ROUTE DECISION (evidence-backed): the STATIC-PROVENANCE map for the compile-fact recovery
The mandate asked to evaluate two routes and pick before implementing.

* **Route 2 (source-run coupling at the OIC splice).** Thread
  `yulToNormalizedStackTypedCfgPrefixForward`
  (`Compiler/OpenInteractionComposition.lean:695`) — which yields a
  `ForwardRel … (Yul exec …) (openRunNPrefix cfg … entryLabel …)` *and the
  `GeneratedContext generated`* in scope — so each reached entry's construct + compile
  fact (and, for dispatch, its `RunState.returns`/`popReturn?` frame facts) is supplied
  from the source run.  Naturally supplies the dispatch runtime frame facts (as
  `openRun_call_exec_under` does via `Rel.regular_elim_of_required_fallthrough`), but
  couples the whole `AllEntriesRealized` proof to the giant source→cfg simulation.
* **Route static (induction over the GENERATION, not the run).** Every block in the cfg
  is generated from some construct; a static map «cfg block label ↦ its compile fact»
  is derived from `GeneratedContext.mainCompile`/`procsCompile`
  (`Core.lean:3395/3400`) + a structural drill over
  `compileBlock?`→`compileStmtListFuel?`→`compileStmtFuel?`
  (`TypedCfgCompiler.lean:377/383/407`).  Decoupled from the run and from fuel; reused
  at EVERY reached entry via `block_category`'s `findBlock?` witness.

**Chosen: static-provenance for the compile-fact recovery.**  Evidence it is strictly
easier for the compile-fact part: the if/call/code suppliers need only the compile
fact + the entry `StateRel`/`SourceFrameFits` (both carried by `realizedWitness`) +
the successor `LabelShape` (already static via `LabelShape.of_compileStmtFuel?` /
`_of_compileStmtListFuel?`, used at `InteractionOwnerPreservation.lean:1575`).  None of
those need the run.  **Residual (deferred, NOT static): the DISPATCH arm's frame-boundary
facts** `hPop`/`hAttach`/`hRetc` are runtime (`bodyState.popReturn?` etc.) and are NOT
derivable from the cfg generation; they must come from the `realizedWitness` `StateRel
bodyState (site.token :: tokens) t` at the exit block (a StateRel⟶frame-facts
derivation), or fall back to route 2 for that single arm.  So the plan is: static
provenance for main/proc/code/if/call; a localized StateRel⟶frame-facts derivation
(or route-2 splice) for dispatch.

### LANDED (green, axiom-clean): `EvmCompiler/Structured/InteractionBlockProvenanceRoot.lean`
`#print axioms` = `[propext, Classical.choice, Quot.sound]`; wired into
`EvmCompiler.Verification` (import after `InteractionCodeConstructCoupling`).
* **`c93ffaf5` — `main_stmtList_provenance`** (`:52`, namespace
  `TypedCfgPreservation.Program.GeneratedContext`) — the ROOT of the static drill for
  the main-body category.  From `block ∈ context.main.blocks` (the first arm of
  `block_category`) concludes `compileStmtListFuel? (blockFuel source.body)
  source.body.stmts { procs := source.procs } 0 entryLabel Shape.caller
  ProcLabel.programEnd = some context.main ∧ block ∈ context.main.blocks` — the exact
  entry point the eventual statement-list provenance drill inducts on.  Proof =
  `context.mainCompile` + the `compileBlock?`/`compileBlockFuel?` unfold.

### THE FRONTIER: gate 2's ENGINE — the statement-list provenance drill (next-session bulk)
With `main_stmtList_provenance` (main root) landed, the remaining gate-2 work is the
**structural drill** that, from `compileStmtListFuel? fuel stmts ctx supply entry input
regular = some result` and `block ∈ result.blocks`, recovers the *specific* source
statement whose `compileStmtFuel?` has `entry = block.label` (drilling through nested
`if`/`switch`/`for`/`call` bodies via `compileBlockFuel?`/`compileStmtListFuel?` until
the entry aligns).  It is a mutual induction mirroring `block_owner`'s generation
skeleton (`InteractionOwnerPreservation.lean:1502`) MINUS the semantic content — the
`head :: bodyResult.blocks` / `head.append tail` cases split block membership across the
head construct and its compiled tail/body.  Once it lands, `hInv`'s proof is:
`block_category` → (main) `main_stmtList_provenance` → drill → `compileStmtFuel?` fact →
`realizedWitness_of_{if,call,code}_compile`; (proc) proc root (analogous, via
`procsCompile`) → drill → same suppliers; (dispatch) the localized StateRel⟶frame-facts
derivation → `realizedWitness_of_dispatch_jump`; (programEnd) `programEnd_openStep_no_jump`.
Feed the resulting `hInv` to `of_openStep_invariant`; then Step B.

### Next-session recipe
* Land the statement-list provenance drill (structural induction over
  `compileStmtListFuel?`/`compileStmtFuel?`/`compileBlockFuel?`), concluding the
  entry-aligned `compileStmtFuel? … entry = block.label … = some subResult` with
  `block = subResult.blocks.head`.  Bank the proc-body root
  (`proc_*_provenance` via `procsCompile`/`ProcFragment`) alongside.
* Then assemble `hInv` per the case split above (dispatch: add the
  `StateRel (…, site.token :: tokens, …) ⟶ popReturn?/attachReturns?/retc` derivation,
  or splice route 2 for that arm only), feed `of_openStep_invariant`, proceed to Step B
  (`openRunNPrefix_peephole_congr_of_source`).
* Do NOT add the swap arm to `peepholeBody` until the whole invariant is green.

### Status handed to session 32
Gate 1 CLOSED.  Landed this session: `InteractionCodeConstructCoupling.lean`
(`jump_state_rel_of_outcome` :64, `realizedWitness_of_regular_jump` :119,
`stmt_openRun_code_only_regular` :162, `realizedWitness_of_code_compile` :205) +
`InteractionBlockProvenanceRoot.lean` (`main_stmtList_provenance` :52), all green,
axiom-clean, wired into `EvmCompiler.Verification`.  Commits `0dee8c29` / `edd64915`
/ `47e12553` / `c93ffaf5`.  `scripts/opt_harness.sh check` = OK (43 public theorems,
axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/
`compile_correct_creation` unchanged; delta +0.  The `hInv` per-entry ARM discharges
are complete for ALL categories; gate 2's route is DECIDED (static-provenance) with the
main root banked; the sole remaining frontier is the statement-list provenance drill
(+ the dispatch StateRel⟶frame-facts derivation), the next-session bulk before
`of_openStep_invariant` → Step B.

## Session-32 update (2026-07-17): the DRILL substrate is COMPLETE — the one-layer membership dichotomies for ALL FIVE generation functions are banked green + axiom-clean; the assembled capstone is precisely teed up (its total-classification predicate should be co-designed with session-33's hInv case split)

Session 32's mandate: build THE DRILL (the static structural induction over
`compileStmtListFuel?`/`compileStmtFuel?`/`compileBlockFuel?` recovering the
per-entry compile fact), banking the green pieces (per-constructor emission-set
lemmas → membership-dichotomy lemmas → assembled drill).  **Result: three green,
axiom-clean commits landing the COMPLETE one-layer membership-dichotomy substrate —
12 lemmas spanning all five generation functions.**  This is the reusable engine the
assembled descent (and `block_category`'s consumer) chains.  The assembled capstone
theorem was scoped OUT this session on purpose (see "Why the capstone waits" below).
`peepholeBody`/public spine UNTOUCHED ⇒ measured delta still **+0**.

### LANDED (green, axiom-clean): `EvmCompiler/Structured/InteractionBlockProvenanceDrill.lean`
All `#print axioms` = `[propext, Classical.choice, Quot.sound]`; wired into
`EvmCompiler.Verification` (import after `InteractionBlockProvenanceRoot`).  Three
progressive commits.  Namespace `TypedCfgPreservation.BlockProvenanceDrill`
(`open TypedCfgCompiler`).

* **`0ff8bcc8` — Phase 1a (statement-list dichotomies):**
  - `mem_of_compileStmtListFuel?_nil` (`:50`) — the empty statement list emits the
    single entry join block (`{label:=entry, body:=[], term:=.jump regular}`); every
    member IS that block.
  - `mem_of_compileStmtListFuel?_cons` (`:77`) — a member of `stmt :: rest`'s
    emission lands in the head statement's emission OR the tail's, each with the
    corresponding compile fact exposed for recursion.  Built on
    `Block.components_of_compileStmtListFuel?_cons` (`Core.lean:2162`).
* **`829008df` — Phase 1b (per-constructor statement dichotomies):**
  - `mem_of_compileStmtFuel?_code` (`:121`), `_terminal` (`:139`) — leaf heads
    (`block.label = entry`).
  - `mem_of_compileStmtFuel?_if` (`:158`) — entry head vs branch-body member, the
    latter with the `compileBlockFuel?` body fact.
  - `mem_of_compileStmtFuel?_switch` (`:188`) — head vs `compileCasesFuel?` fragment
    vs `compileDefaultFuel?` fragment, each with its compile fact.
  - `mem_of_compileStmtFuel?_for` (`:234`) — `compileBlockFuel?` init fragment /
    loop-cond head (`block.label = LabelSupply.label supply 0`) / body fragment /
    post fragment, each recursive fragment with its `compileBlockFuel?` fact.
  All built on the existing `TypedCfgCompilerFacts.{Stmt,Switch,Loop}.components_of_compileStmtFuel?_*`.
* **`9d0f632b` — Phase 1c (block/cases/default connectors):**
  - `stmtList_of_compileBlockFuel?` (`:346`) — the vertical-descent connector:
    `compileBlockFuel? (f+1) body … = compileStmtListFuel? f body.stmts …`.
  - `mem_of_compileCasesFuel?_nil` (`:361`) — empty case list emits no blocks
    (membership vacuous).
  - `mem_of_compileCasesFuel?_cons` (`:379`) — test block (`switchTestLabel base
    idx`) / case-entry block (`switchCaseLabel base idx`) / case-body fragment /
    remaining-cases, each recursive fragment with its compile fact.  (Takes `hHead`/
    `hPopType` per `Switch.components_of_compileCasesFuel?_cons`.)
  - `mem_of_compileDefaultFuel?_none` (`:416`) — absent default is the single entry
    `pop` block.
  - `mem_of_compileDefaultFuel?_some` (`:435`) — entry `pop` block vs compiled
    default body fragment.

**The one-layer membership dichotomy is now banked for EVERY generation function:**
`compileStmtListFuel?` (nil/cons), `compileStmtFuel?` (code/terminal/if/switch/for —
brk/cont/leave/call are leaf singletons already covered by
`components_of_compileStmtFuel?_{brk,cont,leave,call}` in `TypedCfgCompilerFacts`),
`compileBlockFuel?` (connector), `compileCasesFuel?` (nil/cons), `compileDefaultFuel?`
(none/some).  Each recursive-fragment disjunct returns the subfragment's OWN compile
fact, so the assembled descent chains dichotomy→fragment-fact→dichotomy with no
re-derivation.

### THE CAPSTONE frontier: the assembled descent (next-session bulk)
The assembled drill is the strong-induction-on-fuel fixpoint of the substrate,
mirroring the EXISTING generation skeleton `activeResult_of_compile*`
(`TypedCfgCompilerActive.lean:77-508`) EXACTLY — a `mutual`/strong-induction over the
five functions (`compileStmtListFuel?`/`compileStmtFuel?`/`compileBlockFuel?`/
`compileCasesFuel?`/`compileDefaultFuel?`) with a *provenance* payload replacing
`ActiveResult`.  At each membership split (already performed inline by `activeResult`,
now also as the standalone Phase-1 lemmas), a block is either the ENTRY-ALIGNED HEAD of
the current `compileStmtFuel?` (discharge with the in-scope `hCompile`) or a member of
a named recursive subfragment (recurse via IH) or a **non-head machinery/join block**
(for-loop-cond, switch test, switch case-entry, default `pop`, nil-join).

### Why the capstone waits (design blocker, not a proof blocker)
The descent's *proof* is mechanical from the substrate + the `activeResult` skeleton.
The open question is the **conclusion predicate's exact shape**, and it is dictated by
what session-33's `hInv` case split consumes, NOT by the drill:
* The if/call/code arms want the ENTRY-ALIGNED HEAD compile fact
  (`∃ cf stmt ctx supply input regular sub, compileStmtFuel? (cf+1) stmt ctx supply
  block.label input regular = some sub ∧ sub.blocks.head? = some block`), then
  `cases stmt` → `realizedWitness_of_{if,call,code}_compile`.  This is TRUE and
  dischargeable for every `compileStmtFuel?` head (code/if/switch/call/brk/cont/leave/
  terminal — head? = the entry block).
* **But the for-loop-cond, switch test, switch case-entry, default-`pop`, and
  nil-join blocks are NOT `compileStmtFuel?` heads** (their labels are
  `LabelSupply.label supply 0/1/2`, `switchTestLabel`, `switchCaseLabel`, the default
  entry, `restLabel`) and ARE reachable jump targets (e.g. the switch head jumps to
  `casesEntryLabel supply 0 cases = switchTestLabel base 0`).  So the total
  classification predicate MUST carry machinery disjuncts, and those disjuncts need
  the ENCLOSING switch/for compile fact (to expose the successor labels the hInv's
  successor legs consume) — i.e. their precise shape depends on the (not-yet-written)
  switch/for successor suppliers.  Committing a guessed predicate now risks a large
  wrong artifact; the substrate is predicate-agnostic and lands the mechanical 80%.

### Next-session recipe (capstone assembly)
1. First decide the machinery successor story: either (a) add switch/for successor
   suppliers (analogues of `realizedWitness_of_{branch,dispatch}_jump` for the
   `.jump`/`.jumpi` terminators of test/loop/case-entry blocks), or (b) show those
   machinery blocks' `openStep` jumps land on blocks whose `realizedWitness` is
   already carried — THEN the machinery disjuncts' shape is fixed.
2. Define the total predicate `BlockGenShape block :=`
   `IsHead block ∨ (for-loop-cond) ∨ (switch-test) ∨ (switch-case-entry) ∨
   (default-pop) ∨ (nil-join)` with `IsHead block := ∃ cf stmt ctx supply input
   regular sub, compileStmtFuel? (cf+1) stmt ctx supply block.label input regular =
   some sub ∧ sub.blocks.head? = some block`; the five machinery disjuncts threaded
   with the enclosing compile fact per step 1.
3. Prove the 5-function `mutual` (copy `activeResult`'s structure verbatim, swap the
   payload).  Each arm: apply the matching Phase-1 dichotomy
   (`mem_of_compileStmtFuel?_*` / `mem_of_compileCasesFuel?_*` /
   `mem_of_compileDefaultFuel?_*` / `stmtList_of_compileBlockFuel?` /
   `mem_of_compileStmtListFuel?_{nil,cons}`) — head → `IsHead` from `hCompile`;
   fragment → IH; machinery/join → the substrate lemma's own conclusion.
   Termination is on fuel (identical to `activeResult`).
4. Then the proc-body root (item 2, analogue of `main_stmtList_provenance` via
   `procsCompile`/`ProcFragment`) and the dispatch StateRel⟶frame-facts residual
   (item 3), then assemble `hInv` and feed `of_openStep_invariant` → Step B.

### Status handed to session 33
Drill substrate COMPLETE.  Landed this session:
`InteractionBlockProvenanceDrill.lean` — 12 green, axiom-clean membership-dichotomy
lemmas (Phase 1a/1b/1c above), wired into `EvmCompiler.Verification` after
`InteractionBlockProvenanceRoot`.  Commits `0ff8bcc8` / `829008df` / `9d0f632b`.
`scripts/opt_harness.sh check` = OK (43 public theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/
`compile_correct_creation` unchanged; delta +0.  The remaining frontier is the
assembled capstone descent (mechanical from the substrate once its conclusion
predicate is pinned to the switch/for successor story) + the proc-body root + the
dispatch residual, before `of_openStep_invariant` → Step B.

## Session-33 update (2026-07-17): the MACHINERY successor-supplier family is COMPLETE (for-cond + switch-test + case-entry/default-pop + nil-join, all green + axiom-clean); two capstone-blocking DESIGN findings pinned — the switch head reuses the `.code` supplier (no new leg), and the proc-entry ADAPTER is a 6th reachable machinery block the §Session-32 sketch missed (needs its own shape-transporting supplier)

Session 33's mandate: settle the inherited dirty file, land the remaining machinery
successor arms, then attack the assembled capstone descent.  **Result: the machinery
successor-supplier family is now COMPLETE — four green, axiom-clean suppliers keyed on
each machinery block's shape** (three inherited from the session-33 worker + the
nil-join settled this handoff), plus **two concrete design findings that correct and
sharpen the §Session-32 capstone predicate before it is committed** (exactly the "large
wrong artifact" the §Session-32 note warned to avoid).  The capstone mutual itself was
NOT written this session: the second finding (the proc-entry adapter) reveals the
predicate needs a 6th machinery disjunct + a new shape-transporting supplier, so
committing a 5-disjunct predicate now would have been the wrong artifact.  No red code,
no sorries, `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still **+0**.

### LANDED (green, axiom-clean): `EvmCompiler/Structured/InteractionMachineryCoupling.lean`
All `#print axioms` = `[propext, Classical.choice, Quot.sound]`; the module is wired
into `EvmCompiler.Verification` (import after `InteractionConstructCoupling`; it also
imports `InteractionSwitchPreservation`).  Namespace
`EvmCompiler.Structured.InteractionMachineryCoupling`
(`open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness
realizedWitness_of_stateRel)`).  Every supplier consumes ONLY the block's
static shape/type facts (its `findBlock?` or membership fact + `Instr.type?`/`head?`/
condition facts) plus the `realizedWitness` runtime ingredients carried at the entry
(`StateRel` + `SourceFrameFits`) + the successor `LabelShape` — i.e. exactly what the
capstone's machinery disjuncts will hand the `hInv` case split.

* **`81d18660` (inherited) — `realizedWitness_of_condBlock_jump`** (`:67`) — the
  condition-block (`.jumpi` over `Code.toCfg cond`) supplier.  Covers the
  **for-loop-cond** machinery block (`LabelSupply.label supply 0`) and subsumes the
  `if`-condition head.  Keyed on `hFind` + `hType : Code.type? cond input = some output`
  + `hSource : requireSourceWords? 1 output = some ()`.  Proof =
  `Condition.openRunCondition_jumpi_toCfg` ∘ `realizedWitness_of_branch_jump`.
* **`3ce4b586` (inherited) — `realizedWitness_of_test_jump`** (`:131`) — the **switch
  test** block (`[.dup 0, .push caseValue, .prim .eq]` + `.jumpi caseLabel nextTest`).
  The scrutinee is RETAINED (a pure target-side comparison), so the child `StateRel`
  is at the SAME source and the child fits equal the entry fits (`hFits` reused).
  Proof = `Switch.openStep_test` ∘ `realizedWitness_of_stateRel`.
* **`3ce4b586` (inherited) — `realizedWitness_of_pop_jump`** (`:183`) — the **switch
  case-entry / absent-default `pop`** block (`[.pop]` + `.jump label`).  Removes the
  scrutinee; child `StateRel` at the popped source, child fits taken as a hypothesis
  (mirroring `realizedWitness_of_pure_jump`).  Proof = `Switch.openStep_pop_jump` ∘
  `realizedWitness_of_stateRel`.
* **`25345e90` (THIS session — the settled dirty file) —
  `realizedWitness_of_join_jump`** (`:235`) — the **nil-join** block
  (`{ body := [], output := input, term := .jump exitLabel }`, emitted by
  `compileStmtListFuel? … [] …`).  A pure identity jump: its `openStep` reduces to
  `pure (.jump exitLabel target)` with state unchanged, so the child
  `StateRel`/`SourceFrameFits` ARE the entry's.  Proof = the inline `openStep` join
  reduction (`Control.Block.run`/`runBody` + `bind_done`) ∘
  `InteractionRealizedWitnessSuccessor.realizedWitness_of_pure_jump`.  The prior
  session-33 worker had left this uncommitted-but-green; reviewed, built green
  (1159 jobs), `#print axioms` clean, committed.

**The per-terminator machinery successor discharges are now banked for all five blocks
the §Session-32 note listed** (for-loop-cond, switch-test, switch-case-entry,
default-`pop`, nil-join), joining the compile-fact suppliers
`realizedWitness_of_{if,call,code}_compile` (sessions 30/31) and
`realizedWitness_of_dispatch_jump` (session 28), and the vacuous
`programEnd_openStep_no_jump` (session 29).

### KEY FINDING 1 — the switch HEAD is a `.code` block in disguise; NO new supplier needed
The `.switch` lowering (`TypedCfgCompiler.lean:444`) emits its head as
`mkCodeBlock? entry input scrutinee (.jump firstTest)` — **byte-for-byte the block
`compileStmtFuel? (f+1) (.code scrutinee) ctx supply entry input firstTest` produces**
(a code block over `Code.toCfg scrutinee` with terminator `.jump firstTest`; only the
"regular" target differs — `firstTest` instead of the code's `regular`).  So the
capstone's `head` arm for `.switch` synthesises a `.code scrutinee` compile fact at
`entry = block.label` (with `regular := firstTest`) and reuses
`realizedWitness_of_code_compile` (session 31) verbatim.  The switch head is therefore
NOT a missing successor leg — it collapses into the `.code` supplier.  (Cross-check:
`activeResult`'s `.switch` head case treats the head identically to a code block.)

### KEY FINDING 2 — the proc-entry ADAPTER is a 6th reachable machinery block the §Session-32 sketch MISSED
The §Session-32 machinery list (for-cond / test / case-entry / default-pop / nil-join)
is INCOMPLETE for the proc-body category.  `ProcFragment.route`
(`Core.lean:2969`) has TWO routes: the DIRECT route (`entry = ProcLabel.entry`, no
adapter) and the ADAPTER route, which emits an extra block
`mkBlock? (ProcLabel.entry proc.name) (Shape.procEntry proc) [.relabel input]
(.jump (ProcLabel.body proc.name))` — a **`.relabel`-then-`.jump` block** at
`ProcLabel.entry proc.name`, reachable from the call dispatch.  It is NOT part of any
`compileBlock? proc.body …` result (it is prepended in `procFragment_of_lowerProcBodiesWithShapes?`,
`Core.lean:3163/3290`), so the proc-body provenance drill CANNOT reach it via the
statement-list recursion — it must be classified as its own machinery disjunct.

Its successor story is ALREADY proved silent by
`InteractionCallPreservation.openRunNResult_procEntry`
(`InteractionCallPreservation.lean:651`): the adapter's `openStep` reduces to
`pure (.jump (ProcLabel.body proc.name) state)` with the runtime state UNCHANGED
(relabel is a pure retyping; `openRunBody_eq_done_of_forall_not_prim` + `runTerm`).
So an `realizedWitness_of_adapter_jump` supplier is a `pure`-jump composition like
`realizedWitness_of_join_jump`.  **CAVEAT (why it was NOT rushed this session):** the
relabel changes the *shape* (`Shape.procEntry proc` → `input`), so the child
`SourceFrameFits`/`StateRel` handed to the successor `ProcLabel.body` block must be
transported ACROSS the relabel (the successor expects `output`/`input`, not the entry
`blockInput`).  That shape-transport (a `SourceFrameFits`/`StateRel`-across-`.relabel`
lemma; relabel preserves the runtime stack, so it should be a `Instr.type? .relabel`
+ `sourceLength` bookkeeping) is the one genuinely-new obligation — a self-contained
next-session first step, NOT a rush-it-now composition.

### THE REFINED CAPSTONE PREDICATE (corrected by findings 1–2; pin BEFORE writing the mutual)
`BlockGenShape block :=`
* `IsHead block` — `∃ cf stmt ctx supply input regular sub, compileStmtFuel? (cf+1)
  stmt ctx supply block.label input regular = some sub ∧ block ∈ sub.blocks ∧
  block.label = <that entry>` (covers code / terminal / call / if-head / switch-head
  [finding 1: dispatch `.switch` head to the `.code scrutinee` fact] / brk / cont /
  leave).  hInv arm: `cases stmt` → `realizedWitness_of_{if,call,code}_compile`
  (`.switch` head → `_code_compile` with `regular := firstTest`; brk/cont/leave/terminal
  emit no `.jump` successor — vacuous like programEnd), OR
* for-loop-cond disjunct (carry `cond`/`input`/`output` + `hType`+`hSource`) →
  `realizedWitness_of_condBlock_jump`, OR
* switch-test disjunct (carry `valueShape`/`slot`/`caseValue`/labels + `head?`) →
  `realizedWitness_of_test_jump`, OR
* switch-case-entry / default-`pop` disjunct (carry `input`/`output` + `Instr.type? .pop`)
  → `realizedWitness_of_pop_jump`, OR
* nil-join disjunct (carry `input`/`exitLabel`) → `realizedWitness_of_join_jump`, OR
* **proc-entry-adapter disjunct (NEW, finding 2; carry `input`/`output` +
  `Instr.type? (.relabel input)` + the relabel shape-transport) →
  `realizedWitness_of_adapter_jump` (to be written).**

The machinery disjuncts carry only the block's OWN shape + static type facts (NOT the
enclosing compile fact — the §Session-32 worry that they "need the enclosing switch/for
compile fact to expose the successor labels" is resolved: the successor `LabelShape` is
a SEPARATE `hInv` hypothesis, supplied from the destination block's `realizedWitness` /
a static `LabelShape.of_*` lemma, so the disjuncts stay local to the block).

### THE FRONTIER (sharpened)
1. **The proc-entry-adapter supplier `realizedWitness_of_adapter_jump`** + its
   `SourceFrameFits`/`StateRel`-across-`.relabel` transport lemma.  Self-contained;
   the `openStep` reduction is already in `openRunNResult_procEntry`
   (`InteractionCallPreservation.lean:696–740`).  NEXT-SESSION FIRST STEP.
2. **The proc-body provenance ROOT + membership inversion.**  `main_stmtList_provenance`
   (session 31) was a one-liner because `context.main` is a single result; the proc
   analogue needs a MEMBERSHIP INVERSION over `lowerProcBodiesWithShapes?` — from
   `block ∈ context.procBlocks` recover `∃ name proc, lookup? name source.procs =
   some proc ∧ (block = the proc-entry adapter [finding 2] ∨ block ∈ (compileBlock?
   proc.body …).blocks)`.  This is the reverse of `procFragment_of_lowerProcBodiesWithShapes?`
   (`Core.lean:3049`); mirror its induction (adapter / no-adapter × shape-present /
   absent splits) tracking `procBlocks = adapter? :: bodyResult.blocks ++ tailBlocks`.
   The adapter member goes to the adapter disjunct; the body member feeds the drill.
3. **The assembled capstone mutual** — the 5-function strong-induction over
   `compileStmtListFuel?`/`compileStmtFuel?`/`compileBlockFuel?`/`compileCasesFuel?`/
   `compileDefaultFuel?` (copy `activeResult_of_compile*`,
   `TypedCfgCompilerActive.lean:77–508`, swap the `ActiveResult` payload for
   `BlockGenShape`), each arm applying the matching Phase-1 dichotomy
   (`InteractionBlockProvenanceDrill.lean`).  NOTE: the machinery arms of the mutual
   must call `components_of_compileStmtFuel?_{for,switch}` DIRECTLY (not the lossy
   `mem_of_compileStmtFuel?_{for,switch}`, which discard the block shape + type facts)
   to retain the `Code.toCfg cond`/`.jumpi` shape and `hType`/`hSource` the machinery
   disjuncts carry.  Same for the switch test/case-entry shapes via
   `components_of_compileCasesFuel?_cons`.
4. **The dispatch StateRel⟶frame-facts residual** (unchanged from §Session-31): the
   dispatch arm's `hPop`/`hAttach`/`hRetc` are runtime, derived from the exit block's
   `realizedWitness` `StateRel bodyState (site.token :: tokens) t`, or route-2 splice.

### Next-session recipe
1. Bank `realizedWitness_of_adapter_jump` (+ the `.relabel` shape-transport) — the
   only genuinely-new supplier, self-contained (openStep reduction already proved).
2. Bank the proc-body root membership inversion (frontier item 2).
3. Pin `BlockGenShape` (above; six disjuncts), prove the 5-function mutual
   (frontier item 3), banking green.
4. Then the dispatch residual (item 4), assemble `hInv` via `block_category` →
   {main root / proc root} → mutual → matching supplier ; dispatch → frame-facts →
   `realizedWitness_of_dispatch_jump` ; programEnd → `programEnd_openStep_no_jump`.
   Feed `of_openStep_invariant`; proceed to Step B
   (`openRunNPrefix_peephole_congr_of_source`).
* Do NOT add the swap arm to `peepholeBody` until the whole invariant is green.

### Status handed to session 34
MACHINERY successor-supplier family COMPLETE.  Landed / settled this session:
`InteractionMachineryCoupling.lean` — `realizedWitness_of_condBlock_jump` (:67,
`81d18660`), `_test_jump` (:131, `3ce4b586`), `_pop_jump` (:183, `3ce4b586`),
`_join_jump` (:235, `25345e90` — dirty file settled green THIS session), all green,
axiom-clean, wired into `EvmCompiler.Verification`.  `scripts/opt_harness.sh check` =
OK (43 public theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` unchanged; delta +0.  Two design findings
pin the capstone predicate: (1) the switch head reuses `_code_compile` (no new leg);
(2) the proc-entry adapter is a 6th machinery block needing `realizedWitness_of_adapter_jump`
(openStep already silent via `openRunNResult_procEntry`, caveat = `.relabel`
shape-transport).  Frontier = adapter supplier → proc-body root inversion → the
assembled 5-function capstone mutual → dispatch residual, before
`of_openStep_invariant` → Step B.

## Session-34 update (2026-07-19): frontier items 1 & 2 LANDED (adapter supplier + proc-body root inversion), the terminal-arm vacuity LANDED (successor-discharge family now COMPLETE for every reachable block category), and TWO concrete corrections to the §Session-33 capstone predicate pinned before the mutual was written

Session 34's mandate: adapter supplier → proc-body root inversion → the assembled
capstone mutual → dispatch residual.  **Result: the two self-contained "next-session
first steps" (frontier items 1 & 2) are banked green + axiom-clean, PLUS the terminal
vacuity lemma that completes the discharge family; the capstone mutual itself was NOT
written — two predicate CORRECTIONS discovered while nailing down the arms show the
§Session-33 6-disjunct sketch is wrong in two places, so committing that predicate now
would have been the "large wrong artifact" the §Session-32/33 notes warn against.**
No red code, no sorries; `peepholeBody`/public spine UNTOUCHED ⇒ measured delta still
**+0**.

### LANDED (green, axiom-clean) — all `#print axioms = [propext, Classical.choice, Quot.sound]`
* **`d90b60e0` — `realizedWitness_of_adapter_jump`** (`InteractionMachineryCoupling.lean`,
  after `_join_jump`).  The proc-entry ADAPTER block (finding 2, §Session-33):
  `{ input := blockInput, body := [.relabel relabelTarget], output, term := .jump
  bodyLabel }`.  Its `openStep` reduces silently to `pure (.jump bodyLabel target)`
  (state unchanged — the `.relabel` runs no primitive; mirrors the reduction inside
  `openRunNResult_procEntry`, `InteractionCallPreservation.lean:696–740`), then
  `realizedWitness_of_pure_jump` closes it.  **Design resolution of the §Session-33
  caveat:** `StateRel` mentions no shape, so it needs NO relabel transport (carried
  from the entry directly, like `_join_jump`).  `SourceFrameFits` is NOT preserved
  across a relabel in general — `relabelCompatible` (`Syntax.lean:120`) requires equal
  length + equal tail + `slotsAgree`, but `slotsAgree` lets a `.word` slot match any
  slot, so `sourceView`/`returnTokenDepth?` (hence `sourceLength`) can differ.  So —
  exactly as `_pop_jump`/`_pure_jump` — the supplier takes the child fits at the
  SUCCESSOR shape (`hFits : SourceFrameFits output …`) as a hypothesis; the concrete
  transport (at `output = relabelTarget = fragment.input`, since a type-checking
  relabel returns `some target`, `Typing.lean:51`) is discharged at capstone assembly.
  NO standalone `.relabel` `SourceFrameFits` transport lemma was banked because none is
  true in general — that part of the §Session-33 frontier was mis-scoped.
* **`ccad028e` — `mem_procBlocks_provenance` + `GeneratedContext.procBlocks_provenance`**
  (`InteractionProcBlockProvenance.lean`, NEW module, wired into
  `EvmCompiler.Verification`).  The proc-body root (frontier item 2): the reverse of
  `procFragment_of_lowerProcBodiesWithShapes?` (`Core.lean:3049`).  From
  `block ∈ context.procBlocks` recover the generating `proc` (`∈ source.procs` — see
  NOTE) and classify: either `block ∈ (compileBlock? proc.body …).blocks` (the body
  drill entry, analogous to `main_stmtList_provenance`) or `block` = that proc's entry
  ADAPTER (`mkBlock? (ProcLabel.entry proc.name) … = some block`).  Mirrors the forward
  induction (adapter/no-adapter × shape-present/absent) over
  `lowerProcBodiesWithShapes?`, tracking `procBlocks = body.blocks ++ tailBlocks` with
  `body.blocks = compiled.blocks` or `adapter :: compiled.blocks`
  (`TypedCfgCompiler.lean:677`).  **NOTE (design choice):** the lemma surfaces
  `proc ∈ procs` (List.Mem), NOT a `ProcList.lookup?` fact.  A block in the *tail*
  belongs to a proc in `rest`, but if its name collided with `head.name` the
  `lookup?` would return `head`, not the true generator — so `lookup?` is UNPROVABLE
  from block membership without a global proc-name-uniqueness invariant.  `∈` is always
  liftable through the induction and suffices for both consumers (the adapter supplier
  is shape-generic; the body drill consumes only the compile fact).
* **`3dc73f63` — `halt_openStep_no_jump`** (`InteractionMachineryCoupling.lean`, end).
  The `.terminal kind` block `{ input, body := [], output := input, term := .halt kind }`
  (`TypedCfgCompiler.lean:553`): its `openStep` = `.done (runTermChecked input
  (.halt kind) target)`, always `.ok (.halt …)` or `.error .StaticModeViolation`
  (static `selfdestruct`), NEVER `.ok (.jump …)`, so it can't `Executes`-produce a
  jump.  General sibling of `programEnd_openStep_no_jump`.  **This closes the last
  reachable-block category — the successor-discharge family is now COMPLETE.**

### KEY CORRECTION 1 — brk/cont/leave are NOT vacuous; they are nil-join blocks (reuse `_join_jump`, NO new supplier)
The §Session-33 predicate sketch (line ~4059) lumped "brk/cont/leave/terminal emit no
`.jump` successor — vacuous like programEnd" into the `IsHead` arm.  **Wrong for
brk/cont/leave.**  `compileStmtFuel?` for `.brk`/`.cont`/`.leave`
(`TypedCfgCompiler.lean:507–536`) emits `mkBlock? entry input [] term` where
`term = checkedJumpOrInvalid … input = .jump <break/continue/leave label>` (only when
`input = expected`, so `output = input`).  That is **byte-for-byte the nil-join shape**
`{ input, body := [], output := input, term := .jump exitLabel }` — already discharged
by `realizedWitness_of_join_jump` (session 33).  So in the capstone mutual the
brk/cont/leave arms emit the **nil-join disjunct** directly (carrying `input` +
the target label), NOT a head compile-fact.  Only `.terminal` is truly vacuous
(it emits `.halt`, `TypedCfgCompiler.lean:553` — closed by `halt_openStep_no_jump`
this session).

### KEY CORRECTION 2 — brk/cont/leave should be emitted as the join disjunct FROM THEIR OWN mutual arm, not routed through `IsHead`+`cases stmt`
Because there is no `realizedWitness_of_brk_compile` supplier (and none is needed —
the block IS the join shape), the cleanest capstone design does NOT put brk/cont/leave
into a generic `IsHead` disjunct that `hInv` later re-cases with `cases stmt`.
Instead each of the brk/cont/leave arms of `activeResult_of_compileStmtFuel?`'s mirror
extracts the block's concrete `{ [], .jump target }` shape (from
`checkedJumpOrInvalid … = some (.jump target)` under `input = expected`) and emits the
`nilJoin` disjunct.  This keeps `hInv`'s consumer a clean per-disjunct dispatch with no
nested `stmt` case-split.

### THE RE-CORRECTED CAPSTONE PREDICATE (supersedes §Session-33's; pin BEFORE the mutual)
`BlockGenShape cfg block` — a purely-STATIC classification (compile facts + shapes +
type facts; NO runtime `StateRel`/`SourceFrameFits`/`openStep`, and NOT the successor
`LabelShape` — both supplied separately by `hInv`).  Disjuncts (constructors of an
`inductive … : Prop`), each carrying exactly its supplier's static inputs:
1. **`codeHead`** — `∃ cf code ctx supply regular result, compileStmtFuel? (cf+1)
   (.code code) ctx supply block.label block.input regular = some result ∧
   BlocksInProgram result cfg` → `realizedWitness_of_code_compile`.  **Finding 1
   (§Session-33): the `.switch` head folds here** — the switch head is
   `mkCodeBlock? entry input scrutinee (.jump firstTest)` = the block a
   `compileStmtFuel? (.code scrutinee) … (regular := firstTest)` emits; the switch arm
   SYNTHESISES that `.code scrutinee` compile fact for its head block (a small helper
   `codeFact_of_switchHead` is the one genuinely-new supporting lemma the mutual needs
   here — reverse of `mkCodeBlock?`; not yet banked).
2. **`ifHead`** — `∃ cf cond body ctx supply regular result, compileStmtFuel? (cf+1)
   (.if_ cond body) ctx supply block.label block.input regular = some result ∧
   BlocksInProgram result cfg` → `realizedWitness_of_if_compile`.
3. **`callHead`** — `∃ cf name ctx supply regular result, ProcList.lookup? name
   ctx.procs = some proc ∧ compileStmtFuel? (cf+1) (.call name) … = some result ∧
   BlocksInProgram result cfg` (also needs `proc.WF` + the `splitArgs?` runtime — the
   `splitArgs?`/`proc.WF` come from the callee's own `realizedWitness`/a WF invariant at
   `hInv`, so `callHead` need only carry the compile fact + lookup + `BlocksInProgram`)
   → `realizedWitness_of_call_compile`.
4. **`forCond`** — `∃ cond input output trueLabel falseLabel, block = { block.label,
   input, body := Code.toCfg cond, output, term := .jumpi trueLabel falseLabel } ∧
   Code.type? cond input = some output ∧ requireSourceWords? 1 output = some () ∧
   findBlock? block.label = some block` → `realizedWitness_of_condBlock_jump`.
5. **`switchTest`** — carry `valueShape/caseValue/labels` + `head?` +
   `BlocksInProgram result cfg` + membership → `realizedWitness_of_test_jump`.
6. **`caseEntryPop`** — carry `input/output` + `Instr.type? .pop` + `BlocksInProgram` +
   membership → `realizedWitness_of_pop_jump`.
7. **`nilJoin`** — `∃ input exitLabel, findBlock? block.label = some { block.label,
   input, body := [], output := input, term := .jump exitLabel }` →
   `realizedWitness_of_join_jump`.  **COVERS: the empty-stmt-list join block AND
   brk/cont/leave (correction 1).**
8. **`procAdapter`** — `∃ blockInput relabelTarget output bodyLabel, findBlock?
   block.label = some { block.label, blockInput, [.relabel relabelTarget], output,
   .jump bodyLabel } ∧ Instr.type? (.relabel relabelTarget) blockInput = some output`
   → `realizedWitness_of_adapter_jump` (banked this session).
9. **`terminalHalt`** — `∃ input kind, findBlock? block.label = some { block.label,
   input, [], input, .halt kind }` → `halt_openStep_no_jump` (banked this session).

That is NINE disjuncts, not six: the §Session-33 "six" conflated the three head
suppliers into one `IsHead`, and mis-placed brk/cont/leave + terminal.  Splitting the
head into `code/if/call` avoids a nested `cases stmt` in `hInv`; `nilJoin` absorbs
brk/cont/leave; `terminalHalt` is its own vacuity disjunct.  (Dispatch blocks are NOT a
`BlockGenShape` disjunct — they are `block_category`'s THIRD arm, discharged by
`realizedWitness_of_dispatch_jump` directly, outside this predicate, which only classes
the main-body + proc-body categories.)

### THE FRONTIER (sharpened for session 35)
1. **The one supporting lemma the mutual still needs:** `codeFact_of_switchHead`
   (synthesise the `compileStmtFuel? (.code scrutinee) … = some <single-block result>`
   fact for the switch head block, from the switch's `components_of_compileStmtFuel?_switch`
   head `mkCodeBlock?` fact — reverse-engineer the `.code` emission at line 412).  The
   analogous facts for brk/cont/leave (their `{[], .jump target}` shape) come straight
   out of `checkedJumpOrInvalid = some (.jump target)` under `input = expected`; no
   helper needed beyond a `simp` unfold.
2. **The assembled 9-disjunct capstone mutual** — 5 functions
   (`compileBlockFuel?`/`compileStmtListFuel?`/`compileStmtFuel?`/`compileCasesFuel?`/
   `compileDefaultFuel?`) mirroring `activeResult_of_compile*`
   (`TypedCfgCompilerActive.lean:77–508`) but concluding
   `∀ block ∈ result.blocks, BlockGenShape cfg block` (define
   `GenShapeResult result cfg := that ∀`, prove an `append` lemma like
   `ActiveResult.append`).  **Thread `hBlocks : BlocksInProgram result cfg`** DOWN the
   recursion (each sub-result's `BlocksInProgram` follows from block-list inclusion:
   sub.blocks ⊆ result.blocks — small `sublist`/`left_of_append`/`right_of_append`
   helpers; `BlocksInProgram.{left,right}_of_append` already exist at `Core.lean:2085`).
   Per §Session-33: machinery arms must use `components_of_compileStmtFuel?_{for,switch}`
   / `components_of_compileCasesFuel?_cons` DIRECTLY (not the lossy `mem_of_*`) to
   retain the block shape + `hType`/`hSource`/`head?` facts the disjuncts carry.  Arms:
   nil→`nilJoin`; code→`codeHead`; if→`ifHead` for head + recurse body; switch→
   `codeHead`(via `codeFact_of_switchHead`) for head + recurse cases/default; for→recurse
   init + `forCond` for the loop block + recurse body/post; brk/cont/leave→`nilJoin`;
   terminal→`terminalHalt`; call→`callHead`; cases-cons→`switchTest`+`caseEntryPop`+
   recurse body + recurse tail; default-none→`caseEntryPop`; default-some→`caseEntryPop`
   (the `pop` entry) + recurse body.
3. **The dispatch StateRel⟶frame-facts residual** (unchanged, §Session-31 item 4).
4. Then assemble `hInv` via `block_category` → {main root
   (`main_stmtList_provenance`) / proc root (`procBlocks_provenance`, banked this
   session) → drill(capstone) → matching supplier} ; dispatch → frame-facts →
   `realizedWitness_of_dispatch_jump` ; programEnd → `programEnd_openStep_no_jump`.
   Feed `AllEntriesRealized.of_openStep_invariant`; proceed to Step B
   (`openRunNPrefix_peephole_congr_of_source`).
* Do NOT add the swap arm to `peepholeBody` until the whole invariant is green.

### Status handed to session 35
Frontier items 1 & 2 (adapter supplier + proc-body root inversion) LANDED; the
terminal vacuity lemma LANDED ⇒ the **successor-discharge family is COMPLETE** for
EVERY reachable block category (compiled head ×3 / for-cond / switch-test / case-entry /
nil-join [also brk/cont/leave] / proc-entry adapter / dispatch / programEnd / terminal).
Landed: `InteractionMachineryCoupling.lean` — `realizedWitness_of_adapter_jump`
(`d90b60e0`), `halt_openStep_no_jump` (`3dc73f63`);
`InteractionProcBlockProvenance.lean` (NEW, wired into `EvmCompiler.Verification`) —
`mem_procBlocks_provenance` + `GeneratedContext.procBlocks_provenance` (`ccad028e`).
`compile_correct`/`compile_correct_creation` UNCHANGED (frozen `Correctness.lean`
untouched); delta +0.  The capstone mutual was deliberately deferred: two predicate
CORRECTIONS (brk/cont/leave are nil-join, not vacuous; the head splits into
code/if/call, so NINE disjuncts not six) mean the §Session-33 predicate was wrong;
the re-corrected predicate + the single remaining supporting lemma
(`codeFact_of_switchHead`) + the exact arm-by-arm mutual recipe are pinned above.
Frontier = `codeFact_of_switchHead` → the assembled 9-disjunct capstone mutual →
dispatch residual, before `of_openStep_invariant` → Step B.

## Session-35 update (2026-07-19): the CAPSTONE landed — switch-head fact + the assembled 9-disjunct block-generation mutual, both green + axiom-clean

Session 35's mandate: `codeFact_of_switchHead` → the 9-disjunct strong-induction
capstone mutual → dispatch residual → (if all closes) `hInv` assembly.  **Result:
frontier items 1 & 2 (the switch-head fact AND the full capstone mutual) are banked
green + axiom-clean.** The §Session-34 re-corrected NINE-disjunct predicate was
implemented verbatim (no predicate hole found).  Dispatch residual + `hInv` assembly
were deliberately NOT started (green-frontier stop; they are the next-session bulk).
No red code, no sorries; `peepholeBody`/public spine UNTOUCHED ⇒ measured delta **+0**.
`opt_harness.sh check` PASSES (43 public theorems, axioms ⊆
[propext, Classical.choice, Quot.sound]); `compile_correct`/`compile_correct_creation`
UNCHANGED.

### LANDED (green, axiom-clean) — new module `InteractionBlockGenShape.lean`, wired into `EvmCompiler.Verification`
* **`9c3ef25c`** — `codeFact_of_switchHead` (`InteractionBlockGenShape.lean:45`),
  `BlockGenShape` (the 9-disjunct `inductive … : Prop`, `:76`), `GenShapeResult`
  (`:221`), `GenShapeResult.append` (`:227`).  `codeFact_of_switchHead` reverse-engineers
  the switch head's `mkCodeBlock?` emission into a single-block `compileStmtFuel? (.code
  scrutinee) … (regular := casesEntryLabel supply 0 cases)` fact (one-line `simp`).
  `BlockGenShape` carries: head arms (`codeHead`/`ifHead`/`callHead`) the construct's
  `compileStmtFuel? … block.label block.input regular = some result` + `BlocksInProgram
  result cfg`; `forCond` the `Code.toCfg`/`.jumpi` shape + `Code.type?`/`requireSourceWords?`
  + `findBlock?`; `switchTest`/`caseEntryPop` the `[.dup 0,.push,.prim .eq]`/`[.pop]` shape
  + `BlocksInProgram` + membership; `nilJoin` (empty-body `.jump`, covers brk/cont/leave)
  + `procAdapter` (`[.relabel]`) + `terminalHalt` (`.halt`) the `findBlock?` fact.
* **`d1055027`** — the CAPSTONE 5-function mutual (`InteractionBlockGenShape.lean`):
  `genShape_of_compileBlockFuel?` (`:251`), `…StmtListFuel?` (`:268`), `…StmtFuel?`
  (`:310`), `…CasesFuel?` (`:527`), `…DefaultFuel?` (`:581`).  Mirrors
  `activeResult_of_compile*` (`TypedCfgCompilerActive.lean:77`) but concludes
  `GenShapeResult result cfg`, threading `hBlocks : BlocksInProgram result cfg` down the
  recursion (sub-results via `BlocksInProgram.{left,right}_of_append` for `stmtList`-cons
  appends, and `hBlocks b (by simp only [List.mem_cons, List.mem_append]; tauto)` for the
  cons/append block lists of `if`/`switch`/`for`/`cases`/`default`).  NO `ReturnTokenActive`
  invariant needed — classification is purely structural.  Arms per §Session-34 recipe:
  nil→`nilJoin`; code→`codeHead`; if→`ifHead`+recurse body; switch→`codeHead`(via
  `codeFact_of_switchHead`)+recurse cases/default; for→recurse init/body/post +`forCond`
  for the loop block; brk/cont/leave→`nilJoin`; terminal→`terminalHalt`; call→`callHead`;
  cases-cons→`switchTest`+`caseEntryPop`+recurse body/tail; default-none→`caseEntryPop`;
  default-some→`caseEntryPop`+recurse body.

### KEY IMPLEMENTATION FINDING — constructor-arg elaboration order (metavar pinning)
The disjunct suppliers whose block INDEX metavars are not fully pinned by an earlier
explicit arg (`nilJoin`/`terminalHalt`: hFind only; `forCond`: label/trueLabel/falseLabel
free after `hType`) CANNOT be closed by `exact BlockGenShape.X (hBlocks _ (by simp))` nor
`refine … ?_; refine hBlocks _ ?_; simp` — the inner `by simp`/`hBlocks _` forces
`?block ∈ …` (or the stuck projection `?block.label =?= entry`) BEFORE the result-type
unification pins `?block`.  **Robust pattern (used):** capture
`have hFind := hBlocks block hMem` at the arm's `intro block hMem` (block explicit, no
metavar), then `subst block` and `exact BlockGenShape.X … hFind`.  For arms whose `?_`
is a plain membership (`switchTest`/`caseEntryPop`: `record ∈ result.blocks`, no `hBlocks`
projection) `refine BlockGenShape.X hHead hBlocks ?_; simp` works.  Also: `codeFact_of_switchHead`
must be applied with `(compilerFuel := 0) (ctx := ctx) (supply := supply)` explicit — those
implicits are unconstrained by the switch head block (they only touch `result.next`), so
they surface as stray `⊢ ℕ`/`⊢ Context` goals otherwise.  Also: `«a :: b ++ c»` parses as
`(a :: b) ++ c` (`::` binds tighter than `++`), so `simp only [mem_cons, mem_append]`
yields the LEFT-nested `(=a ∨ … ∨ ∈b) ∨ ∈c`; the `rcases` pattern must be
`(rfl | … ) | hTail`, not `rfl | … | hTail`.

### THE FRONTIER (sharpened for session 36)
1. **The dispatch StateRel⟶frame-facts residual** (unchanged, §Session-31 item 4): the
   dispatch arm's `hPop`/`hAttach`/`hRetc` are RUNTIME facts, derived from the exit
   block's `realizedWitness` `StateRel bodyState (site.token :: tokens) t`, feeding
   `realizedWitness_of_dispatch_jump` (`InteractionRealizedWitnessSuccessor.lean:149`).
   This is the last supplier-adjacent obligation NOT covered by `BlockGenShape` (dispatch
   is `block_category`'s third arm, outside the predicate).
2. **Assemble `hInv`** (frontier item 4, now all static ingredients exist): via
   `block_category` (`InteractionBlockProvenance.lean:79`) → {main root
   (`main_stmtList_provenance`) / proc root (`GeneratedContext.procBlocks_provenance`,
   §Session-34) → drill (the 12 dichotomy lemmas, `InteractionBlockProvenanceDrill.lean`)
   feeding the capstone `genShape_of_compileBlock?` (define a `compileBlock?`-level wrapper
   over `genShape_of_compileBlockFuel?`, analogous to `activeResult_of_compileBlock?`,
   `TypedCfgCompilerActive.lean:514`) → `cases`-split the resulting `BlockGenShape` and
   dispatch each disjunct to its matching supplier (`realizedWitness_of_{code,if,call}_compile`,
   `_condBlock_jump`, `_test_jump`, `_pop_jump`, `_join_jump`, `_adapter_jump`,
   `halt_openStep_no_jump`)} ; dispatch → frame-facts (item 1) → `_dispatch_jump` ;
   programEnd → `programEnd_openStep_no_jump`.  Feed
   `AllEntriesRealized.of_openStep_invariant` (`TypedCfg/InteractionEntryRealized.lean:271`).
   NOTE the transports each supplier's runtime hyps (`hFits`/`hRel`/`hLabelShape`) must be
   discharged AT this splice from the threaded in-scope source run — that is the substance
   of the assembly, and where the `SourceFrameFits` transports (e.g. `procAdapter` at
   `output = relabelTarget = fragment.input`, §Session-34) are finally closed.
3. Then proceed to Step B (`openRunNPrefix_peephole_congr_of_source`); do NOT add the swap
   arm to `peepholeBody` until the whole invariant is green.

### Status handed to session 36
The block-generation classification is COMPLETE: `codeFact_of_switchHead` + the 9-disjunct
`BlockGenShape` predicate + the full 5-function capstone mutual proving every emitted block
is classified (`genShape_of_compile*`, all green + axiom-clean, `:45/76/221/227/251/268/310/527/581`).
This closes §Session-34 frontier items 1 & 2.  Remaining = the dispatch runtime residual +
the `hInv` assembly (block_category → root → drill(capstone) → per-disjunct supplier +
runtime-hyp transports) → `of_openStep_invariant` → Step B.  `compile_correct`/
`compile_correct_creation` UNCHANGED (frozen `Correctness.lean` untouched); delta +0;
`opt_harness.sh check` PASSES.  New module `InteractionBlockGenShape.lean` wired into
`EvmCompiler.Verification`.

## Session-36 update (2026-07-19): three hInv-assembly ingredients landed — the public `compileBlock?`-level classifier wrapper, the localized dispatch `StateRel`⟶`popReturn?` derivation, and the MAIN-body `block ⟶ BlockGenShape` composite; all green + axiom-clean.  The proc-body composite's precise blocker isolated (a `BlocksInProgram bodyResult cfg` gap in `procBlocks_provenance`)

Session 36's mandate: (1) the dispatch `StateRel`⟶frame-facts residual, (2) the full
`hInv` assembly (block_category → root → drill/capstone → per-disjunct supplier +
runtime-hyp transports) → `of_openStep_invariant` → (if it closes) Step B.  **Result:
three green, axiom-clean commits banking the static assembly ingredients now reachable
from the §Session-35 capstone; the FULL `hInv` did NOT close (the genuine remaining
blockers — the target-block `LabelShape` transports and the proc-body `BlocksInProgram`
gap — are isolated below, unchanged in essence from every prior session's honest
assessment).**  No red code, no sorries; `peepholeBody`/public spine UNTOUCHED ⇒ delta
**+0**.  `opt_harness.sh check` PASSES (43 public theorems, axioms ⊆ [propext,
Classical.choice, Quot.sound]); `compile_correct`/`compile_correct_creation` UNCHANGED.

### LANDED (green, axiom-clean) — new module `InteractionHInvAssembly.lean`, wired into `EvmCompiler.Verification`
All `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]` (`dispatch_popReturn?_of_stateRel`
is even tighter: `[propext, Quot.sound]`).  Namespace `EvmCompiler.Structured`.
* **`62b7ee8e`** — TWO ingredients:
  * **`genShape_of_compileBlock?`** (`InteractionHInvAssembly.lean:56`) — the public
    `compileBlock?`-level wrapper over the §Session-35 fuel-indexed capstone
    `genShape_of_compileBlockFuel?`, exactly mirroring `activeResult_of_compileBlock?`
    (`TypedCfgCompilerActive.lean:514`).  Proof: unfold `compileBlock?` to
    `compileBlockFuel? (blockFuel block + 1)` via a `have hFuel := by simpa
    [compileBlock?] using hCompile`, then `exact genShape_of_compileBlockFuel? hFuel hBlocks`.
    (NOTE — the `apply … ?_ hBlocks` form FAILS: the `?_` metavar for the fuel-indexed
    `hCompile` unifies against the implicit `{fuel : Nat}` and surfaces a stray `⊢ ℕ`
    goal; the explicit `have hFuel` with the pinned `blockFuel block + 1` fuel avoids it.)
  * **`dispatch_popReturn?_of_stateRel`** (`:96`) — the localized `StateRel`⟶frame-fact
    derivation for `block_category`'s DISPATCH arm (item 1).  From `StateRel bodyState
    (token :: tokens) target` concludes `∃ frame returns, bodyState.returns = frame ::
    returns ∧ bodyState.popReturn? = some (frame, {bodyState with returns := returns})`
    — i.e. the exact `hPop` the return-dispatch successor supplier
    `realizedWitness_of_dispatch_jump` (`InteractionRealizedWitnessSuccessor.lean:149`)
    consumes.  Proof = `StateRel.returns_cons_of_tokens_cons`
    (`TypedCfgPreservation/Core.lean:74`) ∘ `simp only [RunState.popReturn?, hReturns]`.
    **This discharges `hPop` from the `realizedWitness` `StateRel` ALONE — no source run.**
* **`dba3d361`** — **`main_blockGenShape`** (`:127`) — the MAIN-body arm of the eventual
  `hInv` split: from `block ∈ context.main.blocks` (block_category's first arm) concludes
  `BlockGenShape cfg block`.  Proof = `main_stmtList_provenance` (root,
  `InteractionBlockProvenanceRoot.lean:49`) ∘ `genShape_of_compileStmtListFuel?` (capstone)
  ∘ `context.mainBlocks` (`Core.lean:3505`, the `BlocksInProgram context.main cfg` fact).
  Purely static provenance-∘-classification; feeds the per-disjunct supplier dispatch.

### KEY FINDING — the dispatch frame-facts split cleanly into hPop (StateRel-derivable) vs hAttach/hRetc (procedure-identity, NOT StateRel-derivable)
The §Session-31 note framed all three dispatch frame-facts (`hPop`/`hAttach`/`hRetc`) as a
single "StateRel⟶frame-facts residual".  This session **proves the split is real**:
* `hPop` IS derivable from the exit-block `StateRel` alone (`dispatch_popReturn?_of_stateRel`
  above) — the return token at the token-list head forces `bodyState.returns ≠ []`, so
  `popReturn?` succeeds deterministically.
* `hAttach : attachReturns? frame bodyState.evm.stack = some stack` needs
  `bodyState.evm.stack.length = frame.retc` (`EffectSemantics.lean:247`), and
  `hRetc : frame.retc = proc.retc` pins the popped frame's `retc` to the EXITED procedure.
  Neither is `StateRel`-derivable: `realizeStack` (`Core.lean:17`) appends the caller
  frame BENEATH the source stack and never constrains `source.evm.stack.length` against
  `frame.retc`.  These are **procedure-identity** facts — the popped frame's `retc` must
  match the procedure whose exit block we are at — supplied by the same site provenance
  (`hLookup`/`hSiteProc`/`hSiteMem`) the dispatch arm recovers, NOT by `realizedWitness`.
So item 1 is *partially* static: `hPop` banked; `hAttach`/`hRetc` are correctly the
provenance side's job (they ride the `openStep_dispatch` frame-model chain that the
site-coupling produces, exactly as `openRun_call_exec_under` supplies them internally).

### THE FRONTIER (sharpened for session 37)
1. **Proc-body composite `proc_blockGenShape`** (the sibling of `main_blockGenShape`).
   BLOCKER isolated: `procBlocks_provenance` (`InteractionProcBlockProvenance.lean:210`)
   hands back, for the body case, `compileBlock? proc.body … = some bodyResult` with only
   `block ∈ bodyResult.blocks` — but `genShape_of_compileBlock?` needs `BlocksInProgram
   bodyResult cfg` (ALL of `bodyResult`'s blocks in cfg), which the provenance does NOT
   expose.  Two routes: (a) strengthen `mem_procBlocks_provenance`'s induction to ALSO
   emit `bodyResult.blocks ⊆ procBlocks` (a NEW sibling lemma — additive; the induction
   already tracks `procBlocks = body.blocks ++ tailBlocks`, so the subset is right there);
   (b) tie `bodyResult` to the `ProcFragment.result` of `procFragment_of_lookup?`
   (`Core.lean:3525`, which DOES give `BlocksInProgram fragment.result cfg`) via a
   traversal-determinism argument + `proc ∈ procs ⟶ lookup? = some proc` (proc-name
   uniqueness).  Route (a) is the cleaner additive win.  The ADAPTER sub-case needs
   `BlockGenShape.procAdapter` (`InteractionBlockGenShape.lean:180`): unfold the adapter's
   `mkBlock? (ProcLabel.entry proc.name) (procEntry proc) [.relabel input] (.jump (body
   proc.name)) = some adapter` to expose the `Instr.type? (.relabel input) …` fact + the
   exact block shape, then `findBlock?` via `block ∈ procBlocks ⊆ cfg` + `LabelsUnique`.
2. **Assemble `hInv`** — the remaining bulk, UNCHANGED in essence.  With `main_blockGenShape`
   (+ the pending `proc_blockGenShape`) supplying `BlockGenShape cfg block` at each
   compiled-construct entry, the `hInv` split is: get `⟨source, tokens, block, hFind,
   hStateRel, hFits⟩` from `realizedWitness cfg e t`; `block_category hFind` → 4 arms;
   programEnd → `programEnd_openStep_no_jump`; main/proc → `main_blockGenShape`/
   `proc_blockGenShape` → `cases` the `BlockGenShape` → dispatch each disjunct to its
   supplier (`realizedWitness_of_{code,if,call}_compile`, `_condBlock_jump`, `_test_jump`,
   `_pop_jump`, `_join_jump`, `_adapter_jump`, `halt_openStep_no_jump`); dispatch →
   `dispatch_popReturn?_of_stateRel` (hPop, this session) + site provenance (hAttach/hRetc)
   + `realizedWitness_of_dispatch_jump`.  **THE genuine remaining substance is the
   per-supplier RUNTIME-HYP transports** — chiefly `hLabelShape : LabelShape cfg next
   restShape` for the TARGET block `next` (every supplier needs the jumped-TO block's
   declared input shape to match the construct's residual shape), plus `hFits` for the
   child frame.  `hLabelShape` is a CFG-linkage fact (the compile fact's
   `result.fallthrough?`/successor label = the block declared at `next`); it is the
   never-yet-closed piece.  This is where sessions 26→35 kept stopping, and it remains the
   real frontier — the classification (now COMPLETE for main, pending for proc) was only
   ever the *input* to the suppliers, not the transports.
3. Then Step B (`openRunNPrefix_peephole_congr_of_source`); do NOT add the swap arm to
   `peepholeBody` until the whole invariant is green.

### Status handed to session 37
Landed: `InteractionHInvAssembly.lean` — `genShape_of_compileBlock?` (`:56`),
`dispatch_popReturn?_of_stateRel` (`:96`), `main_blockGenShape` (`:127`), all green +
axiom-clean, wired into `EvmCompiler.Verification`.  Commits `62b7ee8e` (wrapper + dispatch
hPop) / `dba3d361` (main composite).  `scripts/opt_harness.sh check` = OK (43 public
theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/
`compile_correct_creation` UNCHANGED (frozen `Correctness.lean` untouched); delta +0.
Item 1 (dispatch residual) is `hPop`-banked with `hAttach`/`hRetc` proven to be
provenance-side (not `StateRel`-derivable).  The main-body classification arm is banked;
proc-body classification + the `hInv` target-`LabelShape` transports are the frontier.
