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

## Session-37 update (2026-07-19): proc-body classification composite CLOSED + the target-`LabelShape` transport DESIGN pinned with its WellTyped-edge half banked

Session 37's mandate (per §Session-36 recipe): (1) `proc_blockGenShape` (proc-body
composite, blocked on a `BlocksInProgram bodyResult cfg` gap in `procBlocks_provenance`);
(2) THE LABELSHAPE TRANSPORT recon + design + implement; (3) remaining runtime-hyp
transports → assemble `hInv`.  **Result: THREE green, axiom-clean commits — item 1 fully
closed (proc classification now COMPLETE, matching main), and item 2's design nailed down
(with concrete evidence) plus its universally-needed WellTyped-edge half banked.**  The
FULL `hInv` did not close — the genuine residual (the `compatible ⟶ exact` step for the
external `regular` successor) is precisely isolated below.  No red code, no sorries;
`peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**.  `opt_harness.sh check` PASSES (43
public theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/
`compile_correct_creation` UNCHANGED.

### LANDED (green, axiom-clean)
* **`d9a80485`** — `InteractionProcBlockProvenance.lean`:
  * **`mem_procBlocks_provenance_subset`** (`:215`) — the §Session-36-item-1 route-(a)
    strengthening: a NEW sibling of `mem_procBlocks_provenance` whose induction ALSO emits
    `∀ b ∈ bodyResult.blocks, b ∈ procBlocks`.  Each leaf threads the inclusion through
    `procBlocks = body.blocks ++ tailBlocks` (`body.blocks = compiled.blocks` no-adapter /
    `adapter :: compiled.blocks` adapter); recursion composes via `List.mem_append_right`.
    Axioms `[propext, Classical.choice, Quot.sound]`.
  * **`GeneratedContext.procBlocks_provenance_inProgram`** (`:417`) — promotes the body
    compile fact straight to `BlocksInProgram bodyResult cfg` by composing the subset with
    `procBlocks ⊆ cfg.blocks` (from `context.cfgEq`) + `findBlock?_eq_some_of_mem`
    (`LabelsUnique`).  This is exactly the hypothesis the body drill consumes.
* **`73c4b4c7`** — **`proc_blockGenShape`** (`InteractionHInvAssembly.lean:149`) — the
  proc-body sibling of `main_blockGenShape`, CLOSING §Session-36 frontier item 1.  From
  `block ∈ context.procBlocks`, `procBlocks_provenance_inProgram` yields the body case
  (feed `genShape_of_compileBlock?` directly) or the adapter case (invert the adapter
  `mkBlock?` exactly as `mkBlock?_label_input`: `unfold mkBlock?; cases hBT : bodyType?
  [.relabel input] (procEntry proc); simp [hBT]; subst`, recovering the `Instr.type?
  (.relabel input) …` fact + exact block shape, then `BlockGenShape.procAdapter hType
  hFind` with `hFind` from `block ∈ cfg.blocks`).  Axiom-clean.  **⇒ block-generation
  classification is now COMPLETE for BOTH main and proc bodies.**
* **`89b3abfe`** — NEW module `InteractionLabelShapeTransport.lean` (wired into
  `EvmCompiler.Verification`), namespace `TypedCfgPreservation.LabelShape`:
  * **`block_wellTyped_of_findBlock?`** (`:50`) — any `cfg.findBlock?`-returned block is
    `Block.WellTyped cfg` (member ⟶ `AllBlocksTyped`).  Axioms `[propext]`.
  * **`edge_jump_of_wellTyped`** (`:66`) — from `cfg.WellTyped` + a found block with
    `.jump target` term: `∃ targetShape, LabelShape cfg target targetShape ∧
    block.output.compatible targetShape`.  The **existence** half of the successor
    transport (the target block IS in `cfg` with a `compatible` input), reusable by every
    route.  Axioms `[propext, Quot.sound]`.

### THE LABELSHAPE-TRANSPORT DESIGN — recon findings + chosen route (item 2, the sessions-26→35 sticking point)
The suppliers (`InteractionRealizedWitnessSuccessor.lean` :63/:101/:149,
`InteractionCodeConstructCoupling.lean:119`) each consume `hLabelShape : LabelShape cfg
next restShape` and package it via `realizedWitness_of_stateRel`
(`InteractionBoundedOwnerRealized.lean:334`), which needs the STRICT
`block.input = restShape` (`LabelShape` = `∃ block, findBlock? next = some block ∧
block.input = restShape`, `GeneratedBoundary.lean:11`).  The `LabelShape` constructor API
is ALREADY complete (`of_hasEntry`/`of_compileBlockFuel?`/`of_compileStmtListFuel?`/
`of_compileStmtFuel?`/`procEntry`/`procExit`/`programEnd`, plus `LabelShape.eq`
uniqueness) — the transport is NOT missing machinery; it is a question of *supplying the
compile/entry fact for the target block*.  Two successor kinds:

1. **Internal successors** (target block ∈ the current construct's own `result` — e.g. an
   `if`'s body-entry `trueLabel`, a loop's body, a switch case-entry).  EXACT `LabelShape`
   is immediate from the disjunct's own compile fact via `of_compileBlockFuel?`/
   `of_hasEntry` restricted to the sub-result — precisely what the forward proofs do
   (`InteractionBranchPreservation.lean:543`, `hBodyShape`).  **No obstruction; this is
   routine per-construct extraction via the `components_of_compileStmtFuel?_*` lemmas.**

2. **The external `regular` successor** (the construct's fallthrough target, NOT in its
   own result — e.g. `codeHead`'s `.jump regular`, `ifHead`'s false/join leg).  **THIS is
   the genuine residual.**  KEY RECON FINDING: the forward preservation proofs *never*
   needed it because they STOP at `regular` (`RecursiveBoundary`/`RegularExit`/`StopPolicy`
   machinery, `InteractionBranchPreservation.lean:377` `hRegular : RegularAtSupply …`), so
   they carry no `LabelShape cfg regular …`.  The whole-program route-B invariant instead
   *continues* into `regular`, so it must show the block declared at `regular` has input
   EXACTLY the construct's fallthrough output.  This is a **generation-threaded exactness**
   fact: generation sets the successor block's input = the source block's output exactly,
   but `cfg.WellTyped` only checks `Shape.compatible` (`Syntax.lean:111` — a genuine
   subtyping: opaque `.caller` rows may instantiate to extra hidden slots), NOT equality.
   `edge_jump_of_wellTyped` (banked) delivers the `compatible` relation + target-block
   existence; the residual is the **`compatible ⟶ exact`** upgrade, which is NOT derivable
   from `WellTyped` alone.

   **CHOSEN ROUTE (option B, refined — a threaded exactness, NOT a giant new mutual):**
   thread an *inherited boundary shape* `hRegular : LabelShape cfg regular fallthroughOut`
   through the SAME `genShape_of_compile*` recursion the capstone already performs, so each
   disjunct additionally carries its external successor's EXACT `LabelShape`.  The
   recursion discharges it: for a non-last statement in a list, the head's `regular` is the
   *entry of the rest*, whose block is in the SAME enclosing result (internal ⟶ `of_hasEntry`
   on the rest's sub-result); the list's LAST statement inherits the enclosing `regular`.
   It **bottoms out cleanly at the two boundaries** — main body: `regular = programEnd`,
   `LabelShape.programEnd` gives `LabelShape cfg programEnd (main.fallthrough?.getD caller)`
   and `requireFallthrough`/main's fallthrough pins the output to match; proc body:
   `regular = ProcLabel.exit proc.name`, `LabelShape.procExit` gives `LabelShape cfg (exit
   proc.name) (Shape.procExit proc)` and the proc's `requireFallthrough? (procExit)` pins
   the body's fallthrough output to `procExit` — so the inherited `hRegular` is exactly the
   boundary `LabelShape` at every top-level entry into the mutual.  (`programEnd`/`procExit`
   `LabelShape`s and `procEntry` already exist in `GeneratedBoundary.lean:97/159`.)

   Concretely for session 38: strengthen the capstone's `GenShapeResult`/`BlockGenShape`
   into a variant carrying, per disjunct, `LabelShape cfg <externalSuccessor> <output>`;
   re-run the `genShape_of_compile*` mutual (mirror of `InteractionBlockGenShape.lean`'s
   5-function mutual) with the added `hRegular` hypothesis threaded exactly as
   `BlocksInProgram` is; seed it at the main/proc composites (`main_blockGenShape`/
   `proc_blockGenShape`) with `LabelShape.programEnd` / `LabelShape.procExit`.  The internal
   successors within each disjunct come free from the sub-result `of_hasEntry`.

### THE FRONTIER (sharpened for session 38)
1. **The exact external-successor `LabelShape` mutual** (item 2, chosen route above) — the
   real remaining substance.  Additive: a strengthened `BlockGenShape`/capstone variant
   threading `hRegular : LabelShape cfg regular <fallthroughOut>`, seeded at the two
   boundaries.  Start from the boundary base cases (`LabelShape.programEnd`/`procExit`
   already banked) and the non-last-statement internal case (`of_hasEntry` on the rest's
   sub-result); the per-construct internal successors reuse `components_of_compileStmtFuel?_*`.
2. **Assemble `hInv`** — with classification COMPLETE (main+proc) and both successor
   `LabelShape` kinds in hand, the split is: `realizedWitness cfg e t` ⟶ `⟨source, tokens,
   block, hFind, hStateRel, hFits⟩`; `block_category hFind` → 4 arms; programEnd →
   `programEnd_openStep_no_jump`; main/proc → `main_blockGenShape`/`proc_blockGenShape` →
   `cases BlockGenShape` → per-disjunct supplier (`realizedWitness_of_{code,if,call}_compile`,
   `_condBlock_jump`, `_test_jump`, `_pop_jump`, `_join_jump`, `_adapter_jump`,
   `halt_openStep_no_jump`) fed the internal + external `LabelShape` + `hFits` (child-frame,
   carried by the coupling); dispatch → `dispatch_popReturn?_of_stateRel` (hPop, banked s36)
   + site provenance (hAttach/hRetc) + `realizedWitness_of_dispatch_jump`.  Then
   `AllEntriesRealized.of_openStep_invariant`.
3. Then Step B (`openRunNPrefix_peephole_congr_of_source`); do NOT add the swap arm to
   `peepholeBody` until the whole invariant is green.

### Status handed to session 38
Landed: `InteractionProcBlockProvenance.lean` — `mem_procBlocks_provenance_subset`,
`GeneratedContext.procBlocks_provenance_inProgram` (`d9a80485`);
`InteractionHInvAssembly.lean` — `proc_blockGenShape` (`73c4b4c7`);
`InteractionLabelShapeTransport.lean` — `block_wellTyped_of_findBlock?`,
`edge_jump_of_wellTyped` (`89b3abfe`), wired into `EvmCompiler.Verification`.  All green +
axiom-clean.  **Block-generation classification is COMPLETE for main AND proc bodies.**  The
target-`LabelShape` transport is DESIGNED (option B: thread inherited boundary
`LabelShape cfg regular fallthroughOut` through the capstone mutual, seeded at
programEnd/procExit) with its WellTyped-edge existence half banked; the `compatible ⟶ exact`
external-successor upgrade is the isolated residual for session 38.  `scripts/opt_harness.sh
check` = OK (43 public theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` UNCHANGED (frozen `Correctness.lean`
untouched); delta +0.

## Session-38 update (2026-07-19): option-B threading toolkit COMPLETE — boundary seeds + the two regular-thread combinators banked; the strengthened-mutual recipe fully worked out (every case, incl. `for_`/`switch`) and pinned for mechanical assembly

Session 38's mandate (per §Session-37): (1) the boundary-threaded strengthened mutual —
enrich the capstone so each disjunct also carries the EXACT `LabelShape` for its external
`regular` successor, threaded from the programEnd/procExit seeds; (2) assemble `hInv`;
(3) Step B.  **Result: FOUR green, axiom-clean lemmas banked — the COMPLETE option-B
threading toolkit** (the two boundary seeds + the two per-recursive-call regular-thread
combinators), plus the strengthened-mutual recipe worked out to the case level (every
construct, including the two hard ones — `for_`'s ctx-modification and the `switch` head's
internal `firstTest`).  The full 10-constructor enriched inductive + 5-function mutual was
NOT assembled this session (a large mechanical body whose `switch`-head `base/idx`
bookkeeping and per-case shape-equalities are build-iteration-heavy) — but every obligation
it raises now reduces to one of the four banked lemmas + `of_hasEntry`, so session 39's
assembly is mechanical.  No red code, no sorries; `peepholeBody`/public spine UNTOUCHED ⇒
delta **+0**.

### LANDED (green, axiom-clean) — all in `InteractionLabelShapeTransport.lean`
* **`318302f1`** — the two **option-B boundary seeds** (external `regular` in threaded form):
  * **`LabelShape.main_regular_labelShape`** (`:116`) — `main.fallthrough? = some out →
    LabelShape cfg ProcLabel.programEnd out`.  From `LabelShape.programEnd` (input =
    `main.fallthrough?.getD caller`) rewritten under the fallthrough hyp.  Axioms
    `[propext, Classical.choice, Quot.sound]`.
  * **`LabelShape.proc_regular_labelShape`** (`:136`) — `bodyResult.requireFallthrough?
    (procExit proc) = some () → bodyResult.fallthrough? = some out → LabelShape cfg
    (ProcLabel.exit proc.name) out`.  `requireFallthrough?_eq_some_iff` forces `out =
    procExit proc`; then `LabelShape.procExit`.  Axiom-clean.
* **`2b166df0`** — the two **regular-thread combinators** (applied at every recursive descent):
  * **`LabelShape.regularThread_of_requireFallthrough`** (`:195`) — SAME-`regular`
    inheritance: `(hRegular : ∀ out, result.fallthrough? = some out → LabelShape cfg regular
    out) → result.fallthrough? = some expected → subResult.requireFallthrough? expected =
    some () → ∀ out, subResult.fallthrough? = some out → LabelShape cfg regular out`.  Axioms
    `[propext]`.  **This is the `if`-body / `switch` case-body / loop-body/post transporter**
    (all compiled with a shared continuation shape).
  * **`LabelShape.regularThread_tail_of_cons`** (`:219`) — SEQUENTIAL threading: head of a
    `stmt :: rest` list is compiled with `regular := restLabel supply` (the tail's entry) and
    falls through to `tailInput` = the tail entry block's input, so `of_compileStmtListFuel?
    hTailCompile hTailBlocks` discharges the head's regular-thread with NO boundary appeal.
    Axiom-clean.  **The "sequential continuation" core of option B.**

### KEY RECON FINDINGS (the design closures sessions 26–37 lacked)
1. **The supplier interface IS the threaded predicate.**  `realizedWitness_of_if_compile`
   (`InteractionConstructCoupling.lean:94`) consumes the external successor as
   `∀ restShape, result.fallthrough? = some restShape → LabelShape cfg next restShape`, and
   `realizedWitness_of_code_compile` (`InteractionCodeConstructCoupling.lean:226`) as
   `hFallthrough : result.fallthrough? = some expected` + `hLabelShape : LabelShape cfg next
   expected`.  Both are EXACTLY the option-B regular-thread `∀ out, result.fallthrough? =
   some out → LabelShape cfg regular out`.  No reshaping — the enriched disjunct stores this
   predicate verbatim and hInv feeds it straight in.  (For the internal `next = trueLabel`
   arm of `if`, hInv derives `LabelShape cfg (label supply 0) bodyInput` itself via
   `of_compileBlockFuel?` on the `if` body sub-fact — a 2-line inline, not a threaded field.)
2. **`callHead` needs NO regular enrichment.**  A compiled `call`'s DIRECT successor is
   `ProcLabel.entry name` (`realizedWitness_of_call_compile` wants `LabelShape cfg
   (ProcLabel.entry name) childInput`), which is the boundary seed `LabelShape.procEntry`
   (`GeneratedBoundary.lean:112`) — hInv supplies it directly from `GeneratedContext`.  The
   call's `regular` (return continuation) is reached via the return-DISPATCH block, not the
   call block, and is handled by the dispatch arm.  So `callHead` stays a base disjunct.
3. **`for_` threads cleanly** (`components_of_compileStmtFuel?_for`,
   `TypedCfgCompilerFacts.lean:1302`).  Body is compiled with `breakLabel? := some regular`
   (the loop's OWN `regular`!), `breakShape? := some {condOutput.tail}`, `continueLabel? :=
   some (label supply 2)` (= post entry), both continue/break shape `= {condOutput.tail}` =
   the loop's fallthrough; leave inherited.  So the body's break-LabelShape comes from the
   loop's own `hRegular {condOutput.tail}`, its continue-LabelShape from `of_hasEntry` on
   `postResult` (internal), and leave from the enclosing ctx-exit thread.  init/post are
   compiled with break/continue CLEARED (vacuous) — leave inherited.
4. **`nilJoin` must split by exit target.**  The base capstone emits `BlockGenShape.nilJoin`
   for BOTH the empty-list join (`.jump regular`, enrich via `hRegular`) AND `brk`/`cont`/
   `leave` (`.jump breakLabel?`/`continueLabel?`/`leaveLabel?`).  The enriched inductive
   splits it: `nilJoinRegular` (regular-thread field) for the nil-list case, `nilJoinExit`
   (a ctx-exit `LabelShape` field) for brk/cont/leave — the latter fed by a threaded
   **ctx-exit bundle** `CtxExitsShaped cfg ctx` (LabelShapes for ctx's break/continue/leave
   labels), which is unchanged through `if`/`code`/`call`/`switch`, re-established for the
   body in `for_` (finding 3), and seeded at the proc body with `leaveLabel? = exit`,
   `leaveShape? = procExit` ⟹ `LabelShape.procExit` (main body has all three None ⟹ vacuous).

### THE STRENGTHENED-MUTUAL RECIPE (pinned for session 39 — mechanical)
Define, in a NEW module `InteractionBlockGenShapeRegular.lean` (import
`InteractionBlockGenShape` + `InteractionLabelShapeTransport`):
* `abbrev HRegular result cfg regular := ∀ out, result.fallthrough? = some out →
  LabelShape cfg regular out`.
* `structure CtxExitsShaped cfg ctx : Prop` with fields `brk`/`cont`/`leave` (each
  `∀ lbl shp, ctx.<x>Label? = some lbl → ctx.<x>Shape? = some shp → LabelShape cfg lbl shp`).
* `inductive BlockGenShapeReg cfg : Block → Prop` — mirror the 9 `BlockGenShape` disjuncts
  but: `codeHead`/`ifHead` add `hReg : HRegular result cfg regular`; `forCond` adds
  `hFalseShape : LabelShape cfg falseLabel {output with slots := output.slots.tail}`; split
  `nilJoin` into `nilJoinRegular` (+ `hReg` at `regular`) and `nilJoinExit` (+ `hExit :
  LabelShape cfg exitLabel input`); `callHead`/`switchTest`/`caseEntryPop`/`procAdapter`/
  `terminalHalt` stay base.
* `def GenShapeResultReg result cfg := ∀ block ∈ result.blocks, BlockGenShapeReg cfg block`
  (+ `append` mirroring `GenShapeResult.append`; NB `(a.append b).fallthrough? =
  b.fallthrough?` by `TypedCfgCompiler.Result.append`).
* 5-function mutual `genShapeReg_of_compile*`, each ADD `(hRegular : HRegular result cfg
  regular) (hCtx : CtxExitsShaped cfg ctx)` beside the existing `hBlocks`, concluding
  `GenShapeResultReg result cfg`.  Per-case threading (all obligations reduce to the four
  banked lemmas + `of_hasEntry`):
  - **stmtList nil** → `nilJoinRegular hFind (hRegular)`.
  - **stmtList cons no-tail** (`result = headResult`) → recurse head with the SAME `hRegular`
    (`result = headResult`) + `hCtx`.
  - **stmtList cons tail** (`result = headResult.append tailResult`): tail recursion gets
    `hRegular` verbatim (append fallthrough = tail's) ; head recursion gets
    `regularThread_tail_of_cons hHeadFall hTailCompile hTailBlocks` for its `restLabel supply`
    regular-thread; both get `hCtx`.
  - **stmt code** → `codeHead hCompile hBlocks hRegular` (result.fallthrough? = some output).
  - **stmt if** → `ifHead hCompile hBlocks hRegular`; body recursion gets
    `regularThread_of_requireFallthrough hRegular (result.fallthrough? = some {output.tail})
    (bodyResult.requireFallthrough? {output.tail})` + `hCtx` (body compiled with SAME ctx,
    same regular).
  - **stmt switch** → head is `codeHead` via `codeFact_of_switchHead` with `regular :=
    casesEntryLabel supply 0 cases`; its `hReg` needs `LabelShape cfg (casesEntryLabel supply
    0 cases) valueShape` = `of_hasEntry` on the cases/default sub-result
    (`cases_cons_test_hasEntry` at `switchTestLabel supply 0` for nonempty, else
    `default_hasEntry` at `label supply 1`; `casesEntryLabel` splits on `cases`).  Case bodies
    & default body recurse with `regularThread_of_requireFallthrough` (they require-fallthrough
    to `{valueShape.tail}` = the switch's fallthrough) + `hCtx`.
  - **stmt for_** → the cond block is `forCond`; its `hFalseShape` = `hRegular {condOutput.tail}`
    (loop fallthrough).  init recurse: `hRegular_init` = `LabelShape cfg (label supply 0)
    loopInput` (the cond block is a listed member of `result.blocks`) via membership+`hBlocks`;
    `hCtx` with break/continue CLEARED (vacuous), leave inherited.  body recurse: `hRegular_body`
    = `regularThread_of_requireFallthrough`-style at `label supply 2` (post entry, via
    `of_hasEntry` on `postResult`); `hCtx_body` from finding 3.  post recurse: `hRegular_post`
    = the cond-block LabelShape again; `hCtx` cleared/leave inherited.
  - **stmt brk/cont/leave** → `nilJoinExit hFind (hCtx.<x> …)` (input = the checked
    break/continue/leave shape).
  - **stmt call** → `callHead hLookup hCompile hBlocks` (base).
  - **stmt terminal** → `terminalHalt hFind` (base).
  - **cases cons** → `switchTest`/`caseEntryPop` base; body recurse with
    `regularThread_of_requireFallthrough` + `hCtx`; tail recurse with same `hRegular`/`hCtx`.
  - **default none/some** → `caseEntryPop` base; body recurse as case bodies.
Then `main`/`proc` composites: seed with `main_regular_labelShape` / `proc_regular_labelShape`
(regular-thread) and `CtxExitsShaped` (main: all-None-vacuous; proc: leave = `LabelShape.procExit`).

### THE FRONTIER (session 39)
1. **Assemble the strengthened mutual** per the recipe above (mechanical; the four banked
   combinators + `of_hasEntry`/`cases_*_hasEntry`/`default_hasEntry` discharge every case).
   Bank green.
2. **Assemble `hInv`** — with the enriched classification, each per-disjunct supplier gets:
   internal `LabelShape` inline (`of_compileBlockFuel?`/`of_hasEntry`), external regular-thread
   from the enriched field, dispatch `popReturn?` from `dispatch_popReturn?_of_stateRel`
   (banked s36) + site provenance.  Then `AllEntriesRealized.of_openStep_invariant`.
3. Then Step B (`openRunNPrefix_peephole_congr_of_source`); no swap arm on `peepholeBody` yet.

### Status handed to session 39
Landed: `InteractionLabelShapeTransport.lean` — `main_regular_labelShape`,
`proc_regular_labelShape` (`318302f1`); `regularThread_of_requireFallthrough`,
`regularThread_tail_of_cons` (`2b166df0`).  All green + axiom-clean.  **The option-B
threading toolkit is COMPLETE** (two boundary seeds + two per-descent combinators) and the
strengthened-mutual recipe is worked to the case level (incl. `for_`/`switch`), so session
39's assembly is mechanical.  `scripts/opt_harness.sh check` status: see run below.
`compile_correct`/`compile_correct_creation` UNCHANGED (frozen `Correctness.lean` untouched);
delta +0.

## Session-39 update (2026-07-19): the STRENGTHENED MUTUAL is ASSEMBLED and GREEN — enriched inductive + 5-function mutual + `compileBlock?` wrapper + MAIN-body composite, all axiom-clean; proc-body composite isolated to one additive provenance-layer gap

Session 39's mandate (per §Session-38 recipe): (1) assemble the strengthened mutual; (2)
assemble `hInv`; (3) Step B.  **Result: FOUR green, axiom-clean commits banking the entire
strengthened classification capstone** — the enriched inductive, all five mutual functions
(the external-regular `LabelShape` thread + ctx-exit bundle threaded through every
construct incl. `for_`/`switch`), the public `compileBlock?` wrapper, and the MAIN-body
composite.  The §Session-38 recipe proved essentially exact: the four banked toolkit lemmas
+ `of_hasEntry`/`of_compileBlockFuel?` discharged every case, and both the mutual (13 s
build) and the composites compiled on the FIRST attempt.  `hInv` (item 2) and Step B (item
3) NOT reached — the proc-body composite (the last piece before `hInv`) is blocked on a
single, precisely-isolated additive provenance-layer lemma (below).  No red code, no
sorries; `peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**; `scripts/opt_harness.sh
check` = OK (43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` axioms UNCHANGED.

### LANDED (green, axiom-clean)
* **`533a4a75`** — `InteractionBlockGenShapeRegular.lean` (NEW module): the threading
  scaffold + enriched inductive.
  * **`HRegular`** (`:59`, abbrev) — the threaded external-successor predicate
    `∀ out, result.fallthrough? = some out → LabelShape cfg regular out`, consumed verbatim.
  * **`CtxExitsShaped`** (`:68`, structure) — the ctx-exit `LabelShape` bundle
    (`brk`/`cont`/`leave` fields).
  * **`thread_of_target_requireFallthrough`** (`:83`) — fixed-target regular thread via a
    `requireFallthrough?` pin (if-body / switch-case-body / default-some / loop-body/post).
  * **`switchHead_regular_labelShape`** (`:105`) — the switch head's external-`regular`
    (`casesEntryLabel supply 0 cases`) `LabelShape`, splitting on `cases` (nonempty ⟶
    `cases_cons_test_hasEntry`; empty ⟶ `default_hasEntry`).
  * **`BlockGenShapeReg`** (`:141`, inductive) — the strengthened classification.  **NINE
    disjuncts, not ten**: the §Session-38 `nilJoinRegular`/`nilJoinExit` split is COLLAPSED
    into a single `nilJoin` carrying `hExit : LabelShape cfg exitLabel input` directly (the
    stored field is identical either way; `hInv` dispatches on block category, not the
    constructor — sound + simpler).  Added fields: `codeHead`/`ifHead` `+hReg`; `forCond`
    `+hFalseShape`; `caseEntryPop` `+hExit` (covers the `default`-less pop's EXTERNAL
    `.jump regular`, a genuine correction over the recipe's "caseEntryPop stays base");
    `nilJoin` `+hExit`; `procAdapter` `+hBodyShape`; `callHead`/`switchTest`/`terminalHalt`
    base.
  * **`GenShapeResultReg`** (`:291`) + `.append`.
* **`3b27318c`** — same module: the **5-function strengthened mutual** (the capstone).
  * **`thread_of_target_fallthrough`** (`:314`) — fallthrough-form fixed-target thread (loop
    `init`, whose `fallthrough?` is pinned directly, not via `requireFallthrough?`).
  * **`genShapeReg_of_compileBlockFuel?`** (`:337`), **`…StmtListFuel?`** (`:356`),
    **`…StmtFuel?`** (`:407`), **`…CasesFuel?`** (`:697`), **`…DefaultFuel?`** (`:758`) —
    each ADDs `(hRegular : HRegular result cfg regular) (hCtx : CtxExitsShaped cfg ctx)`
    beside `hBlocks`, concluding `GenShapeResultReg result cfg`.  Per-case threading exactly
    as the recipe: sequential head via `regularThread_tail_of_cons`, tail via defeq
    `append`-fallthrough; if/switch-case/default bodies via
    `thread_of_target_requireFallthrough (hRegular _ rfl) …`; `for_` cond `hFalseShape =
    hRegular {condOutput.tail} rfl`, init/post via `thread_of_target_*` at the cond-block
    `LabelShape` (membership+`hBlocks`), body via `of_compileBlockFuel? hPost`, ctx cleared
    (break/cont vacuous, leave inherited) / body ctx break=`hRegular`, continue=`hPost`
    entry; brk/cont/leave via `hCtx.{brk,cont,leave}`.
* **`f4231606`** — `InteractionHInvAssemblyRegular.lean` (NEW module): the composites.
  * **`genShapeReg_of_compileBlock?`** (`:42`) — public `compileBlock?` wrapper.
  * **`main_blockGenShapeReg`** (`:67`) — MAIN-body composite; `HRegular` discharged by the
    boundary seed `main_regular_labelShape` (external `regular = programEnd`),
    `CtxExitsShaped` vacuous (main ctx all-`none`).

### THE FRONTIER (session 40)
1. **The proc-body composite `proc_blockGenShapeReg`** — the ONLY remaining piece of the
   §Session-38 recipe.  Blocked on ONE additive provenance-layer lemma: the proc-body's
   external `regular = ProcLabel.exit proc.name` thread needs the seed
   `proc_regular_labelShape` (`InteractionLabelShapeTransport.lean:136`), whose hypothesis
   `bodyResult.requireFallthrough? (procExit proc) = some ()` is CONSUMED-and-discarded
   inside `mem_procBlocks_provenance_subset` (`InteractionProcBlockProvenance.lean:215`,
   the `hRequire` case) and is NOT re-exposed by `procBlocks_provenance_inProgram` (`:417`).
   `procFragment_of_lookup?` (`Core.lean:3525`) DOES expose it (`fragment.fallthrough`) but
   for `fragment.result`, not obviously the provenance's existential `bodyResult`.
   **Recipe for session 40**: add an ADDITIVE sibling
   `procBlocks_provenance_inProgram_fallthrough` (mirror `mem_procBlocks_provenance_subset`
   + `procBlocks_provenance_inProgram`, threading the in-scope `hRequire` into the
   existential — the `body`/`none`/`some` arms already have `hRequire` bound, so it is a
   one-field addition to the returned tuple, ~160-line mirror).  Then
   `proc_blockGenShapeReg`: body arm ⟶ `genShapeReg_of_compileBlock? hCompile hBlocks
   (proc_regular_labelShape context hLookup hRequire) hCtxProc`, where `hLookup` comes from
   `hProcMem : proc ∈ source.procs` via `ProcList.lookup?`-of-nodup, `hCtxProc = ⟨brk
   vacuous, cont vacuous, leave = procExit seed⟩`; adapter arm ⟶ invert `mkBlock?` as in
   base `proc_blockGenShape` + `procAdapter`'s new `hBodyShape` (the body entry `LabelShape`,
   `LabelShape.procEntry`/`of_hasEntry` on the body fragment).
2. **Assemble `hInv`** (item 2, unchanged from §Session-38 frontier) — with
   `main_blockGenShapeReg` + `proc_blockGenShapeReg` (exact-successor-enriched), each
   per-disjunct supplier gets: internal `LabelShape` inline, external regular-thread from the
   enriched field (`hReg`/`hFalseShape`/`hExit`/`hBodyShape`), dispatch `popReturn?` from
   `dispatch_popReturn?_of_stateRel` (banked s36) + site provenance.  Then
   `AllEntriesRealized.of_openStep_invariant`.
3. Then Step B (`openRunNPrefix_peephole_congr_of_source`); no swap arm on `peepholeBody`.

### Status handed to session 40
Landed (all green + axiom-clean): `InteractionBlockGenShapeRegular.lean` — the full enriched
inductive + threading scaffold (`533a4a75`) and the 5-function strengthened mutual
(`3b27318c`); `InteractionHInvAssemblyRegular.lean` — `genShapeReg_of_compileBlock?` +
`main_blockGenShapeReg` (`f4231606`).  Both modules wired into `Verification.lean`.  The
strengthened capstone is COMPLETE for the main body; the proc body needs the one additive
provenance lemma above, then `hInv` is the §Session-38 endgame.  `scripts/opt_harness.sh
check` = OK (43 theorems); `compile_correct`/`compile_correct_creation` axioms UNCHANGED;
delta +0.

## Session-40 update (2026-07-19): frontier items 1 & 2 CLOSED (proc-body strengthened composite `proc_blockGenShapeReg` now complete alongside `main_blockGenShapeReg`) + hInv item-3 STARTED — the two clean machinery dispatch legs banked; all green + axiom-clean in 3 commits

Session 40's mandate (per §Session-39 frontier): (1) the additive fallthrough provenance
lemma; (2) `proc_blockGenShapeReg`; (3) assemble `hInv`; (4) Step B.  **Result: THREE
green, axiom-clean commits** closing frontier items 1 & 2 (the strengthened classification
capstone is now COMPLETE for BOTH bodies) and opening item 3 with the two machinery
dispatch legs whose successor shape coincides with the entry `input`.  The §Session-39
recipe proved exact for items 1–2 (both compiled on the first attempt).  `hInv` (item 3)
is genuinely open — the head-construct legs (`codeHead`/`ifHead`/`callHead`/`forCond`/
`switchTest`) each need the openStep coupling to expose `next = regular`, not a clean
compose; and `caseEntryPop`/`procAdapter` need a fits-transport.  No red, no sorries;
`peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**; `scripts/opt_harness.sh check` = OK
(43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/
`compile_correct_creation` axioms UNCHANGED.

### LANDED (green, axiom-clean)
* **`5bba9a60`** — item 1, `InteractionProcBlockProvenance.lean` (additive):
  * **`mem_procBlocks_provenance_subset_fallthrough`** (`:390`) — the ~160-line mirror of
    `mem_procBlocks_provenance_subset`, additionally threading the in-scope `hRequire`
    (`bodyResult.requireFallthrough? (procExit proc) = some ()`) into the returned tuple,
    AND strengthening the adapter disjunct's `Or.inr` to carry `entry = ProcLabel.body
    proc.name` (needed for the adapter-arm body `LabelShape`).  Every leaf already has
    `hRequire` in scope, and every adapter `Or.inr` sets `entry := ProcLabel.body head.name`
    — one-field / `rfl` additions.
  * **`GeneratedContext.procBlocks_provenance_inProgram_fallthrough`** (`:453`) — the
    context wrapper adding `BlocksInProgram` (same `findBlock?_eq_some_of_mem` promotion as
    `procBlocks_provenance_inProgram`).
* **`ad8046ae`** — item 2, `InteractionHInvAssemblyRegular.lean`:
  * **`proc_blockGenShapeReg`** (`:100`) — the proc-body composite, the sibling of
    `main_blockGenShapeReg`.  Body arm ⟶ `genShapeReg_of_compileBlock? hCompile hBlocks
    (HRegular via `proc_regular_labelShape context hLookup hReq`) (CtxExitsShaped: brk/cont
    vacuous, leave = `LabelShape.procExit context hLookup`) block hBody`; adapter arm ⟶
    invert `mkBlock?` as in base `proc_blockGenShape`, then `procAdapter hType hFind
    hBodyShape` where `hBodyShape = of_compileBlock? hCompile hBlocks` under `output = input`
    (the `.relabel` retype, derived by `split` on the relabel `type?`).  `hLookup` from
    `hProcMem : proc ∈ source.procs` via `lookup?_eq_some_of_mem hSourceWF.1 hProcMem rfl`
    — **`proc_blockGenShapeReg` takes an added `hSourceWF : source.WF` hypothesis** (the
    invariant threads program WF; `main_blockGenShapeReg` needs none).
* **`7ba51a5c`** — item 3 (incremental), `InteractionHInvDispatch.lean` (NEW module, wired
  into `Verification.lean`): the two clean machinery dispatch legs.
  * **`realizedWitness_of_nilJoin_dispatch`** (`:44`) — unifies the entry `realizedWitness`
    to the join block by `findBlock?` uniqueness (so `SourceFrameFits input` transports with
    no extra hypothesis), then `realizedWitness_of_join_jump hFind hFits hStateRel hExec
    hExit`.
  * **`realizedWitness_of_terminalHalt_dispatch`** (`:82`) — vacuous via
    `halt_openStep_no_jump` (no entry witness needed).

### THE FRONTIER (session 41) — assemble `hInv`
The strengthened classification capstone is now COMPLETE for both bodies, and two of the
nine `BlockGenShapeReg` disjuncts have their `hInv` dispatch leg.  Remaining to close
`hInv` (`∀ e t transcript n s, realizedWitness cfg e t → Executes (openStep cfg e t) …
(jump n s) → realizedWitness cfg n s`):
1. **The five head-construct dispatch legs** — `codeHead`/`ifHead`/`callHead`/`forCond`/
   `switchTest`.  Each has its coupling supplier already banked
   (`realizedWitness_of_{code,if,call}_compile`, `realizedWitness_of_{condBlock,test}_jump`)
   BUT the supplier consumes `hLabelShape : LabelShape cfg next expected` at the CONCRETE
   jumped-to `next`, which the enriched `hReg`/`hFalseShape` fields supply only at
   `regular`/`falseLabel`.  So each leg needs `next = regular` (or `next ∈ {trueLabel,
   falseLabel}` for the branch/for legs) exposed FIRST — that fact lives inside
   `jump_state_rel_of_outcome`/`…_of_rel` (currently discarded as `_hNext`).  **Recipe**:
   either (a) expose a `next = regular` corollary of the coupling and feed the enriched
   field at that equality, or (b) generalise the head suppliers to take `hLabelShape` in the
   threaded `∀ out, fallthrough? = some out → …` form the enriched fields already are.
   Option (b) matches the field shapes (`HRegular`/`hFalseShape`) directly and is preferred.
2. **`caseEntryPop` + `procAdapter` legs** — need the child fits at the SHIFTED shape
   (`output` after `.pop` / `.relabel`), which is NOT the entry `SourceFrameFits input`.
   The pop leg needs `source.evm.stack.pop = some (stack, value)` + fits at the popped
   shape; the adapter leg needs `SourceFrameFits output …` (transport `output = input`
   under the no-op relabel).  Both are dischargeable at the capstone where the source
   stack/shape are pinned — defer until the head legs land.
3. **Assemble the `hInv` case split** — from `realizedWitness cfg e t` recover
   `cfg.findBlock? e = some block`; `block_category` splits into main/proc; feed
   `main_blockGenShapeReg` / `proc_blockGenShapeReg` (the latter with `hSourceWF`) to get
   `BlockGenShapeReg cfg block`; `rcases` the nine disjuncts and apply the matching dispatch
   leg (items 1–2 above + the two banked machinery legs).  Then
   `AllEntriesRealized.of_openStep_invariant` with `realized := realizedWitness cfg` and the
   entry witness (`realizedWitness_of_stateRel`).
4. Then Step B (`openRunNPrefix_peephole_congr_of_source`); no swap arm on `peepholeBody`.

### Status handed to session 41
Landed (all green + axiom-clean): `InteractionProcBlockProvenance.lean` —
`mem_procBlocks_provenance_subset_fallthrough` + `procBlocks_provenance_inProgram_fallthrough`
(`5bba9a60`); `InteractionHInvAssemblyRegular.lean` — `proc_blockGenShapeReg` (`ad8046ae`);
`InteractionHInvDispatch.lean` (NEW, wired) — `realizedWitness_of_nilJoin_dispatch` +
`realizedWitness_of_terminalHalt_dispatch` (`7ba51a5c`).  The strengthened capstone is
COMPLETE for both bodies; `hInv` needs the seven remaining dispatch legs (five head
constructs blocked only on exposing the jumped-to label = the threaded regular/false shape;
two machinery legs on a fits-transport) then the case-split assembly.
`scripts/opt_harness.sh check` = OK (43 theorems); `compile_correct`/`compile_correct_creation`
axioms UNCHANGED; delta +0.

## Session-41 update (2026-07-19): the SEVEN remaining `hInv` dispatch legs banked — every one of the nine `BlockGenShapeReg` disjuncts now has its successor leg; all green + axiom-clean in 4 commits

Session 41's mandate (per §Session-40 frontier): (1) the five head-construct dispatch legs;
(2) the two machinery legs (`caseEntryPop`/`procAdapter`); (3) assemble `hInv`; (4) Step B.
**Result: FOUR green, axiom-clean commits** banking SIX new dispatch legs
(`codeHead`/`ifHead`/`forCond`/`switchTest` + `procAdapter`/`caseEntryPop`), all in
`InteractionHInvDispatch.lean`.  With the two §Session-40 machinery legs
(`nilJoin`/`terminalHalt`) and the pre-existing `realizedWitness_of_call_compile` serving
the `callHead` disjunct directly, **all nine `BlockGenShapeReg` disjuncts now have a
`realizedWitness` `openStep`-jump successor leg**.  `peepholeBody`/public spine UNTOUCHED ⇒
delta **+0**; `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation`
axioms UNCHANGED.

### KEY DESIGN FINDING (drives the §Session-40 recipe correction)
The §Session-40 frontier framed all five head legs as "blocked only on exposing the
jumped-to label = the threaded regular/false shape".  That is EXACT only for `codeHead`
(single fallthrough to `regular`, `next = regular`) and `ifHead` (the `.if_` compile fact
IN the field carries the body compile, so the `bodyLabel` shape is derivable via
`of_compileBlockFuel?`).  For the branch machinery legs the enriched field is genuinely
INSUFFICIENT for the non-`regular`/`false` target:
* **`forCond`** — `next = if cond then trueLabel else falseLabel`; the field carries only
  `hFalseShape` (the loop-exit) and the condition block's `hFind` — NOT the loop-body
  compile — so `trueLabel`'s (loop body) `LabelShape` is a genuine parameter.
* **`switchTest`** — `next = if caseValue = value then caseLabel else nextTest`; the field
  carries only the test block (`hMem`) — NOT the case-entry/next-test entries — so both
  target shapes are parameters, as is the scrutinee-pop existence.
* **`caseEntryPop`/`procAdapter`** — unconditional jump, so the enriched `hExit`/`hBodyShape`
  IS the exact target shape, but the child fits is at the SHIFTED shape (`output` after
  `.pop`/`.relabel`), NOT the entry fits at `input`/`blockInput`; the fits-transport is a
  parameter.
CFG well-typedness (`typeWith?` for `.jumpi`, `Typing.lean:393`) gives only
`restShape.compatible targetShape` (compatibility, NOT the `block.input = shape` EQUALITY
`LabelShape` demands), so the branch-target EQUALITY shapes are NOT recoverable from
well-typedness alone — they need the compiler-structure (the body/case compile facts),
which live at the capstone.  Accordingly these four legs (`forCond`/`switchTest`/
`procAdapter`/`caseEntryPop`) take the missing target shapes / fits-transports as clean
**source-quantified hypotheses**, exactly mirroring how the base suppliers
(`realizedWitness_of_{adapter,pop}_jump`) already take their child fits as a hypothesis —
the dispatch/successor reasoning is fully banked, and ONLY the compiler-shape obligations
remain, isolated for discharge at the assembly.

### LANDED (green, axiom-clean) — all in `InteractionHInvDispatch.lean`
* **`4035f64f`** — `realizedWitness_of_codeHead_dispatch` (`:113`).  Self-contained: mirrors
  `realizedWitness_of_code_compile` but consumes the enriched `HRegular` field (`hReg` at
  `regular`), exposing `next = regular` via `jump_state_rel_of_outcome` and feeding `hReg`
  at the fallthrough shape (existing by `fallthrough_code_of_compileStmtFuel?`).  Added
  import `InteractionCodeConstructCoupling`.
* **`ee0fb302`** — `realizedWitness_of_ifHead_dispatch` (`:163`).  Self-contained: builds the
  condition `DoneRel` by `openRunCondition_jumpi_toCfg`, exposes
  `next = if cond then bodyLabel else regular` via `jump_state_rel_of_rel`, case-splits —
  `regular` = `hReg`, `bodyLabel` = body-entry `LabelShape` from
  `components_of_compileStmtFuel?_if` → `of_compileBlockFuel?`.
* **`56f28ff5`** — `realizedWitness_of_procAdapter_dispatch` (`:255`) +
  `realizedWitness_of_caseEntryPop_dispatch` (`:304`).  Unify the block by `findBlock?`
  uniqueness, apply the successor supplier (`realizedWitness_of_adapter_jump` /
  `openStep_pop_jump`) at the enriched exact-target field; the shifted-shape fits-transport
  is the source-quantified `hTransport` / `hPopTransport` parameter.
* **`fdfc43cb`** — `realizedWitness_of_forCond_dispatch` (`:360`) +
  `realizedWitness_of_switchTest_dispatch` (`:430`).  `forCond` mirrors `ifHead` (condition
  `DoneRel` + `jump_state_rel_of_rel` case-split) with `hTrueShape` parameterized (field
  lacks the loop-body compile).  `switchTest` settles `openStep` via `openStep_test`
  (source-preserving comparison, child fits = entry fits) and case-splits on
  `caseValue = value`, with `hCaseShape`/`hNextShape` + `hPopExists` parameterized.

### THE FRONTIER (session 42) — assemble `hInv` (mandate item 3)
Every disjunct's dispatch leg is banked; assembling `hInv` (`∀ e t transcript n s,
realizedWitness cfg e t → Executes (openStep cfg e t) … (jump n s) → realizedWitness cfg n
s`) is now purely: (a) `block_category` split (main/proc/dispatch/programEnd); (b) main/proc
→ `main_blockGenShapeReg`/`proc_blockGenShapeReg` → `BlockGenShapeReg cfg block`; (c) `rcases`
the nine disjuncts and apply the matching leg; (d) dispatch arm via
`realizedWitness_of_dispatch_jump` + its s28/s36 suppliers; (e) programEnd via
`programEnd_openStep_no_jump`; then `AllEntriesRealized.of_openStep_invariant` (with
`realized := realizedWitness cfg`, entry witness `realizedWitness_of_stateRel`).

**The genuine remaining work is step (c)'s per-disjunct obligation discharge** — the
source-quantified parameters the four branch/machinery legs take:
1. **`forCond` `hTrueShape`** — the loop-body entry (`LabelSupply.label supply 1`) input =
   `{condOutput with slots := tail}` (`branchInput`, `TypedCfgCompiler.lean:462+`).  Derive
   from the loop body compile fact (`compileBlockFuel? … bodyLabel branchInput postLabel`)
   via `of_compileBlockFuel?` — needs the `for_` provenance to expose that sub-compile
   (analogous to how `ifHead` gets its body compile from the field, but here it must come
   from the loop provenance, not the disjunct field).
2. **`switchTest` `hCaseShape`/`hNextShape`/`hPopExists`** — both switch successors have
   input `valueShape` (case-entry pop block + next test block, both listed in the switch
   result); derive their `LabelShape` from the switch-result membership + `of_hasEntry`; the
   scrutinee pop from the switch's `requireSourceWords? 1 valueShape` (source stack ≥ 1).
3. **`procAdapter` `hTransport`** (`SourceFrameFits blockInput n → SourceFrameFits output n`,
   `blockInput = Shape.procEntry proc`, `output = fragment.input`) — the relabel retype
   preserves the source frame BECAUSE the compiler builds `fragment.input` with the same
   `sourceView`/`returnTokenDepth?` as `procEntry proc`; needs the proc-fragment shape
   invariant.
4. **`caseEntryPop` `hPopTransport`** (pop existence + `SourceFrameFits output` at the
   popped length) — from the switch's `requireSourceWords? 1` (pop exists) +
   `sourceFrameFits_tail` (popped fits).
5. **`callHead`** (served by `realizedWitness_of_call_compile` directly) — discharge
   `hSplit` (`splitArgs? proc.argc source.evm.stack`), `hProcWF` (`proc.WF` from
   `source.WF`), `hEntryShape` (callee entry `LabelShape`), `hChildFits` (pushed child frame
   fits) from the call provenance + `sourceFrameFits_afterCall`.
These are the compiler-shape invariants at each generated block category — the same facts
the FORWARD realizing recursors establish; the reverse `hInv` now needs them exposed as
standalone shape lemmas.  Once discharged, the assembly is mechanical and yields
`AllEntriesRealized`, closing route-B; **then** Step B (`openRunNPrefix_peephole_congr_of_source`).

### Status handed to session 42
Landed (all green + axiom-clean), all in `InteractionHInvDispatch.lean`:
`realizedWitness_of_codeHead_dispatch` (`:113`, `4035f64f`);
`realizedWitness_of_ifHead_dispatch` (`:163`, `ee0fb302`);
`realizedWitness_of_procAdapter_dispatch` (`:255`) + `realizedWitness_of_caseEntryPop_dispatch`
(`:304`) (`56f28ff5`); `realizedWitness_of_forCond_dispatch` (`:360`) +
`realizedWitness_of_switchTest_dispatch` (`:430`) (`fdfc43cb`).  All nine `BlockGenShapeReg`
disjuncts have a dispatch leg; `hInv` needs the case-split assembly + discharging the five
compiler-shape obligation groups above (the branch/machinery legs' source-quantified
parameters).  `scripts/opt_harness.sh check` = OK (43 theorems);
`compile_correct`/`compile_correct_creation` axioms UNCHANGED; delta +0.

## Session-42 update (2026-07-19): FOUR of the five compiler-shape obligation groups discharged by STRENGTHENING the `BlockGenShapeReg` disjuncts (groups a/b/c/d); only callHead (e) + the `hInv` case-split glue remain — all green + axiom-clean in 4 commits

Session 42's mandate: (1) discharge the five compiler-shape obligation groups the branch/
machinery dispatch legs take as source-quantified hypotheses; (2) assemble `hInv`; (3) Step B.
**Result: FOUR green, axiom-clean commits** moving obligation groups (a) forCond,
(b) switch case/next shapes + pop, (c) proc-adapter relabel transport, (d) caseEntryPop pop
transport OUT of the dispatch-leg hypotheses and INTO the `BlockGenShapeReg` disjunct fields,
supplied at the capstone/composite construction sites where the enclosing construct's
provenance is in scope.  This is exactly mandate item-1's first option ("small additions to
the disjunct fields via enrichment lemmas over the existing capstone results").  The dispatch
legs (`InteractionHInvDispatch.lean`) are UNCHANGED — they already take these as hypotheses,
so the strengthened disjuncts now feed them directly at the (not-yet-written) assembly.
`peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**; full `lake build` green;
`scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation`
axioms UNCHANGED.

### KEY DESIGN FINDING (why disjunct-strengthening, not standalone reverse lemmas)
The §Session-41 frontier framed groups a–d as either "small additions to the disjunct fields"
OR "standalone reverse lemmas".  Investigation confirmed the **standalone-from-disjunct-fields
route is impossible** for every branch/machinery group: the missing shape/transport facts are
NOT derivable from the disjunct fields alone (CFG well-typedness gives only `compatible`, not
the `LabelShape` EQUALITY; `relabelCompatible` permits `.word` wildcards so does NOT pin
`returnTokenDepth?`; `.pop` typing gives `slots` non-empty but not `sourceLength ≥ 1`).  They
need the enclosing construct's provenance, which is LOST once the composite collapses to
`BlockGenShapeReg`.  BUT that provenance IS in scope at the capstone/composite CONSTRUCTION
sites — so strengthening the disjunct fields (supplied there) is the correct additive move.
`BlockGenShapeReg` had NO external consumer (no `rcases`/`cases`) yet, so adding fields only
touched the construction sites; the dispatch legs and everything downstream are unaffected.

### LANDED (green, axiom-clean)
* **`52b47014`** — group (a): `BlockGenShapeReg.forCond` gains `hTrueShape`
  (`InteractionBlockGenShapeRegular.lean:192`), the loop-body entry `LabelShape`
  (`= { output with slots := tail }`), supplied at the capstone forCond site from the
  for-loop body compile fact via `LabelShape.of_compileBlockFuel? hBody hBodyBlocks`.
* **`3c2f05aa`** — new module `InteractionHInvObligations.lean` (wired into the build via an
  import from the capstone): `caseEntryPop_popTransport` (`:38`) — from the switch scrutinee
  source word (`1 ≤ sourceLength input`) + `.pop` typing, every source frame fitting `input`
  has a poppable top and the popped frame fits the `.pop` output (via `sourceFrameFits_tail`);
  `switchTest_popExists` (`:76`) — same source word gives the scrutinee-pop existence.
* **`02b60587`** — groups (b)+(d): `BlockGenShapeReg.switchTest` gains
  `hPopExists`/`hCaseShape`/`hNextShape` (`:212`/`:217`/`:218`); `BlockGenShapeReg.caseEntryPop`
  gains `hPopTransport` (`:238`).  Threads `hValueSource` (`1 ≤ sourceLength valueShape`, from
  the switch's previously-discarded `requireSourceWords? 1`) and `hDefaultShape` (terminal
  default-entry `LabelShape`, from `default_hasEntry`) through
  `genShapeReg_of_compileCasesFuel?`/`genShapeReg_of_compileDefaultFuel?`.  case/next entry
  shapes: `cases_cons_case_hasEntry`/`cases_cons_test_hasEntry` (internal) + `hDefaultShape`
  (last-case EXTERNAL successor = the default entry `LabelSupply.label base 1`).
* **`63fc05c3`** — group (c): `BlockGenShapeReg.procAdapter` gains `hTransport`
  (`:283`), the `SourceFrameFits` transport across the runtime-no-op relabel
  (`procEntry proc` and body `input` both carry `returnTokenDepth? = some proc.argc`, so both
  fits reduce to `n = argc`).  To supply it, the proc-block provenance
  (`mem_procBlocks_provenance_subset_fallthrough` +
  `procBlocks_provenance_inProgram_fallthrough`, `InteractionProcBlockProvenance.lean:416`/`663`)
  adapter disjunct is ENRICHED with `input.returnTokenDepth? = some proc.argc`, drawn from the
  generation-time `requireReturnTokenDepth?` check (`hFrame`) already in the induction;
  `proc_blockGenShapeReg`'s adapter case (`InteractionHInvAssemblyRegular.lean:116`,`:154+`)
  builds `hTransport` via `sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some` +
  `returnTokenDepth?_procEntry`.  (Provenance enrichment strengthens the RETURNED existential;
  the sole consumer `proc_blockGenShapeReg` updated; full build confirms no other breakage.)

### THE FRONTIER (session 43) — group (e) callHead + the `hInv` case-split glue
Eight of the nine `BlockGenShapeReg` disjuncts (codeHead, ifHead, forCond, switchTest,
caseEntryPop, nilJoin, procAdapter, terminalHalt) now carry, in the disjunct, EVERY field
their dispatch leg needs — so at the assembly each of those eight arms feeds its dispatch leg
(`InteractionHInvDispatch.lean`) directly from `rcases`.  Remaining:
1. **callHead group (e)** — served by `realizedWitness_of_call_compile`
   (`InteractionConstructCoupling.lean:123`), which needs `hSplit`/`hProcWF`/`hLabelShape`
   (callee `procEntry`)/`hFits`.  These are NOT static disjunct fields: `hSplit`
   (`splitArgs? proc.argc source.evm.stack`) depends on the RUNTIME source stack, so it is
   discharged at the ASSEMBLY from the realized witness's `SourceFrameFits` + a call
   "needs argc source words" fact; `hProcWF` from `source.WF`; `hLabelShape` from
   `LabelShape.procEntry context hLookup`; `hFits` via `sourceFrameFits_afterCall`-style
   pushed-frame reasoning.  Recommend: bank a `callHead` dispatch supplier that takes the
   `realizedWitness` + `source.WF` + the callHead compile fact and discharges (e) internally
   (mirroring how the other legs consume the witness), then the assembly's callHead arm is a
   one-liner like the other eight.
2. **The dispatch arm** (`block_category`'s 3rd arm) — NOT yet packaged.  Needs a lemma that,
   from a `dispatchBlocks` membership + the realized witness, recovers the site provenance
   (`hLookup`/`hSiteProc`/`hSiteMem`) and the frame facts (`hPop` via
   `dispatch_popReturn?_of_stateRel` when tokens = `site.token :: _`; `hAttach`/`hRetc` from
   the site's `retc` identity) to feed `realizedWitness_of_dispatch_jump`
   (`InteractionRealizedWitnessSuccessor.lean:149`).  This is the heaviest remaining sub-assembly.
3. **`hInv` assembly** — with 1+2 done: from `realizedWitness cfg e t` extract
   `hFind : findBlock? e = some block` (the witness's first component); `block_category context
   hFind` → 4 arms; main → `main_blockGenShapeReg`, proc → `proc_blockGenShapeReg hSourceWF`,
   each `rcases`'d into the 9 disjuncts → matching dispatch leg (8 direct, callHead via item 1);
   dispatch arm via item 2; programEnd via `programEnd_openStep_no_jump`.  Then
   `AllEntriesRealized.of_openStep_invariant` with `realized := realizedWitness cfg`, entry
   witness `realizedWitness_of_stateRel`.  `hInv` is ONE theorem (all-or-nothing — no partial
   commit), so land items 1+2 as their own green banks FIRST, then the glue.
4. Then Step B (`openRunNPrefix_peephole_congr_of_source`, mandate item 3).

### Status handed to session 43
Landed (all green + axiom-clean): forCond `hTrueShape` (`52b47014`); obligations module
`caseEntryPop_popTransport`/`switchTest_popExists` (`3c2f05aa`); switchTest
`hPopExists`/`hCaseShape`/`hNextShape` + caseEntryPop `hPopTransport` (`02b60587`); procAdapter
`hTransport` + proc-provenance depth enrichment (`63fc05c3`).  Obligation groups a/b/c/d are
now CARRIED IN the disjuncts; only callHead (e) + the dispatch-arm recovery + the `hInv`
case-split glue remain (frontier items 1–3 above).  Full `lake build` green;
`scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` axioms UNCHANGED; delta +0.

## Session-43 update (2026-07-20): callHead group-(e) supplier banked (with a new ProcsShaped disjunct thread) + the dispatch arm's structural owning-proc provenance; the dispatch openStep-jump INVERSION + the hInv glue remain — all green + axiom-clean in 2 commits

Session 43's mandate (per §Session-42 frontier): (1) the callHead group-(e) supplier;
(2) the dispatch-arm packaging; (3) the hInv case-split glue; (4) Step B.  **Result: TWO
green, axiom-clean commits** landing item 1 in full and item 2's structural half.  The
hInv glue (item 3, all-or-nothing) and Step B stay closed behind item 2's remaining
*dispatch openStep-jump inversion* (isolated below).  `peepholeBody`/public spine
UNTOUCHED ⇒ delta **+0**; full `lake build` green; `scripts/opt_harness.sh check` = OK
(43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` axioms UNCHANGED.

### KEY DESIGN FINDING (why callHead needed a new thread, not the §Session-42 route)
The §Session-42 frontier framed the callHead supplier as a standalone lemma taking
`realizedWitness + source.WF + the callHead compile fact`, discharging `hLabelShape` from
`LabelShape.procEntry context hLookup`.  Investigation showed this is **not** directly
possible: `LabelShape.procEntry` needs `lookup? name source.procs`, but the callHead
disjunct only exposes `lookup? name ctx.procs` for the LOCAL compile context `ctx`, and the
`ctx.procs = source.procs` link is LOST once the composite collapses to `BlockGenShapeReg`
(the disjunct existentially hides `ctx` without recording the equality, and `source` is not
even in the `BlockGenShapeReg` signature).  `ctx.procs` IS constant through the whole
generation recursion (the compiler never rewrites it — every context update is `{ctx with
break/continue/leave := …}`), and the equality is in scope at the composite CONSTRUCTION
sites (main ctx `= {procs := source.procs}`; proc ctx `= {procs := source.procs, leave…}`).
So the correct additive move — exactly §Session-42's disjunct-strengthening methodology —
is to thread a new `ProcsShaped cfg ctx` predicate (bundling, per `ctx.procs` lookup, the
callee entry `LabelShape` + `proc.WF`) through the mutual and store its output in the
strengthened callHead disjunct.  `ProcsShaped` reads only `ctx.procs`, so it threads
UNCHANGED and transfers across the `for_` re-scopings by `ProcsShaped.of_procs_eq`.

**LANDING PITFALL (do not repeat):** `ProcsShaped.of_procs_eq rfl hProcs` at the `for_`
sites elaborates AMBIGUOUSLY on a clean build — `rfl` greedily unifies the source `ctx`
into the target record, so `hProcs : ProcsShaped cfg ctx` is rejected against
`ProcsShaped cfg {ctx with …}`.  A stale-olean `lake build` masked this; the canonical
`scripts/opt_harness.sh check` caught it.  Fix: pin the source explicitly —
`ProcsShaped.of_procs_eq (ctx := ctx) rfl hProcs`.  **Always gate on the harness, not a
targeted `lake build`, before committing changes to the shared mutual.**

### LANDED (green, axiom-clean)
* **`829a18e0`** — item 1.  `ProcsShaped` structure + `of_procs_eq` + `seed`
  (`InteractionBlockGenShapeRegular.lean:79`/`98`/`110`); the predicate threaded through all
  five `genShapeReg_of_compile*` mutual functions + the `genShapeReg_of_compileBlock?`
  wrapper (`InteractionHInvAssemblyRegular.lean:52`); `BlockGenShapeReg.callHead` gains
  `hEntryShape` + `hProcWF` (`:171`+); seeded in `main_blockGenShapeReg` (now takes
  `hSourceWF`) + `proc_blockGenShapeReg` via `ProcsShaped.seed context hSourceWF rfl`.  The
  group-(e) leg **`realizedWitness_of_callHead_dispatch`**
  (`InteractionHInvDispatch.lean:484`) wraps `realizedWitness_of_call_compile`, deriving
  `splitArgs?` (entry `SourceFrameFits` ∘ `requireSourceWords? proc.argc` from
  `components_of_compileStmtFuel?_call`) and the pushed child fits
  (`SourceFrameFits.procEntry_of_splitArgs`; `pushReturn`/`withEVM` leave `evm.stack = args`)
  internally.
* **`d7494786`** — item 2 (structural half).  **`dispatchBlock_provenance`**
  (`InteractionHInvAssembly.lean:101`): from `block ∈ dispatchBlocks source.procs
  (context.main.calls ++ context.procCalls)` (block_category's 3rd arm) recover
  `proc ∈ source.procs`, `lookup? proc.name source.procs = some proc` (`source.WF`
  name-uniqueness), and `block = dispatchBlock proc context.calls` via `List.mem_map`.

### THE FRONTIER (session 44) — the dispatch openStep-jump inversion, then hInv, then Step B
Eight of nine `BlockGenShapeReg` disjuncts already feed their dispatch leg directly; callHead
(nine) is now served by `realizedWitness_of_callHead_dispatch`.  What blocks `hInv`:

1. **The dispatch openStep-jump inversion** (item 2's remaining heavy half — the genuine
   frontier).  `realizedWitness_of_dispatch_jump`
   (`InteractionRealizedWitnessSuccessor.lean:149`) consumes the SITE facts
   `hSiteProc`/`hSiteMem`/`hRel : StateRel bodyState (site.token :: tokens) target`/`hPop`/
   `hAttach`/`hRetc`.  `dispatchBlock_provenance` gives `hLookup`; `dispatch_popReturn?_of_stateRel`
   (`InteractionHInvAssembly.lean:88`) gives `hPop` ONCE tokens are known non-empty.  The
   missing move: from `hExec` (the exit block's `openStep` PRODUCED a `.jump`, so the
   `returnDispatch` must have SUCCEEDED — `findTarget?` on the runtime return token returned
   `some`), invert to recover the matching `site` (`site.token = head token`, `site.procName =
   proc.name`, `site ∈ context.calls`) plus `hAttach`/`hRetc` (the popped frame's stack-length
   `= proc.retc` — a `procExit` `SourceFrameFits` fact — and `retc` identity — a
   procedure-frame-safety fact, likely needing `source.FrameSafe`, NOT in `realizedWitness`
   alone).  This is a multi-lemma sub-assembly over `returnDispatch`'s `openStep`, the ghost/
   runtime return-token correspondence in `StateRel`, and `findTarget?_some` inversion; budget
   it as its own session.  Recommended intermediate green banks: (a) a `findTarget?`-some ⟶
   `∃ site ∈ returnSitesFor …, site.token = tok` inversion; (b) a `StateRel`-at-`procExit` ⟶
   runtime-return-token-`= head-ghost-token` correspondence; (c) `returnSitesFor ⊆ calls` +
   `procName` (probably already present in `TypedCfgCompilerFacts.Call`).
2. **`hInv` assembly** (item 3, all-or-nothing).  With item 1 done, its 9-disjunct dispatch is
   ready: unpack `realizedWitness cfg e t`; `block_category context hFind` → 4 arms; main →
   `main_blockGenShapeReg context hSourceWF`, proc → `proc_blockGenShapeReg context hSourceWF`,
   each `rcases`'d into 9 disjuncts → matching leg (8 machinery/head + callHead via
   `realizedWitness_of_callHead_dispatch`); dispatch arm via item-1 above once the inversion
   lands; programEnd via `programEnd_openStep_no_jump`.  Then
   `AllEntriesRealized.of_openStep_invariant` with `realized := realizedWitness cfg`, entry
   witness `realizedWitness_of_stateRel`.  Note the head/machinery legs each need their
   disjunct's obligation fields fed from `rcases` (all now carried) plus, at the assembly, the
   block-input/entry unifications from the shared `findBlock?` (mirror
   `realizedWitness_of_procAdapter_dispatch`'s `Option.some.inj (hFindReal.symm.trans hFind)`).
3. Then Step B (`openRunNPrefix_peephole_congr_of_source`).

### Status handed to session 44
Landed (all green + axiom-clean): item 1 in full — `ProcsShaped` thread + callHead
strengthening + `realizedWitness_of_callHead_dispatch` (`829a18e0`); item 2 structural half —
`dispatchBlock_provenance` (`d7494786`).  All nine `BlockGenShapeReg` disjuncts now have a
successor leg AND every field their leg needs.  Sole remaining blocker to `hInv` = the
dispatch openStep-jump inversion (frontier item 1); then the `hInv` glue (item 2) and Step B.
Full `lake build` green; `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation`
axioms UNCHANGED; delta +0.

## Session-44 update (2026-07-20): the dispatch `openStep`-jump INVERSION is DONE (frontier item 1) and the dispatch arm PACKAGED (item 2) — all green + axiom-clean in 2 commits; new leaf module `InteractionDispatchInversion.lean`

Session 44's mandate (per §Session-43 frontier): (1) the dispatch openStep-jump inversion via
the recommended intermediate banks; (2) the dispatch-arm packaging; (3) the `hInv` case-split
(all-or-nothing, only after 1+2); (4) Step B.  **Result: TWO green, axiom-clean commits**
landing items 1 and 2 in full.  The inversion — §Session-43's "genuine frontier … budget it as
its own session" — is **closed**.  Item 3 (`hInv`) and Step B remain blocked ONLY on the
dispatch arm's residual *finisher* (`hFinish`, isolated below): the `source.FrameSafe`-dependent
frame facts + the return-site provenance, exactly the two obligations §Session-43 flagged as not
carried by `realizedWitness`.  `peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**; full
`lake build` green; `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆ `[propext,
Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` axioms UNCHANGED.

### KEY DESIGN FINDING (the inversion is source-run-free; only the finisher needs FrameSafe)
§Session-43 framed the inversion as needing the "StateRel ghost/runtime token correspondence"
and "`findTarget?`-some inversion", with `hRetc` "likely needing `source.FrameSafe`".  The clean
split confirmed: the *core* inversion (recovering `site`/`procName`/membership + `tokens =
site.token :: rest` + `next = site.returnLabel`) is entirely **source-run-free** — it composes
two pure banks.  The single elegant load-bearer is **`get_retc_of_stateRel_procExit`**:
`target.stack[proc.retc]? = tokens.head?`.  This ONE equation does double duty — it pins the
runtime `returnDispatch` token to the ghost head token AND (since a jump forces the slot
populated) forces the token list non-empty — so the whole `runTerm`-of-`returnDispatch` case
analysis (empty table → `.invalid`; empty tokens → out-of-range slot → `.invalid`; no match →
`.invalid`; match → `.jump`) collapses to the one jump branch, discharged by
`findTarget?_returnSitesFor_inv`.  `hPop` then falls out of `dispatch_popReturn?_of_stateRel`.
The ONLY residue needing `source.FrameSafe` is the *finisher*: `attachReturns?`/`frame.retc =
proc.retc` (frame safety) and `LabelShape`/`SourceFrameFits` at `site.returnLabel` (return-site
provenance).  Packaged additively as `hFinish`, exactly the threaded-finisher discipline of the
`caseEntryPop`/`procAdapter` legs.

### LANDED (green, axiom-clean) — all in `InteractionDispatchInversion.lean` (imported into `Verification`)
* **`ee493d26`** — inversion substrate (§Session-43 recommended banks (a)+(b)):
  * **`findTarget?_returnSitesFor_inv`** (`:49`) — the reverse of
    `findTarget?_returnSitesFor_of_mem`: a successful `findTarget?` over `returnSitesFor name
    calls` exposes the owning `DispatchSite ∈ calls` with matching `procName`/`token`/
    `returnLabel`.  Pure `filterMap` induction.
  * **`get_retc_of_stateRel_procExit`** (`:91`) — the `StateRel`-at-`procExit` runtime/ghost
    token correspondence `target.stack[proc.retc]? = tokens.head?` (via `realizeStack_append_prefix`
    + `SourceFrameFits.2` at depth `proc.retc` from `returnTokenDepth?_procExit`).
* **`2eb2686b`** — the inversion core + arm packaging (items 1 core + 2):
  * **`dispatch_openStep_jump_inv`** (`:158`) — THE inversion.  From `hExec` (exit-block
    `openStep` jumped) recover `∃ site ∈ context.calls, site.procName = proc.name ∧ tokens =
    site.token :: rest ∧ next = site.returnLabel ∧ state' = {target with stack :=
    target.stack.eraseIdx proc.retc}`.  Reduces the empty-body dispatch block's `openStep` to
    `pure (runTerm procExit term target)` (explicit-record `findBlock?` via
    `context.dispatchBlock` + `change`/`runTermChecked` mirror of the `LeafPreservation`
    private reductions), splits `sites.isEmpty`, then the token/`findTarget?` case analysis.
  * **`realizedWitness_of_dispatch_arm`** (`:316`) — the dispatch arm (`block_category`'s third
    arm).  Composes `dispatch_openStep_jump_inv` (site recovery) + `dispatch_popReturn?_of_stateRel`
    (`hPop`) + `realizedWitness_of_dispatch_jump` (caller `StateRel` relay), leaving `hFinish`
    (the FrameSafe/return-site obligations) as the sole additive hypothesis.

### THE FRONTIER (session 45) — discharge `hFinish`, then `hInv`, then Step B
The dispatch arm now lands `realizedWitness cfg next state'` modulo `hFinish` — the SAME shape as
the eight machinery/head legs land modulo their threaded fields.  So the residual work before
`hInv` is purely the per-leg field/`hFinish` suppliers, all at the capstone assembly:

1. **Discharge `hFinish`** (the dispatch arm's residual).  For the recovered `site`/`rest`/
   `frame`/`returns`, supply from the in-scope source run + `source.FrameSafe` (thread it as an
   additive `hSourceFrameSafe` hypothesis at the composite level, mirroring how `hSourceWF` was
   threaded through main/proc composites — the OIC splice has it in scope):
   (a) `attachReturns? frame bodyState.evm.stack = some stack` and `frame.retc = proc.retc` — the
       popped frame's `retc` equals the proc's `retc` (procedure-identity / frame-safety);
       `bodyState.evm.stack.length = proc.retc` is already in hand from the `procExit`
       `SourceFrameFits` (`hFits.2`), which makes `attachReturns?` succeed once `frame.retc =
       proc.retc`.
   (b) `LabelShape cfg site.returnLabel callerInput` + `SourceFrameFits callerInput stack.length`
       — the caller-continuation shape at the registered return label.  `site.returnLabel` is the
       call site's `regular` label; recover its compiled block's `LabelShape` via the call-site
       provenance (the `DispatchSite` came from a `compileStmtFuel?_call` whose `regular` block is
       in-program), and the restored-frame fit from the caller `SourceFrameFits` transported
       across the one-activation peel.
2. **`hInv` assembly** (item 3, all-or-nothing).  Unchanged from §Session-43's recipe, now with a
   COMPLETE dispatch arm: `block_category context hFind` → 4 arms; main/proc → the 9
   `BlockGenShapeReg` legs; dispatch → `realizedWitness_of_dispatch_arm` (feed `hFinish` from
   item 1); programEnd → `programEnd_openStep_no_jump`.  Then
   `AllEntriesRealized.of_openStep_invariant` with `realized := realizedWitness cfg`, entry
   witness `realizedWitness_of_stateRel`.
3. Then Step B (`openRunNPrefix_peephole_congr_of_source`).

### Status handed to session 45
Landed (all green + axiom-clean): the dispatch openStep-jump inversion in full
(`findTarget?_returnSitesFor_inv`, `get_retc_of_stateRel_procExit`, `dispatch_openStep_jump_inv`)
+ the dispatch arm packaged (`realizedWitness_of_dispatch_arm`), all in the new leaf module
`InteractionDispatchInversion.lean`.  The dispatch arm lands its successor `realizedWitness`
modulo the single additive `hFinish` (FrameSafe frame facts + return-site provenance) — the last
piece before the `hInv` case-split.  Full `lake build` green; `scripts/opt_harness.sh check` = OK
(43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` axioms UNCHANGED; delta +0.

## Session-45 update (2026-07-20): `hFinish` REDUCED to two clean source-frame-safety atoms + DECISIVE FINDING — the atoms are NOT derivable from `realizedWitness` as defined (concrete counterexample); the `hInv` endgame needs a STRENGTHENED realized predicate, not a composite-level `hSourceFrameSafe`. One green, axiom-clean commit; `hInv`/Step B stay closed behind that strengthening.

Session 45's mandate (per §Session-44 frontier): (1) discharge `hFinish`; (2) the `hInv`
case-split; (3) Step B.  **Result: ONE green, axiom-clean commit** banking the `hFinish`
finisher-reduction substrate, plus a decisive design finding that corrects the §Session-44
recipe.  Items 2/3 stay blocked — see the finding.  `peepholeBody`/public spine UNTOUCHED ⇒
delta **+0**; full `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆ `[propext,
Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` axioms UNCHANGED.

### DECISIVE FINDING (corrects §Session-44 frontier item 1): `hFinish` is UNPROVABLE against the current `realizedWitness`; the recipe "thread `hSourceFrameSafe` at the composite level" does NOT work
The §Session-44 recipe framed `hFinish` as dischargeable by threading a program-level
`hSourceFrameSafe` additively at the composite `hInv` assembly (mirroring `hSourceWF`).  That is
**mathematically impossible** with `realizedWitness` as currently defined
(`InteractionBoundedOwnerRealized.lean:313`):

* `realizedWitness cfg (ProcLabel.exit proc.name) target` only asserts *some* source witness
  `bodyState` with `StateRel bodyState tokens target` and `SourceFrameFits (procExit proc) …`.
* `StateRel`/`realizeStack` (`TypedCfgPreservation/Core.lean:17,51`) place **no** constraint on a
  ghost return frame's `retc`: realization consumes only the head *token* and the *contents* of
  `frame.callerStack`, never a length law or `frame.retc`.
* **Concrete counterexample:** `bodyState.returns = [{ callerStack := [], retc := proc.retc + 1 }]`,
  `bodyState.evm.stack` of length `proc.retc`, `tokens = [site.token]`.  Then
  `StateRel bodyState [site.token] target` holds (with `target.stack = bodyState.evm.stack ++
  [site.token]`) and `SourceFrameFits (procExit proc) proc.retc` holds, yet
  `attachReturns? frame bodyState.evm.stack = none` (`proc.retc ≠ frame.retc`), so **no**
  `stack`/`callerInput` witnessing `hFinish` exist.

Because the composite `hInv` quantifies over `realized := realizedWitness cfg` — whose source
witness is existential and per-entry — a program-level `hSourceFrameSafe` cannot constrain it.
Closing `hInv` therefore requires **strengthening the realized predicate itself** to carry a
per-witness source frame-consistency invariant.

### LANDED (green, axiom-clean) — all in `InteractionDispatchInversion.lean`
* **`9b5f23c4`** — the `hFinish` finisher-reduction substrate (isolates the atoms):
  * **`attachReturns?_of_procExit_fit`** (`:147`) — computational core of `hFinish` part (a):
    at a `procExit` shape a popped frame with `frame.retc = proc.retc` reattaches its return
    vector onto `frame.callerStack` (`attachReturns? … = some (stack ++ callerStack)`).
  * **`dispatch_hFinish_of_frameConsistent`** (`:192`) — discharges the `attachReturns?`-existential
    `hFinish`, reducing it to exactly the **two irreducible source-frame-safety atoms** per return
    frame: `frame.retc = proc.retc` and `∃ callerInput, LabelShape cfg site.returnLabel callerInput
    ∧ SourceFrameFits callerInput (bodyState.evm.stack.length + frame.callerStack.length)`.  Carries
    the full design note + counterexample.
  * **`realizedWitness_of_dispatch_arm_of_frameConsistent`** (`:470`) — composes
    `realizedWitness_of_dispatch_arm` with the reducer, so the eventual `hInv` dispatch arm consumes
    only the two clean atoms (the plug-in point for the strengthened predicate).

### THE FRONTIER (session 46) — strengthen the realized predicate, then discharge the atoms, then `hInv`, then Step B
The bare `realizedWitness` is too weak for the dispatch arm (finding above).  The remaining work,
in order:

1. **Strengthen the realized predicate** to `realizedWitnessFS cfg` = `realizedWitness cfg` PLUS a
   per-witness **source frame-consistency** conjunct on `(source, tokens)` (a `StateRel`-companion
   defined by recursion over `source.returns`/`tokens`, mirroring `realizeStack`), asserting for each
   pending return frame: (i) its `retc` equals the owning proc's `retc`, and (ii) a caller
   continuation shape it fits + a `LabelShape` at the frame's return label.  This is what lets the
   dispatch arm produce `hCons` for `realizedWitness_of_dispatch_arm_of_frameConsistent`.
   * **Cost:** the 9 `BlockGenShapeReg` legs (`InteractionHInvDispatch.lean`) + the entry seed
     (`realizedWitness_of_stateRel`) must be re-established for the strengthened predicate.  Most
     legs relay the source unchanged (nilJoin/terminalHalt/code/if/forCond/switchTest keep
     `source.returns`); callHead/procAdapter/caseEntryPop and the dispatch arm shift it (`pushReturn`
     / `popReturn?`) — those need the invariant's push/pop preservation lemmas.  This is the genuine
     multi-lemma effort; budget it as its own session.  Alternative framing: prove the invariant is
     preserved by `openStep`-jumps once and thread it through `realized_of_reaches_of_invariant` as a
     STRENGTHENED `realized` (`realizedWitness ∧ FrameConsistent`), then weaken to `realizedWitness`
     for the final `AllEntriesRealized` consumer (`FrameConsistent`→`True` weakening is free).
2. **Discharge the two atoms** at the dispatch arm from the strengthened predicate's frame-consistency
   conjunct (feeds `hCons`).  Atom (ii)'s `LabelShape cfg site.returnLabel _` may alternatively come
   from a **calls-provenance** thread over `context.calls` (ProcsShaped-style: each registered
   `DispatchSite.returnLabel` = a compiled call's `regular` block, in-program with the `afterCall`
   returnShape) — a source-run-free structural bank worth landing independently if the strengthened
   predicate does not already carry the caller shape.
3. **`hInv` assembly** (unchanged shape): `block_category context hFind` → 4 arms; main/proc → the 9
   `BlockGenShapeReg` legs; dispatch → `realizedWitness_of_dispatch_arm_of_frameConsistent` (feed
   `hCons` from item 1); programEnd → `programEnd_openStep_no_jump`.  Then
   `AllEntriesRealized.of_openStep_invariant` with `realized := realizedWitness cfg` (or the weakened
   strengthened predicate), entry witness `realizedWitness_of_stateRel`.
4. Then Step B (`openRunNPrefix_peephole_congr_of_source`).

### Status handed to session 46
Landed (green + axiom-clean, `9b5f23c4`): the `hFinish` finisher-reduction substrate
(`attachReturns?_of_procExit_fit`, `dispatch_hFinish_of_frameConsistent`,
`realizedWitness_of_dispatch_arm_of_frameConsistent`) — `hFinish` now reduces to the two
source-frame-safety atoms, and the dispatch arm has a clean atoms-only interface.  **Blocker
re-scoped by the finding:** `hInv` is NOT one composite-level `hSourceFrameSafe` away; it needs the
realized predicate strengthened with a per-witness source frame-consistency invariant (frontier
item 1), which subsumes both atoms.  Full `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` axioms
UNCHANGED; delta +0.

## Session-46 update (2026-07-20): frontier item 1 DONE + item 2 COMPLETE — the strengthened predicate `realizedWitnessFC` + ALL NINE `BlockGenShapeReg` legs + the dispatch (pop) arm now land the strengthened successor, all green + axiom-clean in 6 commits; only the `hInv` case-split assembly (item 3) + Step B remain

Session 46's mandate (per §Session-45 frontier): (1) strengthen the realized predicate with a
per-witness source frame-consistency invariant; (2) re-establish the 9 legs + dispatch + entry seed
at the strengthened predicate; (3) assemble `hInv`; (4) Step B.  **Result: items 1 and 2 landed IN
FULL — 6 green, axiom-clean commits.**  The strengthening design worked cleanly the whole way
down (every leg compiled first-try); items 3/4 remain.  `peepholeBody`/public spine UNTOUCHED ⇒
delta **+0**.

### KEY DESIGN FINDING (what made item 2 tractable in one session, against the §Session-45 "budget it as its own session" estimate)
`FrameConsistent` is a function of `(source.returns, tokens)` and the STATIC context **only —
never the runtime EVM stack**.  Session 45's atom (ii) was stated at `bodyState.evm.stack.length +
frame.callerStack.length`; restating it at `frame.retc + frame.callerStack.length` (the two
coincide at a `procExit proc` witness, where `bodyState.evm.stack.length = proc.retc = frame.retc`)
makes the invariant stack-independent.  **Consequence:** the SEVEN non-frame-shifting legs
transport the entry witness's frame-consistency conjunct with NO push/pop and (for the pure/pop
legs) NO returns-tracking at all — the child witness shares the entry's `(returns, tokens)`, only
the EVM stack shifts.  Only callHead (push) and the dispatch arm (pop) do real frame work.

### LANDED (green, axiom-clean) — six commits, six new leaf modules
* **`9b7feb2f`** — `InteractionFrameConsistent.lean`: the foundation.
  * `FrameHeadConsistent` / `FrameConsistent` (stack-independent recursion over
    `(source.returns, tokens)` + static context) — the per-frame atoms of
    `dispatch_hFinish_of_frameConsistent`, stated so the head condition quantifies over all
    matching sites (no token-uniqueness needed at the consumer).
  * `realizedWitnessFC` — the strengthened predicate (`realizedWitness` + `FrameConsistent` on the
    same existential witness); `realizedWitnessFC.realizedWitness` projection;
    `realizedWitnessFC_of_stateRel` uniform packager; `realizedWitnessFC_of_stateRel_nil` entry
    seed; `FrameConsistent.{nil,tail,cons}` (pop/push); `AllEntriesRealized.weaken` +
    `allEntriesRealized_realizedWitness_of_FC` (recovers the bare `realizedWitness` consumer for
    Step B).
* **`7e25bbfc`** — `InteractionFrameConsistentLegs.lean`: `realizedWitnessFC_of_pure_jump` +
  the 5 transport legs `realizedWitnessFC_of_{nilJoin,terminalHalt,procAdapter,caseEntryPop,
  switchTest}_dispatch`.
* **`3c817210`** — `InteractionFrameConsistentBranchLegs.lean`: `jump_state_rel_returns_of_rel`
  (returns-exposing branch extractor) + `realizedWitnessFC_of_{ifHead,forCond}_dispatch`.
* **`e359202a`** — `InteractionFrameConsistentCodeLeg.lean`: `jump_state_rel_returns_of_outcome`
  + `realizedWitnessFC_of_codeHead_dispatch`.
* **`078b7264`** — `InteractionFrameConsistentDispatchLeg.lean`:
  `realizedWitnessFC_of_dispatch_arm` — the ATOM-MOTIVATING case (§Session-45 counterexample).
  The entry `FrameConsistent` head SUPPLIES the two atoms (instantiate `FrameHeadConsistent` at the
  runtime-selected site + exiting proc); `FrameConsistent.tail` transports the popped caller
  activation.  **No residual `hFinish`, no `source.FrameSafe`.**
* **`dbd50e23`** — `InteractionFrameConsistentCallLeg.lean`:
  `realizedWitnessFC_of_callHead_dispatch` — the only PUSH leg.  Establishes the pushed frame's
  `FrameHeadConsistent` from the call's own site + token uniqueness
  (`context.tokensUnique` + `List.inj_on_of_nodup_map`) + `hReg` + `sourceFrameFits_afterCall`,
  then `FrameConsistent.cons`.

`InteractionFrameConsistentCallLeg` is imported into `Verification.lean` (pulls the whole FS chain
into the correctness build graph).

### THE FRONTIER (session 47) — assemble `hInv`, then Step B
The strengthened successor is now available at every arm.  Remaining, in order:

1. **`hInv` assembly** (mandate item 3).  `block_category context hFind` → 4 arms:
   * main/proc arms: `main_blockGenShape` / `proc_blockGenShape` (→ `BlockGenShape`; the
     `BlockGenShapeReg` strengthenings `main_blockGenShapeReg`/`proc_blockGenShapeReg` carry the
     exact-target `LabelShape` fields) → `cases` the 9 disjuncts → the matching
     `realizedWitnessFC_of_*_dispatch` leg;
   * dispatch arm: `dispatchBlock_provenance` → `realizedWitnessFC_of_dispatch_arm`;
   * programEnd arm: `programEnd_openStep_no_jump`.
   Then `AllEntriesRealized.of_openStep_invariant` with `realized := realizedWitnessFC …`, entry
   witness `realizedWitnessFC_of_stateRel_nil`, then `allEntriesRealized_realizedWitness_of_FC`
   to weaken to the bare `realizedWitness cfg` the downstream consumer wants.
   * **KNOWN GAP (must close first):** the `callHead` leg threads `hReg :
     ∀ out, result.fallthrough? = some out → LabelShape cfg regular out` as a hypothesis, but the
     `BlockGenShapeReg.callHead` disjunct (`InteractionBlockGenShapeRegular.lean:211`) carries
     `hEntryShape`/`hProcWF` but NOT `hReg`.  So the assembly cannot feed `callHead` directly.
     FIX OPTIONS: (a) strengthen the `BlockGenShapeReg.callHead` disjunct with an `HRegular result
     cfg regular` field (mirrors codeHead/ifHead) and re-prove `main_blockGenShapeReg` /
     `proc_blockGenShapeReg` in `InteractionHInvAssemblyRegular.lean`; or (b) derive `hReg` for the
     call from the enclosing statement-list provenance at the assembly site.  Option (a) is the
     §Session-42 disjunct-strengthening methodology and is recommended.
   * Note the FS legs' `calls` param is instantiated to `context.calls` throughout; the seven
     non-call legs are `calls`-polymorphic (they carry `FrameConsistent` opaquely), callHead and
     dispatch pin `context.calls`.
2. **Step B** (`openRunNPrefix_peephole_congr_of_source`).

### Status handed to session 47
Landed (green + axiom-clean, six commits `9b7feb2f`→`dbd50e23`): the strengthened predicate
`realizedWitnessFC` + all foundational plumbing + ALL NINE `BlockGenShapeReg` legs + the dispatch
(pop) arm, each landing `realizedWitnessFC`.  The §Session-45 blocker (bare `realizedWitness` too
weak) is DISSOLVED: `FrameConsistent` (stack-independent) supplies the dispatch atoms and is
preserved by every jump.  **Remaining:** the `hInv` case-split assembly (item 3 — one all-or-nothing
proof, blocked only on the `callHead`/`hReg` disjunct gap above) then Step B.  Full
`scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆ `[propext, Classical.choice,
Quot.sound]`); `compile_correct`/`compile_correct_creation` axioms UNCHANGED; delta +0.

## Session-47 update (2026-07-20): the `hInv` ASSEMBLY is DONE — the campaign's convergence point is closed; Step B STARTED (token-free entry bridge). Four green, axiom-clean commits; the `callHead` gap was bigger than §Session-46 flagged (needed calls-registration + source-lookup threading, not just `hReg`)

Session 47's mandate (per §Session-46 frontier): (1) the `callHead` disjunct fix; (2) assemble
`hInv`; (3) start Step B; (4) stop at the green frontier.  **Result: items 1, 2, and 3-start all
landed — four green, axiom-clean commits `8983c368`→`2201e558`.**  `peepholeBody`/public spine
UNTOUCHED ⇒ delta **+0**.  Full `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` axioms
UNCHANGED.

### KEY DESIGN FINDING (corrects §Session-46 frontier item 1): the `callHead` gap was NOT just `hReg`
§Session-46 framed the `hInv`-blocking gap as the single missing `hReg` field on
`BlockGenShapeReg.callHead`.  Adding `hReg` alone is insufficient: `realizedWitnessFC_of_callHead_dispatch`
ALSO consumes **`hProcs : ctx.procs = sourceProgram.procs`** (to resolve the callee in the source
proc list) and **`hResultCalls : CallsInProgram result context.calls`** (to pin the pushed frame's
return site via `context.tokensUnique`).  Neither is `cfg`-derivable at the assembly site — the
call's local `ctx`/`result` are existentially bound in the disjunct, and `S ∈ context.calls`
requires provenance through the compilation, not the CFG.  So `BlockGenShapeReg` had to be
**parameterized by `(sourceProgram, calls)`** and both facts threaded (the full §Session-42
disjunct-strengthening move, applied to two more fields).  This is why item 1 became a substantial
mutual/provenance change rather than a one-field edit.

### LANDED (green, axiom-clean) — four commits
* **`8983c368`** — `BlockGenShapeReg.callHead` gains the `hReg : HRegular result cfg regular` field
  (`InteractionBlockGenShapeRegular.lean:229`); supplied at the construction site from the mutual's
  threaded `hRegular`.
* **`1e3cfcbc`** — the calls-registration + source-lookup thread (the real enabler):
  * `BlockGenShapeReg` parameterized `(cfg) (sourceProgram) (calls)`
    (`InteractionBlockGenShapeRegular.lean:188`); `callHead` disjunct gains
    `hProcs` (`:218`) + `hResultCalls` (`:224`).
  * the 5-function `genShapeReg_of_compile*` mutual threads `hProcsEq : ctx.procs =
    sourceProgram.procs` (trivially — procs preserved by every `for_` ctx update) and
    `hCalls : CallsInProgram result calls` (parallel to `hBlocks`, via
    `CallsInProgram.left/right_of_append` for the stmt-list append and the per-construct
    `.calls`-record splits `if`=`bodyResult.calls`, `switch`=`caseResult.calls ++ defaultResult.calls`,
    `for`=`init ++ body ++ post`, `cases`=`bodyResult.calls ++ tail.calls`, `default_some`=`bodyResult.calls`,
    `call`=`[S]`).  `GenShapeResultReg` gains `(sourceProgram, calls)`.
  * `main_blockGenShapeReg` seeds calls from `GeneratedContext.mainCalls` + `hProcsEq := rfl`;
    the proc arm needed the proc-body result's calls registered, so
    `mem_procBlocks_provenance_subset_fallthrough` (`InteractionProcBlockProvenance.lean:390`)
    was strengthened with a **calls-subset** `∀ s, s ∈ bodyResult.calls → s ∈ procCalls`
    (`procCalls = compiled.calls ++ tailCalls`, mirroring the block-subset), and
    `procBlocks_provenance_inProgram_fallthrough` (`:650`) now exposes
    `CallsInProgram bodyResult context.calls` (via that subset + `procCalls ⊆ context.calls`).
* **`84324951`** — `InteractionHInvClose.lean`, the `hInv` assembly (THE convergence point):
  * `realizedWitnessFC_of_blockGenShapeReg` (`:48`) — the nine-disjunct case split, shared by the
    main and proc arms; each disjunct dispatches to its `realizedWitnessFC_of_*_dispatch` leg.
    (`codeHead` pins the leg's free `codeSourceProgram`/`sourceFuel` implicits to `source`/`0` — the
    leg is proven ∀ those, so any values work.)
  * `openStep_preserves_realizedWitnessFC` (`:106`) — the global `openStep`-jump invariant at
    `realizedWitnessFC`.  Recovers the block at the reached entry from the witness (pins
    `block.label = e` via `List.find?_some`), `subst e`, classifies with `block_category`, and
    discharges all four arms: main/proc via the case-split helper, dispatch via
    `realizedWitnessFC_of_dispatch_arm`, `programEnd` vacuously via `programEnd_openStep_no_jump`.
    After `subst e` every hypothesis lands at `block.label`, so `cases` on the concrete-record
    disjuncts unifies the entry/exec labels automatically — no per-disjunct label rewriting.
  * `allEntriesRealized_realizedWitness_of_context` (`:150`) — feeds the invariant to the route-B
    master lever `AllEntriesRealized.of_openStep_invariant`, seeds it, and weakens back to the bare
    `realizedWitness cfg` (`allEntriesRealized_realizedWitness_of_FC`) for Step B.
  * imported into `Verification.lean`.
* **`2201e558`** — Step B started: `stackRealizes_of_realizedWitness_of_returnTokenDepth?_eq_none`
  (`InteractionHInvClose.lean:186`) — the token-FREE half of the per-entry `StackRealizes`
  discharge, dischargeable outright from the unpacked `realizedWitness` (via
  `stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none`).

### STEP-B DESIGN FINDING (the frontier for session 48): the token-BEARING entry is NOT bridgeable from bare `realizedWitness`
`stackRealizes_of_stateRel` reduces the token-owning case (`block.input.returnTokenDepth? =
some (length-1)`, every proc-internal block) to **`source.returns ≠ []`** (equivalently a
non-empty realization token list `token :: tokens`, via
`stackRealizes_of_stateRel_of_token_last_of_tokens_cons`).  `realizedWitness cfg` (=
`∃ source tokens block, findBlock? ∧ StateRel ∧ SourceFrameFits`) carries NO token/frame coupling,
so `returns ≠ []` at a token-owning entry is genuinely not derivable from it.  The needed fact is a
whole-run invariant: token-owning blocks are only reached with a live activation
(`returns ≠ []`).  **CORRECTION to §Session-46's Step-B recipe** ("weaken to the bare
`realizedWitness cfg`"): Step B must instead consume the FC-carrying / returns-nonempty-coupled
`AllEntriesRealized` at token-owning entries.  Concretely, either
(a) keep `AllEntriesRealized … (realizedWitnessFC …)` un-weakened and prove the token-owning bridge
    from `realizedWitnessFC` — but note `FrameConsistent (source.returns, tokens)` does NOT by
    itself forbid `returns = []` at a token-owning block, so this needs an additional
    shape-token ⟶ `returns ≠ []` coupling lemma; or
(b) add a per-witness `returnTokenDepth?(block.input) = some _ → source.returns ≠ []` conjunct to a
    (further) strengthened realized predicate and re-run the 9 legs + dispatch (the token-owning
    entries are exactly the proc-body / dispatch categories, where the push/pop legs already track
    the frame).  Option (b) is the clean §Session-42 move and is recommended.

### THE FRONTIER (session 48) — finish Step B
1. Close the **token-owning** block-entry `StackRealizes` bridge per the design finding above
   (recommended: strengthen the realized predicate with the token ⟶ `returns ≠ []` conjunct, or a
   dedicated coupling lemma), giving a total `stackRealizes_of_realizedWitness` at every entry.
2. Assemble `openRunNPrefix_peephole_congr_of_source` — the source-carrying peephole congruence by
   the same fuel induction as `openRunNPrefix_peephole_congr` (`PeepholeProgram.lean:174`),
   discharging `StackRealizes` at each entry via the total bridge (fed from
   `allEntriesRealized_realizedWitness_of_context`) and `openRunBody_swap_swap_congr`
   (`PeepholeSwapOpen.lean:64`, session 6) for the swap arm.
3. Then (Steps C+) add the swap arm to `peepholeBody`.  **Do NOT** add the swap arm until Step B
   is green.

### Status handed to session 48
Landed (green + axiom-clean, four commits `8983c368`→`2201e558`): the `callHead` disjunct fix, the
calls-registration + source-lookup thread through `BlockGenShapeReg`, **the `hInv` assembly (the
strengthened `openStep`-jump invariant `openStep_preserves_realizedWitnessFC` + the
`AllEntriesRealized … (realizedWitness cfg)` production `allEntriesRealized_realizedWitness_of_context`)**,
and the token-free Step-B entry bridge.  The campaign's convergence point is CLOSED — every
`block_category` arm and all nine `BlockGenShapeReg` disjuncts + dispatch + `programEnd` are wired.
**Remaining:** the token-owning Step-B bridge (design finding above), then
`openRunNPrefix_peephole_congr_of_source`, then the swap arm.  Full `scripts/opt_harness.sh check`
= OK (43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
`compile_correct`/`compile_correct_creation` axioms UNCHANGED; delta +0.

## Session-48 update (2026-07-20): STEP 1 CLOSED — the token-owning block-entry `StackRealizes` bridge lands, via strengthening `realizedWitnessFC` with a local liveness conjunct + a `FrameContinuationLive` coupling on `FrameConsistent`; all nine legs + dispatch + callHead re-run, all green + axiom-clean

Session 48's mandate (per §Session-47 frontier): (1) strengthen `realizedWitnessFC` with the
token ⟶ liveness conjunct and re-run the legs; (2) prove the token-owning entry `StackRealizes`
bridge; (3) start Step B if reached; (4) stop at the green frontier.  **Result: item 1 + item 2
LANDED, green + axiom-clean.**  `peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**.
`compile_correct`/`compile_correct_creation` axioms UNCHANGED.

### KEY DESIGN FINDING (corrects §Session-47's "add the conjunct, re-run the 9 legs one-line" estimate)
The bare `∀ d, block.input.returnTokenDepth? = some d → tokens ≠ []` conjunct (call it `hLive`) is
NOT one-line-transportable through every leg, because two transitions cross the token boundary:

* **dispatch (pop):** the child is the caller continuation `callerInput` with residual tokens
  `rest`; `hLive` there (`callerInput owns → rest ≠ []`) is a genuine **below-token coupling**
  not derivable from `FrameConsistent` alone (which places no non-emptiness constraint on the
  tail).  **Fix:** a new per-frame coupling `FrameContinuationLive cfg calls token tokens` folded
  into `FrameConsistent`'s cons case (alongside `FrameHeadConsistent`): "for every registered site
  sharing `token` whose return continuation owns a token, `tokens ≠ []`."  The dispatch arm READS
  it off the popped head frame; the callHead arm PROVES it for the pushed frame from the caller's
  own `hLive` + the reverse afterCall-transport `returnTokenDepth?_some_of_afterCall_some`.
* **procAdapter (relabel):** `relabelCompatible` allows `.word ↔ .returnPC` per `slotsAgree`, so
  `output owns → blockInput owns` is generically FALSE.  BUT the single construction site
  (`InteractionHInvAssemblyRegular.lean:166`) always has `blockInput = procEntry proc`, which owns
  the token.  **Fix:** one new field `hInputActive : blockInput.returnTokenDepth?.isSome` on
  `BlockGenShapeReg.procAdapter`, supplied trivially there; the leg then gets `tokens ≠ []` from
  the entry's own `hLive` and the child obligation is trivial (conclusion always holds).

The other seven legs ARE cheap: nilJoin / switchTest (child input = entry input ⇒ `hLive`
directly); caseEntryPop (child = `.pop` tail ⇒ `returnTokenDepth?_some_of_tail_some`); codeHead /
ifHead / forCond (child = code output / its tail ⇒ the reverse code lemma
`BasicInstr.Code.input_returnTokenDepth?_eq_some_of_output`, Core.lean:1053); callHead (child
tokens `callToken :: tokens` non-empty ⇒ trivial).

### LANDED (green, axiom-clean) — two commits
* **COMMIT 1 (`8371d931`) — the predicate strengthening + all legs:**
  * `InteractionFrameConsistent.lean`: new `FrameContinuationLive` (`:71`); `FrameConsistent` cons
    case gains it (`:103`); `FrameConsistent_cons_cons`/`.tail`/`.cons` updated (`.cons` gains an
    `hLive` arg); `realizedWitnessFC` gains the `hLive` conjunct (`:148`); projection /
    `realizedWitnessFC_of_stateRel` (gains `hLive` arg) / `_of_stateRel_nil` (gains
    `hDepthNone`) updated.
  * the nine legs re-run per the design finding above (`InteractionFrameConsistentLegs.lean`,
    `…BranchLegs.lean`, `…CodeLeg.lean`, `…DispatchLeg.lean`, `…CallLeg.lean`).
  * `BlockGenShapeReg.procAdapter` gains `hInputActive` (`InteractionBlockGenShapeRegular.lean:340`),
    supplied at `InteractionHInvAssemblyRegular.lean:184`; consumed in
    `realizedWitnessFC_of_blockGenShapeReg` (`InteractionHInvClose.lean:72`);
    `openStep_preserves_realizedWitnessFC` unpacks the extra conjunct.
* **COMMIT 2 (`db0ca6ac`) — the bridge + un-weakened production, `InteractionHInvClose.lean`:**
  * `allEntriesRealized_realizedWitnessFC_of_context` (`:200`) — the un-weakened
    `AllEntriesRealized … (realizedWitnessFC …)` production (keeps `hLive` for the token-owning
    consumer; the earlier `…_realizedWitness_of_context` still weakens for the token-free half).
  * `stackRealizes_of_realizedWitnessFC_of_token_last` (`:227`) — **the token-owning bridge**:
    from the strengthened witness + `block.input.returnTokenDepth? = some (block.input.length - 1)`,
    `hLive` yields the non-empty token list and
    `stackRealizes_of_stateRel_of_token_last_of_tokens_cons` (session 8/9) discharges
    `StackRealizes block.input state`.

### THE FRONTIER (session 49) — finish Step B
Both per-entry `StackRealizes` bridges now exist (token-free + token-owning).  Remaining before the
congruence:
1. **The token-at-bottom static fact** — `∀ reached block, block.input.returnTokenDepth? = none ∨
   = some (block.input.length - 1)` — so the token-owning bridge's `hLast` hypothesis can be
   discharged at an arbitrary reached entry (needed to case-split the total bridge).  Provable from
   the `BlockGenShape`/`BlockGenShapeReg` disjuncts (each disjunct's input shape has its token at
   the bottom or none); the `procEntry`/`procExit`/`afterCall`/`tail`/`pop` depth lemmas already
   used this session supply the per-disjunct arithmetic.
2. **The total bridge** `stackRealizes_of_realizedWitnessFC` — case on `block.input.returnTokenDepth?`:
   `none` ⇒ project to `realizedWitness` + token-free bridge; `some _` ⇒ (1) pins it to
   `some (length-1)` ⇒ token-owning bridge.
3. **`openRunNPrefix_peephole_congr_of_source`** (`PeepholeProgram.lean:174` sibling) — fuel
   induction like `openRunNPrefix_peephole_congr`, discharging `StackRealizes` at each `openStep`
   entry from `allEntriesRealized_realizedWitnessFC_of_context` (fed at the seed) + the total
   bridge, feeding `openRunBody_swap_swap_congr` (`PeepholeSwapOpen.lean:64`, session 6) for the
   swap arm.  Then (Step C) swap the OIC call sites; then (Step D) add the swap arm to
   `peepholeBody`.

### Status handed to session 49
Landed (green + axiom-clean, two commits): the `realizedWitnessFC` liveness strengthening +
`FrameContinuationLive` coupling + all nine legs + dispatch + callHead + the `procAdapter`
`hInputActive` field, and **the token-owning block-entry `StackRealizes` bridge**
`stackRealizes_of_realizedWitnessFC_of_token_last` + the un-weakened FC `AllEntriesRealized`
production.  The per-entry `StackRealizes` discharge is now TOTAL modulo the token-at-bottom static
fact (frontier item 1).  Full `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` axioms
UNCHANGED; delta +0.

## Session-49 update (2026-07-20): the TOTAL block-entry `StackRealizes` bridge LANDS (item 2), plus the COMPLETE token-at-bottom preservation arithmetic (item 1 substrate); DECISIVE FINDING that item 1 is NOT a per-`BlockGenShapeReg`-disjunct proof but an input/output shape-invariant THREADING through the compiler classifier. Two green, axiom-clean commits.

Session 49's mandate (per §Session-48 frontier): (1) the token-at-bottom static fact; (2) the
total bridge; (3) `openRunNPrefix_peephole_congr_of_source`; (4) OIC wiring; (5) stop at the
green frontier.  **Result: item 2 LANDED; item 1 REDUCED to its final wiring with the complete
arithmetic banked; items 3–5 not reached.**  `peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**.
`compile_correct`/`compile_correct_creation` axioms UNCHANGED.

### DECISIVE FINDING (corrects the §Session-48 frontier item-1 framing "provable from the `BlockGenShapeReg` disjuncts, per-disjunct arithmetic")
The static token-at-bottom fact is **NOT** a per-disjunct read-off.  Audited all nine
`BlockGenShapeReg` disjuncts (`InteractionBlockGenShapeRegular.lean:188`): the three
straight-line-head disjuncts `codeHead`/`ifHead`/`callHead` conclude about a block whose
`block.input` is an **opaque metavariable** threaded through a `compileStmtFuel?` hypothesis —
the constructor pins **no** token-position fact on it (only `procAdapter` carries any token fact,
`hInputActive : isSome`, and even that is not "at bottom"; `callHead` pins the *callee*
`procEntry`, not its own input).  So token-at-bottom cannot be recovered disjunct-locally; it must
be **threaded as an input↔output shape invariant** through the 5-function compiler classifier
(`genShapeReg_of_compile{Block,StmtList,Stmt,Cases,Default}Fuel?`), seeded at `procEntry`
(token-at-bottom) / the token-free main root, and preserved across every shape transition.  This
is exactly the shape of the existing `GenShapeResultReg` classifier, and mirrors the §Session-48
`realizedWitnessFC` runtime-invariant route as the alternative.

**Key arithmetic (the enabling realization).**  `TokenBottomOrNone shape ⟺
shape.length ≤ sourceLength shape + 1` — token-at-bottom is exactly "hidden suffix
(`length − sourceLength`) ≤ 1 slot".  The hidden suffix is **exactly preserved** by every
accepted `BasicInstr` (`length_balance_of_type`, `Core.lean:942`) and by every compiler shape op
(`pop`/`pushWords`/`afterCall`/`slots.tail`/`Code.type?`), so the invariant propagates cleanly.
This collapses the per-transition reasoning to one-line `omega` steps.

### LANDED (green, axiom-clean) — two commits
* **COMMIT 1 (`dbb9d8f3`) — `EvmCompiler/Structured/TokenBottomShape.lean` (NEW):** the item-1
  substrate.  `TokenBottomOrNone` (`:40`); `tokenBottomOrNone_iff_length_le` (`:49`, the
  `length ≤ sourceLength + 1` characterization); `returnTokenDepth?_eq_pred_length_of_tokenBottomOrNone`
  (`:82`, the token-owning "pin" the bridge consumes).  **Complete route-agnostic op-preservation
  set:** `tokenBottomOrNone_pushWords` (`:179`), `_pop` (`:187`), `_tail` (`:198`), `_afterCall`
  (`:211`), `_procEntry` (`:224`), `_procExit` (`:232`); `code_length_balance` (`:242`, the
  iterated `length_balance_of_type`) + `tokenBottomOrNone_of_code_type?` (`:273`).  Pure shape
  arithmetic, additive.
* **COMMIT 2 (`08d4f53a`) — `InteractionHInvClose.lean:255`:**
  `stackRealizes_of_realizedWitnessFC` — **THE TOTAL block-entry bridge (item 2)**.  Case-splits
  `block.input.returnTokenDepth?`: `none` ⇒ project to bare `realizedWitness` + the token-free
  bridge; `some _` ⇒ the `TokenBottomOrNone block.input` premise (via the pin lemma) discharges the
  `hLast` hypothesis of the token-owning bridge `stackRealizes_of_realizedWitnessFC_of_token_last`.
  **Total modulo** the `TokenBottomOrNone block.input` premise (item 1), consumed as an explicit
  hypothesis for the call site to supply.

### THE FRONTIER (session 50) — finish item 1, then items 3–5
1. **The static token-at-bottom fact** `∀ block, cfg.findBlock? label = some block →
   TokenBottomOrNone block.input`, discharging the `hTB` premise of `stackRealizes_of_realizedWitnessFC`
   at an arbitrary reached entry.  All the ARITHMETIC is now banked (COMMIT 1); the remaining work
   is the **wiring**, two options:
   * **(a) classifier-threading mirror (additive, recommended):** a parallel recursion
     `tbResult_of_compile{Block,StmtList,Stmt,Cases,Default}Fuel?` over the compiler generators,
     threading hypothesis `TokenBottomOrNone input` and concluding
     `(∀ b ∈ result.blocks, TokenBottomOrNone b.input) ∧
      (∀ ft, result.fallthrough? = some ft → TokenBottomOrNone ft)` — the fallthrough conjunct is
     REQUIRED because sequential composition feeds the previous fragment's output as the next
     fragment's input.  Reuses the existing `components_of_compileStmtFuel?_{code,if,terminal,…}`
     inversions (`TypedCfgCompilerFacts.lean:582+`) + the COMMIT-1 op lemmas at each transition
     (per-statement: `code`⇒`of_code_type?`; `if`/`for` sub-inputs⇒`_tail` of the cond output;
     `switch`⇒`_tail`/pop; `call` continuation⇒`_afterCall`; `brk`/`cont`/`leave`/`nilJoin`/`terminal`
     ⇒ input = fragment input, direct).  Then the main/proc wrappers seed it: main root token-free
     (`TokenBottomOrNone` via `none`, since the dispatcher entry shape carries no token), proc root
     `tokenBottomOrNone_procEntry`.  **Open sub-item:** the `block_category`
     (`InteractionBlockProvenance.lean:79`) **dispatch-block** and **programEnd-block** cases have
     NO `BlockGenShapeReg` producer — they need their own token-position reasoning (programEnd input
     `= main.fallthrough?.getD Shape.caller`, token-free; dispatch-block inputs per
     `dispatchBlocks` — audit whether any own a token).
   * **(b) runtime `realizedWitnessFC` conjunct (the §Session-48 hLive pattern):** add
     `TokenBottomOrNone block.input` as a conjunct to `realizedWitnessFC`, re-establish it in the 9
     `hInv` legs (each child input is an op-image of the parent input ⇒ COMMIT-1 lemmas) + dispatch
     (below-token coupling ⇒ new `FrameConsistent` field, as `FrameContinuationLive` in s48) +
     callHead (child = `procEntry`).  Modifies the shared legs (higher risk); the total bridge then
     reads `hTB` off the witness and drops its explicit premise.
2. **`openRunNPrefix_peephole_congr_of_source`** (item 3, `PeepholeProgram.lean:174` sibling) —
   thread `allEntriesRealized_realizedWitnessFC_of_context` through the fuel induction, discharge
   `StackRealizes block.input` at each `openStep` entry via `stackRealizes_of_realizedWitnessFC`
   (COMMIT 2) + item-1's static fact, feeding `openRunBody_swap_swap_congr`
   (`PeepholeSwapOpen.lean:64`).  Then item 4 (OIC sites `OpenInteractionComposition.lean:910/943`,
   seed via `realizedWitnessFC_of_stateRel_nil` at `cfg.entry`) and item 5 (swap arm into
   `peepholeBody`, Step D, with the full bench).

### Status handed to session 50
Landed (green + axiom-clean, two commits `dbb9d8f3`, `08d4f53a`): the complete token-at-bottom
preservation ARITHMETIC (`TokenBottomShape.lean`, incl. the `length ≤ sourceLength + 1`
characterization, the pin, and pushWords/pop/tail/afterCall/Code/procEntry/procExit preservation)
and **the total block-entry `StackRealizes` bridge** `stackRealizes_of_realizedWitnessFC`, total
modulo the `TokenBottomOrNone block.input` static fact.  Per-entry `StackRealizes` is now discharged
for BOTH token cases; the ONLY remaining item-1 work is the classifier-threading wiring (arithmetic
done) + dispatch/programEnd coverage.  Full `scripts/opt_harness.sh check` = OK (43 theorems, axioms
⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` axioms
UNCHANGED; delta +0.  **PROCESS NOTE:** this host is **zsh** — `${PIPESTATUS[0]}` is empty, so
`lake build … | tail; echo $PIPESTATUS` MASKS failures; verify builds with `lake build … > log 2>&1;
echo RC=$?` (no pipe) or zsh `$pipestatus[1]`.

## Session-50 update (2026-07-20): frontier item 1 CLOSED — the per-entry static token-at-bottom fact `tokenBottomOrNone_of_findBlock?` + the SIDE-CONDITION-FREE total bridge `stackRealizes_of_realizedWitnessFC_total`; the classifier-threading mirror + all four `block_category` arms landed. Three green, axiom-clean commits. Step B (runner-level source threading) not reached: the genuine remaining sub-problem is isolated (a `Rel`→`Executes` connector), recipe below.

Session 50's mandate (per §Session-49 frontier): (1) discharge the `TokenBottomOrNone` static fact
via the classifier-threading mirror + dispatch/programEnd coverage, wiring the total bridge; (2)
`openRunNPrefix_peephole_congr_of_source`; (3) OIC wiring; (4) stop at the green frontier.
**Result: item 1 FULLY CLOSED; items 2–4 not reached.**  `peepholeBody`/public spine UNTOUCHED ⇒
delta **+0**.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED.  Full
`scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`).

### LANDED (green, axiom-clean) — `EvmCompiler/Structured/TokenBottomThread.lean` (NEW), three commits
* **COMMIT 1 (`34a1558e`) — the threading mutual.**  `TbResult` (`:40`, the per-fragment payload:
  every emitted block input + the fallthrough output are `TokenBottomOrNone`), `TbResult.append`
  (`:47`), and the additive 5-function mutual
  `tbResult_of_compile{BlockFuel?(:67),StmtListFuel?(:84),StmtFuel?(:126),CasesFuel?(:347),DefaultFuel?(:397)}`
  — the token-at-bottom mirror of `genShapeReg_of_compile*`.  Threads `TokenBottomOrNone input`,
  concludes `TbResult result`; each transition is ONE banked op lemma from `TokenBottomShape.lean`
  (`of_code_type?` / `_tail` / `_afterCall`), the fallthrough conjunct seeding the next fragment
  under sequential composition.  Termination inferred (same recursive-call fuel structure as
  `genShapeReg`).
* **COMMIT 2 (`b67760dd`) — program arms + the static fact + the total bridge.**
  `tbResult_of_compileBlock?` (`:450`, fuel-saturation wrapper); `tokenBottomOrNone_caller` (`:470`,
  the token-free main root seed); `tokenBottomOrNone_of_adapter_frame` (`:477`, the adapter-route
  seed — the relabel is length-preserving so `procEntry`'s bottom token survives to `bodyInput`);
  `input_of_mkBlock?` (`:512`); `mem_procBlocks_tokenBottom` (`:534`, the additive `TokenBottomOrNone
  input`-emitting mirror of `mem_procBlocks_provenance`, covering BOTH the `procEntry` no-adapter and
  the relabel adapter routes — **this dissolves the §Session-49 open sub-item** by proving the
  adapter seed IS token-at-bottom, so no `entryShapes = []` restriction is needed);
  `main_tbResult` (`:690`); `proc_tokenBottom` (`:701`); **`tokenBottomOrNone_of_findBlock?` (`:721`,
  THE static fact)** — `block_category` split, main/proc via the threading arms, dispatch =
  `procExit` (`tokenBottomOrNone_procExit`), programEnd = main fallthrough (token-free-or-at-bottom);
  and **`stackRealizes_of_realizedWitnessFC_total` (`:751`)** — composes the §Session-49 total bridge
  `stackRealizes_of_realizedWitnessFC` (`InteractionHInvClose.lean:255`) with the static fact,
  discharging its `TokenBottomOrNone` premise at ANY reached entry ⇒ side-condition-free
  `StackRealizes block.input state` from `realizedWitnessFC` + `findBlock?`.
* (COMMIT 3 = this doc update.)

### DECISIVE FINDING (corrects the §Session-49 "open sub-item": adapter/dispatch/programEnd coverage)
All three flagged categories are now covered with NO restriction on `entryShapes`:
* **dispatch** — `dispatchBlock proc calls` has `input = Shape.procExit proc` (token at bottom),
  direct `tokenBottomOrNone_procExit`.
* **programEnd** — `input = main.fallthrough?.getD Shape.caller`; token-free (`caller`, empty slots)
  in the `none` case, else the main body's fallthrough, `TokenBottomOrNone` by `main_tbResult.2`.
* **adapter route** (the one that looked open) — `bodyInput` is NOT arbitrary: `relabelCompatible`
  (`Syntax.lean:120`) forces `bodyInput.length = (procEntry proc).length = argc + 1`, and
  `requireReturnTokenDepth? argc bodyInput` pins `returnTokenDepth? = some argc = some (length − 1)`.
  So the relabel target is token-at-bottom too (`tokenBottomOrNone_of_adapter_frame`).  The proc arm
  therefore needs no `entryShapes = []` hypothesis; it is total over arbitrary `GeneratedContext`.

### THE FRONTIER (session 51) — Step B, then C/D
The item-1 connector Step B needs is **already landed**: `stackRealizes_of_realizedWitnessFC_total`
gives `StackRealizes block.input state` at any reached entry from `realizedWitnessFC` + `findBlock?`,
side-condition free.  The remaining Step-B work is the RUNNER-LEVEL threading, which has one real
structural sub-problem:

1. **`openRunN_peephole_congr_of_source` / `openRunNPrefix_peephole_congr_of_source`** — mirror
   `openRunN_peephole_congr` (`PeepholeProgram.lean:139`) but thread the source witness so that at
   each `openStep` entry `realizedWitnessFC source cfg context.calls label state1` holds (⇒
   `StackRealizes` via the total bridge, ready for the swap arm's depth guard).  **THE BLOCKER
   (identified, not yet solved):** the existing congruence recurses via
   `Simulation.Interaction.Rel.bind hStep (fun o1 o2 hOut => …)`; in the `hOut : RuntimeOutcomeRel`
   `jump lbl` branch the continuation sees the *outcomes* but NOT a
   `Simulation.Interaction.Executes (openStep cfg label state1) transcript (.ok (jump lbl s1'))`
   fact — and re-establishing the successor witness needs exactly that Executes-jump to feed
   `openStep_preserves_realizedWitnessFC` (`InteractionHInvClose.lean:107`) or to build a
   `ReachesOpenStepAt.step` for the `AllEntriesRealized` object
   (`InteractionEntryRealized.lean:134`, `= ∀ reached entry, realized`).  **Recipe:** either (a) a
   small connector lemma extracting the left `Executes`-jump from the `Rel`/`RuntimeOutcomeRel` jump
   branch (interaction-monad reasoning), then thread the witness by re-deriving at each successor via
   `openStep_preserves_realizedWitnessFC`; or (b) re-decompose the `openRunN` fuel step WITHOUT
   `Rel.bind` — case-analyze the left `openStep` outcome concretely (exposing its transcript/Executes)
   and relate the peepholed side by hand.  Route (a) is smaller.  Seed the top witness at
   `cfg.entry` via `realizedWitnessFC_of_stateRel_nil` (per §Session-49) +
   `allEntriesRealized_realizedWitnessFC_of_context` (`InteractionHInvClose.lean:205`).
2. **Step C** — once the runner `_of_source` exists, swap the OIC sites
   (`OpenInteractionComposition.lean` prefix `:910`/`:943`, terminal `:1415`/`:1561`/`:1688`; the
   `generated` `GeneratedContext`, `hWellTyped`, `hIndependent` are all in scope) to consume it,
   seeding the witness at `cfg.entry` = `expressionsState.evm`.
3. **Step D** (next after C) — add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`;
   `openRunBody_swap_swap_congr` (`PeepholeSwapOpen.lean:64`) then consumes the threaded
   `StackRealizes` as its depth guard.  With the full bench.

### Status handed to session 51
Item 1 is **CLOSED**: `tokenBottomOrNone_of_findBlock?` (the static fact) + `stackRealizes_of_realizedWitnessFC_total`
(side-condition-free per-entry `StackRealizes`) are green + axiom-clean, total over arbitrary
`GeneratedContext` (all four `block_category` arms, incl. the adapter route, covered without an
`entryShapes = []` restriction).  The complete classifier-threading mirror `tbResult_of_compile*` is
banked.  Commits `34a1558e`, `b67760dd` (+ this doc update).  `scripts/opt_harness.sh check` = OK (43
theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation`
UNCHANGED; delta +0.  **Next session:** Step B runner threading — solve the `Rel`→`Executes` connector
(frontier item 1 above), then Steps C/D.  **PROCESS NOTE (unchanged):** host is **zsh**; verify builds
with `lake build … > log 2>&1; echo RC=$?` (no pipe) — `${PIPESTATUS[0]}` is empty.  No foreground
`sleep`; poll background tasks with an `until grep -q …; do sleep N; done` loop.

## Session-51 update (2026-07-20): STEP B CLOSED — the `Rel`→`Executes` connector is solved and the source-threaded whole-program congruences (`open{Step,RunN,RunNPrefix}_peephole_congr_of_source`) land green + axiom-clean. The §Session-50 frontier blocker is DISSOLVED. Steps C/D not reached (Step C's entry-witness seed is genuine new crown-path work; Step D is gated behind it) — stopped at the green frontier per the never-commit-red discipline.

Session 51's mandate: (1) the `Rel`→`Executes` connector; (2) `openRunNPrefix_peephole_congr_of_source`;
(3) OIC wiring (Step C); (4) swap arm (Step D).  **Result: items 1–2 FULLY CLOSED; items 3–4 not
reached.**  `peepholeBody`/public spine UNTOUCHED ⇒ delta **+0**.
`compile_correct`/`compile_correct_creation` axioms UNCHANGED.  Full `scripts/opt_harness.sh check` =
OK (43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`).

### LANDED (green, axiom-clean) — `EvmCompiler/Structured/PeepholeSourceCongr.lean` (NEW), two commits
* **COMMIT 1 (`24513b8b`) — the connector.**
  * `allDone_of_forall_executes` (`:50`) — the generic **`Executes`→`AllDone` converse** (the missing
    inverse of `AllDone.property_of_executes`): a leaf property holding at every concrete `Executes`
    outcome holds at every terminal leaf.  Trivial induction on the interaction tree.
  * `allDone_realizedWitnessFC_jump` (`:76`) — **THE §Session-50 connector.**  Packages the per-leaf
    `openStep_preserves_realizedWitnessFC` (`InteractionHInvClose.lean:107`) into
    `AllDone (fun o => ∀ lbl s1, o = .ok (jump lbl s1) → realizedWitnessFC … lbl s1) (openStep cfg label state1)`.
    This is what dissolves the blocker: the successor witness now rides ALONGSIDE the
    `RuntimeOutcomeRel` value at every jump leaf, so it is available in the `Rel.bind` continuation —
    no need to recover an `Executes`-jump from the value-only `Rel.bind` branch (which is impossible,
    since `Rel.bind`'s `hNext` quantifies over ALL related value pairs, reachable or not).
* **COMMIT 2 (`d40aed00`) — STEP B, the three source-threaded congruences.**
  * `openStep_peephole_congr_of_source` (`:117`) — strengthens the unconditional
    `openStep_peephole_congr` via **`Rel.strengthen_left`** (folds the `AllDone` left-leaf invariant
    into the value relation as a conjunct) then **`Rel.mono`** (re-seats the conjunction inside the
    `ExceptRel.ok` payload, so the `doneRel` is `ExceptRel (·=·) (fun v1 v2 => RuntimeRel v1 v2 ∧ (∀
    lbl s1, v1 = jump lbl s1 → witness lbl s1))` — an `ExceptRel`-shaped rel `Rel.bind` can decompose).
  * `openRunN_peephole_congr_of_source` (`:160`) — same fuel induction as the unconditional runner;
    the `fuel+1` step feeds the strengthened step congruence to `Rel.bind`, and the jump branch pulls
    the successor witness `hWit lbl _ rfl` out of the (now witness-carrying) value relation to re-seed
    the recursion at the jump target.  Push/pop/other-outcome cases unchanged.
  * `openRunNPrefix_peephole_congr_of_source` (`:210`) — the prefix wrapper; identical body to the
    unconditional (`Rel.bind` over the `_of_source` runner, jump→`.error rfl`), carrying the seed.
  * **Conclusion is the SAME `Rel Block.RuntimeOutcomeRel`** the unconditional congruences produce.
    The threading is internal; its value is placing `realizedWitnessFC … label state` in scope at
    EVERY reached `openStep` entry — the exact hook Step D's swap arm consumes via
    `stackRealizes_of_realizedWitnessFC_total` (`TokenBottomThread.lean:751`).

### DECISIVE FINDING (why the §Session-50 recipe (a) works, recipe (b) unneeded)
The blocker framing was "extract the left `Executes`-jump from the `Rel.bind` jump branch."  That
extraction is genuinely **impossible** — `Rel.bind`'s `hNext : ∀ leftValue rightValue, sourceRel
leftValue rightValue → …` must hold for ALL `sourceRel`-related value pairs, so it carries no
reachability/`Executes` information about any particular pair.  The resolution is to **not need** the
`Executes` in the continuation: derive it ONCE per leaf (via `allDone_of_forall_executes`, which DOES
have an `Executes` at each leaf by construction) BEFORE the bind, fold it into `doneRel` with
`Rel.strengthen_left`, and let the bind carry it through.  Recipe (b) (re-decompose without
`Rel.bind`) is not needed.

### THE FRONTIER (session 52) — Step C (entry seed), then Step D
Step B's runner congruences are ready.  The remaining work to make the swap arm live:

1. **Step C — swap the OIC sites** (`OpenInteractionComposition.lean` prefix `:910`/`:943`, terminal
   `:1415`/`:1561`/`:1688`) from `openRunN{,Prefix}_peephole_congr` to the `_of_source` variants.  The
   swap is SAFE (identical `Rel` conclusion; downstream `Rel.executes` is unaffected) **modulo one new
   obligation: the entry seed** `realizedWitnessFC expressions.toStructured cfg generated.calls
   cfg.entry expressionsState.evm`.  `context := generated`, `hSourceWF := hStructuredWF`,
   `hTyped/hIndependent` are all already in scope at the sites; only the seed is missing.
   * **The seed is genuine new work.**  `GeneratedContext` (`Core.lean:3387`) carries NO entry
     `StateRel` — it is pure compilation provenance.  The entry block input is `Shape.caller`
     (`TypedCfgCompiler.lean:722`; token-free ⇒ `returnTokenDepth? = none`), so
     `realizedWitnessFC_of_stateRel_nil` (`InteractionFrameConsistent.lean:222`) is the right builder —
     it needs `LabelShape cfg cfg.entry Shape.caller` (from `context.cfgEq` + the entry block),
     `StateRel RunState.initial [] expressionsState.evm` with `source.returns = []`, `tokens = []`, and
     `SourceFrameFits Shape.caller source.evm.stack.length`.  The crux is the **entry `StateRel`**
     between `RunState.initial` and `expressionsState.evm`, which must be composed from `hStackInitial`
     (`Functions.StackRelation.StateRel … functionsState expressionsState`) up through the
     Expressions→Structured→TypedCfg layers.  This composition does not yet exist as a lemma; it is the
     one real sub-problem for Step C.  Recommend a dedicated lemma
     `realizedWitnessFC_entry_of_generated` (given `generated` + the OIC entry hypotheses ⇒ the seed at
     `cfg.entry`, `expressionsState.evm`) proved once and applied at all five sites.
2. **Step D — add the `swap d :: swap d :: rest → rest` arm to `peepholeBody`.**  Re-green the
   syntactic (b)-family (`peepholeBody_length_le`, `mem_peepholeBody`, `peepholeBody_bodyType?`,
   `lowerBodyFrom?_peephole_le` — trivial extra arm) and the semantic block congruence (now consuming
   `StackRealizes` at the entry, discharged from the Step-B/-C threaded witness via
   `stackRealizes_of_realizedWitnessFC_total` feeding `openRunBody_swap_swap_congr`
   (`PeepholeSwapOpen.lean:64`)).  Gate on `scripts/opt_harness.sh check`; the orchestrator runs the
   full bench.

### Status handed to session 52
Step B is **CLOSED** and axiom-clean.  New file `EvmCompiler/Structured/PeepholeSourceCongr.lean`
(imports `TypedCfg.PeepholeProgram`, `Structured.InteractionHInvClose`, `Structured.TokenBottomThread`)
holds the connector + the three `_of_source` congruences; it is a standalone banked module (built
green via `lake build EvmCompiler.Structured.PeepholeSourceCongr`), **not yet imported** by anything —
Step C's OIC wiring is its first consumer (which also brings it into the default build graph).  Commits
`24513b8b`, `d40aed00` (+ this doc update).  `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` UNCHANGED;
delta +0.  **Next session:** Step C entry seed (`realizedWitnessFC_entry_of_generated`), swap the five
OIC sites, then Step D.  **PROCESS NOTE (unchanged):** host is **zsh**; verify builds with
`lake build … > log 2>&1; echo RC=$?` (no pipe) — `${PIPESTATUS[0]}` is empty.  No foreground `sleep`;
poll background tasks with an `until grep -q …; do sleep N; done` loop.

## Session-52 update (2026-07-20): STEP C CLOSED — the entry-witness seed + the five OIC site swaps land green + axiom-clean; `PeepholeSourceCongr.lean` is now in the default build graph.  **Step D (the `swap;swap→ε` arm) NOT landed** — the swap arm is **NOT LIVE**; adding it is an *atomic* change that goes red without new infrastructure (identified below), so per the never-commit-red discipline `peepholeBody` is UNTOUCHED (delta **+0**).  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.  Full `scripts/opt_harness.sh check` = OK (43 theorems).

### LANDED (green, axiom-clean) — commit `bcd9cf7a`
* **The entry seed** `realizedWitnessFC_entry_of_generated` (`EvmCompiler/Structured/PeepholeSourceCongr.lean:235`).
  Given a `GeneratedContext` and an entry `StateRel sourceState [] target`, produces
  `realizedWitnessFC source cfg context.calls cfg.entry target`.  The §Session-50/51 "genuine new
  work" turned out **direct**: the entry `StateRel` is not a multi-layer composition — at the program
  entry the source activation is empty (`returns = []`, `tokens = []`), so it is just
  `StateRel.initial` (prefix sites) or the theorem's own `hStructuredInitial` hypothesis (terminal
  sites).  The entry block's input is `Shape.caller` (via `GeneratedContext.mainCompile` +
  `LabelShape.of_compileBlock?` + `mainBlocks`), which is token-free (`returnTokenDepth? = none`,
  `sourceLength = 0`), so the frame-fit and depth side-conditions of
  `realizedWitnessFC_of_stateRel_nil` (`InteractionFrameConsistent.lean:222`) are `simp`-trivial and
  the empty activation makes the `FrameConsistent` conjunct vacuous.
* **Helper** `returns_nil_of_stateRel_nil` (`PeepholeSourceCongr.lean:217`) — `tokens = []` under a
  `StateRel` forces `returns = []` (`realizeStack` pairs each ghost frame with a token).
* **The five OIC site swaps** (`EvmCompiler/Compiler/OpenInteractionComposition.lean`, now imports
  `EvmCompiler.Structured.PeepholeSourceCongr`):
  * prefix sites → `openRunNPrefix_peephole_congr_of_source` at `:928` and `:963`; seeded by
    `hEntrySeed` (built once near the theorem top from `hStackInitial.returns` +
    `StateRel.initial`, `realizedWitnessFC_entry_of_generated generated hEntrySeedRel`).
  * terminal sites → `openRunN_peephole_congr_of_source` at `:1437`, `:1587`, `:1718`; each seeded
    inline by `realizedWitnessFC_entry_of_generated generated hStructuredInitial`.
  The swap is SAFE: the `_of_source` conclusion is the SAME `Rel` (`Block.RuntimeOutcomeRel` /
  prefix), so all downstream `Rel.executes` / `Rel.trans` / `allDone_right` usage is unaffected.
  This brings `PeepholeSourceCongr.lean` (Step B's connector + three source-threaded congruences)
  into the default build graph — the entry witness `realizedWitnessFC … label state` is now in scope
  at EVERY reached `openStep` on the crown path, the hook Step D's swap arm consumes.

### THE FRONTIER (session 53) — Step D is a large ATOMIC change gated on one missing bridge
Step D cannot be partially landed: adding the `swap d :: swap d :: rest → rest` arm to `peepholeBody`
(`Peephole.lean:32`) adds a third match arm, and the `split` inside `openRunBody_peephole_congr`
(`PeepholeOpen.lean:124`) then produces a third semantic goal — so the semantic congruence goes red
until that arm is discharged.  The 4 syntactic (b)-lemmas (`peepholeBody_length_le`,
`mem_peepholeBody`, `peepholeBody_bodyType?`, `lowerBodyFrom?_peephole_le`) are trivial extra arms;
the semantic arm is the real work, and it needs:

1. **THE GATING LEMMA (does not exist).**  An `openRunAt` AllDone-`StackRealizes` bridge:
   `AllDone (fun r => ∀ after out, r = .ok (after,out) → StackRealizes out after) (openRunAt instr input state)`
   given `type? instr input = some output` and `StackRealizes input state`.  Non-prim instrs are
   easy (`openRunAt = .done (runAt …)`, single leaf, discharge by `runAt_stackRealizes`
   (`PeepholeStackRealizes.lean:203`)).  **The prim case is the missing infrastructure**: for
   `instr = .prim op`, `openRunState = Assembly…PrimOp.openStep op state`
   (`Assembly/InteractionSemantics.lean:244`) — an interaction with `.request` nodes for
   call/create/resource.  Need `AllDone (fun r => .ok after → output.length ≤ after.stack.length)`
   over ALL its outcomes: `callStep` (`finishCall` pushes `statusWord :: rest`, out-arity 1),
   `createStep` (`finishCreate` pushes `address :: rest`, out-arity 1), `resourceStep` (pushes one
   value), closed (`op.step`, via `PrimOp.step_stack_length_of_stackArity`
   (`PrimSemantics.lean:3256`)).  Est. ~150–250 lines of Assembly-level case analysis; `finishCall`
   stack machinery exists (`InteractionPreservation.lean:74 finishCall_append_stack`).
2. **Thread the guard through `openRunBody_peephole_congr`'s keep arm.**  The keep-arm recursion
   (`PeepholeOpen.lean:206–223`) goes through `Rel.bind`, whose continuation universally quantifies
   the RHS child state `rightAfter` — the SAME bind-quantification obstacle Step B hit.  Resolve it
   the Step-B way but on the RIGHT tree: `Rel.strengthen_right`
   (`evm-interaction/…/Simulation/Interaction.lean:1490`) folds the gating lemma's RIGHT-side
   `StackRealizes` AllDone into `RuntimeAtRel`, so `StackRealizes middle rightAfter` rides alongside
   in the continuation and re-seeds the recursion.  Push/pop and the new swap arms recurse on
   CONCRETE states (`state2 after push`/`after swap`) so their `StackRealizes` follows directly from
   `runState_stackRealizes` (no bind).  Add `StackRealizes input state2` as a hypothesis to
   `openRunBody_peephole_congr`.
3. **The swap arm itself** — mirror the push;pop cancel arm (`PeepholeOpen.lean:147–205`) but with
   `swap_type_involution` for the shape and `openRunBody_swap_swap_congr` (`PeepholeSwapOpen.lean:64`)
   ingredients; the RHS head swap fires under `StackRealizes input state2`, the LHS second swap
   (`peepholeBody rest = swap d :: rest'`) under `StackRealizes middle (state1 after swap)`.
4. **Propagate the `StackRealizes` hypothesis UP.**  `Block.openRun_peephole_runtimeRel`
   (`PeepholeOpen.lean:244`) → `openStep_peephole_congr` (`PeepholeProgram.lean:98`) gain a
   found-block `StackRealizes block.input state2` obligation.  The **source-threaded** variants supply
   it: in `openStep_peephole_congr_of_source` (`PeepholeSourceCongr.lean:101`), `hReal` +
   `stackRealizes_of_realizedWitnessFC_total` (`TokenBottomThread.lean:751`) discharge
   `StackRealizes block.input state1`, transported to `state2` via `SameRuntimeData.stack_eq`
   (`hRel`).  `openRunN_peephole_congr_of_source` already re-seeds `hReal` at each jump target, so no
   further threading is needed there.  Step C's site swaps mean the unconditional
   `openStep/openRunN_peephole_congr` are only reached THROUGH the `_of_source` variants — good, the
   guard has a witness supply at every use.

### Status handed to session 53
Steps B + C are **CLOSED** and axiom-clean.  `PeepholeSourceCongr.lean` is live in the build graph
(imported by `OpenInteractionComposition.lean`).  Commit `bcd9cf7a` (+ this doc update).
`scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆ `[propext, Classical.choice, Quot.sound]`);
full `lake build` = OK; `compile_correct`/`compile_correct_creation` UNCHANGED; delta **+0**; **swap arm
NOT LIVE**.  **Next session:** build the gating lemma (1), then (2)–(4) in one atomic Step-D commit —
do NOT touch `peepholeBody` until (1)+(2)+(3) are proved green in isolation (the gating lemma can be
banked as a standalone module first, exactly as `PeepholeSourceCongr.lean` was for Step B).
**PROCESS NOTE (unchanged):** host is **zsh**; `lake build … > log 2>&1; echo RC=$?` (no pipe);
harness `check` runs ~3–4 min — launch with `nohup … &` and poll with `until ! kill -0 PID; do sleep
15; done`, never a foreground `sleep`.

## Session-53 update (2026-07-20): Step D items (1) + (2) + (4-propagation) LANDED green + axiom-clean; the atomic `peepholeBody` swap arm is **NOT LIVE** — blocked by TWO obstacles the §Session-52 frontier under-scoped (documented below).  `scripts/opt_harness.sh check` = OK (43 theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct` / `compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]`.  Single-contract sanity (pinned solc 0.8.26 → `solidus-backend raw-summary` on `examples/AdversarialStackPressure.sol`): SUCCESS, runtime **8557** bytes / creation **8591** bytes (codegen byte-identical — the `peepholeProgram` transform is untouched; commits are proof-only).

### LANDED (green, axiom-clean)
* **Commit `d3abf555`** — Step D item (1), the gating lemma as a STANDALONE BANKED MODULE
  `EvmCompiler/TypedCfg/PeepholeOpenStackRealizes.lean` (as `PeepholeSourceCongr.lean` was for Step B):
  * `StackRealizesState` (`:40`) / `StackRealizesPair` (`:48`) — terminal-leaf `StackRealizes`
    properties for the open state-step / `runAt`-step result carriers.
  * `openRunState_stackRealizes` (`:56`) — every terminal leaf of `openRunState instr input state`
    realizes the output shape.  **Prim case delegates to the pre-existing Assembly
    `InteractionPreservation.PrimOp.openStep_realizesStackArity`** (which already covers `callStep` /
    `createStep` / `resourceStep` / closed `op.step` via `RealizesStackArity`), then `omega` with
    `length_of_type?_prim`; bookkeeping cases delegate to `runState_stackRealizes`.  The
    ~150–250-line "prim `openStep` case analysis" the frontier estimated was **already built**
    (`Assembly/InteractionPreservation.lean:978`) — the module just wires it to `StackRealizes`.
  * `openRunAt_stackRealizes` (`:102`) — the `runAt`-level bridge (the Step D gating lemma), by
    `AllDone.map` through the `type?` pairing, mirroring `Instr.openRunAt_atLoweredEnd`.
* **Commit `c1481a34`** — items (2) + (4-propagation): thread the `StackRealizes` depth guard through
  the whole OPEN congruence chain (peephole transform still 2-arm; guard USED in keep/push recursion):
  * `openRunBody_peephole_congr` (`PeepholeOpen.lean:125`) — **+hypothesis `StackRealizes input
    state2`**.  Keep arm resolves the RIGHT-tree bind-quantification via
    `Rel.strengthen_right` on `openRunAt_stackRealizes` (+`Rel.mono` to re-seat the guard inside the
    `ExceptRel.ok` payload), so `StackRealizes middle rightAfter` rides into the `Rel.bind`
    continuation and re-seeds the recursion (mirror of Step B's LEFT-tree resolution).  Push cancel
    arm supplies the concrete guard by `omega`.
  * `Block.openRun_peephole_runtimeRel` (`PeepholeOpen.lean:274`) — +`StackRealizes block.input state`.
  * `openStep_peephole_congr` (`PeepholeProgram.lean:98`) — +`hReal2 : ∀ block, findBlock? label =
    some block → StackRealizes block.input state2`.
  * `openStep_peephole_congr_of_source` (`PeepholeSourceCongr.lean:101`, guard built at `:123`) —
    discharges the per-found-block guard from `stackRealizes_of_realizedWitnessFC_total` (at `state1`)
    transported to `state2` along `SameRuntimeData.stack_eq`.  `openRunN/openRunNPrefix_…_of_source`
    already re-seed the witness per jump, so no further threading.
  * **RETIRED** the guard-free unconditional `openRunN_peephole_congr` / `openRunNPrefix_peephole_congr`
    (were dead — referenced only in one doc comment; unstatable once the swap arm's per-entry guard
    exists; superseded by the `_of_source` variants used at all 5 OIC sites).

### THE FRONTIER (session 54) — the atomic swap arm, with TWO obstacles the §Session-52 frontier MISSED
Adding `swap d :: swap d :: rest → rest` to `peepholeBody` (`Peephole.lean:32` — the arm is
`| .swap d, .swap d' :: rest' => if d = d' then rest' else .swap d :: .swap d' :: rest'`, and
`peepholeBody_cons` / `peepholeBody_length_le` re-green trivially, VERIFIED green in a reverted spike)
breaks **SIX** `split`-on-`peepholeBody_cons` sites, not the 5 the frontier listed:
  1. `peepholeBody_length_le` (`Peephole.lean`) — trivial (`omega`); **spiked green**.
  2. `mem_peepholeBody` (`PeepholeSemantics.lean`) — trivial; **spiked green** (`if_pos`/`if_neg hdd`).
  3. `peepholeBody_bodyType?` (`PeepholeOpen.lean:35`) — **OBSTACLE B, see below**.
  4. `lowerBodyFrom?_peephole_le` (`PeepholeFuel.lean:64`) — depends on (3).
  5. `openRunBody_peephole_congr` swap arm (`PeepholeOpen.lean`) — the OPEN semantic arm (the real
     crown work); needs the module reshuffle in the note below + a NEW open swap-cancellation proof.
  6. **`peepholeBody_runBody_erase` (`PeepholeSemantics.lean:236`) — OBSTACLE A, the MISSED closed
     tower.**

**OBSTACLE A — the closed-level tower needs the guard too.**  `peepholeBody_runBody_erase` (closed
`runBody` preservation, `BodySafe`-only signature) and its dead lift `PeepholeBlock.Block.
run_peephole_runtimeRel` (`PeepholeBlock.lean`, imported by NOBODY) also `split` on
`peepholeBody_cons`.  The swap cancellation is UNSOUND without a runtime depth guard, which the
`BodySafe`-only signature cannot supply.  Options: (a) RETIRE both (same justification as the
unconditional runners: the crown path routes only through the OPEN level; `PeepholeBlock` is dead) —
lowest-risk; or (b) add a `StackRealizes`/depth hypothesis and thread through the (dead) `PeepholeBlock`
mirror of the open work.  Recommend (a).

**OBSTACLE B — swap;swap breaks UNCONDITIONAL `bodyType?` preservation (unlike push;pop).**
`peepholeBody_bodyType?` currently proves `bodyType? (peepholeBody body) input = bodyType? body input`
for ALL `body, input`.  `push v ; pop` is ALWAYS well-typed + shape-neutral, so this is unconditional.
`swap d ; swap d` is type-neutral **only when the swap is well-typed at the shape** (the type-level
depth guard `d + 2 ≤ input.length`).  Counterexample: pick `input` with `type? (.swap d) input = none`
(shallow shape) but the cancelled tail `rest'` well-typed at `input` — then LHS `bodyType?
(peepholeBody body) input = bodyType? rest' input = some …` while RHS `bodyType? body input = none`.
So the equality FAILS unconditionally.  **Fix:** weaken `peepholeBody_bodyType?` to the DIRECTIONAL
form `bodyType? body input = some output → bodyType? (peepholeBody body) input = some output` (TRUE:
if the original types, the swaps are well-typed → involution → cancellation preserves the typing).
This suffices for the two consumers (both already carry the `= some output` hypothesis:
`openRunBody_peephole_congr`'s `hRestBodyType`, and `lowerBodyFrom?_peephole_le`) but requires
re-examining both call sites and `lowerBodyFrom?_peephole_le`'s structure.  This is a DESIGN change to
a core syntactic invariant, not a mechanical arm addition — the reason the swap arm was NOT rushed in
this session.

**MODULE-CYCLE NOTE for site 5.**  The open swap-cancellation proof needs `swap_type_involution` +
`swap_swap_sameRuntimeData` + `runState_swap_eq` + `openRunBody_swap_cons_ok`.  The latter two live in
`PeepholeSwapOpen.lean`, which *imports* `PeepholeOpen` (cycle).  BUT `PeepholeSwapKernel` and
`PeepholeStackRealizes` do NOT import `PeepholeOpen`, so **move `runState_swap_eq` +
`openRunBody_swap_cons_ok` into `PeepholeOpen`** (add `import …PeepholeSwapKernel`; `PeepholeStackRealizes`
already arrives via `PeepholeOpenStackRealizes`).  IMPORTANT: the session-6 lemma
`openRunBody_swap_swap_congr` (`PeepholeSwapOpen.lean:64`) does **NOT** directly discharge site 5 — it
assumes the ORIGINAL body is literally `swap d :: swap d :: rest`, but `peepholeBody`'s cancel arm has
the original as `swap d :: rest` where only `peepholeBody rest = swap d :: rest'`.  The correct proof
MIRRORS the push;pop cancel arm (`PeepholeOpen.lean:149–215`): the RHS head `swap d` fires on `state2`
under `StackRealizes input state2` (the new hypothesis), the recursion (`ihRest`) handles `rest`, and
the LHS second `swap d` (head of `peepholeBody rest = swap d :: rest'`) fires on `state1`-after-swap
under `StackRealizes middle (state1-swapped)` (from `StackRealizes input state1` via
`SameRuntimeData.stack_eq hRel` + `runState_stackRealizes`), then `swap_swap_sameRuntimeData` collapses
`state1`-swapped-twice back to `~ state1` and `openRunBody_runtimeRel` carries the tail.  Use the
INGREDIENTS, not the monolithic lemma.

### Status handed to session 54
Steps B + C **CLOSED**; Step D items (1), (2), (4-prop) **CLOSED** green + axiom-clean (commits
`d3abf555`, `c1481a34`).  The gating lemma `openRunAt_stackRealizes` is banked and the depth guard is
threaded to every reached `openStep` via the `_of_source` path.  **Swap arm NOT LIVE** (peephole delta
still push;pop-only).  Next session = the atomic `peepholeBody` swap-arm commit, but FIRST resolve
Obstacle B (directional `bodyType?`) as its own green commit, retire the closed tower (Obstacle A, do
it as its own green commit), then land the 4 syntactic + open semantic arm with the module reshuffle
above.  `compile_correct`/`compile_correct_creation` axioms MUST stay `[propext, Classical.choice,
Quot.sound]`.
**PROCESS NOTE (unchanged):** host is **zsh**; `lake build … > log 2>&1; echo RC=$?` (no pipe);
harness `check` ~3–4 min — `nohup … &`, poll `until ! kill -0 PID; do sleep 15; done`.

## Session-54 update (2026-07-20): THE `swap d ; swap d → ε` ARM IS **LIVE**. All three §Session-53 items landed as three green, axiom-clean commits; the atomic `peepholeBody` swap arm is committed and every re-greening is done. `scripts/opt_harness.sh check` = OK (**43** public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`). `compile_correct` / `compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]`. Single-contract sanity (pinned solc 0.8.26 → `solidus-backend summary` on `examples/AdversarialStackPressure.sol`): runtime **8557** / creation **8591** bytes — **byte-identical** to the §Session-53 baseline (the `peepholeProgram` transform is proof scaffolding, NOT spliced into emitted codegen, so a live arm changes no bytes; the arm firing is proven, not yet wired to output).

### LANDED (green, axiom-clean)
* **Commit `29fdcd5f`** — Obstacle B: **directional** `peepholeBody_bodyType?` (`PeepholeOpen.lean:36`). Weakened the equational shape-neutrality to `bodyType? body input = some output → bodyType? (peepholeBody body) input = some output`. The equational form is FALSE under the swap arm (shallow input untypeable on the original while the cancelled tail types); the directional form is TRUE (an original typing forces the swaps well-typed → involution preserves it) and suffices for both consumers, each carrying the original `= some output`: `openRunBody_peephole_congr`'s `hRestBodyType` and `block_wellTyped_peepholeProgram` (`PeepholeSpine.lean:52`, now `exact peepholeBody_bodyType? _ _ _ hTyped.1`).
* **Commit `681872dc`** — Obstacle A: **retired the dead closed-level `runBody` tower**. Removed `peepholeBody_runBody_erase` (`PeepholeSemantics.lean`, split on `peepholeBody_cons`, unsound under the swap arm with a `BodySafe`-only signature) and deleted `EvmCompiler/TypedCfg/PeepholeBlock.lean` (its dead lift; imported by nobody — job count unchanged at 1356). The crown routes only through the OPEN level, which carries the `StackRealizes` guard. Kept `mem_peepholeBody` / `runPops_map_erase` (live external users).
* **Commit `c97f533b`** — **THE LIVE SWAP ARM**. Added `| .swap d, .swap d' :: rest' => if d = d' then rest' else .swap d :: .swap d' :: rest'` to `peepholeBody` (`Peephole.lean:32`) + `peepholeBody_cons`.
  * **Syntactic 3-arm splits re-greened**: `peepholeBody_length_le` (`Peephole.lean`, `split <;> simp only [List.length_cons] <;> omega`), `mem_peepholeBody` (`PeepholeSemantics.lean`, nested `if_pos`/`if_neg`), directional `peepholeBody_bodyType?` swap arm (`PeepholeOpen.lean`, `swap_type_involution` for the d=d' cancel, `rw [← hEq]` reducing d≠d' to keep).
  * **Open semantic crown** — `openRunBody_peephole_congr` swap arm (`PeepholeOpen.lean:~260`). Ingredients `runState_swap_eq` + `openRunBody_swap_cons_ok` **moved into `PeepholeOpen`** (+`import …PeepholeSwapKernel`) per the §Session-53 module-cycle note. d=d' cancellation MIRRORS the push;pop arm (did NOT use the mis-shaped monolithic `openRunBody_swap_swap_congr`): fire the RHS head swap on `state2` under `StackRealizes input state2`; recurse `openRunBody_peephole_congr rest` from `s1a` (=`swap state1`) to `s2a` (=`swap state2`) with `s1a ~ s2a` via `runState_map_erase`; fire the LHS second swap on `s1a` (involution `middle→input`) to `s1b`; `swap_swap_sameRuntimeData` gives `s1b ~ state1`, then `openRunBody_runtimeRel` carries the tail. d≠d' = `rw [← hEq]` + the verbatim keep arm.
  * **OBSTACLE C (the §Session-53 frontier MISSED it — a THIRD site)**: the fuel-size bound. `LowerLe` breaks unconditionally for `swap;swap` — a shallow input makes the original body fail to lower (`CompiledBlock.fuelBudget` none-arm = 0) while the cancelled tail lowers (positive), so `peephole ≤ orig` fails. **Fixed by threading the body typing guard** through `PeepholeFuel.lean`: `lowerBodyFrom?_peephole_le` now carries `(output)` + `Block.bodyType? body input = some output`; head-typed `LowerLe.cons` (via `Preservation.Instr.type?_eq_some_of_lowerAt?`); new `lowerAt?_swap_of_type?` (typing → lowering, exact fragment length irrelevant — the swap codes only ADD bytes to the original); `compiledBlock_fuelBudget_peephole_le` + block typing; new `fuelBudget_blocks_le`; `fuelBudget_peepholeProgram_le` + `program.WellTyped`. Supplied `hWellTyped` at the **4** `fuelBudget_peepholeProgram_le cfg` call sites in `EvmCompiler/Compiler/OpenInteractionComposition.lean` (each already carries `hWellTyped : cfg.WellTyped`).
  * **Retired** dead `PeepholeSwapOpen.lean` (its two helpers now live in `PeepholeOpen`; `openRunBody_swap_swap_congr` was referenced only in a doc comment — unused) + its `Verification.lean` import. Job count 1356 → **1355**.

### Status handed to session 55
Steps B + C **CLOSED**; Step D (all items) **CLOSED**; the `swap d ; swap d → ε` arm is **LIVE** in `peepholeBody` and every dependent proof is green + axiom-clean. `peepholeProgram` now cancels BOTH `push;pop` and `swap;swap` and its whole-program OPEN congruence (`Block.openRun_peephole_runtimeRel`) + `WellTyped` preservation + fuel bound all hold. **Not yet done**: splicing `peepholeProgram` into the emitted codegen (currently the transform is proven but the public spine emits the un-peepholed program, so byte counts are unchanged). Next natural target = the spine splice (emit `peepholeProgram cfg` and re-route `compile_correct` through `Block.openRun_peephole_runtimeRel`), or a further peephole rule (`dup;pop`, `swapN;…`). `compile_correct`/`compile_correct_creation` axioms MUST stay `[propext, Classical.choice, Quot.sound]`.

## Session-55 update (2026-07-20): GROUND-TRUTH RESOLVED — the spine splice is **ALREADY LIVE** in the emitted-bytes path (has been since §Session-4); the §Session-54 parenthetical "NOT spliced into emitted codegen" is **STALE / WRONG**. The `swap;swap→ε` arm is genuinely wired into the shipped bytes but is **live-but-inert** (outcome (a)): the redundant swap pairs do **not exist at the TypedCfg block-body granularity** the cfg-level `peepholeBody` operates on — they are a **lowering / compaction-phase artifact**. No code change (splice needs none); this session is investigation + measurement + this note. `scripts/opt_harness.sh check` = **OK** (1355 jobs, **43** public theorems; `compile_correct`/`compile_correct_creation` axioms = `[propext, Classical.choice, Quot.sound]`).

### The contradiction and its resolution (the mandate's first task)
The §Session-3/4 note claimed the splice landed: `StackArtifact.compile?` certifies `(peepholeProgram cfg).compileCertified?`. The §Session-54 note claimed the opposite ("the public spine emits the un-peepholed program"). **Ground truth by code trace, not by re-reading the notes:**
* **`EvmCompiler/Compiler/StackArtifact.lean:60`**: `let certified ← (TypedCfg.Peephole.peepholeProgram cfg).compileCertified?` — the emitted target is derived from the **peepholed** cfg. (`compile?_parts`' 11th field, line 92, pins `(peepholeProgram artifact.cfg).compileCertified? = some artifact.certified`.)
* **`EvmCompiler/TypedCfg/Certificate.lean:497`**: `compileCertified?` does `let target ← program.lower?`, so `certified.target = (peepholeProgram cfg).lower?`.
* **`StackArtifact.compile?:61`**: `let target ← Assembly.compileExecutable? certified.target` → the emitted `artifact.target` is the lowering of the **peepholed** program.
* **CLI raw path** (the corpus/measurement path): `runRaw` → `Solidity.RawAst.compileArtifactFromRawSolcIr?` → `Program.compileArtifactWithLinkerSymbols?` → per-object `compileVerifiedStackCodeArtifactIn?` (`Frontend.lean:3862/3867`) → `Compiler.StackArtifact.compile? lower.toFunctions`. Same `compile?`, same peephole. **The shipped bytes go through `peepholeProgram`.**

So §Session-54's parenthetical is simply incorrect (its author measured ASP byte-identical and inferred "no splice"; the real reason is "no targets"). **The splice has been live in emitted bytes continuously since §Session-4** — it was never reverted; the Step B–D restructure (sessions 51–54) kept `StackArtifact.compile?:60` pointed at `peepholeProgram cfg` throughout.

### Why bytes are unchanged — RIGOROUS, not "probably no targets"
`peepholeBody`'s swap arm deletes an adjacent same-depth `swap d :: swap d` from a TypedCfg **block body**; each deleted `Instr.swap` lowers to ≥1 byte, so **any** firing strictly shrinks the emitted image. Therefore *unchanged emitted bytes ⟺ the cfg-body peephole fires zero times* for a contract. Measured (pinned solc 0.8.26, current HEAD e073b629 build, peephole ON):
| contract | runtime | creation | matches baseline |
|---|---|---|---|
| AdversarialStackPressure | **8557** | **8591** | = §Session-53/54 |
| ExternalCallBox | **2791** | **2825** | = §Session-4 (2791 rt) |

Both byte-identical to their pre-swap-arm baselines ⟹ **zero cfg-body firings** on both. No wiring changed this session, so **no determinism double-compile is required** (byte counts did not move).

### WHERE the swap;swap pairs actually live (the mandate's scan)
Disassembled the **emitted, shipped** bytecode (properly skipping PUSH immediates) and counted adjacent *equal-opcode* `SWAPn;SWAPn` (the exact rule the arm cancels) and `PUSHx;POP`:
| contract | runtime bytes | ops | `SWAPn;SWAPn` adj | `PUSHx;POP` adj |
|---|---|---|---|---|
| AdversarialStackPressure | 8557 | 8308 | **3** | 0 |
| ExternalCallBox | 2791 | 2146 | **61** | 0 |
| MiniToken | 1991 | 1354 | **15** | 0 |
| LoopBox | 923 | 639 | **15** | 0 |

The ExternalCallBox count **61** reproduces §Session-4's physical `swapPair` figure exactly (`controlPatternStats.swapPair`, `BackendCli.lean:629`, is the identical adjacency rule). These pairs **survive all the way into the shipped bytes** yet the cfg-level peephole cancelled **none** of them → they are **created downstream of the TypedCfg point**, during `cfg.lower?` / StackShuffle expansion / fallthrough compaction (adjacencies that span block boundaries or arise from per-block cleanup-shuffle expansion are invisible to a single-block-body `peepholeBody`). `PUSHx;POP` = 0 corpus-wide (confirms push;pop is inert too). **This is outcome (a): the arm is correctly wired and provably sound, but structurally cannot fire because the target adjacencies do not exist at cfg-body granularity.**

### The honest next lever (highest value observed)
The cfg-body `peepholeProgram` is the wrong altitude for these no-ops. The 61+15+15+3 removable `SWAPn;SWAPn` pairs live in the **lowered assembly** (post-`lower?`, in `Assembly.Program`/physical). The real byte win requires one of:
1. **An assembly-level (post-lowering) involution peephole** on `Assembly.TargetProgram` (or on the compacted physical stream), cancelling adjacent equal `SWAPn;SWAPn` and `PUSHx;POP`. This is a **new proof lever** at the Assembly layer — the sessions-12–54 chain is entirely TypedCfg-level and does NOT transfer; it would need its own `RuntimeOutcomeRel`-style congruence against `Assembly.compileExecutable?`/`Compact`. Est. large. Watch the frozen boundary: `EvmCompiler/Assembly/*` is FROZEN, so an assembly-level transform must live in a NEW non-frozen module and be spliced at `StackArtifact.compile?:61` (the `compileExecutable?` seam), NOT inside `Assembly/`.
2. **Shuffle-scheduler canonicalization** in `TypedCfg/Lower.lean` (StackShuffle) so it never emits an adjacent `swapN;swapN` in the first place — a codegen-quality fix, cheaper to make correct-by-construction but touches the lowering the whole certificate rests on.

Either is a genuine multi-session effort; neither is a "splice" of the existing `peepholeProgram`. The cfg-level `push;pop`+`swap;swap` tower (sessions 3–54) remains a correct, axiom-clean, **already-emitted-path-wired** substrate that is simply inert on this corpus.

### Files touched this session
Documentation only (`PEEPHOLE_PROGRESS.md`). No `.lean` change; scratch probe/measure scripts live outside the repo and are not committed. `compile_correct`/`compile_correct_creation` axioms unchanged.

## Session-56 update (2026-07-20): ROUTE DECISION — the removable pairs are **PROVABLY `swap d ; <zero-width no-op> ; swap d` inside cfg block bodies**, NOT a lowering/StackShuffle artifact. §Session-55's "downstream of the TypedCfg point / StackShuffle expansion" attribution is **corrected**: the pairs are visible at cfg-body granularity, just not at *literal* list adjacency. **Route 2 (shuffle-scheduler canonicalization) is FALSIFIED** as a premise; **Route 1 (assembly-level peephole) is real but strictly larger and breaks the certificate contract**. Chosen route = **Refined Route 3: a TYPE-DIRECTED cfg-body peephole that cancels `swap d ; z ; swap d` by remapping `z`'s position parameters through the 0↔d+1 transposition** — same altitude as the sessions-3–54 tower (reuses the swap-involution semantics), no assembly-layer harness, no frozen-file edits. This session is route-decision + rigorous/empirical evidence + recipe; **no live `.lean` change landed** (the full transform is a multi-session build — the *literal*-adjacency swap arm alone cost sessions 53–54 with three obstacles, and this adds shape-threading). `scripts/opt_harness.sh check` = **OK** (1355 jobs, **43** public theorems; `compile_correct`/`compile_correct_creation` axioms = `[propext, Classical.choice, Quot.sound]`, UNCHANGED). Bytes unchanged (no live edit) ⟹ no determinism double-compile required.

### THE MECHANISM — proven by pure reasoning, then confirmed empirically
**Airtight deduction (no probe needed for the category):**
1. `TypedCfg.Instr.lower?` (`Lower.lean:9-55`) maps every body instruction **1:1 to opcodes**, EXCEPT `bindLocals`/`bindScratch`/`relabel` → `[]` (zero-width) and `unwind` → `replicate (…) pop`. `swap d` → exactly one `swapN` opcode.
2. `Block.lowerBodyFrom?` (`Lower.lean:242`) concatenates per-instruction lowerings; `Block.lower?` emits `label :: body ++ term` (`:250`); `Program.lowerBlocks?` concatenates blocks, **each starting with `.label`** (`:343`).
3. Every terminator lowering **starts with a non-swap**: `fallthrough/jump`→`jump`, `jumpi`→`jumpi;jump`, `halt`→opcode, `returnDispatch`→`dupInstr …` (a DUP). And `StackShuffle.liftBuriedToTop`/`sinkTopUnder` (`Assembly/StackShuffle.lean:46-57`) emit **strictly distinct** swap indices `swap2,swap3,…`. ⟹ **no adjacent equal `swapN;swapN` is ever born at a block/terminator/shuffle seam.**
4. Therefore an adjacent equal `swapN;swapN` in the emitted image can ONLY be two body `Instr.swap d` whose intervening instructions all lower to `[]` — i.e. **only `bindLocals`/`bindScratch`/`relabel` sit between them** (≥1 of them, else the pair is *literally* adjacent and `peepholeBody`'s existing swap arm would cancel it, shrinking bytes — contradicting §Session-55's measured byte-identical corpus).

**`peepholeBody` (`Peephole.lean:32`) matches on LITERAL list adjacency** (`.swap d, .swap d' :: rest'`); a kept zero-width instr in `peepholeBody rest`'s head breaks the match ("keep arm"). That is *exactly why* the arm fires zero times yet the pairs ship.

**Empirical confirmation** (`lake env lean` probe on `body = [swap 2, bindLocals 0 ["x"], swap 2]`, input `s0=[word,word,word,local "a"]`):
* `peepholeBody body = body` (unchanged — NOT cancelled). ✓ cfg-body inertness.
* `Block.lowerBodyFrom? body s0` body-image = `[swap3, swap3]` — the exact 2-byte removable pair reaching the shipped stream. ✓
* output shape `s3 = [word,word,word,local "x"]`.

### The sound transform + the shape subtlety (why it is type-directed, not syntactic)
Runtime: `swap d ; z ; swap d` on the concrete `EVMState` = `swap_d ∘ id ∘ swap_d = id` (all three zero-width instrs have `runState = .ok state`, `Semantics.lean:78-83`); `z` alone is also `id`. **Runtime always matches** regardless of shape.

Shape (typing) is the catch. `swap d`'s `type?` (`Typing.lean:37`) transposes slot positions `0 ↔ d+1`; `z` preserves `length` and `tail` but mutates slot *kinds/names* (`bindLocals?`/`bindScratch?`/`relabelCompatible`, `Syntax.lean:71-123`). So `s3 = swap_d(z(swap_d(s0))) ≠ z(s0)` in general — **naively deleting the two swaps changes the shape fed to the block's remaining instructions and can break their typing/lowering.** Probe: the "shape-restoring `relabel s3`" replacement is **only conditionally legal** — `relabelCompatible s0 s3 = false` for the bindLocals example (position 3 is `local "a"` vs `local "x"`, neither `.word`, so `slotsAgree` fails), but `= true` for the bindScratch example.

**The correct-by-construction replacement:** replace `swap d ; z ; swap d` with `z'`, where `z'` is `z` with its position parameters remapped through the `0↔d+1` transposition (`bindLocals` offset, `bindScratch` baseDepth, `relabel` target permuted). Probe: `type?(bindLocals 3 ["x"]) s0 = s3` **exactly** — so `swap 2 ; bindLocals 0 ["x"] ; swap 2 → bindLocals 3 ["x"]` preserves the output shape `s3` AND the runtime, while dropping the 2-byte `swap3;swap3`. `z'` still lowers to `[]`. This is the byte win, sound by construction, at cfg-body altitude.

### Route comparison (byte-win / proof-risk)
* **Route 2 — FALSIFIED.** Premise ("adjacent pairs born in StackShuffle/fallthrough compaction") is false by step 3 above: shuffle expansion emits strictly-distinct indices and block/terminator seams never abut two equal swaps. Nothing to canonicalize there. Discard.
* **Route 1 — assembly-level peephole (real, but strictly larger).** Local soundness is trivial (`swapN` is a stack involution, no shapes). But: (i) the emitted `artifact.target` is pinned by the certificate — `StackArtifact.compile?:60-61` builds `certified` from `(peepholeProgram cfg).compileCertified?` and `certified.target = (peepholeProgram cfg).lower?` (`Certificate.lean:497`); `compile?_parts`' 11th/12th fields pin `certified`↔`target`. Splicing a rewrite at `:61` means the shipped bytes no longer equal `encode(certified.target)`, so a **new certificate** relating the peepholed assembly to the source is required. (ii) `Correctness.compile_correct` rests on `optimizedRawSolcIrToGasfulRawBytecodeTotal hArtifact hCert hInitial` carrying the outcome down `Assembly.Compact.InteractionSemantics.openRunNResult` / `GasfulBridge.RunRefinesOpenTotal` — an **assembly/Compact/GasfulBridge interaction-semantics congruence** for the rewrite must be threaded through that whole chain. New harness, does not reuse the TypedCfg tower. Larger surface, higher integration risk.
* **Route 3 (Refined) — CHOSEN.** Right altitude: the pairs live here; the swap-involution runtime semantics is already proven (sessions 51–54). Cost is (a) making `peepholeBody` **type-directed** (`List Instr → Shape → List Instr`, threading a shape so `z'` can be computed) — an architectural change the current purely-syntactic tower does not have, so the semantic/open-crown/fuel congruence lemmas and the 4/5 OIC call sites must be re-stated over the shape-carrying variant; (b) the `z`-param remap + its `type?`-preservation lemma per zero-width constructor; (c) re-run the swap-arm cancellation proof with `z'` (not `ε`) as the residue. No frozen edits, no assembly harness. **Est. 2–3 sessions**, but every piece is a known-shape extension of landed work.

### Blast-radius note for Route 3
The purely-syntactic `peepholeBody : List Instr → List Instr` is congruence-proved across `PeepholeSemantics`/`PeepholeOpen`/`PeepholeFuel`/`PeepholeSpine` and wired at the 4 `fuelBudget_peepholeProgram_le` sites in `OpenInteractionComposition.lean` + the 5 OIC sites (`PeepholeSourceCongr`). A type-directed variant either (A) threads `Shape` everywhere (large restate) or (B) — **recommended** — runs as a **separate pre-normalization** `normalizeNoopSwaps : Block → Block` computed *with* the block's `input` shape (available: blocks carry `input`), proved to preserve `Block.lower?` image-minus-the-two-swaps and `Block.runBody`, then composed BEFORE the existing syntactic `peepholeProgram`. (B) keeps the sessions-3–54 tower untouched and adds one new congruence at the block granularity — smaller blast radius. Next session should scope (B) first.

### Next-session recipe (Refined Route 3, variant B)
1. New non-frozen module `EvmCompiler/TypedCfg/PeepholeNoopSwap.lean`: define `remapZeroWidth (d : Nat) : Instr → Instr` (offset/baseDepth/target permuted by the `0↔d+1` transposition; identity on non-zero-width) and `normalizeBody : List Instr → Shape → List Instr` that, on `swap d :: zs ++ swap d :: rest` with all `zs` zero-width, emits `zs.map (remapZeroWidth d) ++ normalizeBody rest s3`.
2. Prove `type?`-preservation: `type?_normalizeBody : Block.lowerBodyFrom? (normalizeBody body input) input` types to the **same output shape** as `body`, per-constructor via the transposition lemma (probe already shows the `bindLocals` case numerically).
3. Prove runtime congruence: `runBody (normalizeBody body input) input state = runBody body input state` — the swap-involution + zero-width `runState = .ok state` facts (sessions 51–54 kernels: `runState_swap_eq`, `swap_swap_sameRuntimeData`) carry directly since the residue `z'` is still state-`id`.
4. Prove `lower?`-shrinks: emitted image drops exactly the `swapN;swapN` per fired pair (mirror `PeepholeFuel.lowerAt?_swap_of_type?` / `compiledBlock_fuelBudget_peephole_le`).
5. Splice `normalizeBody` into `Block`/`Program` normalization consumed by `peepholeProgram` (or compose at `StackArtifact.compile?:60` as `peepholeProgram (normalizeProgram cfg)`), re-green the 4+5 sites.
6. Re-scan ASP/ExternalCallBox/MiniToken/LoopBox: expect `swapN;swapN adj` to drop by the fired count (≤ 3/61/15/15) with matching runtime-byte deltas; determinism double-compile the movers.

### Files touched this session
Documentation only (`PEEPHOLE_PROGRESS.md`). No `.lean` change; the two `lake env lean` probes were run from the scratchpad and are not committed. `compile_correct`/`compile_correct_creation` axioms unchanged = `[propext, Classical.choice, Quot.sound]`.

## Session-57 update (2026-07-20): the Route-3 variant-B TRANSFORM + its SYNTACTIC lemmas + the SEMANTIC-CORE **type (shape) half** are LANDED green + axiom-clean across SIX commits.  Steps 1–2 of the §Session-56 recipe are COMPLETE; step 3 is closed on its *type-transposition* half for the remap-safe cases (`bindScratch`, `relabel`, single-name `bindLocals`).  The transform is a standalone leaf (imported by nobody in the certified spine), so it is NOT yet spliced — steps 3-runtime / 4 / 5 / 6 remain the frontier.  `compile_correct` / `compile_correct_creation` axioms **UNCHANGED** = `[propext, Classical.choice, Quot.sound]` (verified by `#print axioms`; the new modules cannot affect them since the spine does not import them).  No byte measurement (no live splice ⟹ codegen unchanged ⟹ no determinism double-compile).

### What landed (two new NON-FROZEN modules)
**`EvmCompiler/TypedCfg/PeepholeNoopSwap.lean`** — the transform + syntactic lemmas (steps 1–2):
* `swapPos`/`remapDepth`/`remapShape` (`:39`/`:46`/`:50`) — the `0↔d+1` position transposition on lists / indices / shapes.
* `isZeroWidth` (`:55`), `remapZeroWidth` (`:63`) — the `0↔d+1` conjugation of a zero-width instr's position params (identity on non-zero-width).
* `leadingZeroWidth` (`:71`) + `leadingZeroWidth_length`/`_snd_length_le` (`:80`/`:94`) — maximal zero-width-prefix splitter for the window scan.
* `normalizeBody` (`:105`) — the **well-founded** (`termination_by body.length`) transform cancelling `swap d ; z* ; swap d` windows: drops both swaps, remaps the intervening zero-width run.
* Syntactic family: `isZeroWidth_remapZeroWidth` (`:131`), `remapZeroWidth_of_not_zeroWidth` (`:136`), `leadingZeroWidth_fst_all_zeroWidth` (`:141`), `leadingZeroWidth_append` (`:159`), the four WF-unfolding lemmas `normalizeBody_fire`/`_keep_swap`/`_keep_noTail`/`_cons_generic` (`:172`/`:179`/`:185`/`:194`), and `normalizeBody_length_le` (`:202`, via `normalizeBody.induct`).

**`EvmCompiler/TypedCfg/PeepholeNoopSwapType.lean`** — the `type?`-preservation core (step 3, type half):
* `swapPos` calculus: `swapPos_getElem?` (`:43`, pointwise), `swapPos_involutive` (`:55`), `swapPos_set_comm` (`:69`, `set` commutes through the transposition via `transpIdx`).
* `type?_swap_eq` (`:89`) — **the swap bridge**: `Instr.type? (.swap d) s = some s'` ⟹ `s'.slots = swapPos 0 (d+1) s.slots ∧ s'.tail = s.tail`.
* `getElem?_swapPos_remapDepth` (`:118`), `swap_bounds` (`:134`) — index-transfer + the two-exchanged-positions-exist bound.
* `type?_window_bindScratch` (`:144`), `type?_window_relabel` (`:259`), `type?_window_bindLocals_single` (`:345`) — the three per-constructor **window `type?`-preservation** lemmas: `swap d ; z ; swap d` ↦ `remapZeroWidth d z` reaches the *identical output shape*.
* `slotsAgree` machinery for `relabel`: `pairAgree`/`pairAgree?` (`:198`/`:204`), `slotsAgree_cons` (`:208`), `slotsAgree_iff_pointwise` (`:214`, `slotsAgree` = pairwise agreement on the common prefix), `slotsAgree_swapPos` (`:241`, transposition invariance).
* `bindLocals`-single support: `take_append_single_drop` (`:322`), `type?_bindLocals_single` (`:334`, single-name `bindLocals` = a `set`).
* **Capstone** `type?_remapZeroWidth_window` (`:411`) guarded by `RemapSafe` (`:398`) = `bindScratch | relabel | single-name bindLocals`.

### KEY FINDING — `remapZeroWidth`'s `bindLocals` arm is only a single-instruction residue for `names.length ≤ 1` (or non-straddling ranges)
The naive `remapZeroWidth d (.bindLocals offset names) = .bindLocals (remapDepth d offset) names` is **shape-correct only when the bound range `[offset, offset+len)` does not straddle exactly one of the transposed positions `{0, d+1}`**.  A single-name bind (`len = 1`) is always a single position, so it is always safe (and is exactly the §Session-56 empirical case `bindLocals 0 ["x"]`).  For a multi-name range straddling one endpoint the transposition image is **non-contiguous**, so it cannot be any single `bindLocals` with the same name list.  This is the precise reason `RemapSafe` gates `bindLocals` to `names.length = 1`.

### FRONTIER for the next session (in priority order)
1. **Multi-name `bindLocals`** — decide between (a) a *firing guard* on `normalizeBody` (only fire the window when every zero-width instr is `RemapSafe`; skip otherwise — soundness-preserving, loses the rare straddling win), or (b) a *multi-instruction residue* (emit ≥2 `bindLocals`/`set` instrs for the non-contiguous image).  (a) is far smaller; recommend scoping (a) first, which also makes `normalizeBody` sound-by-construction (currently `remapZeroWidth`'s multi-name arm is unsound-in-definition — harmless while unspliced, MUST be gated before splice).
2. **Runtime half of step 3** — `runBody (normalizeBody body input) input state ≈ runBody body input state` up to `eraseFst`/`SameRuntimeData`.  Ingredients ready: the swap-involution kernel `PeepholeSwapKernel.swap_swap_sameRuntimeData` + every zero-width `runState = .ok state` (`Semantics.lean:78-83`).  The residue `remapZeroWidth d z` is still `runState = .ok state` (`isZeroWidth_remapZeroWidth` + the `runState` zero-width arms), so the window's runtime collapses to `SameRuntimeData`.  This half is **gated on the type half** (which is now done) because `runBody` threads `type?` through `runAt` and errors on a `none` — the shapes must match, which the window `type?`-lemmas now supply.
3. **`lower?`-shrink (step 4)** + **splice (steps 5–6)** — compose `normalizeBody` at the block level, re-green the 4 `fuelBudget` + 5 OIC sites, splice `peepholeProgram (normalizeProgram cfg)` at `StackArtifact.compile?:60`, then re-scan ASP/ExternalCallBox/MiniToken/LoopBox (`swapN;swapN adj` targets 3/61/15/15; ASP 8557/8591, ECB 2791/2825 baselines) + determinism double-compile the movers.

### Files touched this session
Two NEW non-frozen modules: `EvmCompiler/TypedCfg/PeepholeNoopSwap.lean`, `EvmCompiler/TypedCfg/PeepholeNoopSwapType.lean`.  No frozen file touched; no existing file modified; the certified spine is byte-identical.  Six green, axiom-clean commits (step1 / step2 / step3a swapPos+bridge / step3b bindScratch / step3c relabel / step3d bindLocals-single / step3e capstone — banked incrementally).

## Session-58 update (2026-07-20): §Session-57 frontier items 1–2 CLOSED and the WHOLE congruence chain landed green up TO the splice.  Seven green, axiom-clean commits: the firing GUARD, the type run-fold + directional `bodyType?`, the open RUNTIME congruence, the block/one-step PROGRAM congruence, the SOURCE-THREADED congruences, and the FUEL bound.  The transform is still a standalone leaf (imported by nobody in the certified spine), so it is NOT yet spliced — ONLY the OIC/StackArtifact rewire remains.  `compile_correct` / `compile_correct_creation` axioms **UNCHANGED** = `[propext, Classical.choice, Quot.sound]` (the new modules are unimported by the spine).  No byte measurement (no live splice ⟹ codegen byte-identical ⟹ no determinism double-compile).

### What landed (six NEW non-frozen modules + gating edit)
1. **THE FIRING GUARD** (`PeepholeNoopSwap.lean`, edited): `normalizeBody`'s firing arm is now gated on `(leadingZeroWidth rest).1.all RemapSafe` — it only cancels a window whose *entire* interior zero-width run remaps to a single shape-preserving instruction.  `RemapSafe`/`remapSafe_isZeroWidth` moved into the base module.  This closes §Session-57 frontier item 1 (`remapZeroWidth`'s multi-name `bindLocals` arm is no longer reachable at firing) and makes `normalizeBody` **sound-by-construction**.  Re-greened `normalizeBody_fire` (+`hSafe`), new `normalizeBody_keep_unsafe`, `normalizeBody_length_le` over the new 5-case `normalizeBody.induct`.  (commit `1b1f7ee5`)
2. **Type run-fold + directional `bodyType?`** (`PeepholeNoopSwapConj.lean`): `type?_conj_remap` — `remapZeroWidth d` conjugates `type? z` by the shape transposition `remapShape d` for every `RemapSafe z` (the primitive the per-window s57 lemmas could NOT compose across a multi-instruction interior).  `bodyType?_map_remap_conj` folds it over a run; `normalizeBody_bodyType?` is the whole-body directional `type?`-preservation (analogue of `peepholeBody_bodyType?`).  Support: `remapDepth/remapShape` involution, `slotsAgree_swapPos_eq`, `bodyType?_cons/_append`, `type?_remapSafe_length`.  (commit `50b95fe0`)
3. **Open RUNTIME congruence** (`PeepholeNoopSwapRuntime.lean`): `openRunBody_normalize_congr` — the genuinely-new lemma, the analogue of `openRunBody_peephole_congr`; the normalized body is `Rel (RuntimeAtRel output)`-related (up to `SameRuntimeData`) to the original from any `SameRuntimeData` state.  Firing arm collapses `swap;zrun;swap` via `swap_swap_sameRuntimeData` + the zero-width run reduction `openRunBody_zeroWidth_run` (zero-width instrs run as state-identity: `runState_zeroWidth`).  Keep arms via `openRunBody_normalize_keep` (the peephole keep-arm skeleton abstracted over the tail congruence).  This is §Session-57 frontier item 2, CLOSED.  (commit `485872e5`)
4. **Block + one-step PROGRAM congruence** (`PeepholeNoopSwapProgram.lean`): `normalizeBlock`/`normalizeProgram` + `Block.openRun_normalize_runtimeRel` + `openStep_normalize_congr` (analogues of `PeepholeProgram`).  `forall_pcIndependent_normalize` (remapped zero-width instrs have empty effects ⟹ PC-independent regardless of position params) + `normalizeProgram_programCounterIndependent` + `findBlock?_normalizeProgram`.  (commit `10d9b999`)
5. **SOURCE-THREADED congruences** (`Structured/PeepholeNoopSwapSourceCongr.lean`): `openStep/openRunN/openRunNPrefix_normalize_congr_of_source` carry the `realizedWitnessFC` entry witness and re-establish it at each jump target, discharging the per-entry depth guard.  The witness machinery (`allDone_realizedWitnessFC_jump`, `stackRealizes_of_realizedWitnessFC_total`) is pass-agnostic and reused verbatim from Step B's `PeepholeSourceCongr`; only the RHS transform changes to `normalizeProgram` via `openStep_normalize_congr`.  (commit `ed63edc3`)
6. **FUEL bound** (`PeepholeNoopSwapFuel.lean`): `fuelBudget_normalizeProgram_le` (well-typed cfg) via `lowerBodyFrom?_normalize_le` — the normalized body lowers to the same output shape with ≤ bytes (firing drops 2 swap fragments + the interior zero-width run lowers to `[]` on both sides: `lowerAt?_zeroWidth`, `lowerBodyFrom?_zeroWidth_run`; keep arms via the pass-agnostic `LowerLe.cons`).  (commit `3f03b077`)

### THE FRONTIER (session 59) — the OIC/StackArtifact SPLICE, the only remaining step
The certified path `StackArtifact.compile?:60` = `(peepholeProgram cfg).compileCertified?`.  The correctness plumbing lives in `Compiler/OpenInteractionComposition.lean` (3398 lines) at **five** sites that call `openRunN{,Prefix}_peephole_congr_of_source generated …` + `fuelBudget_peepholeProgram_le` + `peepholeProgram_programCounterIndependent`.  To emit normalized bytes, splice `peepholeProgram (normalizeProgram cfg)`.
* **DEAD END (do not attempt):** composing at the OIC sites via `…_peephole_congr_of_source` applied with `cfg := normalizeProgram cfg` needs `GeneratedContext source entryShapes (normalizeProgram cfg)` — **FALSE**: the context asserts `cfg` IS the exact compiled program, and `normalizeProgram cfg` has different block bodies.
* **THE ROUTE:** a **combined** transform `combined cfg := peepholeProgram (normalizeProgram cfg)` with its OWN source-threaded congruence proved *relative to `cfg`* (the real compiled program) — `openStep_combined_congr_of_source` = `Rel.trans` of `openStep_normalize_congr_of_source` (cfg ~ normalizeProgram cfg @ state2) and `openStep_peephole_congr` (normalizeProgram cfg ~ combined cfg @ state2, with state2~state2).  The peephole step needs `(normalizeProgram cfg).WellTyped` + `.ProgramCounterIndependent` (have the latter; the former needs a new `normalizeProgram_wellTyped` — normalizeBlock preserves input/output/term and `normalizeBody_bodyType?` preserves the body typing, so it holds) + per-found-block `StackRealizes` at state2 (normalizeProgram cfg's blocks have the SAME input shapes as cfg's — `normalizeBlock` preserves `.input` — so `stackRealizes_of_realizedWitnessFC_total` on cfg supplies it directly).  All ingredients above (`openStep_normalize_congr`, the source-threaded normalize congruences, the fuel bound) are landed and green.
* **Then:** combined fuel bound = `fuelBudget_normalizeProgram_le` ∘ `fuelBudget_peepholeProgram_le` (trans of the two ≤); rewire the 5 OIC sites + `StackArtifact.compile?:60/92/147` from `peepholeProgram cfg` → `peepholeProgram (normalizeProgram cfg)`; `scripts/opt_harness.sh check` green; recompile ASP/ECB/MiniToken/LoopBox; report byte deltas (ASP 8557/8591, ECB 2791/2825 baselines; `swapN;swapN adj` targets 3/61/15/15); determinism double-compile if bytes move.  This is invasive surgery on the certified-spine composition (alters emitted bytes + touches `compile_correct`'s dependency graph), hence deferred to its own focused session per the never-commit-red discipline.

### Files touched (session 58)
Edited: `EvmCompiler/TypedCfg/PeepholeNoopSwap.lean` (guard).  Five NEW non-frozen modules: `PeepholeNoopSwapConj.lean`, `PeepholeNoopSwapRuntime.lean`, `PeepholeNoopSwapProgram.lean`, `PeepholeNoopSwapFuel.lean`, `Structured/PeepholeNoopSwapSourceCongr.lean`.  No frozen file touched; the certified spine is byte-identical (transform still unimported).  Seven green, axiom-clean commits.

## Session-59 update (2026-07-20): THE SPLICE IS DONE — the combined transform `peepholeProgram (normalizeProgram cfg)` is **LIVE in the emitted-bytes path**; **live-but-inert on the corpus (byte delta +0)**.  Three green, axiom-clean commits.  `scripts/opt_harness.sh check` = **OK** (43 public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct` / `compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]` (verified in the full Verification build).

### What landed
1. **`normalizeProgram_wellTyped`** (item 1, NEW module `EvmCompiler/TypedCfg/PeepholeNoopSwapSpine.lean`): the Route-3 analogue of `peepholeProgram_wellTyped` — `labelShape?_normalizeProgram` / `terminator_type?_normalizeProgram` / `emittedLabels_normalizeProgram` / `labelsUnique_normalizeProgram` / `block_wellTyped_normalizeProgram` (via `normalizeBody_bodyType?`).  (commit `c0c74125`)
2. **The combined transform congruence chain** (item 2, NEW module `EvmCompiler/Structured/PeepholeNoopSwapCombined.lean`): `combined_programCounterIndependent`, `fuelBudget_combined_le` (`le_trans` of `fuelBudget_peepholeProgram_le (normalizeProgram cfg) (normalizeProgram_wellTyped …)` and `fuelBudget_normalizeProgram_le cfg`), and `openStep/openRunN/openRunNPrefix_combined_congr_of_source`.  The one-step combined congruence is `Rel.trans` of `openStep_normalize_congr_of_source` (LEFT tree `cfg`, carrying the successor witness) and `openStep_peephole_congr (program := normalizeProgram cfg)` (its per-found-block `StackRealizes` at `state2` discharged from `stackRealizes_of_realizedWitnessFC_total` on `cfg` through `findBlock?_normalizeProgram` + `normalizeBlock_input`), then `Rel.mono` collapsing `(RuntimeRel ∧ witness) ∘ RuntimeRel` to `RuntimeRel ∧ witness` via `Outcome.RuntimeRel.trans`.  **Same argument shape as the peephole `*_of_source` family**, so the OIC swaps are pure name changes.  (commit `c0c74125`)
3. **THE SPLICE** (item 3, commit `452f7280`): `StackArtifact.compile?` (:60/:92/:147) now emits `(peepholeProgram (normalizeProgram cfg)).compileCertified?`.  The 5 OIC consumption sites rewired `peephole` → `combined` (`combined_programCounterIndependent`, `fuelBudget_combined_le`, `openRunN{,Prefix}_combined_congr_of_source`), and every `peepholeProgram cfg` value occurrence → `peepholeProgram (normalizeProgram cfg)`.  The DEAD-END (applying `…_peephole_congr_of_source` with `cfg := normalizeProgram cfg`, which needs a FALSE `GeneratedContext … (normalizeProgram cfg)`) is avoided exactly as the §Session-58 route prescribed — the combined congruence is relative to the real compiled `cfg`.  `EvmCompiler.Verification` full build green.

### MEASUREMENT (pinned solc 0.8.26, `solidus-backend raw-summary`)
| contract | runtime | creation | baseline | Δ | identical `swapN;swapN` adj (runtime) | baseline | Δ |
|---|---|---|---|---|---|---|---|
| AdversarialStackPressure | 8557 | 8591 | 8557/8591 | **+0** | 3 | 3 | 0 |
| ExternalCallBox | 2791 | 2825 | 2791/2825 | **+0** | 61 | 61 | 0 |
| MiniToken | 1991 | 2234 | — | — | 15 | 15 | 0 |
| LoopBox | 923 | 957 | — | — | 15 | 15 | 0 |

**Determinism:** all 4 contracts × {runtime, creation} **byte-identical across two independent compiles** (required, PASS).

**INTERPRETATION — NOT a live byte delta.**  The combined transform is genuinely wired into the shipped bytes (the certificate is now `(peepholeProgram (normalizeProgram cfg)).compileCertified?` and `compile_correct` routes through it), but it **fires nowhere on the corpus**: byte counts and the identical-swap-pair counts (3/61/15/15) are all unchanged.  This confirms the §Session-55/56 ground truth — the removable `swap d ; swap d` and `swap d ; z* ; swap d` windows do **not occur at the TypedCfg block-body granularity** these passes operate on (the adjacent bytecode swap pairs are a lowering/compaction-phase artifact downstream of the cfg-body point).  The campaign's first *byte-shrinking* delta will require either a lowering-phase peephole (Route 1, breaks the frozen certificate contract) or a source/cfg-shape that actually produces the window — neither is this splice.

### THE FRONTIER (session 60)
The splice infrastructure is complete and live.  To produce a real byte delta the frontier is now **either** (a) a *corpus* whose cfg block bodies genuinely contain `swap d ; z* ; swap d` windows (find/synthesize one, then measure a shrink through the now-live spine), **or** (b) a Route-1 assembly/lowering-phase peephole with its own certified congruence at the lower altitude (strictly larger, and must not touch the frozen `Assembly/*` — needs a new non-frozen post-lowering pass module).  The cfg-body transform tower (sessions 3–59) is done and shipping.

### Files touched (session 59)
Two NEW non-frozen modules: `EvmCompiler/TypedCfg/PeepholeNoopSwapSpine.lean`, `EvmCompiler/Structured/PeepholeNoopSwapCombined.lean`.  Edited (both non-frozen): `EvmCompiler/Compiler/StackArtifact.lean` (splice + import), `EvmCompiler/Compiler/OpenInteractionComposition.lean` (5-site rewire + import).  No frozen file touched.  Three green, axiom-clean commits.

## Session-60 update (2026-07-20): EMPIRICAL PINPOINTING — the birth site of ALL 61 ExternalCallBox `SWAPn;SWAPn` pairs is MEASURED, not deduced: **100 % are fallthrough BLOCK SEAMS created by the compaction phase** (`Assembly.Compact.prepare` = `elideFallthroughJumps` + `pruneUnreferencedLabels`).  **Both §55 (StackShuffle/lowering) and §56 (cfg-body `swap d ; z* ; swap d`) are EMPIRICALLY REFUTED.**  The pairs do NOT exist in the lowered image `certified.target` at all — they are manufactured downstream, during byte compaction, by removing the `jump G ; label G` that separated block A's tail swap from block B's head swap.  This is why the entire sessions-3–59 cfg-body peephole∘normalize tower fires nowhere: it operates at the wrong altitude (single cfg block bodies), and the redundancy is inherently a **cross-block seam** phenomenon.  No `.lean` change landed (the fix is a multi-session cfg-level cross-block transform — no small localized re-proof exists, so per the never-commit-red discipline this session is measurement + route decision + this note).  `scripts/opt_harness.sh check` unaffected (no `.lean` edit); `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.  Docs-only commit.

### METHOD (empirical, reproducible; probes run from scratch dir OUTSIDE the repo, NOT committed)
Generated ExternalCallBox runtime solc IR with **pinned solc 0.8.26** (`viaIR`, Yul optimizer, `details.yul`), fed it through the exact corpus path in a `lake env lean --run` probe: `Solidity.RawAst.decodeAndElaborateSolcIr? … (objectSelector := .runtime)` → `Program.compileArtifactWithLinkerSymbols? []` → `artifact.codeArtifact`.  From the code artifact:
* `L := codeArtifact.compiled.certified.target` — the LOWERED combined program `(peepholeProgram (normalizeProgram cfg)).lower?` (WITH `.label`/`.jump` pseudo-instrs, pre-compaction).
* `P := codeArtifact.compact.physicalSource` — the POST-compaction `Assembly.Program` on which the CLI's `controlPatternStats.swapPair` is computed (`BackendCli.lean:745`), i.e. the exact 61-count metric.

### THE DECISIVE MEASUREMENT
| program | adjacent-equal `SWAPn;SWAPn` |
|---|---|
| `L` = `certified.target` (lowered, pre-compaction) | **0** |
| `elideFallthroughJumps L` (jumps elided, labels kept) | **0** |
| `prepare L` = `physicalSource` = `P` (jumps elided + labels pruned) | **61** |

`decide (prepare L = physicalSource) = true` (my `P` IS the shipped physical source).  **The 61 pairs are born entirely by `pruneUnreferencedLabels` acting after `elideFallthroughJumps`** — neither lowering (`L` has 0) nor jump-elision alone (`elide L` has 0) produces a single one.  Splitting `L` into its 1056 per-block segments (delimited by `.label`): **intra-block swap pairs = 0** across all blocks — no cfg block body contains the pattern, confirming the cfg-body tower structurally cannot fire.

### BIRTH-SITE CLASSIFICATION (all 61, via greedy `P`-back-to-`L` subsequence alignment — compaction only DELETES, so `P ⊆ L` in order)
For every pair at `P[i],P[i+1]` I recovered the `L` window `L[la..lb]` and the deleted gap `L[la+1 .. lb-1]`:

| birth category | count | gap removed by compaction | swap depth |
|---|---|---|---|
| **fallthrough block seam** (A.term = `.fallthrough G`, A.body tail `swap 0`, B=block `G` head `swap 0`) | **61 / 61** | exactly `[jump G ; label G]`, `G` matching | **all SWAP1 (d=0)** — histogram `{0x90 ↦ 61}` |
| lowering-internal (StackShuffle / terminator) | 0 | — | — |
| cfg-body `swap;z*;swap` (the §56 premise) | 0 | — | — |

Additional structural facts proven from the data (all 61/61):
* Gap is **exactly** `[jump G, label G]` with the jump target = the pruned label (a genuine fallthrough).
* `G` is referenced **exactly once** in all of `L` (only by the seam jump) ⟹ after elision `G` is unreferenced ⟹ pruned ⟹ **block B has a UNIQUE predecessor** (the fallthrough from A).  This is the crucial soundness lever: deleting B's head swap cannot break any other in-edge because there is none.

Representative `L` windows (probe output):
```
pair#1  SWAP1@P[32]   L[71..74]   gap=[jump  generated 21_100 ; label generated 21_100]
pair#8  SWAP1@P[230]  L[511..514] gap=[jump  generated 149_100; label generated 149_100]
pair#20 SWAP1@P[744]  L[1431..1434] gap=[jump generated 370_100; label generated 370_100]
```
i.e. `L` locally is `… , swap1 , jump G , label G , swap1 , …`  →  compaction  →  `… , swap1 , swap1 , …`.

### WHY THIS FORCES THE CATEGORY (airtight, matches the measurement)
`L` is a concatenation of per-block lowerings, each `= .label :: body ++ term` (`Lower.lean:250`); block bodies contain NO labels (labels only lead blocks / returnDispatch cases).  Compaction's only edits are (i) `elideFallthroughJumps` deletes a `jump t` immediately followed by `label t`, (ii) `pruneUnreferencedLabels` deletes labels with no remaining reference.  Therefore any adjacent equal `swapN;swapN` in `P` that is NOT already adjacent in `L` (measured: none are) can ONLY arise from deleting a `.label` (a block boundary) — and, given `L` has no `jump;label` pairs whose removal leaves two equal swaps except across a fallthrough seam, EVERY such pair is `blockA(…swap d) —fallthrough→ blockB(swap d …)`.  §56 step-3's claim that "block/terminator seams never abut two equal swaps" is TRUE *in `L`* but MISSES that compaction *creates* the abutment by erasing the seam.  That is the precise error in the §55/§56 deductions.

### ROUTE RE-DECISION (evidence-based)
The redundancy is a **cross-block fallthrough seam** with a **unique-predecessor** successor, all at **SWAP1 (d=0)**.  Three routes, with blast radius:

* **Route 1 / assembly-level (post-`prepare`) peephole — REAL, where the bytes are, but LARGEST.**  Cancel adjacent equal swaps in `physicalSource`.  Local soundness trivial (SWAP is a stack involution, shape-free).  BUT `physicalSource` feeds `layout?/emit?/bytes` and the `Compact.DecodingCorrect` + `GasfulBridge.RunRefinesOpenTotal` interaction-semantics chain; `Assembly/*` and `Compact.lean` are FROZEN, so the pass must live in a NEW non-frozen module spliced at the `Compact` seam with its OWN assembly-layer congruence.  The entire sessions-3–59 tower is TypedCfg-level and does NOT transfer.  Blast radius: LARGE + new altitude.  (Unchanged from §55/§56 assessment.)

* **Route A — cfg-level FALLTHROUGH-SEAM swap cancellation (block-structure-preserving) — CHOSEN as primary.**  A cfg→cfg pass that, for each block A with `term = .fallthrough B` where B has a unique predecessor (computable: B's label referenced exactly once in the cfg) and A.body ends `swap d` and B.body starts `swap d`, DELETES both swaps.  Runtime: `swap d ; (fallthrough) ; swap d = id` across the seam — reuses the swap-involution kernels already proven (`PeepholeSwapKernel.swap_swap_sameRuntimeData`, `runState_swap_eq`, sessions 51–54).  Preserves block COUNT / labels / lowering order (like `normalizeProgram`, NOT like a block-merge), so it slots into the SAME congruence-family template (runtime/type/fuel/source/spine) that sessions 57–59 built for `normalizeProgram`.  NEW obligations vs normalize: (a) a fallthrough-successor + unique-predecessor cfg analysis (a `findBlock?`/reference-count query), (b) **cross-block edge-shape threading** — A.output and B.input must be re-typed through the removed `swap d` consistently (normalize was purely intra-block, so this edge coupling is genuinely new).  Blast radius: MEDIUM–LARGE, but same altitude + heavy proof reuse.  Est. 2–3 sessions.

* **Route A-coalesce — variant: merge A into B first, then the EXISTING live peephole fires.**  Coalescing A;B (unique edge) yields body `A.body ++ B.body` with `swap d :: swap d` LITERALLY adjacent → the already-live, already-proven `peepholeBody` swap arm cancels it with ZERO new cancellation proof.  Trades the bespoke canceller of Route A for a structural block-MERGE transform (changes block count/labels/`findBlock?`/`blocksInLoweringOrder?`/label-uniqueness `WellTyped`).  Bigger structural surface than Route A but maximal cancellation-proof reuse.  Ranked second.

**Decision:** pursue **Route A** (block-preserving cfg seam cancellation) as primary — it is the cheapest SOUND fix at the altitude where the verified tower already lives, reuses the swap-involution semantics and the normalize congruence-family template, and the unique-predecessor property (measured 61/61) makes it unconditionally sound with a cheap, decidable firing guard.  Route 1 (assembly) is the fallback if the cross-block edge-shape threading proves harder than the block-merge.  All routes are genuinely multi-session; **no small localized re-proof exists**, so no starter `.lean` commit this session (never-commit-red).

### KEY CORRECTION TO THE CAMPAIGN MODEL
The sessions-3–59 assumption that removable swap pairs live in **cfg block BODIES** is empirically false for the corpus: on ExternalCallBox they live ONLY at **cross-block fallthrough seams** and are made adjacent by **byte compaction**.  The live-but-inert peephole∘normalize splice (§59) is correct and harmless but will remain inert on this corpus regardless of contract — the target adjacency is structurally never intra-block here.  The first byte-shrinking delta requires a cross-block (Route A) or assembly-level (Route 1) pass.

### Files touched this session
Documentation only (`PEEPHOLE_PROGRESS.md`).  Three `lake env lean --run` probes (`probe1/2/3.lean`) were run from the scratch dir OUTSIDE the repo and are NOT committed.  No `.lean` change; no frozen file touched.  `compile_correct`/`compile_correct_creation` axioms unchanged = `[propext, Classical.choice, Quot.sound]`.

## Session-61 update (2026-07-20): ROUTE A **FINALIZED** (block-structure-preserving seam canceller) with decisive provenance evidence, and the transform's GREEN PREFIX is LANDED — definition + static firing analysis + label-structure preservation + the WellTyped body-typing kernels.  Three green, axiom-clean commits; NEW non-frozen leaf `EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (imported by nobody in the spine ⟹ cannot affect axioms).  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; `compile_correct`/`compile_correct_creation` = `[propext, Classical.choice, Quot.sound]`, verified in the full Verification build).  No splice yet ⟹ no byte measurement (codegen byte-identical to §59).

### ROUTE FINALIZATION — Route A over A-coalesce (decisive, code-grounded)
The §Session-60 mandate: pick Route A (bespoke, block-preserving seam canceller) vs A-coalesce (merge A;B on the unique fallthrough edge so the ALREADY-LIVE `peepholeBody` swap arm cancels the literal adjacency) by which congruence obligations each creates at the sessions-57–59 template's altitude.  **Decision: Route A.**  Evidence read directly from the tower:

* The whole sessions-3–59 source-threaded congruence + hInv/provenance machinery quantifies **per cfg block identity**.  Concretely, the normalize spine's preservation lemmas are `findBlock?_normalizeProgram` (label lookup commutes — labels preserved), `emittedLabels_normalizeProgram` (label multiset preserved), `labelsUnique_normalizeProgram`, and the source-threaded congruence is stated **relative to the ORIGINAL compiled `cfg`** (§59: the combined congruence discharges each found-block `StackRealizes` via `findBlock?_normalizeProgram` + `normalizeBlock_input`, and `GeneratedContext … cfg` is the ORIGINAL cfg).  Every one of these relies on the transformed program having the **same block set / labels / count / block-identity** as `cfg`.
* **A-coalesce DESTROYS block identity**: merging A;B deletes B's label, changes block count, changes `EmittedLabels`, and breaks the 1:1 `findBlock? label` correspondence between `cfg` and the transformed program.  `emittedLabels_*`, `labelsUnique_*`, `findBlock?_*` ALL fail for a merge, and `GeneratedContext … cfg` / `BlockGenShapeReg` (which enumerate `cfg`'s blocks per-label) no longer match the transformed program's blocks.  The §59 source-threading would need re-derivation from scratch at the new block granularity.
* **Route A PRESERVES block identity**: labels / count / terminators / entry all untouched (it only edits two seam blocks' `body`+`input`/`output`).  So `findBlock?`, `EmittedLabels`, `LabelsUnique`, `EmittedLabelsUnique`, entry-existence, and the `GeneratedContext`/`BlockGenShapeReg` block-identity structure are ALL still valid — landed green this session as the exact analogues of the normalize spine (see below).  Only the two seam blocks' **shapes** change (`labelShape? B` = B.input changes), and B is referenced by exactly ONE terminator (its unique-pred fallthrough, refCount = 1), which is edited consistently — this is the bounded, tractable new obligation.

Route A is strictly the cheaper SOUND fix at the altitude where the verified tower already lives.  A-coalesce is retained only as the deep fallback if the cross-block runtime bisimulation (below) proves harder than a block merge.

### WHAT LANDED (green prefix, 3 commits on `arena-opt`)
NEW leaf module `EvmCompiler/TypedCfg/PeepholeSeamCancel.lean`:
1. **Definition + static firing analysis** (commit `8a1312f7`): `refCount` (terminator-target multiplicity), `sourceFire?` / `targetFire?` (the decidable seam-firing queries), `seamBlock` (per-block edit: drop tail swap + `remapShape d` output if source, drop head swap + `remapShape d` input if target — both firing values computed against the ORIGINAL program), `seamCancelProgram` (block-preserving whole-program map).  Firing guard `2 ≤ A.body.length ∧ 2 ≤ B.body.length` makes head-idx (0) ≠ tail-idx in every participating block, so no single swap is double-claimed; `refCount B = 1` makes source-side and target-side firing agree on the same `(A,B)` pair with no priority resolution.  `seamBlock_label` / `seamBlock_term` / `seamCancelProgram_entry` / `_blocks` / `findBlock?_seamCancelProgram`.
2. **Label-structure preservation** (commit `9ddcdb01`): `emittedLabels_seamCancelProgram`, `labelsUnique_seamCancelProgram`, `emittedLabelsUnique_seamCancelProgram`, `entry_findBlock?_seamCancelProgram` — the label half of `WellTyped` preservation (mirrors the normalize spine).  `labelShape?` is deliberately NOT among these: target-block inputs change, so shape/type preservation is the frontier.
3. **WellTyped body-typing kernels** (commit `1756b7b8`): `type?_swap_eq_remapShape` (`Instr.type? (.swap d)` IS the `remapShape d` transposition on the running shape), and the two directional `bodyType?` kernels `bodyType?_dropTail_swap` (drop trailing swap ⟹ output un-swapped through `remapShape d`) / `bodyType?_dropHead_swap` (drop leading swap ⟹ input un-swapped, output unchanged).  These are the intra-block load-bearing lemmas the per-block `bodyType?` conjunct of `WellTyped` is assembled from.

### THE FRONTIER (session 62) + a DECISIVE design finding
Two obligations remain to reach the splice:

* **(WellTyped, shape half) — MEDIUM.**  Assemble `seamCancelProgram_wellTyped` from the step-3 kernels.  Two parts: (i) per-block `bodyType?` — combine `bodyType?_dropTail_swap` / `bodyType?_dropHead_swap` across the four fire cases (neither/source/target/both); the "both" case needs `dropLast`∘`tail` on a length-≥2 body (guard supplies distinctness) and the `findBlock? B.label = some block` step (from `LabelsUnique` + membership) to connect `targetFire?`'s internal `b.body.head?` to the block being edited.  (ii) **terminator `type?`** — the ONLY affected check is the seam predecessor A's `.fallthrough B`, whose `A.output.compatible (labelShape? B)` becomes `(remapShape d A.output).compatible (remapShape d B.input)`; preserved because `remapShape` (= `swapPos 0 (d+1)`) preserves `Shape.compatible` (reuse `slotsAgree_swapPos` from `PeepholeNoopSwapConj`/`Type`).  All OTHER terminators reference labels whose inputs are unchanged (only unique-pred target inputs move, each referenced solely by its consistently-edited source), turned into a lemma from `refCount = 1`.

* **(runtime congruence) — HARD; the campaign's real gate.**  DECISIVE FINDING: **the sessions-57–59 one-step congruence template does NOT transfer to seam blocks.**  `openStep_normalize_congr` proves a per-block `RuntimeOutcomeRel` from `SameRuntimeData` in AND out, because normalize preserved each block's runtime output *data*.  A seam **source** block A' (tail swap dropped) produces next-state `s'` while A produces `swap_d(s')` — **NOT `SameRuntimeData`**; the states only re-sync one step later, after B' (head swap dropped) runs from `s'` and B runs `swap d` from `swap_d(s')` to the same `runBody(rest) s'`.  So the whole-program `openRunN` congruence must carry a **2-state "pending-swap" bisimulation invariant** — "SameRuntimeData, OR the two runs differ by `swap_d` and are currently at the unique target B' whose head-swap-drop will re-sync" — instead of the plain `SameRuntimeData` congruence normalize used.  This is genuinely new crown-path work (the swap-involution kernels `PeepholeSwapKernel.swap_swap_sameRuntimeData` / `runState_swap_eq` supply the re-sync step, but the invariant threading is the new structure).  Estimate: 1–2 sessions.  Once it lands, the source-threaded / fuel / spine-splice steps follow the §57–59 template mechanically (block identity is preserved, so the OIC rewire is a name-change as in §59).

### Files touched (session 61)
NEW non-frozen leaf: `EvmCompiler/TypedCfg/PeepholeSeamCancel.lean`.  Doc: `PEEPHOLE_PROGRESS.md`.  No frozen file touched.  No splice ⟹ codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; identical-swap-pair counts 3/61/15/15 unchanged) ⟹ no determinism double-compile required.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-62 update (2026-07-20): GATE 1 (WellTyped) **CLOSED** — `seamCancelProgram_wellTyped` lands green + axiom-clean; the runtime pending-swap bisimulation (gate 2) is the sole remaining frontier, now materially de-risked.  One green commit on `arena-opt`.  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; `compile_correct`/`compile_correct_creation` = `[propext, Classical.choice, Quot.sound]`, verified in the full Verification build).  Leaf still imported by nobody in the spine ⟹ no splice ⟹ codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; pair counts 3/61/15/15) ⟹ no determinism double-compile.

### WHAT LANDED — the §Session-61 (WellTyped, shape half) gate, fully assembled (commit `319cfdc1`)
`seamCancelProgram_wellTyped` (`PeepholeSeamCancel.lean:714`) is proved from `program.WellTyped`.  The four sub-parts the §61 frontier flagged are all discharged; the **whole type side of the seam canceller is now closed**.  Load-bearing new lemmas (all in `PeepholeSeamCancel.lean`):

* **`compatible` under the seam transposition** — `compatible_remapShape_eq` (`:277`): `Shape.compatible` is invariant when BOTH shapes are remapped by `remapShape d = swapPos 0 (d+1)`, given `d+1` in range on both slot lists.  Needed an **unequal-length** variant of `slotsAgree_swapPos_eq` — `slotsAgree_swapPos_true_of_bounds` (`:238`) / `slotsAgree_swapPos_eq_of_bounds` (`:255`) — reusing `slotsAgree_iff_pointwise` + `swapPos_getElem?` (the existing `PeepholeNoopSwapConj.slotsAgree_swapPos_eq` required `a.length = b.length`, which the compatible check does NOT give).
* **`refCount = 1` uniqueness** — `count_le_flatMap_of_mem` (`:292`), `count_flatMap_two_mem` (`:305`), `two_le_refCount` (`:326`): turn `refCount B.label = 1` into "any two distinct blocks both referencing L give `2 ≤ refCount L`", i.e. the seam target has a genuinely unique referencer.
* **Firing-query specs + the two-sided connection** — `sourceFire?_spec` (`:345`) / `targetFire?_spec` (`:374`) unpack the nested-match queries (via `split at h`); `targetFire?_target_of_sourceFire` (`:464`) shows the source's fallthrough target itself fires (so its input moves consistently) and `head_swap_of_targetFire` (`:498`) recovers the dropped head swap; `targetFire?_none_of_sourceFire_none` (`:517`) discharges the non-source case via the `refCount` uniqueness.
* **Terminator invariance** — `typeWith?_congr` (`:554`) + `targetsHaveShapeWith?_congr` (`:540`): `Terminator.typeWith?` agrees under two label maps that agree on the term's `targets`; `term_type?_seamCancelProgram_eq` (`:576`) applies it to a non-source block (whose targets' inputs are all unchanged); `type?_fallthrough_some` (`:619`) reduces the seam-edge `.fallthrough` once its (remapped) target shape is known.
* **Bodies + assembly** — `output_bound_of_sourceFire` (`:427`) / `input_bound_of_head_swap` (`:446`) supply the `d+1 < …length` bounds `compatible_remapShape_eq` needs, from the dropped swaps' `Instr.type?` (via `Instr.length_of_type?_swap`); `seamBlock_input` (`:392`) / `seamBlock_output` (`:401`) / `labelShape?_seamCancelProgram` (`:410`) describe the moved fields; `head_tail_decomp`/`dropLast_head_tail` (`:595`/`:602`) rebuild the head after `dropLast`; `seamBlock_bodyType?` (`:660`) does the four fire cases (neither/source/target/both) from the §61 `bodyType?_dropTail_swap`/`bodyType?_dropHead_swap` kernels; `seamBlock_term_type?` (`:626`) + `seamBlock_wellTyped` (`:704`) combine to `seamCancelProgram_wellTyped`.

### THE FRONTIER (session 63) — ONLY the runtime pending-swap bisimulation remains, and it is now sharper
Gate 1 done means **the entire type/label/structure side of Route A is closed** (WellTyped + `findBlock?`/`EmittedLabels`/`LabelsUnique`/entry preservation from §61).  The sole remaining gate is the §61 "(runtime congruence) — HARD" 2-state invariant.  Two concrete findings from this session sharpen the recipe:

1. **The TARGET-side re-sync is nearly free.**  For a fired target `B` (`B.body = swap d :: rest`, `B'.body = rest`, `B'.input = remapShape d B.input`), the existing `PeepholeOpen.openRunBody_swap_cons_ok` already states `openRunBody (swap d :: rest) B.input s_sync = openRunBody rest middle next` with `middle = remapShape d B.input = B'.input` and `next = runState (swap d) B.input s_sync`.  So "B from the SYNCED state = B' from the PENDING state" is a direct instance: the **pending state IS `next` = the post-swap state**, and `runState_swap_eq` + `swap_swap_sameRuntimeData` characterize it (`next` is `swap_d` of `s_sync`, `SameRuntimeData` off slots `0↔d+1`).
2. **The SOURCE-side is the one genuinely-missing runtime lemma.**  For a fired source `A` (`A.body = pre ++ [swap d]`, `A'.body = pre`), `A'` produces `mid` while `A` produces `swap_d(mid)` (the trailing swap transposes slots `0↔d+1` and bumps pc).  There is **no `openRunBody`/`Control.Block.runBody` append lemma** in the tree (only `openRunBody_nonprim_cons` / `openRunBody_swap_cons_ok` for the head).  The missing piece is `openRunBody_append` (or a direct `openRunBody_dropLast_tail_swap`) in the `Simulation.Interaction` monad (`runBody (l1 ++ l2) = runBody l1 >>= runBody l2`, by induction on `l1` with bind-assoc); from it the source-side "A = swap∘A'" runtime fact follows.

Recipe for session 63 (unchanged in shape from §61, now with the above two facts in hand):
* Define the runtime **pending-swap state relation** `PendingSwap d s_pend s_sync` (≈ `s_pend = runState (.swap d) B.input s_sync` / stacks differ by the `0↔d+1` transposition, `SameRuntimeData` otherwise) and the **2-state block invariant** `SeamRel : Label → EVMState → EVMState → Prop` = `SameRuntimeData ∨ (at the unique fired target B ∧ PendingSwap)`.
* One-step diagram over every `openStep` case: normal blocks fall back to the §57–59 `SameRuntimeData` congruence (identical bodies); a fired source A **enters** the pending state (source-side fact from `openRunBody_append`); the fired target B **exits** it (target-side `openRunBody_swap_cons_ok`); the `refCount = 1` guard (already proved as `two_le_refCount` / `targetFire?_none_of_sourceFire_none`) rules out any other entry into B in the pending state.
* Lift to `openRunN`/`openRunNPrefix`, thread the source variants via the pass-agnostic `realizedWitnessFC` machinery (reuse as §58–59), fuel bound, then the OIC/StackArtifact rewire is a name-change (block identity preserved — same as §59) and MEASURE.

### Files touched (session 62)
`EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (+ this doc).  No frozen file touched.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-63 update (2026-07-20): GATE-2 RUNTIME **PRIMITIVES BANKED** — `openRunBody_append` + the target-side re-sync kernel + `PendingSwap` land green & axiom-clean; the whole-program 2-state `openRunN` lift is re-scoped as a NEW source-threaded congruence tower (NOT the pass-agnostic reuse §61/§62 assumed) and remains the frontier.  Two green commits on `arena-opt`.  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; `compile_correct`/`compile_correct_creation` = `[propext, Classical.choice, Quot.sound]`, verified in the full Verification build).  Leaf still imported by nobody in the spine ⟹ **NO SPLICE, so codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; pair counts 3/61/15/15) and NO byte delta yet** — the campaign's first live delta is still gated on closing the whole-program lift + splice below.

### WHAT LANDED (green, axiom-clean)
* **`openRunBody_append`** (`PeepholeOpen.lean:141`, commit `92af5d1f`) — the interaction-monad body-concatenation run law `openRunBody (l1 ++ l2) shape state = bind (openRunBody l1 shape state) (fun r => openRunBody l2 r.2 r.1)`, by induction on `l1` with `Simulation.Interaction.bind_assoc` on the head (new helper `openRunBody_cons_eq` gives the one-step cons unfolding).  This is the §62-identified sole-missing SOURCE-side primitive (`A.body = A.body.dropLast ++ [swap d]`).
* **`openRunBody_swap_cons_resync`** + **`PendingSwap`** + **`sameRuntimeData_next_of_pendingSwap`** (`PeepholeSeamCancel.lean:756-806`, commit `050caaaf`) — the TARGET-side re-sync kernel and the inter-block state relation.  `PendingSwap d s_c s_o := ∃ next, EvmYul.swap (d+1) s_o = .ok next ∧ SameRuntimeData next s_c`.  The kernel: `B` (`swap d :: rest`) run from the pending `s_o` is `Rel (Instr.RuntimeAtRel output)`-related to `B'` (`rest`) run from the synced `s_c`, directly from `openRunBody_swap_cons_ok` (`B`'s head swap lands `SameRuntimeData` to `s_c`) + the existing `InteractionCongruence.Block.openRunBody_runtimeRel`.  The bridge unfolds `PendingSwap` to the kernel's `SameRuntimeData next s_c` hypothesis via `runState_swap_eq`.

### THE FRONTIER (session 64) — a NEW 2-state source-threaded `openRunN` congruence, not a reuse
The §61/§62 recipe assumed the whole-program lift reuses `Structured.PeepholeSourceCongr.openRunN_peephole_congr_of_source` verbatim (relation stays `SameRuntimeData` at every block; `realizedWitnessFC` only discharges the depth guard).  Reading the tower shows that is **not** available for seam-cancel, and this is the true remaining cost:

1. **The inter-block relation is NON-UNIFORM.**  `openStep_peephole_congr` (`PeepholeProgram.lean:98`) produces `Rel Block.RuntimeOutcomeRel` outcomes — same jump label, `SameRuntimeData` states — at EVERY block, and `openRunN_peephole_congr_of_source` just re-feeds `SameRuntimeData` into the fuel recursion.  For seam-cancel, at a fired **source** `A` (term `.fallthrough B`, which `runTerm` maps to outcome `.jump B.label state'` — see `InteractionCongruence.runTerm_runtimeRel`) the two `openStep` outcomes are `.jump B.label s_o` (orig) and `.jump B.label s_c` (cancelled) with **`PendingSwap d s_c s_o`, NOT `RuntimeOutcomeRel`**.  So the carried invariant must become `SameRuntimeData ∨ (label = the unique fired target B ∧ PendingSwap d)`, and a new outcome relation `SeamOutcomeRel := RuntimeOutcomeRel ∨ (jump-to-fired-target with PendingSwap)` is needed.
2. **A new one-step congruence `openStep_seamCancel_congr`** casing on `sourceFire?`/`targetFire?` of the current block: (a) NORMAL block from `SameRuntimeData` → `SameRuntimeData` successors (the §57–59 `openStep_*_congr` argument, block bodies identical off the seam); (b) fired SOURCE `A` from `SameRuntimeData` → `.jump B` outcomes in `PendingSwap` (the source primitive: `A.body = pre ++ [swap d]`, so `openRunBody_append` splits off the trailing swap that orig keeps and `A'` drops — this introduces the pending desync); (c) fired TARGET `B` entered in `PendingSwap` → `SameRuntimeData` successors (the banked `openRunBody_swap_cons_resync` + `sameRuntimeData_next_of_pendingSwap` re-sync; `B`'s terminator is unchanged so the successor label matches and re-synced state is `SameRuntimeData`).  The `refCount B = 1` uniqueness (already proved: `two_le_refCount`, `targetFire?_none_of_sourceFire_none`) guarantees a `PendingSwap` state is only ever presented at label `B` and never at any other block — so case (a) never receives a pending state.
3. **The fuel induction** (`openRunN`/`openRunNPrefix`, `openRunNWithStop_succ` at `InteractionSemantics.lean:839`) carrying the disjunctive invariant, plus the `realizedWitnessFC` threading (this part IS pass-agnostic — reuse `allDone_realizedWitnessFC_jump` / `stackRealizes_of_realizedWitnessFC_total` for the depth guard exactly as §58–59).  Then fuel bound (`fuelBudget` is preserved since block bodies only shrink) + the OIC/StackArtifact splice.  Two remaining source-side sub-facts to formalize for step (b): the trailing-swap outcome IS `PendingSwap` w.r.t. `A'`'s outcome (needs `openRunBody_append` + that `EvmYul.swap` respects `SameRuntimeData` — a small swap-under-SRD congruence lemma), and that the whole-block `openRun` (body ++ terminator, `Control.Block.run`) threads the pending state through the unchanged `.fallthrough` terminator.

Bottom line: gate-2's two mathematical kernels (source append-split, target swap re-sync) are now GREEN Lean, not prose.  What is left is the disjunctive-invariant `openStep`/`openRunN` congruence + splice — a bespoke tower on the order of `PeepholeProgram.lean` + the seam-specific slice of `PeepholeSourceCongr.lean`, i.e. genuinely a session's build, gated behind the non-uniform relation above.  Per the never-commit-red discipline, no splice was attempted this session (a half-wired splice would red the spine), so **there is still no live byte delta** — landing it is session 64's headline.

### Files touched (session 63)
`EvmCompiler/TypedCfg/PeepholeOpen.lean` (`openRunBody_cons_eq`, `openRunBody_append`), `EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (runtime kernels), + this doc.  No frozen file touched.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-64 update (2026-07-20): GATE-2 **SOURCE-side pending-birth kernel BANKED** — the dual of §63's target re-sync now green, closing §Session-63 frontier step (b)'s "two remaining source-side sub-facts".  The disjunctive-invariant one-step / fuel congruence + splice remain the frontier (NOT attempted → never-commit-red), so **no live byte delta yet**.  One green commit on `arena-opt` (`2b3e5cf0`).  `scripts/opt_harness.sh check` = **OK** (43 public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct`/`compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]`.  Leaf still imported by nobody in the spine ⟹ codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; pair counts 3/61/15/15), NO determinism double-compile.

### WHAT LANDED (green, axiom-clean; commit `2b3e5cf0`, all in `PeepholeSeamCancel.lean`)
* **`openRunAt_realizes_shape`** (`:808`) + **`openRunBody_stackRealizes`** (`:838`) — lift the per-instruction `openRunAt_stackRealizes` (`PeepholeOpenStackRealizes.lean`) to a SHAPE-TAGGED `AllDone` `StackRealizes` invariant over the WHOLE open body run (`AllDone.bind` induction on the body; each `ok` leaf reports `pair.2 = output ∧ StackRealizes output pair.1`).  This is the depth supply the trailing swap of the source kernel needs, and it is reusable infra (the peephole tower re-derived per-instruction realizes ad hoc; this is the first body-level open realizes `AllDone`).
* **`openRunBody_dropLast_swap_pending`** (`:887`) — **the SOURCE-side birth kernel**, dual to §63's `openRunBody_swap_cons_resync` (`:765`).  Running the original source body `pre ++ [swap d]` from `s_o` is `Rel (ExceptRel eq (fun lp rp => PendingSwap d rp.1 lp.1 ∧ lp.2 = output ∧ rp.2 = mid))`-related to running the cancelled body `pre` from a `SameRuntimeData` `s_c`.  Proof: `openRunBody_append` (§63) splits off the trailing swap; `openRunBody_runtimeRel` handles `pre` up to `SameRuntimeData`, STRENGTHENED (`Rel.strengthen_right`) with `openRunBody_stackRealizes` so the right-tree depth rides into the bind continuation; `swap_swap_sameRuntimeData` (the depth-guarded involution) closes the `PendingSwap` witness — the SECOND swap of the involution pair is exactly the `PendingSwap.next` that lands `SameRuntimeData` back to the cancelled state.

Net: §Session-63's frontier item "**step (b)** — the trailing-swap outcome IS `PendingSwap` w.r.t. `A'`'s outcome (needs `openRunBody_append` + swap-under-SRD)" is now GREEN Lean, at the body-run granularity.  Both mathematical kernels of the 2-state bisimulation (source append-split→pending, target swap→resync) plus the depth infra are banked.

### THE FRONTIER (session 65) — the disjunctive one-step diagram + fuel lift + splice (UNCHANGED shape from §63, now with BOTH body kernels green)
What remains is exactly the §Session-63 items 1–3, and reading the tower this session sharpens the recipe with the concrete API now in hand:

1. **The disjunctive outcome relation** `SeamOutcomeRel P` (Except-carrier): `RuntimeOutcomeRel a b ∨ (∃ B d s_o s_c, a = .ok (.jump B s_o) ∧ b = .ok (.jump B s_c) ∧ targetFire? P (block@B) = some d ∧ PendingSwap d s_c s_o)`.  And the carried STATE invariant `SeamStepRel P label s_o s_c := (SameRuntimeData s_o s_c ∧ targetFire? P (block@label) = none) ∨ (∃ d, targetFire? P (block@label) = some d ∧ PendingSwap d s_c s_o)` — the disjunct is discriminated by `targetFire?` of the CURRENT block, which is why the invariant re-establishment at successors is the crux.

2. **`openStep_seamCancel_congr`** (block-level, then program-level): three arms on `sourceFire?`/`targetFire?` of `block@label`.  The two body kernels now supply the meat:
   * a fired SOURCE `A` (`.fallthrough B` term) run from `SameRuntimeData` → `.jump B` outcomes in `PendingSwap`: lift `openRunBody_dropLast_swap_pending` through `Control.Block.run` — the terminator is unchanged `.fallthrough B`, and `runTerm (.fallthrough B) = .jump B state'` (`Semantics.lean:114`) is state-forwarding, so the body-result `PendingSwap` becomes the jump-state `PendingSwap` verbatim (the `output`-shape check on `A` uses `A.output` on the left, `remapShape d A.output = mid` on the right — both bodies type through, so `runTermChecked` reaches the jump on both);
   * a fired TARGET `B` (`swap d :: rest`) entered in `PendingSwap` → `SameRuntimeData` successors: `openRunBody_swap_cons_resync` + `sameRuntimeData_next_of_pendingSwap` (both §63) re-sync, `B`'s terminator unchanged ⟹ successor label matches, state `SameRuntimeData`;
   * a NORMAL block (neither) from `SameRuntimeData` → `SameRuntimeData` successors: reuse `openRun_runtimeRel` / `Block.openRun_peephole_runtimeRel` verbatim (seamBlock = block).
   The invariant re-establishment at each produced `.jump next` is discharged by the §62 refCount uniqueness ALREADY GREEN: `targetFire?_none_of_sourceFire_none` (a non-source block never jumps into a target-fire block, so its successors are `targetFire? = none` ⟹ SameRuntimeData branch), `targetFire?_target_of_sourceFire` (a fired source's fallthrough target IS target-fire with the same `d` ⟹ pending branch), `head_swap_of_targetFire`.  These three are the dynamic-reachability plumbing; they mean the one-step diagram needs NO new refCount lemma.

3. **Fuel induction** carrying `SeamStepRel` → `Rel (SeamOutcomeRel P) (openRunN P …) (openRunN (seamCancelProgram P) …)`, then the PREFIX congruence recovers the clean `Rel RuntimeOutcomeRel`: `finishPrefixOutcome` maps every residual `.jump` (the only place a `PendingSwap` state surfaces) to `error .OutOfFuel` on BOTH sides (`.done (.error rfl)`), and halts are always produced from a re-synced (`SameRuntimeData`) state — so the pending disjunct never reaches a halt leaf.  Then `realizedWitnessFC` depth threading (pass-agnostic, reuse §58–59), fuel bound (`fuelBudget` shrinks: bodies only drop instructions), and the 4-site splice by `Rel.trans`-composing seamCancel AFTER `peepholeProgram ∘ normalizeProgram` relative to the real `cfg` (mirror `PeepholeNoopSwapCombined.lean`; the seam leg's LEFT tree is the ALREADY-transformed `peepholeProgram (normalizeProgram cfg)`, so its `WellTyped`/`ProgramCounterIndependent`/`StackRealizes` guards come from the combined-transform lemmas + `seamCancelProgram_wellTyped`).  Composition soundness: upstream is uniformly `RuntimeOutcomeRel` (SameRuntimeData at jumps); `SameRuntimeData` absorbs into `PendingSwap` on the left (`PendingSwap d s_c s_o` with `SameRuntimeData s_o' s_o` upstream stays pending since the witness `swap` acts on stacks and SRD preserves stacks), so `RuntimeOutcomeRel ∘ SeamOutcomeRel ⊆ SeamOutcomeRel`.

Scale estimate holds: on the order of `PeepholeProgram.lean` + the seam slice of `PeepholeSourceCongr.lean`.  What is DIFFERENT from §63's estimate: NO new mathematical kernel and NO new refCount lemma are needed — every body-level and static-uniqueness fact the one-step diagram consumes is now GREEN.  Session 65 is assembly (the disjunctive relation + its three-arm one-step + fuel/prefix + splice), not discovery.

### Files touched (session 64)
`EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (source birth kernel + open-body realizes), + this doc.  No frozen file touched.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-65 update (2026-07-20): GATE-2 **DISJUNCTIVE ONE-STEP CONGRUENCE BANKED** — the §Session-64 "assembly" crux (disjunctive relation + three-arm `openStep` congruence) is now GREEN Lean, plus the unified 4-fire-case body kernel and the seamCancel PCI preservation.  Three green, axiom-clean commits on `arena-opt` (`038bd198`, `252c8536`, `7ce3c0a2`).  The fuel/prefix **source-threaded** lift + splice remain the frontier (NOT attempted → never-commit-red), so **no live byte delta yet**.  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct`/`compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]`.  Leaf `PeepholeSeamCancel.lean` still imported by nobody in the spine ⟹ codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; pair counts 3/61/15/15), NO determinism double-compile.

### WHAT LANDED (green, axiom-clean; all in `PeepholeSeamCancel.lean`)
* **`seamBlock_body_rel`** (`:1018`, commit `038bd198`) — **the unified body kernel**.  Running the original block body from `s_o` is `Rel`-related to running the seam-edited body from `s_c`, with the ENTRY relation discriminated by `targetFire?` (SRD if `none`, `PendingSwap d` if `some d`) and the RESULT relation by `sourceFire?` (SRD if `none`, `PendingSwap e` if `some e`).  Composes the §63/§64 body kernels (`openRunBody_swap_cons_resync`, `openRunBody_dropLast_swap_pending`) plus `openRunBody_runtimeRel` across ALL FOUR fire cases — crucially including the **both-fire chain block** (target *and* source: a mid-chain `A→B→C`), which §64's 3-arm sketch under-specified.  The both-case is `resync ∘ birth`: peel the head swap (`openRunBody_swap_cons_ok`, resync to `s_c`), then birth the trailing pending swap on the resynced state.  Support: `seamBlock_body` (`:957`), `sourceFire_body_facts` (`:969`), `targetFire_body_facts` (`:994`), `forall_sub` (sublist-monotone PCI).
* **`SeamStepRel`** (`:1125`) / **`SeamOutcomeRel`** (`:1138`) — the carried entry invariant (SRD unless the block tails a fired seam, then `PendingSwap d`) and the disjunctive step outcome (a `.jump` to a common successor carrying `SeamStepRel` there, OR plain `RuntimeOutcomeRel` — the only source of halts, always from re-synced states).
* **`openRun_seamCancel_congr`** (`:1190`) / **`openStep_seamCancel_congr`** (`:1270`, commit `252c8536`) — **the three-arm one-step diagram**.  Body kernel supplies the internal relation; the terminator either forwards a source-fire block's `.fallthrough` into a `PendingSwap` jump (successor `targetFire? = some e` via `targetFire?_target_of_sourceFire`), or discharges the invariant at a non-firing successor (`targetFire? = none` via `targetFire?_none_of_sourceFire_none`, needing `runTerm_jump_mem_targets`).  No new refCount lemma — the §62 uniqueness stack sufficed exactly as §64 predicted.
* **`runTerm_jump_mem_targets`** (`:1148`) / **`findTarget?_mem`** (`:1109`) — every terminator-produced `.jump` lands at a static `term.targets` (all five terminator kinds incl. `returnDispatch`'s `findTarget?`).  The dynamic-reachability plumbing the successor-invariant discharge consumes.
* **`seamBlock_programCounterIndependent`** / **`seamCancelProgram_programCounterIndependent`** (`:1317`, commit `7ce3c0a2`) — PCI preservation (edited body is a `dropLast`/`tail` sublist).  A splice prerequisite (the seam program's runtime guards).

Net: both mathematical kernels (§63/§64) are now assembled into a GREEN whole-program **one-step** disjunctive bisimulation.  §Session-64's frontier item **2** (`openStep_seamCancel_congr`, three arms) is DONE, and the both-fire chain gap is closed.

### THE FRONTIER (session 66) — fuel/prefix SOURCE-THREADED lift + splice
Reading the tower this session pins the remaining shape precisely.  The self-contained fuel lift is **impossible** (the one-step needs `StackRealizes (seamBlock P b0).input s_c` at EVERY reached entry, which only a re-established source witness supplies — confirming §63's "NOT pass-agnostic" finding).  The path is the **trans-composed source-threaded** congruence, mirroring `PeepholeNoopSwapCombined.openStep_combined_congr_of_source` (which composed normalize∘peephole):

1. **`openStep_seamCombined_congr_of_source`** = `Rel.trans` of
   * `openStep_combined_congr_of_source context … hReal hRel` (`cfg ~ P := peephole(normalize cfg)`, carrying `realizedWitnessFC` at each jump successor — LEFT tree `cfg`), and
   * `openStep_seamCancel_congr (program := P) …` (`P ~ seamCancel P`, carrying `SeamStepRel P`).
   The seam leg's `hReal_c : StackRealizes (seamBlock P b0).input s_c` is DERIVABLE (not a new axiom): `stackRealizes_of_realizedWitnessFC_total` gives it at `state1`; `findBlock?_{peephole,normalize}Program` + `{peephole,normalize}Block_input` carry it to `P`'s block; `SameRuntimeData.stack_eq` + PendingSwap/SRD stack-**length** preservation (swap preserves length; `remapShape` preserves length) transport `state1 → state2 → s_c`.  Needs two tiny support lemmas: `(remapShape d s).length = s.length` and `PendingSwap d s_c s_o → s_o.stack.length = s_c.stack.length`.
   `P`'s guards: `hTypedP = peepholeProgram_wellTyped (normalizeProgram_wellTyped hTyped)`; `hUniqueP = hTypedP.1`; `hIndepP = combined_programCounterIndependent hIndependent`.
2. **Fuel + prefix lifts** carry a 3-tuple invariant at each entry — `realizedWitnessFC cfg … state1`, `SameRuntimeData state1 state2`, `SeamStepRel P … state2 s_c` — re-established at every jump (combined re-seeds the witness+SRD; seam re-seeds `SeamStepRel`).  The PREFIX recovers **clean** `Rel Block.RuntimeOutcomeRel` (residual jumps → `OutOfFuel` both sides; halts only via the RuntimeOutcomeRel disjunct, i.e. re-synced states) — exactly the OIC-consumable shape.  The N-level lift is `SeamOutcomeRel`-valued (not clean); the openRunN OIC sites (`OpenInteractionComposition.lean:1438/1588/1719`) transport only `AllDone AssemblySafeHalted`, so they need a `assemblySafeHalted_of_seamOutcomeRel` (trivial on non-halts; SRD on halts).
3. **`fuelBudget_seamCancelProgram_le`** — seamCancel drops instructions so the lowered fuel budget is `≤`; needs `lowerBodyFrom?`-length reasoning for dropped swaps (NOT yet built).
4. **SPLICE**: `StackArtifact.compile?` (3 sites) wrap `peephole(normalize cfg)` → `seamCancel (peephole(normalize cfg))`; `OpenInteractionComposition.lean` (~20 refs) swap the program + the `*_combined_congr_of_source` → `*_seamCombined_congr_of_source` lemma names and supply the seam guards.  `seamCancelProgram_wellTyped` (§62, banked) already covers the `compileCertified?` success precondition; the OIC downstream `compileCertified?_entry_*` lemmas are generic over the program given its `compileCertified?`/WellTyped/PCI, so no new seam "compile spine" beyond WellTyped/PCI is needed — but `labelShape?` DOES move under seamCancel (`labelShape?_seamCancelProgram`, banked), so any OIC step that assumed label-shape invariance must be re-checked.

Scale of remaining: `openStep_seamCombined_congr_of_source` + fuel/prefix ≈ the seam slice of `PeepholeSourceCongr.lean` (~120 lines) + 2 support lemmas + `fuelBudget_le` + the ~20-site OIC/StackArtifact rewire.  NO new mathematical kernel (all body-level facts + the one-step diagram are now GREEN); session 66 is source-threaded plumbing + the mechanical splice.

### Files touched (session 65)
`EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (unified body kernel + disjunctive one-step + PCI), + this doc.  No frozen file touched.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-66 update (2026-07-20): GATE-2 **SOURCE-THREADED CONGRUENCE TOWER BANKED** — the §Session-65 frontier items **1** (`openStep_seamCombined_congr_of_source`, the `Rel.trans` composition) and **2** (the fuel + prefix lifts) are now GREEN Lean, plus the two support length lemmas.  Two green, axiom-clean commits on `arena-opt` (`a9633192`, `cc6aad5a`); NEW non-frozen leaf `EvmCompiler/Structured/PeepholeSeamCombined.lean` (imported by nobody in the spine ⟹ cannot affect axioms).  Frontier item **3** (`fuelBudget_seamCancelProgram_le`) + item **4** (the ~20-site OIC / 3-site StackArtifact SPLICE) remain (NOT attempted → never-commit-red), so **NO live byte delta yet**.  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct`/`compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]` (verified in the full Verification build).  Both seam leaves still imported by nobody in the spine ⟹ codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; pair counts 3/61/15/15), NO determinism double-compile.

### WHAT LANDED (green, axiom-clean; all in `PeepholeSeamCombined.lean` unless noted)
* **`remapShape_length`** (`:39`) / **`swap_ok_stack_length`** (`:44`) / **`pendingSwap_stack_length`** (`:71`) — the two §Session-65 "tiny support lemmas": `remapShape` (the `0↔d+1` transposition) preserves shape length via `swapPos_length`; `EvmYul.swap n` (on success) preserves runtime stack length via `exists_swap_decomp` + `StackShuffle.swap_snoc`; hence a `PendingSwap d` relates equal-length stacks.  These transport the source witness's depth to the seam state.
* **`SeamCombinedStepRel`** (`:86`) / **`SeamCombinedOutcomeRel`** (`:98`) — the carried 3-tuple entry invariant (`∃ s2, realizedWitnessFC cfg … s1 ∧ SameRuntimeData s1 s2 ∧ SeamStepRel P … s2 s_c`) and the disjunctive one-step outcome (jump-to-common-successor carrying the 3-tuple, OR terminal `RuntimeOutcomeRel`).
* **`openStep_seamCombined_congr_of_source`** (`:118`) — **frontier item 1.**  `Rel.mono (Rel.trans hCombined hSeam)`: the combined leg `openStep_combined_congr_of_source` (cfg ~ `P := peephole(normalize cfg)`, carrying `realizedWitnessFC`) composed with the banked `openStep_seamCancel_congr` (P ~ `seamCancel P`, carrying `SeamStepRel`).  The seam leg's per-entry `hReal_c : StackRealizes (seamBlock P b0).input s_c` is DERIVED (not axiomatic): `stackRealizes_of_realizedWitnessFC_total` on cfg + `findBlock?_{peephole,normalize}Program` + `{peephole,normalize}Block_input` + the three support-length lemmas, exactly as §65 predicted.
* **`openRunN_seamCombined_congr_of_source`** (`:213`) / **`openRunNPrefix_seamCombined_congr_of_source`** (`:259`) — **frontier item 2.**  Fuel lift threads the 3-tuple via `Rel.bind_custom` (the outcome relation is NOT an `ExceptRel`, so `bind_custom` — not `Rel.bind` — is required); the PREFIX lift collapses `SeamCombinedOutcomeRel` to **clean `Rel Block.RuntimeOutcomeRel`** (residual jumps → `OutOfFuel` both sides; halts only via the re-synced terminal disjunct) — exactly the OIC prefix shape.
* **Non-jump guard on the terminal disjunct** (`PeepholeSeamCancel.lean` `SeamOutcomeRel` def + 5 construction sites re-greened; mirrored on `SeamCombinedOutcomeRel`).  The §65 `SeamOutcomeRel`'s Or.inr was `Block.RuntimeOutcomeRel a b`, which as a *relation* admits jumps — making the fuel recursion's Or.inr case carry an unprovable jump sub-goal (no witness at the successor).  Fix: strengthen Or.inr to `RuntimeOutcomeRel a b ∧ ∀ next s, a ≠ .ok (.jump next s)`.  The existing `openRun_seamCancel_congr` provers already produce only non-jumps there, so the guard is discharged by `by simp` at each site.  DECISIVE for closing the fuel induction.

Net: §Session-65's frontier items 1 + 2 are DONE — the whole-program **fuel-and-prefix** source-threaded seam-combined bisimulation is GREEN, recovering the clean OIC-consumable prefix shape.  NO new mathematical kernel was needed (as §65 predicted); this session was the trans-composition plumbing + the fuel/prefix induction + the non-jump-guard correction.

### THE FRONTIER (session 67) — fuel bound + splice
Two items remain, both un-attempted this session (never-commit-red):

1. **`fuelBudget_seamCancelProgram_le : fuelBudget (seamCancelProgram P) ≤ fuelBudget P`** (frontier item 3).  Reduces (via `fuelBudget = (blocks.map CompiledBlock.fuelBudget).sum`, `seamCancelProgram_blocks`) to a **per-block** `CompiledBlock.fuelBudget (seamBlock program b) ≤ CompiledBlock.fuelBudget b`.  Un-built sub-lemmas identified this session:
   * **`remapShape_involution`** — `remapShape d (remapShape d s) = s`, via `swapPos_involutive 0 (d+1)` (SIDE CONDITIONS `0 < s.slots.length`, `d+1 < s.slots.length`, supplied by the swap's typing `depth+2 ≤ input.length`).
   * **`lowerBodyFrom?_snoc_swap`** (source-fire, drop tail swap) + **tail-swap lowering** (target-fire, drop head swap): the seam body lowers to code no longer than the original, with the output shape aligned through the involution.  Mirror the `LowerLe` framework in `PeepholeFuel.lean`, but note `LowerLe` as written demands **equal** output shapes — the seam edit REMAPS the output, so a bespoke variant carrying the `remapShape` output is needed.
   * **Terminator-length preservation** is FREE in every firing case (KEY finding): a **source-firing** block has `term = .fallthrough B` by the firing condition, and `Terminator.lowerAt? shape (.fallthrough B) = some [.jump B]` is **shape-independent** (`Lower.lean:105`); a **target-only-firing** block keeps its output unchanged.  So `1 + bodyCode.length + termCode.length` shrinks purely through the body.
   Estimated ~200-400 lines across the 4 `seamBlock` firing cases with the involution/shape-equality bookkeeping.
2. **SPLICE** (frontier item 4).  `StackArtifact.compile?` (3 sites) wrap `peephole(normalize cfg)` → `seamCancel (peephole(normalize cfg))`; `OpenInteractionComposition.lean` (~20 refs) swap the program + `combined` → `seamCombined` lemma names.  **The two PREFIX sites (`OIC:929/964`) are near-drop-in** (the seam prefix lemma has the SAME clean `Rel Block.RuntimeOutcomeRel` conclusion), needing only the 3-tuple seed `SeamCombinedStepRel … cfg.entry (initial) (initial)` (from `realizedWitnessFC_entry_of_generated` + `SameRuntimeData.refl` + `SeamStepRel`-at-entry = SRD when `targetFire? = none`, true at the entry which no fallthrough targets) and the seam guards (`seamCancelProgram_wellTyped`/`_programCounterIndependent`, banked).  **The three openRunN sites (`OIC:1438/1588/1719`) are NOT drop-in**: the seam N-level bridge is `SeamCombinedOutcomeRel`-valued (not clean), so (a) the `AllDone AssemblySafeHalted` transport needs a new `assemblySafeHalted_of_seamCombinedOutcomeRel` (on a halt the jump disjunct is impossible ⟹ falls to `assemblySafeHalted_of_runtimeRel`), and (b) the `Rel.trans hBridge hCfgAssemblyPeepPad` step needs `SeamCombinedOutcomeRel ∘ RunSimulates ⊆ RunSimulates` on the halted path.  This is the genuinely new (non-mechanical) splice work the §65 "mechanical splice" estimate under-scoped.

### Files touched (session 66)
`EvmCompiler/Structured/PeepholeSeamCombined.lean` (NEW: support lemmas + 3-tuple relations + source-threaded one-step/fuel/prefix), `EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (non-jump guard on `SeamOutcomeRel` + 5 re-greened sites), + this doc.  No frozen file touched.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-67 update (2026-07-20): FUEL BOUND (item 3) + halted-path bridges (item 4's non-mechanical half) BANKED green; the SPLICE is BLOCKED on a newly-isolated compiler-structural invariant that §66 under-scoped ⟹ **NO byte delta yet** (never-commit-red).  Two green, axiom-clean commits on `arena-opt` (`6ac679f2`, `69478041`), both in `EvmCompiler/Structured/PeepholeSeamCombined.lean`.  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct`/`compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]` (verified in the full Verification build).  Both seam leaves still imported by nobody in the spine ⟹ codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; pair counts 3/61/15/15), NO determinism double-compile.

### WHAT LANDED (green, axiom-clean; all in `PeepholeSeamCombined.lean`)
* **`fuelBudget_seamCancelProgram_le`** + **`fuelBudget_seamCombined_le`** (commit `6ac679f2`) — **frontier item 3 CLOSED.**  Reduces via `seamCancelProgram_blocks` + `fuelBudget_seamBlocks_le` to the per-block **`compiledBlock_fuelBudget_seamBlock_le`** (4 firing cases).  In every firing case the edited body is a `dropLast`/`tail` sub-list whose lowering has ≤ the original bytes (the dropped `swap` fragments are appended back on the ORIGINAL side via `lowerBodyFrom?_append` + `lowerBodyFrom?_singleton_swap`), and the terminator code length is UNCHANGED — a source-firing block has `term = .fallthrough B` which lowers **shape-independently** to `[.jump B]` (`Lower.lean:105`), a target-only-firing block keeps its output.  New support lemmas: `lowerBodyFrom?_append`, `bodyType?_of_lowerBodyFrom?`, `lowerBodyFrom?_singleton_swap`.  `fuelBudget_seamCombined_le = le_trans fuelBudget_seamCancelProgram_le fuelBudget_combined_le` — the drop-in replacement for `fuelBudget_combined_le` at the 5 OIC fuel sites.  (§66's `remapShape_involution` guess was NOT needed; the involution is already inside the banked `sourceFire_body_facts`/`targetFire_body_facts`, and a bespoke `LowerLe`-variant was NOT needed — the append-back structure is cleaner.)
* **`assemblySafeHalted_of_seamCombinedOutcomeRel`** (bridge a) + **`runSimulates_of_seamCombinedOutcomeRel_halted`** (bridge b) + supports `assemblySafeHalted_not_jump`, `runtimeOutcomeRel_of_seamCombinedOutcomeRel_of_not_jump` (commit `69478041`) — **item 4's genuinely-new (non-mechanical) half CLOSED.**  At a halt the left outcome is `AssemblySafeHalted` ⟹ not a `.jump` ⟹ the jump disjunct of `SeamCombinedOutcomeRel` is impossible ⟹ it collapses to the plain `RuntimeOutcomeRel` disjunct, where the pass-agnostic `assemblySafeHalted_of_runtimeRel` / `OpenBlock.runtime_left` transports apply.  These are exactly the two lemmas §66 flagged the 3 `openRunN` OIC sites (`:1438/1588/1719`) need.  (New import: `EvmCompiler.TypedCfg.PeepholeTransfer`, non-frozen.)

### THE FRONTIER (session 68) — the SPLICE is gated on ONE compiler-structural invariant §66 under-scoped
The remaining item 4 work is the OIC/StackArtifact rewire.  Reading the tower this session, ALL 5 congruence-call sites (prefix `OIC:929/964` **and** openRunN `OIC:1438/1588/1719`) seed with the SAME entry seed `SeamCombinedStepRel context.calls cfg.entry cfgState cfgState` (equal states: `realizedWitnessFC_entry_of_generated` + `SameRuntimeData.refl` at all 5 sites).  Unfolding, this requires `SeamStepRel (peephole(normalize cfg)) cfg.entry cfgState cfgState`, i.e. — since equal states can only satisfy the SRD disjunct, never `PendingSwap` —

> **`targetFire? (peepholeProgram (normalizeProgram cfg)) entryBlock = none`**   (the entry block does NOT tail a fired seam).

§66's parenthetical "`SeamStepRel`-at-entry = SRD when `targetFire? = none`, **true at the entry which no fallthrough targets**" treated this as trivial.  It is NOT: `targetFire?` is preserved through the pass terminators (`{peephole,normalize,seam}Block_term`), so the fact reduces to the **generated-cfg invariant**

> **`∀ b ∈ cfg.blocks, b.term ≠ .fallthrough cfg.entry`**   (equivalently `refCount (peephole(normalize cfg)) entryLabel ≠ 1` / no terminator fallthroughs to the `.named "structured:typedcfg:entry"` entry label),

which **does not exist as a lemma** and is genuine new crown-path work: an induction over `compileBlock?` / `generateWithProcEntryShapes?` showing every generated terminator target is a `.generated`/`ProcLabel` label and never the `entryLabel`.  It is TRUE (the dispatcher entry is the root; sequential blocks fall through to `restLabel`, loops/switches use their own generated labels), but not banked, and NO reachability/predecessor invariant on the generated cfg exists to shortcut it (searched: `TypedCfgPreservation*`, `Certificate`, no `Reachable`/predecessor/`entry ∉ targets` fact).  This is why the splice — and hence the first byte delta — did NOT land this session: seeding any of the 5 sites with a false `targetFire? = some d` at the entry would demand `PendingSwap d cfgState cfgState` (false) ⟹ the arm goes red.  Per never-commit-red, the splice was NOT attempted.

**Session-68 recipe** (with the seam fuel bound + both halted bridges now in hand, the ONLY remaining prerequisite is the invariant above):
1. Prove `entryLabel_not_fallthrough_target` : `∀ b ∈ cfg.blocks, b.term ≠ .fallthrough cfg.entry` for a generated `cfg` (via `generated` / `GeneratedContext`) — the one genuine new proof.  Corollary `targetFire?_entry_none : targetFire? (peephole(normalize cfg)) entryBlock = none` (terminators preserved).
2. Entry seed `seamCombinedStepRel_entry_of_generated` : `SeamCombinedStepRel context.calls cfg.entry cfgState cfgState` = `⟨cfgState, realizedWitnessFC_entry_of_generated …, SameRuntimeData.refl, SeamStepRel-via-(1)⟩`.
3. Rewire `StackArtifact.compile?` (3 sites: def `:62`, `compile?_parts` stmt `:95` + proof `:151`) `peephole(normalize cfg)` → `seamCancelProgram (peephole(normalize cfg))` — this is the LIVE emitted-bytes edit.
4. Rewire OIC (~8 `hCompile` theorems + their `combined_programCounterIndependent`→`seamCancelProgram_programCounterIndependent∘combined`, `fuelBudget_combined_le`→`fuelBudget_seamCombined_le`, and the 5 congruence sites `openRunN{,Prefix}_combined_congr_of_source`→`…seamCombined…` with seed (2)).  Prefix sites (`:929/964`): drop-in (clean `Rel RuntimeOutcomeRel`).  openRunN sites (`:1438/1588/1719`): use bridge (a) for `hCfgSafeAtEntryPeep`, and for `hCfgAssembly` **strengthen with `hCfgSafeAtEntry` FIRST** then `Rel.mono` via bridge (b) — the `SeamCombinedOutcomeRel`-valued bridge only cleans to `RunSimulates` on the halted path.
5. MEASURE (the FIRST LIVE DELTA): recompile ASP/ECB/MiniToken/LoopBox @ pinned solc 0.8.26; bytes + SWAPn;SWAPn pair re-scan vs baselines; determinism double-compile of changed contracts.

### Files touched (session 67)
`EvmCompiler/Structured/PeepholeSeamCombined.lean` (fuel bound section: `lowerBodyFrom?_append`, `bodyType?_of_lowerBodyFrom?`, `lowerBodyFrom?_singleton_swap`, `compiledBlock_fuelBudget_seamBlock_le`, `fuelBudget_seamBlocks_le`, `fuelBudget_seamCancelProgram_le`, `fuelBudget_seamCombined_le`; halted-bridge section: `assemblySafeHalted_not_jump`, `runtimeOutcomeRel_of_seamCombinedOutcomeRel_of_not_jump`, `assemblySafeHalted_of_seamCombinedOutcomeRel`, `runSimulates_of_seamCombinedOutcomeRel_halted`; new import `PeepholeTransfer`), + this doc.  No frozen file touched.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-68 update (2026-07-20): **DECISIVE FINDING — the TypedCfg seam-cancel is ARCHITECTURALLY INERT on the real spine; the splice would be byte-IDENTICAL (zero delta), so it was NOT performed.**  Instead the inertness is now a **green, verified fact** (kernel banked), and the §67 entry invariant is subsumed by it.  One green, axiom-clean commit on `arena-opt` in `EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (non-frozen leaf, imported by nobody in the spine ⟹ cannot affect axioms).  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct`/`compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]` (verified in the full Verification build).  Codegen byte-identical to §59 (8557/8591 · 2791/2825 · 1991/2234 · 923/957; pair counts 3/61/15/15) — **NO splice, NO byte delta, NO determinism run** (nothing in the emitted-bytes path changed).  **seamCancel is NOT live in emitted bytes, and provably cannot be at this altitude.**

### THE FINDING (source-airtight; verified by exhaustive search + a green Lean kernel)
Attempting the §67 splice recipe, the entry seed reduces (as §67 said) to `targetFire? (peephole(normalize cfg)) entryBlock = none`.  Investigating the generator to prove it revealed something stronger and campaign-altering:

> **The generated TypedCfg — and hence `peepholeProgram (normalizeProgram cfg)`, both passes preserving `.term` exactly (`normalizeBlock_term`, `peepholeBlock_term`) — contains NO `Terminator.fallthrough` terminator AT ALL.**

Exhaustive grep of `EvmCompiler/` for any *construction* of `Terminator.fallthrough`: the ONLY hits are (a) the seam-cancel's own firing predicates in `PeepholeSeamCancel.lean`, and (b) semantics / preservation *proof* files that `cases term with | fallthrough … ` or model the runtime `Outcome.fallthrough`.  **No compiler pass ever emits a `.fallthrough` terminator.**  Reading `TypedCfgCompiler` (`compileBlockFuel?`/`StmtList`/`Stmt`/`Cases`/`Default` + `generateWithProcEntryShapes?`): every `mkBlock?`/`mkCodeBlock?` sets `term` to `.jump` / `.jumpi` / `.halt` / `.invalid` (`checkedJumpOrInvalid` / `jumpOrInvalid` → `.jump`/`.invalid`, never `.fallthrough`), and `dispatchBlock` → `.invalid`/`.returnDispatch`, `endBlock` → `.halt .stop`.  Sequential continuation is emitted as **`Terminator.jump (restLabel supply)`** (a jump to a `refCount`-1 generated label), NOT `Terminator.fallthrough`.

**Root of the multi-session conflation:** the compiler threads a `TypedCfgCompiler.Result.fallthrough? : Option Shape` field — metadata meaning "this fragment has a regular exit path with this shape" — which was conflated with the **`Terminator.fallthrough` constructor** that `sourceFire?`/`targetFire?` pattern-match.  §67's "sequential blocks fall through to `restLabel`" described the `Result.fallthrough?` metadatum, but the actual terminator is `.jump restLabel`.

**Consequence:** `sourceFire?` (matches the block's own `.term = .fallthrough _`) and `targetFire?` (searches the block list for a predecessor with `.term = .fallthrough b.label`) **NEVER fire** on any generated program.  Hence `seamBlock program b = b` for every block, and `seamCancelProgram (peephole(normalize cfg)) = peephole(normalize cfg)` verbatim.  Splicing it in compiles/verifies but produces **byte-identical** output.  This is fully consistent with §60's own empirical birth-site result: the `SWAPn;SWAPn` pairs are manufactured at `Assembly.Compact.prepare` (`elideFallthroughJumps` removing `jump G ; label G`), **strictly downstream** of the TypedCfg altitude — the lowered image `certified.target` has `… , swap d , jump G , label G , swap d , …`, i.e. a **`.jump`**, and the TypedCfg IR never carries the post-elision `.fallthrough` the transform models.  The seam-cancel (Route A) was built to match a terminator shape the TypedCfg IR does not produce.

### WHAT LANDED (green, axiom-clean; `EvmCompiler/TypedCfg/PeepholeSeamCancel.lean`)
The inertness is now a verified kernel, not just prose:
* **`NoFallthrough`** (`:1337`) — a program carries no `.fallthrough` terminator.
* **`sourceFire?_eq_none_of_noFallthrough`** (`:1341`) / **`targetFire?_eq_none_of_noFallthrough`** (`:1354`) — neither seam fires on a fallthrough-free program (source: the `.term` match falls through to `none`; target: `List.find? (·.term == .fallthrough b.label)` = `none`).
* **`seamBlock_eq_of_noFallthrough`** (`:1371`) — every per-block edit is the identity.
* **`seamCancelProgram_eq_of_noFallthrough`** (`:1382`) — **`seamCancelProgram program = program` verbatim on any fallthrough-free program** (blocks/labels/count/entry/terminators/bodies all unchanged), via `List.map_congr_left` + `List.map_id`.

Combined with the source-airtight fact that generated programs are `NoFallthrough`, this is the verified statement of inertness.  (The remaining `generated_cfg ⟹ NoFallthrough` half is a ~300-line mirror of the `genShape_of_compile*` mutual — deferred: it would only formalize what the exhaustive grep already establishes, for zero optimization payoff.)  The §67 target invariant `∀ b ∈ cfg.blocks, b.term ≠ .fallthrough cfg.entry` is a trivial corollary of `NoFallthrough`.

### WHY THE SPLICE WAS NOT PERFORMED
Splicing an identity transform into the (compile_correct-cone) spine buys **zero** bytes while adding a large, delicate OIC rewire (4 theorems × ~150 lines) and artifact-definition churn — a strict negative.  Per never-commit-red and the "land the green prefix / document the frontier" clause, the splice was skipped in favor of banking the inertness kernel and this finding.

### THE REAL FRONTIER (route correction for a future session)
To get a LIVE byte delta on the `SWAPn;SWAPn` seams, the canceller must be **retargeted to where the seams actually exist**:
1. **Assembly-compaction altitude (matches §60's birth site).**  Run the swap-pair cancellation at/after `Assembly.Compact.prepare`, on the *lowered `Assembly` program*, where the redundant `swap d ; swap d` literally appears after `jump G ; label G` elision.  New correctness obligations live in the Assembly layer, not TypedCfg.
2. **TypedCfg with the correct predicate.**  Keep Route A's block-preserving structure but change `sourceFire?`/`targetFire?` to match **`.jump G` with `refCount program G = 1`** (the actual TypedCfg seam) instead of `.fallthrough G`.  The whole banked congruence tower (§61–67: WellTyped preservation, pending-swap bisimulation, fuel bound, halted bridges) is REUSABLE — it only needs the firing predicate swapped and the seam runtime-model re-derived for the `.jump`-with-unique-pred edge (the runtime semantics of `.jump G` then falling into G is the same one-step-later re-sync the pending-swap invariant already models).
3. **(Alternative) upstream `.jump`→`.fallthrough` pass.**  Insert a TypedCfg pass converting unique-target `.jump` into `.fallthrough` *before* `seamCancelProgram`, mirroring the assembly `elideFallthroughJumps`; then the existing predicate fires.  Heaviest (adds a pass + its correctness) and least motivated.

### Files touched (session 68)
`EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (new inertness section: `NoFallthrough`, `sourceFire?_eq_none_of_noFallthrough`, `targetFire?_eq_none_of_noFallthrough`, `seamBlock_eq_of_noFallthrough`, `seamCancelProgram_eq_of_noFallthrough`), + this doc.  No frozen file touched.  No splice ⟹ `StackArtifact.compile?` / OIC UNCHANGED ⟹ emitted bytes UNCHANGED.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-69 update (2026-07-20): **THE SEAM CANCELLER IS LIVE IN EMITTED BYTES** — retargeted to `.jump` seams, tower ported, spliced through the frozen `compile_correct` cone, axiom-clean.  **BUT the measured byte delta is ZERO on the corpus** (the retargeted predicate fires on none of the real seams).  Four green, axiom-clean commits on `arena-opt` (`a9a1bd68`, `293ed81c`, `7fedbd8e`, + this doc).  `scripts/opt_harness.sh check` = **OK** (1364 jobs, **43** public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`).  `compile_correct`/`compile_correct_creation` **UNCHANGED** = `[propext, Classical.choice, Quot.sound]` (verified in the full Verification build, 1366 jobs green).  No frozen file touched.

### WHAT LANDED (green, axiom-clean)
1. **Retargeted firing predicates** (`PeepholeSeamCancel.lean`, commit `a9a1bd68`).  Per §68's route-correction option (2): `sourceFire?`/`targetFire?` now match **`.jump G`** (with `refCount G = 1`) instead of `.fallthrough G`, plus an explicit **`b.label ≠ program.entry`** guard.  Because `.fallthrough` and `.jump` are byte-identical in `Typing.typeWith?` (`:387-392`), `targets`, `lowerAt?` (`Lower.lean:105-106` → `[.jump _]`), and runtime `runTerm` (`Semantics.lean:114-115` → `Outcome.jump _ state`), the ENTIRE §61-67 tower ported mechanically: structural preservation, WellTyped (`type?_jump_some`), the pending-swap runtime bisimulation, the fuel bound, the halted bridges — all rebuilt green with only the constructor name swapped.  The §68 `NoFallthrough` inertness kernel (now moot) was replaced by **`targetFire?_entry_eq_none`** + **`seamStepRel_entry`** (the entry seed hinge; the `≠ entry` guard makes it a one-liner, no generated-cfg reachability invariant needed).
2. **Entry seed** (`PeepholeSeamCombined.lean`, commit `293ed81c`, §67 recipe item 2): **`seamCombinedStepRel_entry_of_generated`** — `realizedWitnessFC` at entry + `SameRuntimeData.refl` + the `SeamStepRel` entry branch ⟹ `SeamCombinedStepRel calls cfg.entry s s`.  The last tower prerequisite before the splice.
3. **THE SPLICE** (commit `7fedbd8e`, the LIVE emitted-bytes edit):
   * `StackArtifact.compile?` (+ `compile?_parts`): compile `seamCancelProgram (peephole(normalize cfg))`, not the bare peephole program.  `compile?_parts` reshaped verbatim (the `simp/cases` script absorbed the new certified shape).
   * `OpenInteractionComposition.lean`: rewired the **4 core OIC theorems** (prefix `:853` + openRunN done/branch `:1376/:1534` + finished `:1665`) and the **4 forwarding wrappers** to relate `cfg` to the seam-cancelled program: `hIndepPeep` = `seamCancelProgram_programCounterIndependent ∘ combined`; congruence = `openRunN{,Prefix}_seamCombined_congr_of_source` + the entry seed (dropping the old two-arg seed); fuel = `fuelBudget_seamCombined_le`; halted path = `assemblySafeHalted/Finished_of_seamCombinedOutcomeRel` (bridge a) and `runSimulates_of_seamCombinedOutcomeRel_halted/finished` (bridge b, via `strengthen_left … hCfgSafeAtEntry` first).  The prefix collapses to clean `RuntimeOutcomeRel` (§66) ⟹ drop-in.  Added the two **`AssemblySafeFinished`** variants of the halted bridges to `PeepholeSeamCombined.lean` for the finished site.  The entry alignment `(seamCancelProgram P).entry = cfg.entry` is definitional (all passes keep the `entry` field).
   * Only 3 `compile?_parts` consumption sites broke on the concrete certified shape; the interior theorems are generic in `hCompile` (its shape propagated via one signature `replace_all`).

### THE MEASUREMENT — FIRST LIVE MEASUREMENT OF THE SPLICE (solc 0.8.26, via-IR + Yul optimizer)
| contract | runtime | creation | rt SWAPn;SWAPn pairs | vs §59 baseline |
|---|---|---|---|---|
| AdversarialStackPressure (ASP) | 8557 | 8591 | 3 | 8557/8591 · 3 — **IDENTICAL** |
| ExternalCallBox (ECB) | 2791 | 2825 | 61 | 2791/2825 · 61 — **IDENTICAL** |
| MiniToken | 1991 | 2234 | 15 | 1991/2234 · 15 — **IDENTICAL** |
| LoopBox | 923 | 957 | 15 | 923/957 · 15 — **IDENTICAL** |

**BYTE DELTA = 0 on all four; pair counts unchanged.**  Determinism double-compile (ECB, MiniToken) = **DETERMINISTIC** (byte-identical across runs; the output reproduces the §59 baseline exactly).  The splice compiles/verifies but the retargeted `.jump`-seam predicate fires on **zero** blocks in all four programs (byte-identical output across even the simple LoopBox/MiniToken ⟹ `seamBlock = id` everywhere).

### THE FINDING — why zero: the real seams are TERMINATOR-lowered, not block-body
The `.jump`-with-`refCount=1` predicate is genuinely live, yet fires on nothing.  Structural root cause (consistent with §60's `elideFallthroughJumps` birth site): the `SWAPn;SWAPn` pairs are born where the pre-jump `swap` is emitted by **terminator lowering**, NOT a block `.body` tail.  `returnDispatchCase` (`Lower.lean:88-90`) lowers a case to `label; removeBuriedUnder depth (…swaps…); jump target`; the `jump target ; label target` that compaction elides abuts the `removeBuriedUnder` shuffle's last `swap` (in the TERMINATOR's lowered code) with `target`'s body-head `swap`.  A TypedCfg **block-body** predicate (`sourceFire?` keys on `a.body.getLast?`) cannot see a terminator-lowered swap, so NO block-body variant — `.fallthrough` (§68) OR `.jump` (§69) — matches these seams.  ECB (ExternalCallBox) is return-dispatch-heavy, hence all 61 pairs; even LoopBox/MiniToken show zero body-body jump seams.

### THE REAL FRONTIER (route correction, confirmed twice over)
The block-body altitude is the wrong altitude for these seams — proven now for BOTH terminator constructors.  The genuine byte win requires **§68 route-correction option (1): the assembly-compaction altitude.**  Run the `swap d ; swap d` cancellation at/after `Assembly.Compact.prepare` on the *lowered `Assembly` program*, where the redundant pair literally appears after `elideFallthroughJumps` removes `jump G ; label G`, spanning terminator-shuffle and body swaps indiscriminately.  New correctness obligations live in the Assembly layer, not TypedCfg.  The §61-69 tower (WellTyped, pending-swap bisimulation, fuel bound, halted bridges, entry seed) does not transfer to that altitude, but the SPLICE PLUMBING banked this session (the OIC/StackArtifact rewire threading a program transform through the frozen `compile_correct` cone, axiom-clean) is the reusable template for wiring any Assembly-level pass into the emitted-bytes path.

### NOTE ON THE INERT SPLICE
The splice is byte-inert on the corpus, so by §68's "don't add inert surface to the compile_correct cone" principle it is arguably a strict negative.  It was RETAINED (not reverted) because: (a) it is green + axiom-clean and closes the whole frozen cone; (b) it is NOT provably inert (unlike §68's `NoFallthrough`) — it is a genuine live transform that fires on zero *current-corpus* seams but would fire on any block-body `.jump` seam; (c) the expensive, reusable part is the OIC/StackArtifact plumbing, now proven end-to-end.  If a clean cone is preferred, revert `7fedbd8e` (keeps the tower + entry seed `a9a1bd68`, `293ed81c`) — the splice plumbing is fully documented here for re-application.

### Files touched (session 69)
`EvmCompiler/TypedCfg/PeepholeSeamCancel.lean` (predicate retarget + entry-seed lemmas), `EvmCompiler/Structured/PeepholeSeamCombined.lean` (entry seed + finished-variant bridges), `EvmCompiler/Compiler/StackArtifact.lean` (splice + import), `EvmCompiler/Compiler/OpenInteractionComposition.lean` (4 core + 4 wrapper rewires + import), + this doc.  No frozen file touched.  `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-70 update (2026-07-20): **EMPIRICAL RECONCILIATION — §69's terminator-lowering root cause is REFUTED; §60's body-to-body seam is CONFIRMED. The real defect: `sourceFire?`'s `getLast?`/`dropLast` are fooled by a trailing zero-lowering, runtime-IDENTITY `bindLocals` masking the tail swap.** Route decision: **Route α** — correct the seam canceller's tail-swap identification + edit at the (correct) TypedCfg block-body altitude, reusing the §61-69 tower. No live byte delta yet (the runtime-tower re-derivation for the corrected edit is the frontier; never-commit-red). Docs + green static-prefix commits only. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`. No frozen file touched.

### THE MEASUREMENT (probe run from `scratch_probe/` OUTSIDE the repo commit; solc 0.8.26 via-IR + Yul optimizer; ECB runtime)
Reconstructed the EXACT spliced pipeline: `artifact.codeArtifact.compiled.cfg` → `finalCfg := seamCancelProgram (peepholeProgram (normalizeProgram cfg))`; `L := compiled.certified.target` (lowered, pre-compaction); `P := compact.physicalSource` (post-compaction). Verified `finalCfg.lower? = L` (`decide = true`) and reconstructed `L` with **per-instruction provenance** by lowering each block in `blocksInLoweringOrder?` and tagging every emitted asm instr with `(blockIdx, LABEL | body[i]=<cfgInstr> | TERM)`. Tagged reconstruction is byte-exact vs `L` (**0 mismatches**, len 3851).

| quantity | value |
|---|---|
| `finalCfg` blocks | 1030 |
| `L` length (pre-compaction) | 3851 |
| `P` length (post-compaction) | 1987 |
| `P` adjacent-equal `SWAPn;SWAPn` pairs | **61** (reproduces §59/§69 baseline exactly) |
| seams matching `swap, jump G, label G, swap` in `L` | **61** |
| &nbsp;&nbsp;→ **body-tail → body-head** seams | **61 / 61** |
| &nbsp;&nbsp;→ **terminator-involved** seams | **0 / 61** |
| blocks where the shipped `sourceFire?` fires | **0 / 1030** |

Every seam is SWAP1 (cfg `.swap 0` → opcode 0x90). Representative provenance (probe output):
```
seam j=71  d=SWAP1 G=generated 21_100   PRE B23.body[0]=swap 0   POST B24.body[0]=swap 0
seam j=139 d=SWAP1 G=generated 40_100   PRE B42.body[0]=swap 0   POST B43.body[0]=swap 0
```
i.e. `L` locally is `label A ; swap1 ; jump G ; label G ; swap1 ; …` where **both** swaps are BLOCK-BODY instructions (`A.body[0]` and `G.body[0]`), NOT terminator-lowered.

### RECONCILIATION — who was right
* **§60 CONFIRMED.** The 61 pairs are cross-block **fallthrough body-to-body seams**: `A.term = .jump G`, `G` laid out immediately after `A`, gap `[jump G ; label G]` elided by `elideFallthroughJumps`, abutting `A`'s emitted tail swap with `G`'s emitted head swap. All body-body (0 terminator).
* **§69 REFUTED.** §69 attributed the pre-jump swap to `returnDispatchCase`/`removeBuriedUnder` (terminator lowering). This is impossible: `removeBuriedUnder depth = liftBuriedToTop depth ++ [.prim .pop]` **ends in `pop`, never a swap** (`Assembly/StackShuffle.lean:56-57`), so a return-dispatch case seam would abut `pop ; swap`, not `swap ; swap`. Measured terminator-involved seams = **0**. §69's "block-body altitude is the wrong altitude" conclusion is therefore WRONG — the altitude is RIGHT.

### THE ACTUAL ROOT CAUSE OF THE ZERO-FIRE (decisive, source-airtight)
`sourceFire? program a` keys the tail swap on **`a.body.getLast? = some (.swap d)`** (`PeepholeSeamCancel.lean:62`). But the 61 source blocks look like `A.body = [.swap 0, .bindLocals …]` (`bodyLen` 2/3/4; probe `A.body.getLast? = bindLocals` on all sampled seams). The swap is at `body[0]`; the CFG-**last** instruction is a **`.bindLocals`** that lowers to `[]` (`Lower.lean:52`). So:
* the **emitted** last instruction of `A` before `jump G` is the swap (from `body[0]`), because everything after it lowers to nothing, but
* `a.body.getLast?` sees the trailing `.bindLocals`, not the swap ⟹ `sourceFire?` returns `none`.

`bindLocals`/`bindScratch`/`relabel` are all **zero-lowering** (`Instr.lower? = some []`) **and runtime IDENTITIES** on `EVMState` (`Semantics.lean:78-83`: `runState _ state = .ok state`); they only re-thread the typed `Shape` (`Typing.lean:46-51`). So they are transparent to the emitted bytes and to the EVMState pending-swap invariant, and opaque only to the typed shape. The fix must identify the tail swap as **the last body instruction with non-empty lowering** (skipping trailing zero-lowering binds) and remove *that* swap — not `dropLast`, which would remove the `bindLocals` and leave the swap emitted (an UNSOUND half-cancel: `A` keeps its swap while `G` loses its head swap).

### ROUTE DECISION — **Route α** (correct the canceller at the TypedCfg block-body altitude)
Evidence forces the altitude: the seams ARE block-body (61/61), and the entire §61-69 congruence tower (WellTyped preservation, pending-swap runtime bisimulation, fuel bound, halted bridges, entry seed, and the §69 OIC/StackArtifact splice plumbing) already lives at exactly this altitude and is **reusable**. The change is localized:
1. **Predicate** (`sourceFire?`): replace `a.body.getLast?` with the last **non-empty-lowering** body instruction (`effectiveTailSwap?`), i.e. drop trailing instrs whose `lower? = some []`, then require `.swap d`. Same for the length guard.
2. **Edit** (`seamBlock` source arm): replace `body := block.body.dropLast` with "remove the last non-empty-lowering swap, retain the trailing binds", re-typing `output` through `remapShape d` as before. The target arm (`body.tail`, drop `G.body[0]` head swap) is already correct.
3. **Tower re-derivation** (the frontier): the runtime pending-swap bisimulation (§62-67) is stated over `dropLast`. Because the trailing binds are **runtime identities**, `runBody A.body state = runBody (prefix ++ [swap d]) state` on the EVMState (binds don't touch state), so the EVMState pending-swap invariant carries through UNCHANGED; the extra work is purely **shape-level** — threading the trailing binds' `Shape` transformations through `remapShape` (the WellTyped half). This is the §61-69 mathematics with the swap no longer literally last; no new runtime kernel is expected (mirrors §64/§65's "assembly not discovery").

**Rejected — Route (a)/Lower.lean (terminator shuffle):** the mandate's emission-side candidate presumed the pre-jump swap came from terminator lowering. Measured **0/61** terminator-involved; `removeBuriedUnder` ends in `pop`. There is nothing to fix in `Lower.lean`'s terminator shuffle. Premise refuted.
**Rejected as primary — Route (b)/assembly-compaction altitude:** larger, new correctness altitude in the frozen `Compact`/`GasfulBridge` cone, and it DISCARDS the banked §61-69 tower. Kept as fallback only if the Route α shape-threading proves harder than the block-body edit.

Note a soundness bonus surfaced by the measurement: the cfg-level cancellation is sound **regardless of layout adjacency** — `A` (emitted) `…swap d ; jump G` then `G` (emitted) `swap d ; …` are consecutive in EXECUTION (jump preserves the stack) and `refCount G = 1` (unique predecessor, measured 61/61), so `swap d ∘ swap d = id` across the seam whether or not compaction merges them. Removing both saves 2 bytes per firing seam (≈122 B on ECB runtime) even without the compaction adjacency.

### METHOD / files
Probe: `scratch_probe/probe.lean` (+ `ecb_solc_out.json` generated by solc 0.8.26 with `viaIR`, `optimizer.details.yul`, requesting `irOptimizedAst`+`metadata`; selection `objectSelector := .runtime`, evmVersion read from solc metadata). Run OUTSIDE the repo commit, NOT committed. `scripts/opt_harness.sh check` unaffected by the docs edit. No frozen file touched. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

### GREEN PREFIX BANKED + FRONTIER SHARPENED (validated empirically)
New non-frozen leaf `EvmCompiler/TypedCfg/PeepholeSeamCancelEff.lean` (imported by **nobody** ⟹ cannot touch axioms), the **static half** of Route α:
* `lowersToNothing` / `emittedTail?` / `effTailSwap?` — the emitted-tail-swap key (last body instr with non-empty lowering, trailing binds skipped); `removeEffTail` — remove that swap, retain trailing binds; `sourceFireEff?` / `targetFireEff?` / `seamBlockEff` / `seamCancelProgramEff`.
* Structural preservation proved green (mirrors the `seamCancelProgram` spine): `seamBlockEff_{label,term}`, `seamCancelProgramEff_{entry,blocks}`, `findBlock?_seamCancelProgramEff`, `emittedLabels_…`, `labelsUnique_…`, `emittedLabelsUnique_…`, `entry_findBlock?_…`.

**Empirical validation (same ECB probe):** `sourceFireEff?` fires on **61/1030** blocks and `targetFireEff?` on **61/1030** — i.e. it identifies **exactly** the measured 61 seams, versus the shipped `sourceFire?`'s **0**. Block count / entry preserved (1030, entry unchanged).

**FRONTIER (sharpened, now with a concrete failing probe):** `(seamCancelProgramEff finalCfg).lower? = none`. The predicate is right, but the edit's **output re-typing is not yet consistent** when binds trail the swap: the shipped edit re-types with `remapShape d block.output` (the swap's `0↔d+1` transposition), which is correct only when the swap is literally last. With `A.body = prefix ++ [swap d] ++ binds`, `output = type?(binds)(remapShape d (type?(prefix) input))` whereas after removing the swap `output' = type?(binds)(type?(prefix) input)` — related by the transposition **conjugated through the binds' shape maps**, not by a bare `remapShape d`. Threading the trailing binds' `Shape` transformations through the re-typing (so `Block.lower?` succeeds) is the shape-level frontier; the EVMState pending-swap invariant is expected to carry through unchanged because the binds are runtime identities (`Semantics.lean:78-83`). This is the §61-69 shape half re-derived for "swap not literally last", plus the runtime-tower port (§62-67) and the §69 OIC/StackArtifact splice reuse. No live byte delta until `lower?` succeeds on the corrected output; never-commit-red ⟹ deferred to a successor session.

### Files touched (session 70)
`EvmCompiler/TypedCfg/PEEPHOLE_PROGRESS.md` (this note), NEW `EvmCompiler/TypedCfg/PeepholeSeamCancelEff.lean` (static-half leaf, imported by nobody). No frozen file touched. No splice ⟹ emitted bytes UNCHANGED (byte-identical to §59/§69: 8557/8591·3, 2791/2825·61, 1991/2234·15, 923/957·15). `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-71 update (2026-07-20): **§70's premise was INCOMPLETE — the sound Route-α needs NAME-CONJUGATION + CLEAN-SEAM disjointness, not just an output re-typing. The corrected transform is now proven WELL-TYPED and axiom-clean; the gate `seamCancelProgramEff_wellTyped` is GREEN.** No live byte delta yet (runtime bisimulation + splice remain the frontier). Five green, axiom-clean commits on `arena-opt`. `compile_correct`/`compile_correct_creation` axioms UNCHANGED. No frozen file touched.

### THE CORRECTION (empirical, decisive — three uncommitted probes on ExternalCallBox, solc 0.8.26 via-IR + Yul optimizer, runtime)
§70 proposed "drop the tail swap, retain the trailing binds, re-type `output` by re-running `bodyType?`" (the `getD` fix, commit `e2836628`). Probes show this is **UNSOUND at the type level**:
* The getD fix makes `(seamCancelProgramEff finalCfg).lower? = some` (lowered len 3733 vs 3851) **BUT** `eff.wellTyped? = false` — **termFail = 61**. `lower?` does *not* check inter-block terminator compatibility; `WellTyped` does, and it fails at every source block.
* Root cause (`probe_shapes`): every source block is **exactly** `A.body = [swap d, bindLocals 0 names]` (`d = 0`, `names.length ∈ {3,4}`, `d+1 < names.length`, `61/61`). The trailing `bindLocals` **relabels** the swapped slots — it names position 0 `param` when after the swap the value there is `param_1`. Merely dropping the swap makes the bind *mislabel the runtime values*. The sound edit must **conjugate the bind's names** through the `0↔d+1` transposition (`bindLocals 0 names ↦ bindLocals 0 (swapPos 0 (d+1) names)`) and re-type `output := remapShape d output` (exactly the shipped `seamCancelProgram` formula — so the terminator obligation reuses `compatible_remapShape_eq` verbatim; only the body-typing is new). `bindLocals` is a runtime identity for *any* names, so the runtime is untouched by the permutation.
* Second hazard: these blocks emit a **single** swap (head = emitted-tail), so a swap shared by a chain `C→A→B` is double-claimed (probe: **4** blocks are both raw-source and raw-target). The shipped `2≤length`-distinct-index disjointness does NOT hold here. A seam now fires only when **both endpoint swaps are private** (`cleanSrc?`/`cleanTgt?`: source is not a target, its target is not a source), proven disjoint (`cleanSrc?_cleanTgt?_disjoint`). On ECB this fires **53/61** seams (8 dropped to the overlap guard) and yields `eff.wellTyped? = TRUE`, `eff.lower? = some` (lowered len **3745** vs 3851, **−106 = 53 seams × 2 swaps** pre-compaction).

### WHAT LANDED (green, axiom-clean — commits `e2836628` `51e1e7d3` `4352b253` `34d5d38e` `f61d7495`)
All in the non-frozen orphan leaf `EvmCompiler/TypedCfg/PeepholeSeamCancelEff.lean` (imported by **nobody** ⟹ cannot touch the `compile_correct` cone).
1. **Corrected transform** (`51e1e7d3`, supersedes getD `e2836628`): `conjBind`; `srcRaw?`/`tgtRaw?`/`cleanSrc?`/`cleanTgt?` (exact `[swap d, bindLocals 0 names]` source shape); `seamBlockEff` (source: conjugate the bind + `remapShape d output`; target: drop head swap + `remapShape d input`); `seamCancelProgramEff`. Structural preservation + `cleanSrc?_cleanTgt?_disjoint`.
2. **Body-conjugation kernel** (`4352b253`, the crux): `swapPos_map`/`_append_left`/`_drop`/`_eq_of_oob`; `type?_bindLocals0`/`_of_le`; **`bodyType?_conj`** = `bodyType? [bindLocals 0 (swapPos 0 (d+1) names)] input = some (remapShape d output)`. Expressible as a single permuted `bindLocals` since the swap positions lie inside the offset-0 name range (the §57 `remapZeroWidth`/`RemapSafe` machinery does NOT cover multi-name binds — `RemapSafe` requires `names.length = 1`).
3. **Specs + field descriptions** (`34d5d38e`): `srcRaw?_spec`, `cleanSrc?_spec`, `cleanTgt?_spec`, `seamBlockEff_{output,input,body}`.
4. **The WellTyped gate** (`f61d7495`): `cleanTgt_head_swap`, `cleanTgt?_of_cleanSrc?`, `cleanTgt?_none_of_cleanSrc?_none` (non-source terminator invariance via `refCount=1` / `two_le_refCount`), `output_bound_of_cleanSrc`/`input_bound_of_cleanTgt`, `labelShape?_seamCancelProgramEff`, `seamBlockEff_term_type?`, `seamBlockEff_bodyType?`, `seamBlockEff_wellTyped`, and **`seamCancelProgramEff_wellTyped : program.WellTyped → (seamCancelProgramEff program).WellTyped`**. `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### THE MEASUREMENT (probe, OUTSIDE the repo commit; ECB runtime)
| quantity | value |
|---|---|
| `cleanSrc?` / `cleanTgt?` fires | **53 / 53** (disjoint; 8 dropped to overlap vs the 61 raw seams) |
| `finalCfg.wellTyped?` | true |
| `(seamCancelProgramEff finalCfg).wellTyped?` | **true** |
| `finalCfg.lower?` len (pre-compaction) | 3851 |
| `(seamCancelProgramEff finalCfg).lower?` len | **3745** (**−106** = 53 × 2 swaps) |

**EMITTED-BYTES DELTA = 0 (no splice this session).** `seamCancelProgramEff` is imported by nobody, so ASP/ECB/MiniToken/LoopBox are byte-identical to §59/§69 (8557/8591·3, 2791/2825·61, 1991/2234·15, 923/957·15). Determinism: N/A (no changed contracts). The −106 is a *probe* of the transform on the lowered (pre-compaction) CFG; expected live ECB runtime once spliced ≈ 2791 − 2·53 ≈ **2685** (to be confirmed post-compaction).

### THE REMAINING FRONTIER (runtime bisimulation + splice)
Type layer closed; remaining:
1. **Runtime birth kernel (Eff variant).** Source `A`: original `[swap d, bindLocals 0 names]`, edited `[bindLocals 0 (swapPos…)]`. Swap is the HEAD (not the shipped trailing-swap) and the (conjugated) bind is a runtime identity for any names (`Semantics.lean:78-83`), so running the original from `s_o` ≡ running the edited from an `s_c` one `swap (d+1)` behind — `PendingSwap d` born by the *head* swap through a runtime-identity bind. Target arm = shipped exactly.
2. Port `SeamStepRel`/`SeamOutcomeRel` congruence, fuel bound, entry seed (`cleanTgt?` at entry = none via the `≠ entry` guard), PCI preservation — mechanical over the shipped tower with `sourceFire?→cleanSrc?`, `targetFire?→cleanTgt?`.
3. **Splice** `seamCancelProgram → seamCancelProgramEff` at the §69 StackArtifact/OIC sites (banked plumbing), then `scripts/opt_harness.sh check` + LIVE delta + double-compile determinism.

### Files touched (session 71)
`EvmCompiler/TypedCfg/PEEPHOLE_PROGRESS.md` (this note); `EvmCompiler/TypedCfg/PeepholeSeamCancelEff.lean` (rewritten to the correct conjugating clean-seam transform + WellTyped tower, still imported by nobody). No frozen file touched. No splice ⟹ emitted bytes UNCHANGED. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-72 update (2026-07-20): **THE FIRST LIVE BYTE DELTA — the corrected clean-seam conjugating canceller is LIVE in the public compile spine. Runtime pending-swap bisimulation ported, spliced at StackArtifact.compile? + OIC; `scripts/opt_harness.sh check` = OK (43 theorems, axioms ⊆ [propext, Classical.choice, Quot.sound]); ECB runtime 2791→2685 (−106, EXACTLY the §71 prediction), byte-identical on double-compile.** Four green, axiom-clean commits on `arena-opt`. `compile_correct`/`compile_correct_creation` axioms UNCHANGED. No frozen file touched.

### WHAT LANDED (green, axiom-clean — commits `f4278b79` `ebac2bbf` `ab97e4ff` + this doc)
1. **Runtime tower** (`f4278b79`, `EvmCompiler/TypedCfg/PeepholeSeamCancelEffRuntime.lean`): ported §62-67 of `PeepholeSeamCancel` to the clean-seam canceller. The one genuinely-new kernel is the SOURCE HEAD-swap birth through a runtime-identity conjugated bind — **`openRunBody_headSwap_bind_pending`** (`:36`): running the original `[swap d, bindLocals 0 names]` from `s_o` vs the edited `[bindLocals 0 names']` from a SRD `s_c` gives `PendingSwap d` by the head swap's involution; both `bindLocals` are EVMState identities (`Semantics.lean:78-83`), transparent to the trailing bind. Because `cleanSrc?`/`cleanTgt?` are disjoint (`cleanSrc?_cleanTgt?_disjoint`), the body kernel **`seamBlockEff_body_rel`** (`:126`) has only THREE reachable cases (shipped some/some chain case vacuous). Then `SeamStepRelEff`/`SeamOutcomeRelEff`, `openRun_seamCancelEff_congr` (`:197`), `openStep_seamCancelEff_congr` (`:271`), `conjBind`/`seamBlockEff`/whole-program PCI preservation, `cleanTgt?_entry_eq_none`, `seamStepRelEff_entry`.
2. **Combined tower + fuel bound** (`ebac2bbf`, `EvmCompiler/Structured/PeepholeSeamCombinedEff.lean`): ported `PeepholeSeamCombined` to `seamCancelProgramEff` — `SeamCombinedStepRelEff`/`OutcomeRelEff`, `seamCombinedStepRelEff_entry_of_generated`, `openStep_seamCombinedEff_congr_of_source` (`:96`, the per-entry StackRealizes guard via `seamBlockEff_input_cleanTgt` + `pendingSwap_stack_length`), fuelled + prefix congruences, halted/finished bridges, and **`fuelBudget_seamCombinedEff_le`** — the source-case fuel argument redone for the bindLocals-conjugation edit (edited body `[bindLocals names']` lowers to `[]` via `lowerBodyFrom?_singleton_bindLocals`). Stack-length support and the `cfg→P` combined leg reused verbatim.
3. **The SPLICE** (`ab97e4ff`): `StackArtifact.compile?` + `compile?_parts` and OIC now route `seamCancelProgram → seamCancelProgramEff` and consume the Eff combined tower. `seamCancelProgram` is an internal name flowing StackArtifact→OIC — **no frozen file references it** — so the splice is localized to two non-frozen files; the whole downstream consumer graph (Yul/Solidity crowns, 1323/1369 jobs) rebuilds green.

### THE FIRST LIVE BYTE DELTA (solc 0.8.26 via-IR + Yul optimizer; runtime & creation; determinism = double-compile)
| contract | runtime (base→now, Δ) | creation (base→now, Δ) | swap-pairs (base→now, Δ) | double-compile |
|---|---|---|---|---|
| **ExternalCallBox** | 2791 → **2685** (**−106**) | 2825 → **2719** (−106) | 61 → 12 (−49) | **byte-identical** |
| **AdversarialStackPressure** | 8557 → **8551** (−6) | 8591 → **8585** (−6) | 3 → 1 (−2) | **byte-identical** |
| **MiniToken** | 1991 → **1965** (−26) | 2234 → **2204** (−30) | 15 → 5 (−10) | **byte-identical** |
| **LoopBox** | 923 → **897** (−26) | 957 → **931** (−26) | 15 → 3 (−12) | **byte-identical** |

ECB hits the §71-predicted 2685 (= 2791 − 2·53 clean seams) **exactly**. All four contracts shrink and are deterministic (identical bytes on re-compile). The residual swap-pairs are seams excluded by the clean-endpoint guard (chain overlaps) plus non-`bindLocals`-shaped adjacencies; these are the next campaign's target.

### GATES
`scripts/opt_harness.sh check` = **OK** (43 public theorems; axioms contained in `[propext, Classical.choice, Quot.sound]`). `#print axioms` confirms `Solidus.compile_correct` and `Solidus.compile_correct_creation` depend on exactly `[propext, Classical.choice, Quot.sound]` — UNCHANGED. Production smoke (`stack_backend_production_smoke.lean`) exercised inside the check. Forge differential deferred to CI (not run). No frozen file touched.

### REMAINING FRONTIER
* The 8 double-claimed chain seams on ECB (and analogous overlaps elsewhere) dropped by the clean-endpoint guard — recovering them needs a chain-aware pending-swap invariant (multiple pending desyncs threaded through `C→A→B`).
* Non-`bindLocals`-shaped adjacent swap pairs (the residual 12 on ECB, 5 MiniToken, 3 LoopBox, 1 ASP) — different source shapes not yet covered by `srcRaw?`.

### Files touched (session 72)
NEW `EvmCompiler/TypedCfg/PeepholeSeamCancelEffRuntime.lean`, NEW `EvmCompiler/Structured/PeepholeSeamCombinedEff.lean`; spliced `EvmCompiler/Compiler/StackArtifact.lean` + `EvmCompiler/Compiler/OpenInteractionComposition.lean` (seamCancelProgram→seamCancelProgramEff); this note. No frozen file touched. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-73 update (2026-07-20): **PROBED BOTH §72 RESIDUAL TARGETS EMPIRICALLY; BOTH ARE OUT OF CHEAP REACH. Iteration is a proven fixpoint dead-end; the 8 chain overlaps need the non-local matching invariant §72 named; the 4 extra ECB pairs are `swap2;swap2` created by our own transform + compaction, living in the FROZEN `Assembly/Compact.lean`. No sound cheap extension exists ⟹ NO live change; codegen byte-identical to §72 (corpus −0.43% shipped state intact).** Docs-only commit. `scripts/opt_harness.sh check` = **OK** (1369 jobs, **43** public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`). `compile_correct`/`compile_correct_creation` UNCHANGED = `[propext, Classical.choice, Quot.sound]` (verified in the full Verification build). No frozen file touched. No byte change ⟹ no determinism double-compile, no bench re-run (would reproduce §72's shipped numbers).

### PROBE (a) — DOES ITERATING `seamCancelProgramEff` UNLOCK THE 8 CHAIN SEAMS? **NO — it is a fixpoint at pass 1.**
`lake env lean --run` probe on the ECB corpus value `seamCancelProgram (peepholeProgram (normalizeProgram cfg0))` (the live-fed program), counting `srcRaw?`/`tgtRaw?`/`cleanSrc?`/`cleanTgt?` firings + `lower?` length per iteration of `seamCancelProgramEff`:

| iter | srcRaw | tgtRaw | cleanSrc | cleanTgt | loweredLen | wt |
|---|---|---|---|---|---|---|
| 0 | 61 | 61 | 53 | 53 | 3851 | T |
| 1 | 8 | 8 | **0** | **0** | 3745 | T |
| 2 | 8 | 8 | 0 | 0 | 3745 | T |
| 3+ | 8 | 8 | 0 | 0 | 3745 | T |

Pass 0 fires the 53 clean seams (loweredLen 3851→3745, −106 = the §72 delta). Pass 1 leaves **8 raw seams** but **zero** clean firings, and the program is a fixpoint from there. The 8 residual raw seams never become clean because `srcRaw?`/`tgtRaw?`/`cleanSrc?`/`cleanTgt?` depend only on each block's **local** body shape + `refCount` + entry — none of which the disjoint clean edits (elsewhere in the program) touch. **The iterate-to-fixpoint wrapper is a dead end and was NOT built.**

### PROBE (b) — CLASSIFY THE RESIDUAL 12 ECB EMITTED PAIRS. Two categories, both non-cheap.
Probe: lower `seamCancelProgramEff base` → `Assembly.Compact.prepare` → scan adjacent equal `SWAPn;SWAPn` with lookbehind/lookahead context. Base (pre-eff) had **61** pairs, **all `swap1;swap1`**. LIVE (post-eff) has **12**:

* **8 pairs = 4 three-block chains** `A→B→C`, blocks (generated) `148→149→150`, `302→303→304`, `323→324→325`, `731→732→733`; each block body `[.swap 0, .bindLocals 0 #{3or4}]`, `refCount = 1`, all `srcRaw? = true`. Three consecutive emitted `swap1`s ⟹ two overlapping pairs per chain. These are exactly the `srcRaw?`-firing-but-clean-guard-blocked overlaps: B is both `A`'s target and `B→C`'s source, so `cleanSrc?`/`cleanTgt?` drop **both** seams.
* **4 pairs = `swap2;swap2`** (`[swap1] swap2;swap2 [push|dup2]`). These exist in **neither** the base compacted image **nor** the LIVE **pre-compaction** lowered image — they appear **only** after `Compact.prepare` on the eff-transformed program. They are a pure **compaction-phase artifact created by our own transform**: dropping the clean-seam `swap1`s changes fallthrough abutment, so `elideFallthroughJumps` newly juxtaposes two `swap2`-emitting block ends. There is **no** `swap2` seam at cfg-body granularity even post-eff (a dedicated emitted-tail(`.swap d`)→head(`.swap d`) scan finds only the 8 `d=0` chain seams).

### VERDICT — NO CHEAP SOUND EXTENSION; STOP GREEN.
* **Iteration**: proven fixpoint dead-end (probe a). Not built.
* **The 8 chain pairs**: recovering even *one* seam per 3-block chain needs a **matching** (fire `A→B`, skip `B→C`). But firing `A→B` target-edits `B` (drops B's only swap); then C's surviving lone swap must **not** be dropped — yet `tgtRaw?(C) ≠ none` (C is a raw target of raw-source B), so a local `cleanTgt?(C)` *would* fire and wrongly drop C's swap, corrupting the program. Suppressing it requires the **non-local** "B's swap was already consumed upstream" fact threaded along the chain — precisely §72's chain-aware **multi-pending** invariant (and its runtime bisimulation re-derivation). This is a multi-session build, not a local predicate tweak. NOT attempted (never-commit-red).
* **The 4 `swap2` pairs**: a compaction-phase redundancy in `EvmCompiler/Assembly/Compact.lean`, which is **FROZEN**. Invisible at cfg-body granularity, so no cfg-body predicate can reach it; the only route is an assembly-level peephole that breaks the frozen certificate contract. NOT allowed.

Both §72 frontier items are thus confirmed genuinely multi-session / contract-breaking, not the "cheap" targets the session hoped for. The −0.43% corpus / §72 per-contract deltas (ECB 2685/2719, ASP 8551/8585, MiniToken 1965/2204, LoopBox 897/931) remain the shipped state, unchanged.

### GATES
`scripts/opt_harness.sh check` = **OK** (1369 jobs, 43 public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`). `#print axioms` (in the full Verification build) confirms `Solidus.compile_correct` / `Solidus.compile_correct_creation` = `[propext, Classical.choice, Quot.sound]` — UNCHANGED. No `.lean`/frozen file touched (docs-only); scratch `lake env lean --run` probes (`scratch_probe/probe_iter.lean`, `probe_residual.lean`, `probe_swap2*.lean`) are uncommitted.

### Files touched (session 73)
`EvmCompiler/TypedCfg/PEEPHOLE_PROGRESS.md` ONLY (this note). No `.lean` change, no frozen file, no codegen change. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-74 update (2026-07-20): **STRATEGY + START — opportunity scan picks THE big vein (shuffle-window canonicalisation, 22 244 B / 43 % of the worst-8 sample) and the transform algebra is BANKED green; but a decisive pre/post-compaction provenance probe proves the ENTIRE vein is a `Compact.prepare` (FROZEN) cross-block artifact — 0 reducible at cfg-body altitude, ALL of it (ASP 7430 · ECB 412 · DynStorage 5798) created by `elideFallthroughJumps`. The §60/§68/§73 pattern, generalised from adjacent-pairs to full permutations.** Green, axiom-neutral leaf `EvmCompiler/TypedCfg/ShuffleCanon.lean` (imported by nobody). NO splice (a cfg-body splice is byte-identical, §68-style). `compile_correct`/`compile_correct_creation` axioms UNCHANGED. No frozen file touched.

### THE OPPORTUNITY SCAN (probes OUTSIDE the repo commit; solc 0.8.26 via-IR + Yul optimizer; LIVE shipped runtime bytecode; worst-8 size-ratio contracts, 51 547 B)
Opcode histogram of the shipped bytecode (`scratch/probe_hist.py`, `probe_perm.py`):

| opcode family | count | bytes | % of sample |
|---|---|---|---|
| **SWAP** | 28 423 | 28 423 | **55.1 %** |
| PUSH | 4 457 | 12 169 | 23.6 % |
| DUP | 2 711 | 2 711 | 5.3 % |
| POP | 2 011 | 2 011 | 3.9 % |
| JUMPDEST | 1 349 | 1 349 | 2.6 % |
| JUMP | 961 | 961 | 1.9 % |

`AdversarialStackPressure` (15.4× vs solc) is **90.4 % SWAP** (7731 of 8302 ops). Every emitted SWAP sits in a maximal run; minimising each run to a same-net-permutation swap list (star-transposition decomposition, correct-by-construction, gated "fire only if shorter") recovers **22 244 B = 43.2 % of the sample** (97 % of the 22 890 B perm-min ideal). Per-contract recoverable: ASP 7484, DynStorage 6056, PostCancun 2456, Semantic 2372, CreateLifecycle 1948, ReentrantTryCatch 1206, EffectOrdering 946, ECB 422. Runs up to length **240** (ASP) collapsing to **0–1** swaps (repeated `swap1;swap2;…;swapN` rotations returning to identity).

Other patterns were negligible or non-cheap: `DUPn;POP` = 1×, `PUSHn;POP` = 0× (solc's Yul optimizer already removes dead push/dup-pop); `PUSH1 0x00` (should be `PUSH0`) = 971 B but provenance unprobed (likely frozen serialisation — deferred side-probe); adjacent `SWAPn;SWAPn` = 122 (the §72 seam residual, subsumed).

### RANKED CAMPAIGN TABLE
| # | campaign | recoverable (sample) | difficulty | verdict |
|---|---|---|---|---|
| **a** | **shuffle-window canonicalisation** (rewrite any swap run to its minimal same-permutation form) | **22 244 B (43 %)** | HIGH — provenance = 100 % post-compaction cross-block (see below); needs assembly-post-pass OR cfg-cross-block-anticipation altitude | **CHOSEN** (subsumes b) |
| b | multi-pending chain seams (§72/§73 residual) | ~16 B (ECB) | HIGH — non-local multi-pending invariant | subsumed by (a) at full-permutation generality |
| c | dup/pop, push/pop family | ~2 B | LOW | not worth it (solc already removes) |
| d | block-merge for refCount-1 jump chains | ~2 310 B (JUMP+JUMPDEST) | MED — compaction already elides fallthrough jumps; residual is real control flow | lower priority; synergistic with (a) |
| e | `PUSH1 0x00 → PUSH0` | 971 B | UNKNOWN — provenance unprobed | deferred cheap side-probe |

### THE DECISIVE PROVENANCE FINDING (Lean probes; reconstruct `finalCfg = seamCancelProgramEff (peepholeProgram (normalizeProgram cfg0))`, `finalCfg.lower? = certified.target` verified byte-exact)
Two independent measurements, **each refuting the cfg-body-altitude deduction** (the §70-73 lesson: MEASURE, don't deduce):

1. **Emitted swap runs are 100 % single-block, and 100 % irreducible PRE-compaction.** A per-instruction provenance probe (`scratch/probe_swaprun.lean`, `probe_emitprov.lean`) found **0 / 400 (ECB), 0 / 2574 (DynStorage) emitted swap runs cross a block boundary** — every run is one block's body/term. Yet running the same `canonSwaps` over the pre-compaction lowered image `L` yields **canon-saving = 0** on every contract (body-only and term-only alike).

2. **ALL reducibility is created by `Assembly.Compact.prepare`.** Scanning `prepare L` (`scratch/probe_compact.lean`):

| contract | L (pre) len | pre canon-saving | P (post) len | **post canon-saving** |
|---|---|---|---|---|
| AdversarialStackPressure | 10 600 | **0** | 8 259 | **7 430** |
| ExternalCallBox | 3 745 | **0** | 1 881 | **412** |
| DynamicStorageSurfaceBox | 21 870 | **0** | 12 510 | **5 798** |

`elideFallthroughJumps` merges fallthrough-adjacent blocks, concatenating one block's tail swaps with the next block's head swaps into longer runs whose *net* permutation is reducible. Pre-compaction every block's run is already minimal. This is exactly §60's seam phenomenon, generalised from `SWAPn;SWAPn` adjacent pairs to arbitrary permutations — and the post-8259/12510 numbers reproduce the shipped-bytecode python figures (7484 / 6056).

### VERDICT + WHAT LANDED
* **The 22k-byte vein is real but lives 100 % post-compaction, across merged fallthrough seams, in the FROZEN `Assembly/Compact.lean`.** A cfg-BODY transform (`shuffleCanonProgram`, banked) fires on nothing in the real corpus (byte delta 0, `wellTyped?`/`lower?` byte-identical — verified). Splicing it is §68-style byte-identical inert, so it was **NOT spliced** (never-ship-inert).
* **BANKED green** (`ShuffleCanon.lean`, commit `2e2afb83`, imported by nobody ⟹ cannot touch axioms): the reusable, altitude-independent **permutation algebra** (`applySwap`, `netStack`, `maxDepth`, `sortStep`/`sortToId`/`starDecompose`, `canonSwaps` + `canonSwaps_length_le`), the block-body rewrite (`swapDepth?`, `emitRun`, `canonBodyGo`/`canonBody`, `canonBlock`, `shuffleCanonProgram`), and full structural preservation (`findBlock?_`, `emittedLabels_`, `labelsUnique_`, `emittedLabelsUnique_`, `entry_findBlock?_`). `canonSwaps` validated on sanity cases (`[0,0,0,0]→[]`, `[0,1,0,1,0,1]→[]`, `[0,1]` irreducible-3-cycle kept) and on the live corpus cfg (`wellTyped?` + `lower?` preserved ⟹ same permutation ⟹ same shape threading, the type-preservation half confirmed empirically).

### SHARPENED FRONTIER — the successor's two legal routes to the vein (both multi-session)
The permutation minimiser is done and altitude-independent; only the **run extraction** changes. Neither touches `Compact.lean`.
1. **Assembly post-pass (Route 1).** Apply the swap-run canonicaliser to the assembly program *after* `prepare`, in a non-frozen wrapper, proving assembly-level semantic preservation (pure stack-permutation equality through the frozen open-interpreter fuel/pc model). Captures the full 22k; new assembly-altitude correctness cone (larger, but the transform is pure-permutation-equality — cleaner than the §62-67 pending-swap bisimulation).
2. **Cfg cross-block anticipation (Route 2).** At cfg level, identify the fallthrough chains `elideFallthroughJumps` *will* merge (refCount-1 non-entry seams, as §72's canceller already does) and canonicalise the concatenated would-be-merged swap run, reusing the §72 seam tower. This is the §72/§73-named "non-local matching / multi-pending" invariant generalised from 2-swap cancellation to full permutations — with the payoff now quantified at **100× the §72 seam delta (43 % vs 0.43 %)**, which reframes its priority.

### GATES
`scripts/opt_harness.sh check` = **OK** (see below). `#print axioms` confirms `Solidus.compile_correct` / `Solidus.compile_correct_creation` = `[propext, Classical.choice, Quot.sound]` — UNCHANGED (the new leaf is imported by nobody). No frozen file touched. No splice ⟹ codegen byte-identical to §72 (corpus −0.43 % shipped state intact) ⟹ no determinism double-compile, no bench re-run.

### Files touched (session 74)
NEW `EvmCompiler/TypedCfg/ShuffleCanon.lean` (green, imported by nobody); `EvmCompiler/TypedCfg/PEEPHOLE_PROGRESS.md` (this note). Uncommitted scratch probes under `scratch_probe/` (`probe_hist.py`, `probe_perm.py`, `probe_canon.py`, `probe_swaprun.lean`, `probe_shufflecanon.lean`, `probe_grouping.lean`, `probe_emitprov.lean`, `probe_compact.lean`) + hand-generated solc IR JSON. No frozen file touched. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-75 update (2026-07-20): **ROUTE DECISION — Route 2 (cfg cross-block anticipation) CHOSEN over Route 1 (assembly post-pass), on decisive attach-point + proof-risk evidence: Route 1's only vein-capturing attach point is INSIDE `compileExecutable?`/`Compact.prepare` (the mandate-frozen `Assembly/*` cone) and would require a brand-new layout+decode+gas correctness cone under byte-length changes; Route 2 attaches at the ALREADY-LIVE `seamCancelProgramEff` seam (StackArtifact.compile?:64), reuses the mature §61-72 tower + the banked ShuffleCanon permutation algebra, and is proven-effective (§72 is the existence proof that cfg-altitude merge-anticipation survives compaction and reduces bytes).** First milestone this session = the **permutation-algebra type-preservation core** (the §74-documented frontier "netStack determines bodyType?; starDecompose realises its argument") — the reusable crux BOTH the single-block and the chain transform need. Green commits below; no splice yet (no live byte delta). `compile_correct`/`compile_correct_creation` axioms UNCHANGED. No frozen file touched.

### THE ROUTE DECISION — evidence (read the certificate contract + the §72 tower extension surface)

**The certificate contract (what the spine pins about the physical stream).** `StackArtifact.compile?` (`EvmCompiler/Compiler/StackArtifact.lean:37-77`) has exactly one compaction seam:
```
let certified ← (seamCancelProgramEff (peepholeProgram (normalizeProgram cfg))).compileCertified?   -- L : Assembly.Program, PRE-compaction
let target    ← Assembly.compileExecutable? certified.target                                          -- compaction happens HERE
```
`certified.target : Assembly.Program` is the **pre-compaction** lowered image `L` (§74's `L`). `Assembly.compileExecutable?` (`EvmCompiler/Assembly/Accepted.lean:371`, `= Assembly.compile?` via `compileExecutable?_eq_compile?`) calls `Compact.compile?` (`Compact.lean:2435`), whose FIRST step is `physicalSource := prepare source` (`Compact.lean:2438`) — `prepare`'s `elideFallthroughJumps` is where §74 proved 100 % of the 22 244 B vein is created (pre-`prepare` canon-saving = **0** on every contract; post-`prepare` = 7430 ASP / 412 ECB / 5798 DynStorage). `compile?_parts` (StackArtifact.lean:79) pins `compileExecutable? certified.target = some target`, and the correctness cone (GasfulBridge*: `GasfulBridgeLayout.lean:477/497/548/582` all key off `artifact.physicalSource.byteLength`) proves the **executable bytecode semantically refines `certified.target`** through a full layout/PC/gas contract — it is NOT a mere `lower?`-output equality; it is an interaction-semantics simulation on the laid-out physical program with byte-exact PC arithmetic.

**Route 1 verdict — the vein-capturing attach point is unreachable without a new frozen-cone cone.**
* The vein exists ONLY in `prepare source`'s output (post-`prepare`, pre-layout). The three candidate non-frozen attach points all fail:
  - **Rewrite `certified.target` (pre-`compileExecutable?`)**: pre-compaction canon-saving = 0 (§74). Captures nothing.
  - **Rewrite `target` (post-`compileExecutable?`, the laid-out `TargetProgram`)**: canonicalising swap runs changes byte lengths ⟹ shifts every PC ⟹ breaks every `PUSH <addr>` jump target ⟹ requires a full re-layout ≈ re-running compaction. Not a pure post-pass.
  - **Rewrite `prepare source` between prepare and layout**: the ONLY point where the vein is present in a re-layoutable form — but `prepare` is called inside `Compact.compile?` (`Assembly/Compact.lean`, mandate-frozen `Assembly/*`). Reaching it means a **non-frozen twin of the entire `Compact.compile?` pipeline** (prepare→alignPreparation?→layout?→emit?→emitBlocks?→GasfulBridge decode/layout/gas), re-proving the layout+PC+gas+decode contract on the canonicalised physical source — a brand-new correctness cone in the compiler's most PC/byte-length-sensitive region, with no existence proof and maximal risk of not closing green.

**Route 2 verdict — attaches at a live green seam, reuses the mature tower, is proven-effective.**
* Attach point = the EXISTING `seamCancelProgramEff` call (StackArtifact.compile?:64 + OIC), already spliced and green since §72. NO new splice, NO new certificate/layout contract, and the no-`Assembly/*` constraint is trivially met (all work at TypedCfg altitude).
* **Existence proof (decisive):** §72's canceller edits at cfg-body altitude, anticipating exactly the refCount-1 non-entry fallthrough merges `elideFallthroughJumps` performs, and its edits DID survive compaction and reduce shipped bytes (ECB 2791→2685, etc.). So cfg-altitude merge-anticipation provably reaches the post-compaction stream. Route 2 generalises this proven-effective mechanism from 2-swap cancellation (`PendingSwap d`, `PeepholeSeamCancel.lean:766` = "s_o one `swap (d+1)` from `SameRuntimeData` to s_c") to full-permutation multi-block chains (`PendingPerm σ`, the §73-named multi-pending invariant).
* **Reuse surface:** the entire `SeamStepRelEff`/`SeamOutcomeRelEff` congruence spine (`PeepholeSeamCancelEffRuntime.lean:198-396`), the fuel bound (`PeepholeSeamCombinedEff.lean:fuelBudget_…`), the OIC/StackArtifact plumbing, AND the banked `ShuffleCanon` permutation algebra (`netStack`/`canonSwaps`/`canonSwaps_length_le`) all carry over; only `PendingSwap d`→`PendingPerm σ` (Prop generalisation) and the chain-threading are new.

**Route-2 open question (composition across ≤240-swap chains) — assessed tractable.** The pending state is a *value* (`σ : List Nat`, a residual permutation), not a proof that grows with chain length; each fallthrough seam updates `σ` by one block's swap contribution and the invariant `PendingPerm σ s_c s_o` is threaded structurally — the same shape as `PendingSwap` but carrying a list. Chain length enters only the fuel/length bookkeeping (`canonSwaps_length_le` already bounds the emitted length), not the invariant's structure. So composition is an induction over the chain, not a per-length special case. (Contrast Route 1, whose byte-length changes ripple through the entire PC/gas layout non-inductively.)

**Chosen: Route 2.** Less proof risk (live seam, reused tower, proven-effective, inductive composition), no frozen-cone exposure. Route 1 captures a strictly-larger vein but only through a new layout/gas cone inside the frozen `Assembly` region — deferred as fallback only if Route 2's chain threading proves intractable.

### FIRST MILESTONE (this session) — the permutation-algebra type-preservation core
Per the §57/§61/§71 pattern (transform/extraction + syntactic + type-preservation FIRST, runtime/certificate AFTER): the single-block `shuffleCanonProgram` (`ShuffleCanon.lean`) has its transform + structural preservation banked (§74) but its **type-preservation is only empirical** ("wellTyped?/lower? preservation empirically confirmed"). That type-preservation core — `type? (.swap d)` transposes `shape.slots` positions `0`↔`d+1` exactly as `applySwap (d+1)`, a swap run threads the shape by its `netStack`, and `canonSwaps` preserves `netStack` (via `starDecompose` realising its target) ⟹ preserves `bodyType?` ⟹ preserves WellTyped/`lower?` — is the reusable crux that BOTH the single-block and the chain (Route 2) transform need. Landed in a new orphan leaf (imported by nobody ⟹ cannot touch axioms).

### WHAT LANDED (green, axiom-clean — commits `8638e436` doc, `52a5eb4e` dictionary, `15da79df` naturality+reduction)
NEW `EvmCompiler/TypedCfg/ShuffleCanonType.lean` (imported by **nobody** ⟹ cannot touch the `compile_correct` cone; `#print axioms` on its theorems ⊆ `[propext, Quot.sound]`). The `type?`/`bodyType?` ⇔ `applySwap`/`applySwaps` permutation-algebra dictionary + the per-run preservation reduction:
1. **`applySwaps`** (`:40`) = fold `applySwap` over a position list (`netStack ps m = applySwaps ps (range m)`, `netStack_eq_applySwaps :55`); `length_applySwap`/`length_applySwaps` (swaps keep length); `applySwaps_append`/`_cons`/`_nil`.
2. **The swap-typing dictionary.** `applySwap_succ_cons` (`:80`): `applySwap (d+1) (top::rest) = slot :: rest.set d top`. **`type?_swap_eq_applySwap`** (`:93`, forward): `type? (.swap d) input = some out ⟹ d<16 ∧ d+1 < slots.length ∧ out = { slots := applySwap (d+1) input.slots, tail := input.tail }` — i.e. swap typing IS the `(0,d+1)` slot transposition, frame `tail` fixed. **`type?_swap_of_lt`** (`:119`, converse definedness).
3. **Run threading.** **`bodyType?_map_swap_eq`** (`:146`, forward): a typed `.swap` run threads slots by `applySwaps (ds.map (·+1))`. **`bodyType?_map_swap_of`** (`:170`, definedness): under a uniform depth/length bound the run types with the `applySwaps` result (swaps preserve length ⟹ the bound self-propagates).
4. **(P2) naturality (PROVED).** `applySwap_map`/`applySwaps_map` (`:200`/`:214`, the transposition action is natural under `List.map`); `range_map_getElem!` (`:221`); `applySwaps_eq_gather` (`:232`, `applySwaps ps xs = (netStack ps xs.length).map (xs[·]!)`); **`applySwaps_congr_of_netStack`** (`:241`): equal `netStack` over the length window ⟹ equal `applySwaps` on any list — the second frontier fact, now GREEN.
5. **The reduction (the milestone).** **`canonSwaps_bodyType?_preserve`** (`:274`): a swap run's `bodyType?` output is preserved by `canonSwaps`, reduced to exactly two explicit `ShuffleCanon`-internal permutation hypotheses — `hNet` (`canonSwaps` preserves the net window permutation) and `hBound` (canonical depths in range). With (P2) discharged, `hNet` in the fired branch is precisely **(P1) `netStack (starDecompose t) t.length = t`** (selection-sort realisability) transported from the decomposition window `maxDepth+1` to the slot window; unfired branch = `rfl`.

### REMAINING FRONTIER (the single pure-permutation fact + the lift)
* **(P1) selection-sort realisability** `netStack (starDecompose target) target.length = target` (`ShuffleCanon.lean:94` comment already flags it "the frontier correctness lemma"). This is the ONLY hard fact left for the single-block type-preservation. It is pure `List Nat` combinatorics (`sortStep`/`sortToId` a selection sort, `starDecompose = (sortToId ·).reverse`), independent of the `Shape` layer. Plus two mechanical supports: (i) the **window-extension** lemma `netStack ps L = netStack ps W`-agreement when all positions `< W ≤ L` (to lift `hNet` from window `maxDepth+1` to `input.slots.length`), and (ii) the **output-range bound** `∀ e ∈ starDecompose t, e < t.length` (to discharge `hBound`, since a run that types caps `maxDepth+1 ≤ input.slots.length`). Discharging P1+(i)+(ii) via `canonSwaps_bodyType?_preserve` upgrades to unconditional per-run preservation.
* **Lift run → body → block → program.** `canonBody` interleaves the per-run rewrite with untouched non-swap instrs (`canonBodyGo`); lift `canonSwaps_bodyType?_preserve` over that structure (induction on `canonBodyGo`, non-swap instrs identical) to `canonBody` preserves `bodyType?`, then `canonBlock` preserves `WellTyped`/`lower?` (bodies-only, `input`/`output`/`term` already preserved structurally §74), then `shuffleCanonProgram` preserves `Program.WellTyped` (the §74 structural lemmas + this body-typing). This is the single-block WellTyped gate — the last piece before the CHAIN transform.

### NEXT-SESSION RECIPE (Route 2, continued)
1. Prove **(P1)** `netStack_starDecompose` in `ShuffleCanonType.lean` (or a sibling): selection-sort round-trip on `List Nat`. Suggested shape: an invariant that after processing positions `n-1..i`, positions `[i, n)` hold their identity values; `starDecompose` reverses `sortToId`, and `netStack` of the reversal undoes the sort. Consider the oracle skill if the sort invariant resists. Add the window-extension (i) and output-range (ii) supports.
2. Discharge `hNet`/`hBound` ⟹ unconditional `canonSwaps_bodyType?_preserve'`; lift to `canonBody`/`canonBlock`/`shuffleCanonProgram` WellTyped preservation (single-block gate closed).
3. THEN build the **chain transform** (the actual vein): identify maximal refCount-1 non-entry fallthrough chains (as §72's canceller already locates its seams — reuse `cleanSrc?`/refCount machinery), concatenate their would-be-merged swap runs, canonicalise the net permutation, and redistribute (all swaps to the chain head, interior blocks emptied — sound because interior entries are unobserved, refCount-1). Generalise `PendingSwap d` → `PendingPerm σ` (a residual `List Nat`) threaded across the chain, porting `SeamStepRelEff`/`SeamOutcomeRelEff`/fuel-bound from `PeepholeSeamCancelEffRuntime.lean`/`PeepholeSeamCombinedEff.lean`. Splice at the EXISTING `seamCancelProgramEff` seam (StackArtifact.compile?:64 + OIC) — no new certificate contract. Measure bytes + double-compile determinism only once it goes live.

### GATES (session 75)
`scripts/opt_harness.sh check` = **OK** (43 public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`). `#print axioms Solidus.compile_correct` / `compile_correct_creation` = `[propext, Classical.choice, Quot.sound]` — UNCHANGED (new leaf imported by nobody). No frozen file touched. No splice ⟹ codegen byte-identical to §72 (corpus −0.43 % shipped state intact) ⟹ no determinism double-compile, no bench re-run.

### Files touched (session 75)
NEW `EvmCompiler/TypedCfg/ShuffleCanonType.lean` (green, imported by nobody); `EvmCompiler/TypedCfg/PEEPHOLE_PROGRESS.md` (this note). No frozen file touched. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`.

## Session-76 update (2026-07-20): **(P1) CLOSED + the entire single-block WellTyped gate CLOSED. The §75 frontier (P1 selection-sort realisability + the two mechanical supports + the discharge of `canonSwaps_bodyType?_preserve`'s two hypotheses + the lift to `canonBody`/`canonBlock`/`shuffleCanonProgram`) is fully proved green and axiom-clean.** Route-2 is now: everything at cfg-body altitude for the *single-block* shuffle canonicaliser is verified; the only remaining work before a live splice is the **chain transform** (multi-block `PendingPerm σ`) — NOT started this session, documented as the sharpened frontier below. New leaf `EvmCompiler/TypedCfg/ShuffleCanonPerm.lean` (imported by nobody ⟹ cannot touch the `compile_correct` cone). `scripts/opt_harness.sh check` = **OK** (43 theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`); `compile_correct`/`compile_correct_creation` = `[propext, Classical.choice, Quot.sound]` UNCHANGED. No frozen file touched. No splice (still no live byte delta — the chain transform is what fires).

### THE (P1) CORRECTION (measure, don't assume — the §70-73 lesson again)
`ShuffleCanon.lean:94` flagged `netStack (starDecompose t) t.length = t` as "the frontier correctness lemma" for **arbitrary** `t`. A decisive numeric probe (`scratch model.py` over all perms n≤7 + the `[0,0]` witness) proved it **FALSE in general**: `t = [0,0]` gives `netStack (starDecompose [0,0]) 2 = [1,0] ≠ [0,0]`. It holds **exactly for permutations of `range t.length`** — which is always the case at the one call site, where `starDecompose` is applied to `netStack ps (maxDepth ps + 1)`, a permutation of `range` of its own length by construction. So the banked lemma carries that hypothesis and is fed by `netStack_perm_range`.

### WHAT LANDED (green, axiom-clean) — `EvmCompiler/TypedCfg/ShuffleCanonPerm.lean` (815 lines)
**Inverse structure + permutation preservation**
* `getElem?_applySwap` (`:60`) — `applySwap k` reindexes by the involution `swapIdx k` (transpose `0`↔`k`) on the active window; `applySwap_involutive` (`:89`), `applySwaps_reverse_cancel` (`:172`, reversed run = inverse), `applySwap_perm` (`:143`, multiset preservation via `List.count_set`).

**(P1) selection-sort realisability**
* `sortFoldr_inv` (`:255`) — the combinatorial core: a **downward `foldr` invariant** ("processed suffix `[k,n)` already in place") over `range' k m` (`k+m=n`), carrying length=n, `Perm … (range n)`, `working = applySwaps acc b0`, the suffix-in-place claim, AND (5th conjunct, session-76) every accumulated swap position ∈ `[1,n)` (needs the perm to know `findIdx k < n`).
* `sortToId_correct` (`:393`) — `applySwaps (sortToId t) t = range t.length` (perm input), via the invariant + nodup at position 0.
* **`netStack_starDecompose_of_perm` (`:449`) = (P1)** — `netStack (starDecompose t) t.length = t` for `t ~ range t.length`, via `sortToId_correct` + `applySwaps_reverse_cancel` (the inverse trick avoids reasoning about `starDecompose` directly).
* `netStack_perm_range` (`:464`), `netStack_length` — feed P1 at the call site.

**The two mechanical supports (§75 (i)/(ii))**
* `starDecompose_elem_bounds` (`:489`) — canonical positions ∈ `[1, t.length)` (from the 5th invariant conjunct via `sortToId_elem_bounds`).
* `mem_le_maxDepth` (`:517`, + `foldl_max_le`/`maxDepth_le` `:610`).
* window-extension: `applySwap_append_left` → `applySwaps_append_left` → `range_split` → `netStack_window_extend` (`:561`) → **`netStack_congr_window` (`:570`)** — equal `netStack` over window `W` ⟹ equal over any wider `L` (positions `< W ≤ L`; the tail `range' W (L-W)` is identity-fixed).
* `bodyType?_map_swap_bound` (`:578`) — a typed `.swap` run bounds every depth (`< 16`, in range), lengths preserved.

**The discharge + the single-block gate**
* **`canonSwaps_bodyType?_preserve_uncond` (`:619`)** — discharges BOTH `hNet` and `hBound` of `ShuffleCanonType.canonSwaps_bodyType?_preserve`; **no side hypotheses**. Fired branch: `W = maxDepth(r.map(·+1))+1 ≤ 17` (depths `< 16`) and `W ≤ input.slots.length`, canon depths land in `[0,16)`, net window permutation preserved by P1 and lifted `L≥W` by `netStack_congr_window`; `(c.map(·-1)).map(·+1)=c` (canon positions `≥ 1`). Unfired: identity.
* `canonBodyGo_bodyType?_preserve`/`canonBody_bodyType?_preserve` (`:763`) — lift over interleaved swap-runs + non-swap instrs (`bodyType?_append` + `swapDepth?_eq_some`).
* `labelShape?_shuffleCanonProgram` (`:773`)/`term_type?_shuffleCanonProgram` (`:780`) — terminator typing is invariant under the canonicalisation (it reads `.input`, preserved by `canonBlock` §74).
* `canonBlock_WellTyped` (`:787`), **`shuffleCanonProgram_WellTyped` (`:800`)** — the **single-block WellTyped gate**: `program.WellTyped → (shuffleCanonProgram program).WellTyped`, combining the §74 structural lemmas (LabelsUnique/entry/EmittedLabelsUnique) with the new body-typing + terminator invariance.

### SHARPENED FRONTIER — the CHAIN transform (the actual live vein; not started)
The single-block canonicaliser (`shuffleCanonProgram`) is now fully WellTyped-verified but fires on **nothing in the real corpus** (§74: every emitted run is one block's body, already minimal PRE-compaction; the 22k-byte vein is created by `Compact.prepare`'s fallthrough merges). The payoff needs the **chain** transform that anticipates those merges at cfg altitude (§75 Route 2, the §72 canceller generalised from `PendingSwap d` to `PendingPerm σ`). Remaining, in order:
1. **Chain identification** — reuse §72's refCount-1 non-entry fallthrough-chain locator (`cleanSrc?`/refCount machinery in `PeepholeSeamCancel*`). Bank the pure def + a `WellTyped`-preservation proof of the *static* rewrite (concatenate each chain's would-be-merged swap runs, canonicalise the net permutation via the now-verified `canonSwaps`, redistribute all swaps to the chain head / empty interior blocks — sound because refCount-1 interior entries are unobserved). The banked single-block lemmas (`canonSwaps_bodyType?_preserve_uncond`, the `applySwaps`/`netStack` algebra) carry over verbatim; the new content is only the block-concatenation typing (compose `bodyType?_append` across the chain).
2. **`PendingPerm σ` runtime invariant** — generalise `PeepholeSeamCancelEffRuntime.lean`'s `SeamStepRelEff`/`SeamOutcomeRelEff` congruence + `PeepholeSeamCombinedEff.lean` fuel bound from a single `swap (d+1)` residual to a residual list `σ : List Nat` (birth accumulates each block's net permutation; resync applies `canonSwaps` at the chain end). Composition is an induction over the chain (σ is a *value*, not a proof that grows) — `canonSwaps_length_le` already bounds emitted length.
3. **Splice** at the EXISTING `seamCancelProgramEff` seam (`StackArtifact.compile?:64` + OIC) — no new certificate/layout contract. Only then measure bytes + double-compile determinism.

### NEXT-SESSION RECIPE
1. Read this note + §74/§75. The single-block gate is DONE — do not redo it; import `ShuffleCanonPerm` and reuse `canonSwaps_bodyType?_preserve_uncond` + the `applySwaps`/`netStack`/`netStack_congr_window` algebra.
2. Build the chain **static** prefix first (identification + block-concatenation `WellTyped` preservation), banking it green as an orphan leaf, BEFORE any runtime bisimulation — same discipline as §57/§61/§71 (transform + syntactic + type-preservation FIRST).
3. Then port the `PendingSwap d → PendingPerm σ` runtime tower; splice; measure. Consider the oracle skill only if the `PendingPerm` composition induction resists.

### GATES (session 76)
`scripts/opt_harness.sh check` = **OK** (43 public theorems; axioms ⊆ `[propext, Classical.choice, Quot.sound]`). `#print axioms` on `Solidus.compile_correct` / `compile_correct_creation` = `[propext, Classical.choice, Quot.sound]` — UNCHANGED (new leaf imported by nobody). No frozen file touched. No splice ⟹ codegen byte-identical to §72 (corpus −0.43% shipped state intact) ⟹ no determinism double-compile, no bench re-run.

### Files touched (session 76)
NEW `EvmCompiler/TypedCfg/ShuffleCanonPerm.lean` (green, imported by nobody); `EvmCompiler/TypedCfg/PEEPHOLE_PROGRESS.md` (this note). No frozen file touched. `compile_correct`/`compile_correct_creation` axioms UNCHANGED = `[propext, Classical.choice, Quot.sound]`. Commits: `80e1805b` (P1), `d3e37591` (acc-bounds), `b0f94181` (supports), `4df73d5e` (unconditional discharge), `3f383094` (single-block WellTyped gate).

