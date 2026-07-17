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
