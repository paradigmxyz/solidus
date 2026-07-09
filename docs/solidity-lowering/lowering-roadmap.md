# Lowering roadmap: layer semantics → compilers → preservation statements

Status: roadmap, 2026-07-09 (moved from the source repo; planning now lives
here in `evm-compiler/docs/solidity-lowering/`). **Naming**: "solidity-lean"
is the source-semantics project (`../solidity-lean`, formerly
solid-core-spine); "the backend" is this repo's existing verified Yul→EVM
tower (Solidus). This repo pins solidity-lean as its topmost source language
the same way it pins EVMYulLean for the EVM/Yul semantics; solidity-lean
itself contains no compiler code.

Executes the plan converged in `compile-to-yul-readiness.md` (§3 tower),
`memory-layer-design.md` (Sm/Sx design, both in this folder), and the
executable-first strategy: **definitions and compilers first,
corpus-validated; proofs after, against pinned statements.** This document
covers stages 0–5 (through placeholder theorem statements); the proof
campaign is stage 6, sketched at the end, with its own future roadmap.

Method notes that govern everything below:
- Every layer gets its **own syntax and its own independent interpreter**
  returning `SolI`-style interaction trees over the shared frozen
  `Query`/`Answer` alphabet. "Lower it and run the layer below" is never a
  semantics.
- **Placeholder theorems are `Prop`-valued statement definitions, not
  `sorry`ed theorems.** `def SkPreservation : Prop := …` elaborates and
  type-checks the statement (catching vocabulary/quantifier errors now)
  while keeping the build sorry-free; the proof phase later supplies
  `theorem sk_preservation : SkPreservation`. CI can then honestly enforce
  "no `sorry` anywhere" from day one.
- Corpus replay (solidity-lean's 98 paired Forge cases + scripted
  responders) is the merge gate for every executable step:
  transcript-identical queries, related final state, byte-identical outputs.
- The tower lives in this repo beside the backend. The challenge-frozen
  files (`benchmarks/frozen_manifest.txt`) and `../evm-interaction` are
  never edited; `../solidity-lean` is consumed as a pinned, read-only
  dependency (its only lowering-era changes are the Stage-0 items, which are
  source-semantics work).

Layer names used throughout (top-down; seams in parentheses):

| Layer | Name        | Abstraction it still has (removed by the seam below it) |
| ----- | ----------- | -------------------------------------------------------- |
| L5    | source      | = `CoreContract` + solidity-lean's interpreter (unchanged) |
| —Sd—  |             | contract-as-callable: selector dispatch, ABI entry, creation |
| L4    | `Functions` | internal-function boundary, framed calls, fn pointers     |
| —Sc—  |             | calling convention → Yul functions/`leave`                |
| L3    | `MemValues` | structural values + object-heap memory + typed ABI codec  |
| —Sm/Sx— |           | aggregates → flat bytes + FMP; codec → byte writes        |
| L2    | `TypedStorage` | typed storage paths (mappings/arrays/packing)          |
| —Sy—  |             | paths → slot arithmetic via materialized `E`              |
| L1    | `WordIR`    | Solidity statement forms over pure Yul representation     |
| —Sk—  |             | near-1:1 syntax map to `EvmYul.Yul.Ast` objects           |
| Yul   | (frozen)    | the backend's (Solidus's) source; everything below is inherited |

---

## Stage 0 — Source-semantics prerequisites (in solidity-lean, before any lowering code)

0.1 **Close the M4-family residue** surfaced by the memory study
    (`docs/memory-layer-design.md` §5): deep-deref for `emit`/custom-error
    encoders; `assignTupleNested` ref-preserving walk; `bytes(string)`
    reinterpret as a ref-preserving RHS shape. Each with paired Forge lanes.
    (Coordinate with the gap-hunt agent; these are its lane.)
0.2 **Gap-hunt convergence**: divergence rounds reach zero non-intentional
    residue; full replay gate green (per the standing policy).
0.3 **`checkedExp` closed form** (hinder-E): replace the O(exponent) loop
    with a closed form / `UInt256.exp`-shaped definition, corpus-pinned.
0.4 **P1 — materialize the storage-layout encoding `E`** as a standalone
    spec-owned `CoreContract → (storage path → slot/packing)` function that
    the interpreter itself uses (per-access path proved equal later, in Sy).
    This is the first compiler artifact and Sy's input; do it here where the
    corpus can arbitrate behavior-preservation.
0.5 **Phase 6 freeze** (ROADMAP.md): docs, boundary restatement, corpus
    freeze, and hash-pinning of the public surface (`Interpreter.lean`
    public entry points, `Checked.lean` tree entries, `Interaction.lean`) —
    solidity-lean graduates to frozen-spec status, the left-hand vocabulary of
    the crown.

Gate: full replay green; freeze manifest in place; `E` landed with
behavior-preservation validated by the corpus.

## Stage 1 — Scaffold in this repo + dependency architecture + crown statement

1.1 **Home**: a new `lean_lib SolidityCompiler` in this repo (module root
    `SolidityCompiler/`, kept apart from the frozen `EvmCompiler` lib), with
    `require solidity-lean` added to the lakefile as a pinned dependency —
    the same pattern as the EVMYulLean pin. The backend's theorems
    (`compile_correct`, `ForwardRel.trans`) are then ordinary imports.
    Nothing in `benchmarks/frozen_manifest.txt` changes.
1.2 **Alphabet single-sourcing (hard prerequisite).** Both sides currently
    declare the module `EvmCompiler.Simulation.*` — this repo owns the
    frozen originals; solidity-lean re-exports the byte-identical
    `../evm-interaction` extraction. Lake cannot load both: adding the
    solidity-lean dependency collides until this repo itself adopts
    `evm-interaction` as the single source (deleting its local copies) —
    the switch already anticipated by the extraction plan, gated on the
    next challenge freeze rev. Sequence Stage 1 to land at (or just after)
    that rev; nothing else in this roadmap can build before it.
1.3 **Primitive unification (keccak).** Words are already shared
    definitionally (`EvmYul.UInt256`-lifted ops on both sides). Keccak is
    not: EVMYulLean's `ffi.keccak256` is `opaque @[extern]` (nothing is
    provable about it), so solidity-lean keeps a repo-owned pure Keccak-256
    with only a runtime byte-parity witness (`lake exe keccakParity`).
    Plan: (interim) seam/crown statements carry one named hypothesis
    `hKec : SourceKeccak = ffi.KEC` (pointwise) — the honest
    trusted-primitive bridge, runtime-validated, no wider than the trust
    already placed in the extern; (permanent) in the `danrobinson/EVMYulLean`
    fork, replace `opaque keccak256` with a `def` whose body is the pure
    Keccak-256 (relocate solidity-lean's implementation or the package's
    own `SpongeHash`) with `@[extern]`/`implemented_by` acceleration, bump
    the pin on both sides at the same freeze rev as 1.2, and the hypothesis
    dissolves into a pure-vs-pure theorem (or `rfl` if both use the same
    def). Until then, `hKec` is a recorded fundamental premise, not debt to
    hide.
1.4 **CI from day one**: `lake build` of the new lib; a
    `SolidityCompiler/Verification.lean` root that imports every statement
    module and (once proofs exist) runs `#print axioms`; a
    no-`sorry`/no-new-`axiom` scan scoped to the new lib; pin checks for
    solidity-lean.
1.5 **Seam vocabulary module** (`SolidityCompiler/Seam.lean`): the shared
    truncation predicate (source `outOfFuel` ↔ the backend's `Truncated`), the
    top done-relation (code-erased `OpenWorld` + exact output/revert bytes +
    log entries — the Sd relation), and the initial-state relation over
    public data. Re-export, never redefine, the alphabet.
1.6 **Crown statement** (`SolidityCompiler/Correctness.lean`,
    statement-only): `def CompilerCorrect : Prop` in spec vocabulary —
    checked source program + `solidityCompile? = some bytes` +
    initial-state relation ⇒ the `Checked.lean` tree run `ForwardRel`-refines
    the open bytecode run (via the backend theorems), truncation = source `outOfFuel`.
    Resolve the two recorded transcript residues **in the statement now**:
    creation (`initCode`) in or out of the v1 crown; `requestedGas`
    quantified or discharged. Theorem-truth review of this Prop is a Stage-1
    deliverable.

Gate: the new lib builds with the solidity-lean pin (post-1.2 rev);
`CompilerCorrect` elaborates; statement reviewed against `compile_correct`'s
actual shape; the `hKec` premise recorded.

## Stage 2 — Substrates (shared modules the layers consume)

2.1 **Flat memory substrate** (`SolidityCompiler/Mem/`): byte memory +
    FMP model mirroring EvmYulLean's memory ops; allocator operations that
    are definitionally the Yul util-function bodies (`allocate_memory`,
    `finalize_allocation` with the 2^64 Panic 0x41, `round_up_to_mul_of_32`,
    zero-fill via the calldatacopy trick, word/byte copy, `mcopy`).
    Per-type layout functions (`memoryHeadSize`, stride, data-area offset)
    per `docs/memory-layer-design.md` §1.
2.2 **Storage slot substrate**: import `E` from Stage 0.4; slot-arithmetic
    helpers (mapping keccak, array data slots, packed bit-ranges) shared by
    L1/L2 semantics and the Sy compiler.
2.3 **Yul emission utilities**: builders over the pinned `EvmYul.Yul.Ast`
    (object skeleton, dispatcher `switch`, the runtime-function catalog we
    emit — allocation, cleanup, checked-arith snippets, copy loops —
    solc-shaped per the memory study, minus the P1-excluded warts).
2.4 **Witness harness adapter**: a small runner that executes any layer's
    interpreter against the existing scripted responders + manifest
    fixtures, so every layer replays the corpus with zero per-layer harness
    work. (This is infrastructure, not new coverage — the corpus stays
    frozen.)

Gate: substrates build; memory substrate unit-witnessed against hand cases
(allocation alignment, 0x41 boundary, zero-fill, bytes padding).

## Stage 3 — Layer semantics, top-down (L4 → L1)

Each layer directory gets `Syntax.lean`, `Semantics.lean` (independent
interaction-tree interpreter), `WF.lean`, `Witness.lean` (hand cases for the
layer's distinctive behaviors). Top-down order so each definition is a
controlled delta of the one above it, and so Stage 4's compilers can
corpus-replay immediately as they land.

3.1 **L4 `Functions`**: source core minus the contract-as-callable
    abstraction — a function table + framed calls (`internalCall`/
    `internalCallPtr` survive), explicit entry wrappers replaced by direct
    function invocation; values/storage/memory as at L5. Distinctive
    semantics to pin: dispatch-ID pointer calls, named-return zero-init,
    early return.
3.2 **L3 `MemValues`**: L4 minus the function-boundary abstraction (bodies
    are Yul-function-shaped: params/rets/`leave`-style control), still with
    structural values, the object heap, and the typed ABI codec.
3.3 **L2 `TypedStorage`**: L3 with aggregates/memory lowered onto the
    Stage-2.1 flat-byte substrate (FMP allocator live here, incl. the
    cumulative 0x41), codec over bytes; storage still typed paths.
3.4 **L1 `WordIR`**: L2 with storage paths lowered to slot words via `E`.
    Everything is words/bytes/slots; only Solidity statement forms and the
    six-way `Result` remain above Yul.

Note the semantic deltas are cumulative by construction: L2 and L1 share the
memory substrate; L1 additionally owns the `AllocationBound`-relevant
allocator state. Each layer is corpus-*unreachable* until Stage 4 gives it a
compiler from above — Stage 3's gate is witnesses, not replay.

Gate per layer: builds; witnesses green; a short written note of the layer's
WF predicate and what it rejects (no proof-convenience narrowing).

## Stage 4 — Compilers, top-down, corpus-gated at every step

Executable lowerings, each fail-closed (`… → Option Lower.Program`), each
landing with a **differential gate**: run the corpus at the layer above and
below the new seam; compare query transcripts exactly and final states under
the seam's (informal, executable) done-check. This is where design errors
die cheaply.

4.1 **Sd: source → L4** (`Compile/Dispatch.lean`): selector table →
    dispatcher; ABI entry wrappers (decode args / encode returns+reverts);
    receive/fallback; constructor → creation path. Gate: full corpus runs on
    L4 with identical transcripts/outputs vs the source interpreter.
4.2 **Sc: L4 → L3** (`Compile/Functions.lean`): internal functions → Yul
    functions; early return → `leave`; pointer calls → internal-dispatch
    switch. Gate: corpus on L3.
4.3 **Sm/Sx: L3 → L2** (`Compile/Memory.lean`): the memory-design plan
    (`docs/memory-layer-design.md` §4) — allocation sites, alias ops as
    pointer moves, cross-location copy loops, codec over bytes, `0x60`
    empty-array rule. Gate: corpus on L2 (the highest-risk gate in the whole
    program; budget for iteration here).
4.4 **Sy: L2 → L1** (`Compile/Storage.lean`): apply `E`; packed bit-range
    read/writes; bytes/string short-long forms already handled at word
    level. Gate: corpus on L1.
4.5 **Sk: L1 → Yul** (`Compile/Word.lean`): the near-1:1 map onto
    `EvmYul.Yul.Ast` using the Stage-2.3 catalog. Gates, in order:
    (a) corpus on the emitted Yul **under the backend's frozen Yul
    interpreter** (the strongest oracle in the project);
    (b) feed emitted Yul objects to `Solidus.compile?` and record the
    fail-closed rate (expect stack-headroom failures — this measures the
    deferred spill-pass need, `compile-to-yul-readiness.md` deferred items);
    (c) where `compile?` succeeds, full-stack differential: bytecode run
    (the backend's bridge runners) vs source interpreter vs Forge.
4.6 **`solidityCompile?`**: the composed fail-closed pipeline
    `Sd ∘ Sc ∘ SmSx ∘ Sy ∘ Sk` (+ later the spill pass), the function named
    by the crown statement.

Gate for the stage: end-to-end pipeline compiles the corpus (minus recorded
headroom failures); all differentials green; a written ledger of every
fixture that fails closed and why.

## Stage 5 — Placeholder preservation statements

One `Statements.lean` per seam (elaborated `Prop` definitions, no proofs,
no `sorry`), plus the crown from Stage 1 revisited against the now-real
definitions. Shapes (schematic — exact binders fixed here, in this stage):

```lean
-- Sk (L1 → Yul), the template all seams follow:
def SkPreservation : Prop :=
  ∀ (p : WordIR.Program), WordIR.WF p →
  ∀ (yul : Yul.Program), Sk.compile? p = some yul →
  ∀ (ctx : Ctx) (s : WordIR.State) (t : Yul.State),
    SkStateRel p s t →
  ∀ (fuel : Nat),
    ∃ yulFuel,
      Simulation.Interaction.ForwardRel
        SkTruncated SkDoneRel
        (WordIR.run fuel ctx p s)
        (Yul.exec yulFuel ctx yul t)
```

- `SyPreservation`, `SmSxPreservation`, `ScPreservation`, `SdPreservation`:
  same shape with their own `StateRel`/`DoneRel`; the done-relations grow
  more concrete downward (Sd: observable-only; Sm: adds the σ/`Repr` memory
  invariant *inside* `StateRel`, never in the conclusion; Sy: storage words
  under `E`). `SmSxPreservation` additionally carries the explicit
  source-facing `AllocationBound run` premise (memory-design P4), with its
  planned gasful-layer elimination recorded in the docstring.
- `ScPreservation` is stated over the call graph via plain quantification on
  source fuel (the induction is the proof's business, not the statement's);
  the modifiers-inlined fragment is named in its docstring.
- **Composition statement**: `def TowerComposes : Prop :=` the five seams +
  `compile_correct` chain via `ForwardRel.trans` into `CompilerCorrect` —
  stated as an implication from the five seam Props + `compile_correct`, so
  the trans side-conditions (`hReflect`, discharged by solidity-lean's
  fuel-monotonicity theorems) are checked to line up *now*.
- **Statement audit**: for each Prop, a recorded theorem-truth pass
  (counterexample hunt: fuel-zero, truncation direction, `requestedGas`/
  initCode residues, allocation bound, creation vs runtime code) and a
  spec-vocabulary check (no compiler-internal names in `CompilerCorrect`;
  seam Props may use layer vocabulary — they are internal).

Gate: everything elaborates; `TowerComposes` type-checks the whole chain;
audit notes written; CI enforcing no-`sorry` still green (trivially — there
are no proofs yet).

## Stage 6 (future, own roadmap) — the proof campaign

Bottom-up, target-up: Sk → Sy → Sm/Sx → Sc → Sd, each seam's theorem
`… : SkPreservation` etc. landed with its layer-audit gate, then
`TowerComposes` discharged, then the escape-elimination campaign
(`AllocationBound` via the gasful layer; headroom via the spill pass when
built). Expected cost ordering per the revised ranking: Sm/Sx ≫ Sc >
Sd > Sy > Sk. Instruments already in hand: fuel monotonicity (landed on
main, `SolidCore/Solidity/FuelMonotonicity.lean`), `E` (Stage 0.4),
`ForwardRel` lemma kit (frozen dep).

---

## Sequencing summary

```
Stage 0  source fixes + E + freeze          (solidity-lean; gap-hunt coordination)
Stage 1  scaffold + crown statement         (new project; statement-first)
Stage 2  substrates: memory, slots, Yul emission, harness adapter
Stage 3  layer semantics  L4 → L3 → L2 → L1 (witness-gated)
Stage 4  compilers        Sd → Sc → Sm/Sx → Sy → Sk (corpus-gated, then
         Yul-interpreter + compile? + full-stack differentials)
Stage 5  statement modules per seam + TowerComposes + audits
Stage 6  proofs, bottom-up (future roadmap)
```

Definitions and compilers flow **top-down** (each layer is a small delta of
the one above; every compiler step immediately inherits the full corpus as
its oracle). Proofs flow **bottom-up** (target-up doctrine; every verified
layer rests on a verified floor). The placeholder-statement stage sits
between, so the proof campaign starts against pinned, audited,
corpus-exercised interfaces.
