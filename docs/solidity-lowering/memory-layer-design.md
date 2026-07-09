# Sm/Sx memory-layer design study: solc's memory model and the L3→L2 lowering

Status: design study, 2026-07-08. Inputs: (a) solc 0.8.35 via-IR codegen read
against `/Users/dan/Projects/solidity-src` @ `47b9dedd` (anchors below cite
that tree); (b) the interpreter's heap model in
`SolidCore/Solidity/Interpreter.lean` post M1–M4; (c) the prior reviews
`docs/solc-memory-semantics-review{,-2}.md`. Companion to
`docs/compile-to-yul-readiness.md` §3 (layers Sm/Sx = the L3→L2 seam).

---

## 1. The target model: what solc's emitted Yul actually implements

Verified facts a formalization builds on (anchors in `libsolidity/codegen/`):

**Memory map.** Scratch `0x00–0x3f`; free-memory pointer (FMP) word at `0x40`;
zero slot at `0x60` (never written; the shared representation of every
*default* empty dynamic array, `zeroValueFunction`); allocations from `0x80`
(`CompilerUtils.cpp:46-48`). FMP initialized once per frame to
`memoryguard(0x80 + reservedImmutables)` (`IRGenerator.cpp:1132-1149`);
creation code reserves static slots for immutables.

**Allocator.** Bump-only: `allocate_memory = mload(0x40)` +
`finalize_allocation(ptr, size)` which rounds `size` up to a multiple of 32
and panics **0x41** if the new FMP exceeds `0xffffffffffffffff` or wraps
(`YulUtilFunctions.cpp:3224-3274`). `arrayAllocationSizeFunction` also panics
0x41 on `length > 2^64-1` (this per-allocation check is the one our
interpreter already models, `Context.checkMemoryAllocation`). Memory is never
freed; the FMP never decreases — with one sanctioned wart:
`abi.encodeWithSignature` with a non-literal signature checkpoints and resets
the FMP (`IRGeneratorForStatements.cpp:~1278-1296`).

**Per-type layout** (documented language spec, "Layout in Memory"):
- value types: one full 32-byte word, **cleaned before write**
  (`writeToMemoryFunction:3063`) and **cleaned again on read**
  (`readFromMemoryOrCalldata:4522` — memory may be dirty via assembly);
- static arrays: `n` consecutive head words, **no length word**;
- dynamic arrays: length word + `n` head words;
- reference-typed elements/members: **pointer words** into other objects;
- `bytes`/`string`: length word + tightly packed data, allocation padded to
  a word boundary;
- structs: exactly one word per non-mapping member
  (`Types.cpp:2306-2312`);
- external function values: one left-aligned word
  `shl64(or(shl32(addr), selector))`.

**Reference semantics.** Memory→memory assignment/conversion is a **pointer
copy** (`arrayConversionFunction`, struct conversion: `converted := value`);
member/index access is pointer arithmetic; aliasing is unrestricted. Deep
copies happen only across locations: storage→memory
(`copyArrayFromStorageToMemoryFunction:2611`), calldata→memory (the ABI
decoder), memory→storage (`copyArrayToStorageFunction`). `new T[](n)`
allocates and zero-initializes (zeroing via the
`calldatacopy(dst, calldatasize(), n)` trick, or per-slot fresh default
objects for reference elements); array literals allocate without zeroing and
write each element; string literals are materialized by constant `mstore`s.

**Transient (unfinalized) use above the FMP is routine.** External-call
argument encoding + return staging, event data for `logN`, packed hashing for
dynamic mapping keys, revert payload encoding, and forwarding reverts all
write at `allocate_unbounded()` without finalizing
(`IRGeneratorForStatements.cpp:2655-2833`, `:1073-1136`;
`YulUtilFunctions.cpp:~4110-4145`, `~230-300`). Small value-only error
payloads are even encoded at offset **0**, spanning the FMP/zero slots,
immediately before `revert`. try/catch's `tryDecodeErrorMessage` finalizes an
allocation but returns an **interior pointer** and can leave dirty bytes above
the new FMP.

**Invariants that hold (and their caveats):** FMP ≥ 0x80, 32-aligned,
monotone modulo the one wart; finalized allocations are pairwise disjoint;
`0x60` is never written; fresh memory is *not* guaranteed zero except via the
initializing allocators; region above the FMP must be modeled as scratch, not
zeros; emitted IR never reads `msize`.

## 2. The source model: what L3 must relate (post M1–M4)

The interpreter heap is `Runtime.memory : Std.HashMap Nat Value` with
monotonic never-freed ids (`allocMemory`), `Value.memoryRef id` pointers, and
**ref-nesting**: aggregates stored in memory have each reference-typed
element replaced by its own fresh cell (`memoryStoredValue`), i.e. the heap is
a pointer graph that already mirrors solc's array-of-pointers layout. After
M1–M4: memory→memory assignment/tuple-destructuring/element-store all
**alias** (`wantsMemoryRefRhs` + `memoryRefOrValue…` + `memoryStoreValue`
pass-through); storage/calldata↔memory are deep copies;
`abi.encode*`/`keccak256` deep-deref before encoding
(`derefMemoryValueDeep`). Scalars stay inline; `bytes`/`string` are
`List Byte` values; calldata refs are inline immutable trees with lazy
validators (no ids). Memory is **not observable**: `State` carries no heap;
memory reaches the boundary only as ABI-encoded bytes (returns, event data,
revert payloads, call arguments) and keccak inputs.

Alignment luck that is not luck: the M1–M4 alias fixes are **load-bearing for
the lowering** — before them the source deep-copied where the target
pointer-copies, which is only observationally equal absent mutation. With
them, source aliasing (shared ids) and target aliasing (shared addresses) are
structurally parallel, and the relation below is a near-homomorphism.

## 3. Design principles for the Sm/Sx layer

**P1 — The layout is spec; solc's codegen warts are not.** Solidity's memory
layout (FMP discipline, per-type encodings, 0x41) is documented language spec
and becomes spec vocabulary for the layer. But we are building a compiler,
not replicating solc's: our emitted Yul must refine *our source semantics*,
not reproduce solc's memory traffic. We therefore **do not** reproduce the
`encodeWithSignature` FMP-reset, the offset-0 revert encoding, or the
interior-pointer try/catch shape — plain allocations behave observably
identically and are far cheaper to verify. (The *source semantics* must match
solc — that is the repo's standing mission and the divergence hunt's job; the
*emitted code* need only match the source semantics.)

**P2 — Memory never appears in a public relation.** Since source memory is
boundary-invisible and `Query`/`OpenWorld` carry no memory, the Sm done- and
seam-relations constrain only: storage words, transcript bytes (calldata,
initCode), output/revert bytes, log entries, and keccak arguments. Yul-side
final memory is existentially quantified at our seam (the backend's own crown
constrains it further down). The heap↔bytes correspondence is **internal
simulation machinery**: one named invariant, never a theorem premise a reader
sees.

**P3 — The invariant: allocation map + per-type representation.** The
simulation state relation carries a partial map `σ : Id ⇀ Addr` and, per
live id, `Repr σ mem ty v addr` stating the cell's value is laid out at
`addr` per §1's per-type layout, pointer fields relating through `σ`.
Requirements:
- `σ` maps distinct ids to **disjoint, below-FMP** regions (mirrors bump
  allocation; justifies frame-local mutation), with the one exception that
  ids of *empty dynamic arrays* may map to `0x60` — soundness argument:
  no write path exists through a zero-length array (length is immutable in
  memory, element writes are OOB-panicked), and `0x60` is never written.
- FMP ≥ 0x80, 32-aligned, monotone; everything **above** the FMP is
  unconstrained scratch (this absorbs call staging, event encoding, packed
  hashing on the target side).
- "Clean after typed write": `Repr` for value types asserts the stored word
  is cleanup-normal; the target's read-side cleanup makes dirty-memory
  concerns local to the assembly boundary (out of scope) and the bytes-array
  padding (unobservable — length-bounded reads).
- Source-side monotone ids ↔ target-side monotone FMP: allocation order is
  deterministic on both sides, so `σ` extends monotonically; no reuse on
  either side.

**P4 — The one theorem-truth landmine: cumulative-allocation Panic(0x41).**
Our source models the *per-allocation* `length > 2^64-1` panic but has no
cumulative allocator, so a gasless source run can succeed where the target's
`finalize_allocation` would panic 0x41 (FMP past `2^64`) — and 0x41 is an
ordinary observable revert, not an escape frame. Resolution, in the solidity-lean
escape-elimination style: state the adjacent theorem with an explicit
source-facing premise `AllocationBound run` ("the run's total rounded
allocation stays below `2^64`") — computable from the source run since
allocation is deterministic — and plan its **elimination at the gasful
layer**: real gas bounds memory expansion to a few million words, so the
gasful crown discharges the premise for every gas-bounded execution, exactly
as gas kills the other resource escapes. Do **not** silently add a cumulative
allocator to the top-level source semantics now (it would be dead weight at
L5 and unreachable for the corpus); the counter lives in L2's semantics where
it is the allocator.

**P5 — Sx rides on Sm as "encoder = byte-writes".** The ABI codec layer's
obligation is: our `List Byte` spec encoders (`encodeValues?`, event
encoding, `encodeRevertData?`) equal the byte effect of the emitted Yul's
encode loops on the L2 memory model, at the region the transcript/output
reads. That single lemma family discharges dispatch calldata, returns, event
data, revert payloads, and external-call arguments all at once — which is why
Sm and Sx land as one layer (L3→L2) with the codec proved after the
representation predicate stabilizes.

## 4. The L2 semantics and the lowering, concretely

**L2 memory substrate.** Flat bytes + FMP, mirroring EvmYulLean's memory so
the L1→Yul hop stays trivial: `mload/mstore/mstore8/mcopy/keccak(ptr,len)`
plus allocator operations that are definitionally the Yul util-function
bodies (`allocate_memory`, `finalize_allocation`, `round_up_to_mul_of_32`,
zero-fill, copy). Emit the same *runtime-function shapes* solc emits
(allocation, per-type copy/zero/encode helpers) so differential testing
against real solc Yul output stays meaningful — but generated by us, minus
the P1 warts.

**Lowering of operations** (source op → L2 code, each with one lemma):
- alloc/`new`/literals → `allocate` (+ zero-init per §1 for `new`, none for
  literals which fully initialize);
- alias ops (assignment, destructuring, element store of refs, ref-passing
  internal-call args/returns) → pointer word moves; the M1–M4 parallelism
  makes these the *easy* cases;
- deep copies (storage→memory, calldata→memory decode, memory→storage) →
  the copy loops; these are the volume of the per-type proof work;
- `derefMemoryValueDeep` at encode/keccak sites → nothing (the target reads
  through pointers natively); the deep-deref is pure source-side machinery
  the relation absorbs;
- `delete` → default-store per layout; empty dynamic arrays may take the
  `0x60` representation.

**Staging inside the layer** (each step corpus-replayed L3-vs-L2 by
transcript + related final state before the next):
1. substrate + allocator + `Repr` for value types and `bytes`/`string`;
   keccak and the byte paths first (smallest layouts, immediately exercised
   by hash-heavy corpus cases);
2. dynamic/static arrays and structs incl. pointer elements and the `0x60`
   rule; alias-op lemmas;
3. cross-location copies (storage/calldata), which pull in Sy's `E` from the
   layer below;
4. the ABI codec (P5), then events/reverts/dispatch byte paths;
5. the `AllocationBound` premise wired into the seam statement + the
   fuel-truncation threading.

## 5. Pre-freeze source-semantics items this study surfaced

Found by the heap-map pass; these are gap-hunt items (M4 family) that should
close **before** the semantics freezes under the tower, since the Sm proof
will otherwise relate against buggy encoders:
1. `Stmt.emitEvent` (8719) and `Stmt.revert`/custom errors evaluate args with
   shallow eval and `encodeFields?`/`abiEventTopic?` have no `memoryRef`
   case — `emit E(x)` / `revert Err(x)` with ref-nested memory `x` likely
   spuriously reverts `typeMismatch`. Needs the M4 deep-deref treatment +
   paired Forge lanes.
2. `Stmt.assignTupleNested` (7985) bypasses the M2 ref-preserving component
   walk — nested-tuple destructuring of memory refs likely still deep-copies.
3. `bytes(string)`/`string(bytes)` reinterpret RHS is not a recognized
   ref-preserving shape in `memoryRefOrValue…` (round-2 flag, still open).
Also confirm (round-2 checklist) M2/M3/M4 against Forge with executed lanes.

## 6. What makes this tractable (summary)

The scary version of this layer — "relate an abstract heap to dirty flat
bytes with scratch reuse, interior pointers, and FMP resets" — dissolves
under three observations: memory is not observable (P2), so the relation is
internal and the target's above-FMP chaos is existentially absorbed; we emit
our own Yul (P1), so solc's codegen warts need not be modeled, only its
documented layout; and the source heap already has solc's pointer structure
(ref-nesting + post-M1–M4 aliasing), so per-type `Repr` plus a monotone
allocation map is a near-homomorphism rather than a translation. The genuinely
new proof content is: the per-type representation predicates, the deep-copy
loop lemmas, the encoder-equals-byte-writes family (Sx), and the
`AllocationBound` boundary — a large but conventional forward simulation, not
a research problem.
