# Compile-to-Yul readiness: mapping the source semantics for a composing Solidity→Yul lowering

> Relocated 2026-07-09 from the source repo (`../solidity-lean`, formerly
> solid-core-spine) to `evm-compiler/docs/solidity-lowering/`; compiler
> planning lives in this repo now. "This repo" in the body below still means
> the source-semantics repo (solidity-lean).

Status: design/mapping study, 2026-07-06; **revised 2026-07-08** against the
current tree. Read-only analysis of `SolidCore/Solidity/*` against
`../evm-compiler` (Solidus) and the shared `evm-interaction` alphabet. **No
source changes proposed for this document to land** — it is input for the
orchestrator. `file:line` anchors drift; declaration names are the stable
anchor.

**2026-07-08 status update — what has landed since the first draft:**
- **D1 is RESOLVED** (the "boundary-completion arc"): internal calls are now
  first-class core constructs (`Stmt.internalCall` / `Stmt.internalCallPtr`)
  evaluated against a `FunctionTable` at call time; the inline-splice path is
  deleted and **recursion is representable** (bounded only by interpreter
  statement fuel). The Sc layer has a source IR to refine. Modifiers are still
  inlined (see §1b).
- **N1–N4 are DONE**: the ~14 dead observation-era enums are deleted; the dead
  byte-memory shadow is deleted from `Runtime`; the in-file example defs moved
  to `SolidCore/Witness/InterpreterExamples.lean`; `Ast.lean` now imports only
  `Shared/{Word,Precompile}`.
- **Phase 5 landed**: `Interaction.lean` pins the shared alphabet (verbatim
  `EvmCompiler.Simulation.*` re-exports); `Checked.lean` carries `SolI`-tree
  entry points (`constructFromTree`/`callTree`/…); the Context oracle residue
  (`lowLevelCallResults`/`contractCreationResults`) is deleted;
  `SolidityFailure.outOfFuel` is in place.
- **Openworld/postworld landed**: `State` now carries a dynamic `selfBalance`
  (A2 — the old "self-balance never mutates" recorded gap is fixed),
  `selfNonce`, an adopted-world view (`envWorld?` held verbatim from answered
  `postWorld`s, with a snapshot/adopt round-trip law), and adopted log/
  selfdestruct prefixes.
- **NumberRat is now signed** (`num : Int`, total `sub`) — the old
  "non-negative, fails closed on negatives" description is obsolete.
- **V3 is DONE (2026-07-08)**: the unspecified-order quantification scaffolding
  (`unspecifiedOrders`, `withUnspecifiedChildEvalOrders`, `callUnspecifiedResults`,
  `CallsUnspecified`, the ABI/Checked wrappers and their witnesses) is deleted;
  the order is pinned to `ChildEvalOrder.yulCompatible` permanently (doc comment
  at the definition records this).
- **Still open**: P1 (materialize the storage-layout `E`; in flight), fuel
  monotonicity for the eval cluster (in flight), hinder-E (`checkedExpLoop`
  O(exponent); in flight), hinder-I/R, and the recorded `requestedGas`/initCode
  transcript residues (intentional at this layer).

Sections below are updated in place to match; stale line anchors from the
first draft may remain where the claim itself is unchanged.

Scope: everything **except** the external-world/interaction boundary, which was
mid-refactor when first drafted (Phase 5 and openworld/postworld have since
landed; boundary facts below are updated but not re-mapped in depth). Where the
boundary is load-bearing for a lowering seam it is named, but no boundary
refactor is recommended here.

---

## 0. What "composes with the evm-compiler proof" concretely requires

Solidus's crown theorem is `EvmCompiler.Solidus.compile_correct`
(`evm-compiler EvmCompiler/Correctness.lean:99`): for a decoded Yul object,
`rawObjectRun` **`ForwardRel`-refines** the open bytecode run, with
`truncated := Yul.FunctionsInteractionPrimitive.Truncated` and
`doneRel := ObservableDoneRel`. `ForwardRel`
(`evm-interaction/EvmCompiler/Simulation/Interaction.lean:1909`) has three
constructors: `truncated` (a source `done`-error tagged `truncated` relates to
*any* target — the source ran out of fuel, no claim), `done` (`doneRel` on the
two leaves), and `request` (**identical query on both sides**, and for **every**
answer the continuations are related). So a composing lowering step must be a
theorem of shape

```
ForwardRel truncatedSol solYulDoneRel
    (soliditySourceRun … initState)
    (rawObjectRun fuel ctx yulObject initState')
```

then `ForwardRel.trans` (`Interaction.lean:2244`) chains it with
`compile_correct`. `trans` carries one non-trivial side condition,
`hReflect`: if the Solidity leaf relates to a Yul `.OutOfFuel` failure, the
Solidity side must **already** have been truncated. Practically this is the
"the compiler cannot manufacture a fuel failure the source didn't have"
obligation, and it dictates that **fuel exhaustion in the source semantics must
be a distinguished, reflectable outcome** — exactly the `SolidityFailure.outOfFuel`
constructor Phase 5 introduced (not an `Option`/`none`).

Three consequences fix everything downstream:

1. **Same query transcript.** The source execution and the emitted Yul must
   emit the *identical* `Query` sequence on identical answers. This is why the
   interaction-monad boundary (Phase 5) is a precondition for *any* lowering,
   and why the deterministic child-evaluation order is load-bearing.
2. **A done-relation on final states.** Not per-construct records (the deleted
   observation layer) — the *states themselves*. On the Yul side the comparison
   is `ObservableDoneRel` over `FinalStateObs` (`evm-compiler Solidus/Defs.lean:88`):
   code-erased `OpenWorld` equality (nonces, balances, storage, transient,
   code), `gasAvailable`, `activeWords`, `memory` bytes, `H_return`, and exact
   output bytes per halt kind. **The source's final state must be able to
   produce an `OpenWorld` and byte-exact output/revert data** to sit on the left
   of that relation.
3. **The alphabet and the entire Yul source semantics are frozen.**
   `Simulation/{Interaction,OpenWorld}.lean` and
   `Yul/{Syntax,EffectSemantics,InteractionSemantics}.lean` are in
   `evm-compiler benchmarks/frozen_manifest.txt`. New theorems compose *on top*
   via `trans`; they must not require editing those files. The `evm-interaction`
   extraction must stay byte-identical.

**The lowering target is not raw bytecode.** The top of Solidus is
`rawObjectRun` (`evm-compiler Solidus/SourceRun.lean:56`) / the canonical
`Yul.InteractionSemantics.exec` layer. A Solidity→Yul step only has to reach a
**Yul object** (dispatcher `Stmt` + function map, `EvmYul.Yul.Ast`); Solidus
carries it the rest of the way. That is the single most important fact for
sizing the future project: **we produce Yul, and inherit Solidus's ~7 verified
intermediate IRs below it** (Yul → Functions → Locals → Expressions → Structured
→ TypedCfg → Assembly → Bytecode; enumerated in §3). But "produce Yul" is itself
a tower, not one hop — see §3.

---

## 1. Internal-semantics map (the "rest")

### 1a. Surface AST — `Ast.lean` (~450 lines)
Untyped, permissive, solc-shaped: full surface `Ty` grammar (arbitrary
`uint n`/`int n`, `fixed`/`ufixed`, `bytesN`, structs, mappings, function types
with data locations/visibility/mutability), `Literal` keeping numbers as **raw
strings** with denominations (`Ast.lean:140,165`), `Expr`/`Stmt` covering
try/catch, `unchecked`, modifier placeholder, and `inlineAssembly : String`
(opaque payload, `Ast.lean:293`). No expression-level type annotations — typing
is re-derived. This is a parser-frontend artifact; it is **not** the lowering
IR (see 2a).

### 1b. Elaboration — `Interface.lean` (~20.6k lines, `namespace Executable`)
Surface `SourceUnit` → the **interpreter's own core** (`Source.CoreExpr/CoreStmt/
CoreContract`, re-exported `Interface.lean:20`). There is no third IR: elaboration
emits exactly what the interpreter runs. The driver is `SourceUnit.toCoreContract?`
(`:19134`) → `ContractDecl.toCoreWithBasesAndUsing?` (`:18788`) →
`ContractDecl.toCoreFromOrders?` (`:18195`). Compute-once at elaboration:
- **Inheritance**: real C3 linearization (`mergeLinearizationsWithFuel?` `:17475`)
  for dispatch order; storage-append order (`storageOrder?` `:17422`).
- **Internal calls are preserved as boundary nodes** (boundary-completion arc,
  stage E): a resolved internal call elaborates to `Stmt.internalCall` keyed by
  name into the contract's `FunctionTable`, and an unresolvable name is tried
  as a call through an internal function *pointer* (`Stmt.internalCallPtr`,
  dispatch IDs on `FunctionDef.dispatchId?`, stage C). The historical
  inline-splice path (α-renaming callee bodies into the caller) is **deleted**;
  `defaultInternalCallInlineFuel := 64` survives only as the nested-call-argument
  hoisting bound for the elaboration cluster's termination measure — **recursion
  is representable**, bounded only by the interpreter's statement fuel.
  **Modifiers are still inlined** by placeholder substitution
  (`functionExpandModifiersToCoreWithInternalCalls?`), so the core has no
  modifier/`super`/inheritance construct — but it *does* have the
  internal-call boundary.
- **Selectors, event topics, external-fn-pointer address words** — keccak-computed
  at elaboration (`resolveSelectorsWithUnqualified` `:7733`,
  `resolveEventSelectors` `:7916`).
- **Storage slot/packing assignment** (`toCoreStorageFieldsFromSlot` `:17611`,
  `StoragePackingCursor` `:17530`, ERC-7201 `layoutBaseSlot?`), public-getter
  synthesis (`publicGetterBodyExpr` `:17772`), constant inlining
  (`inlineConstants` `:312`).
- **Type erasure** `Ty.toCore?` (`:2058`): `uintN/intN→uint256/int256`,
  `enum→uint256`, `struct→tuple` (field names erased), `string/bytes→bytesCalldata`,
  function types→`externalFunction`. Width survives as explicit core cast/cleanup
  nodes and packed-field metadata.
- **`NumberRat`** (`:2656`): **signed** rational constant folding
  `{num : Int, den : Nat}` with a canonicalizing `mk?` and a total `sub`.
  Fractional and negative intermediates both fold; the old "non-negative,
  fails closed on negative results" behavior is gone. The recorded "rational
  constant" gap has been closed to this signed model.

The output `CoreContract` (`Interpreter.lean:7768` —
`storageFields/immutableFields/eventDecls/errorDecls/functions`) is a **closed
IR with zero surface references**. Two caveats: constructor entry points
**re-run the whole elaboration per construction** (`SourceUnit.constructContract?`
`:19145`), and `CheckedContract` deliberately keeps the surface `decl` beside
`core`.

### 1c. Typechecker — `TypeCheck.lean` (~13.6k lines)
Pure accept/reject: output is `Except TypeError CheckedSourceUnit` where
`CheckedSourceUnit = { source : SourceUnit }` (`:12116`) — **no typed
annotations flow downstream**; elaboration re-derives all types. Checks name
resolution, types, data locations, overrides, mutability (`view`/`pure`),
payable, try-catch shape, break/continue/placeholder placement. **Not
load-bearing for interpreter soundness** — the interpreter is defensively
dynamically typed (~257 `typeMismatch` sites) — but load-bearing for
*acceptance* (the pinned-solc rejection lanes) and for justifying
elaboration assumptions (e.g. constant exprs contain no call nodes).

### 1d. Checked entry layer — `Checked.lean` (~2k lines)
`CheckedProgram` / `CheckedContract` bundle the invariant "typechecked +
type-resolved + elaboration succeeded"; runtime entries delegate to the core
(`CheckedContract.call?` → the core on `contract.core`, calls threaded through
`contract.core.table`). Phase 5's `*Tree` twins returning `SolI` are landed
(`constructFromTree` `:502`, `callTree` `:533`, plus `constructWithContextTree`/
`callTransactionTree`/…) beside the `?` adapters. Note the tree constructor
entries resolve the constructor from the **already-elaborated**
`CheckedProgram` (`constructorFunctionFor?`) rather than re-running elaboration.

### 1e. Value / type model — `Interpreter.lean` + `Shared/Word.lean`
- **`Word := Nat`** normalized mod `2^256` (`Shared/Word.lean:10,14`); every op
  lifts through `EvmYul.UInt256` (`liftEvmBinary` `:26`), so word arithmetic is
  **definitionally the pinned EVM package's**, round-tripped through `Nat`.
  Un-normalized `Nat` leaks only into intermediates; all stores/lookups normalize.
- **`Ty`** (`Interpreter.lean:68`): `bool|address|uint256|int256|fixedBytes n|
  bytesCalldata|externalFunction|fixedArray|dynamicArray|tuple` — **no sub-256-bit
  scalars**; narrow widths live only as cleanup annotations / packed-field widths.
- **`Value`** (`:91`): `word|int|bytes (List Byte)|externalFunction|fixedArray/
  dynamicArray/tuple (List Value)|storageRef String|storagePathRef String (List
  Value)|memoryRef Nat|abiLazy AbiCleanup Value`. Yul-friendly parts: `word`/`int`
  both carry a 256-bit two's-complement word (the signed tag is IR metadata a
  lowering erases); `externalFunction` uses solc's `addr·2^32+selector` word;
  `memoryRef Nat` is pointer-shaped. **Not** Yul-shaped: structural
  `fixedArray/dynamicArray/tuple` values passed by value as Lean lists; `bytes`
  as a byte list; `abiLazy` a deferred-cleanup wrapper value; `storageRef`/
  `storagePathRef` naming storage by **field-name String + typed index values**
  (slot recomputed per access); locals string-keyed (`Frame := List (String ×
  Value)`).

### 1f. State model
- **`State`**: `storage : StorageMap` (**already word-addressed**, word→word),
  `transient : StorageMap`, `immutables : ImmutableMap` (**typed, name-keyed,
  not word-encoded**), `selfdestructs` + `selfdestructEffects`,
  `externalInteractions : List ExternalInteraction` (recorded transcript),
  `events`, and — since openworld/postworld — the live self-account and adopted
  environment: **`selfBalance` is dynamic** (A2: re-based at each external
  entry from the environment fact plus credited `msg.value`; the outgoing-call
  debit arrives through world adoption — the old "self-balance never mutates"
  recorded gap is **fixed**), `selfNonce` (carried so the outgoing `OpenWorld`
  snapshot covers every `OpenAccount` field), `envWorld? : Option OpenWorld`
  (the answered `postWorld` held **verbatim**, with `worldMutatedSinceAdoption`
  making the snapshot/adopt round-trip law exact), and adopted log/selfdestruct
  prefixes (`adoptedLogPrefix`/`adoptedEventCount`/`adoptedSelfdestructCount`)
  so the canonical log series composes callee logs wholesale. No returndata
  buffer (each call's result *is* a `Value.bytes`).
- **`Context`**: per-call constants (self/sender/value, block/tx env, account
  maps, contract-name maps, `gasleft` ambient constant, `childEvalOrder?`).
  The oracle residue `lowLevelCallResults/contractCreationResults` is
  **deleted** (Phase-5 stage 3, done) — external answers come from the
  interaction tree.
- **`Runtime`**: `state`, `locals`, and the live **object heap**
  `memory : List (Nat × Value)` with `memoryRef` aliasing and deep deref
  (`allocMemory`, `derefMemoryValueDeep`). The old dead byte/EVM-shaped shadow
  (`memoryByteMap`/`memoryFreePointer`) is **deleted** (N2, done) — the real
  byte model is to be built by the lowering's memory layer, from nothing rather
  than beside an impostor. See §4 finding **hinder-M**.
- **Rollback** is purely functional: `FunctionDef.callBodyResult` (`:7647`) maps
  `Result.reverted` to a `CallResult.reverted` carrying the **pre-call `State`
  snapshot**; storage/events/transient roll back by discarding. Pinned by
  `FunctionDef.call?_reverted_rolls_back` (`:7750`).

### 1g. Arithmetic
Exactly "Yul builtin + explicit overflow check". Unchecked → EvmYul-lifted wrap
(`addWord` …). Checked → test the mathematical result then throw
`RevertData.overflow = Panic 0x11` (`checkedAdd/Sub/Mul` `:4561`);
`checkedDiv/Mod` Panic 0x12 on zero; signed family via `Int` range check +
`signedToWord` (`:4630`), incl. MIN/−1 (`checkedSignedDiv` `:4659`);
`addmod/mulmod`. Sub-256-bit checked arithmetic = full-word op +
`uintCleanup?/intCleanup?` (Panic on out-of-range) — matching solc's cleanup
discipline. `BinaryOp` (`:4346`) is 20 ops incl. `shl/shr/sar`, dispatched
signed/unsigned by operand mode. **No fixed-point** (also unimplemented in solc).
No rationals in the interpreter. One naïveté: `checkedExp` is an O(exponent)
loop (`checkedExpLoop` `:5315`) — semantically fine, but see §4 **hinder-E**.

### 1h. Storage layout — spec-owned, solc-exact
`StorageLayout` (`:1182`) = `scalar|packedScalar|struct|fixedArray|dynamicArray|
bytes|string|mapping`; packing cursor reproduces solc sequential packing.
Slot derivation with **real keccak** (`mappingStorageSlot = keccak(key‖slot)`
`:1604`, `dynamicArrayDataSlot = keccak(slot)` `:1629`, ERC-7201 `erc7201Slot`
`:1597`). Packed read/write via bit-range ops (`:2224`); bytes/string short/long
form exactly (`storageBytesHeader?` `:2248`, long chunks at `keccak(slot)+i`).
One recursive load/store/clear family per layout
(`State.loadStorageLayoutAt`/`storeStorageLayoutAt`/deep-clear on shrink), and
the resolver `State.resolveStoragePathSlot` (`:3985`) that turns
`storagePathRef name indexes` into a concrete `(slot, layout)`. **This resolver
*is* the layout encoding `E : (typed access) → word slot` a lowering needs** —
but it is re-derived per access, not a standalone compiled artifact (§4
**help-S / neither-S**). Transient uses the same machinery on a separate map.
**Immutables are name-keyed typed values** (`ImmutableMap`), with no
code-substitution model — abstract vs the EVM's code-embedded immutables (§4
**hinder-I**).

### 1i. Control flow / functions / dispatch
`Expr` (~60 ctors) and `Stmt` (~55 ctors) are a **desugared, monomorphic
core**: storage/memory locations explicit, ABI/encode/cast/cleanup nodes
explicit, and — since the boundary-completion arc — **internal calls explicit**
(`Stmt.internalCall targets callee args` and `Stmt.internalCallPtr` for calls
through internal function pointers, `:7118`/`:7126`). `Result` is six-way
`normal|returned|selfdestructed|reverted|broke|continued`, each carrying
`Runtime`. `FunctionDef` (now carrying `dispatchId?` for function-pointer
words) → `Contract` a **flat `List FunctionDef`** found by name or selector,
projected by `Contract.table` (`:8916`) to the `FunctionTable` that
`Stmt.eval` threads and `internalCall` looks up at call time
(`FunctionTable.lookup?`/`lookupById?`; a miss — including the uninitialized
pointer ID 0 — is a runtime check, `:7123`). Try-catch
(`Stmt.tryExternalCall`/`tryContractCreate` `:6246`) branches on the
environment-answered result's `success`; catch dispatch matches
`Error(string)`/`Panic(uint)`/low-level bytes on the answer (`:6478`); the callee
**never executes** (open-world). Evaluation order: `ChildEvalOrder` (`:1483`)
with `yulCompatible := rightToLeft` (`:6047`), `effectiveChildEvalOrder`
defaulting to it; `unspecifiedOrders` is the **singleton** `[yulCompatible]`
(`:6053`) — deterministic in practice (§4 **help-O**).

### 1j. Events / errors
Events: `emitEvent` → `EventDecl.encodeFields?` (`:4252`) — topic0 = real-keccak
signature hash, indexed dynamic params hashed per ABI, non-indexed
ABI-encoded to data; anonymous = no topic0. `Event.toLogEntry` (`:742`) projects
to the shared `Log.Entry {address, topics, data}` — the EVM-observable form.
Reverts: **`RevertData`** (`:218`) is a *structured* sum
`empty|panic Word|error String|custom String (List Value)|raw (List Byte)`, not
bytes; the ABI layer encodes it to bytes at the boundary (`Contract.encodeRevertData?`
`ABI.lean:475`, real-keccak selectors). A lowering's done-relation must relate
this structured form to Yul's revert bytes (§4 **hinder-R**).

### 1k. ABI — `ABI.lean` (~1k lines)
Full head/tail spec encoding over core `Ty`/`Value`, `Bytes := List Byte`:
`isDynamicAbi`, `encodeStaticValue?`/`encodeDynamicPayload?`/`encodeValues?`,
fuel-bounded decode. Dispatch `Contract.callCalldataAtFromWithContext?` (`:669`):
4-byte selector → `findFunctionBySelector?` → **lenient** decode (lazy cleanups)
→ payable check → call → encode returns/revert; unknown selector → fallback;
short calldata → receive-or-fallback. Strict variant `decodeFunctionArgsStrict?`
(`:447`). Faithful; `string ≡ bytes` (no UTF-8 validation);
`List Byte`-of-`Nat` ↔ shared `ByteArray` bridged at the Phase-5 boundary.

---

## 2. Compile-to-Yul-composable analysis, area by area

The central alignment fact, from the three maps: **the interpreter is already
"Yul builtins + explicit checks over 256-bit words with word-addressed storage,
right-to-left deterministic evaluation, external effects as an interaction
tree."** That is a remarkably good starting point — most of the semantics is a
thin structured layer over exactly the primitives Yul exposes. The friction is
concentrated in a few representations that carry *typed/structural* information
Yul flattens, and in a few abstractions that erase information the done-relation
needs.

### 2a. The core language as the top lowering layer
**Helps.** The elaborated `CoreContract` is a genuinely clean IR candidate:
flat function list, word-valued expressions, explicit cast/cleanup nodes,
precomputed selectors/topics/slots, external effects already queries, zero
surface references, `Interpreter.lean` importing only `Shared.*` (clean
dependency floor). This is the natural anchor for the lowering's top layer.

**Hinders / seam risk.**
- ~~Internal calls and modifiers are inlined away before the core~~ —
  **RESOLVED for internal calls** (boundary-completion arc): internal calls and
  internal-function-pointer calls are core constructs evaluated against the
  `FunctionTable`, recursion is representable, and the inline-splice path is
  deleted (see §1b, D1). The **residual** mismatch is smaller: **modifiers are
  still inlined** by placeholder substitution, so a lowering either accepts the
  inlined form or reconstructs a modifier split — a much shallower question
  than the old function-boundary erasure, since inlined modifiers neither hide
  recursion nor erase the call-graph structure the Sc proof inducts over.
- **Legacy `?` constructor entries re-run elaboration per construction**
  (`SourceUnit.constructContract?`) — fine for an executable oracle. The
  Phase-5 tree entries (`constructFromTree`) instead resolve the constructor
  from the already-elaborated `CheckedProgram`, which is the fixed-artifact
  shape a creation lowering theorem wants.
- String-keyed storage/locals at core level (`Expr.storage : String`,
  `Value.storageRef : String`) — a lowering must map these to slots/stack, which
  the layout resolver already computes but per-access (see 2d).

### 2b. Value / memory model vs Yul's word/memory model
**Helps.** `word`/`int` are 256-bit words; `memoryRef` is pointer-shaped;
`externalFunction` uses solc's exact word encoding.

**Hinders.** Structural `tuple/array` values and `bytes`-as-list are the classic
"abstract value that Yul represents as a memory region." A lowering to Yul must
pick a memory layout (head/tail, length-prefixed) for these and prove the
structural operations refine the pointer-arithmetic Yul emits. The interpreter's
**object-heap memory** (`memory : List (Nat × Value)` with aliasing) does **not**
correspond to Yul's flat `ByteArray` memory + free-memory-pointer at all (the
old dead byte-shadow that superficially resembled it has been **deleted**, N2).
This is the memory-model translation layer the lowering will need; the current
abstract heap is convenient for execution but is *not* the representation a
memory-refinement proof wants. Per the roadmap this is deliberately deferred
(memory layout is not spec-owned; it reaches queries only via ABI-encoded
calldata bytes, which the ABI layer already concretizes).

### 2c. Arithmetic
**Helps, strongly.** Word ops are definitionally `EvmYul.UInt256` ops, and the
checked/unchecked split is already "wrapping builtin + explicit Panic guard" —
which is *exactly* what solc emits into Yul (`checked_add_t_uint256` = the
add plus a comparison-and-revert). This is close to a 1:1 lowering: each
`BinaryOp` arm maps to a Yul builtin call, each checked guard to the Yul
overflow-check snippet, each `*Cleanup` to the Yul cleanup function. The signed
tag on `Value.int` selects `sdiv/smod/slt/…` and is erased into the word.
**Neither.** `checkedExp` as an O(exponent) loop (§4 **hinder-E**) is a
performance/latitude wart, not a correctness one; a lowering would emit Yul's
`exp` builtin (environment/EVM-computed), so the source loop and the Yul builtin
must be proved equal — cheaper if the source uses a closed-form/`UInt256.exp`.

### 2d. Storage layout — the best-positioned seam
**Helps, strongly.** Storage is **already word-addressed** and the layout is
solc-exact with real keccak. Per the roadmap this is spec-owned and in scope.
The done-relation's `OpenWorld` storage is word→word; `State.storage` is
word→word; the snapshot is a near-direct read. This is the area where the source
semantics is *already* at the Yul level.
**Neither-S.** The layout encoding `E` (`resolveStoragePathSlot` `:3985`) exists
but is **re-derived per access** rather than materialized once as a
`CoreContract → (path → slot)` artifact. For a lowering proof you want a single
named total function (the "compiler-generated layout" the skill insists must
have a checked constructor). The logic is all present; it wants to be *lifted
out* into a standalone spec-owned definition (recommendation **P1**).

### 2e. Control flow / dispatch / try-catch
**Helps.** Structured control (`if`/`while`/`for`/`do-while`, six-way `Result`)
maps cleanly onto Yul's structured control (`if`/`for`/`switch`/`break`/
`continue`/`leave`) — the Structured layer in Solidus is precisely this
abstraction, so the shapes line up. Dispatch is a flat selector table → Yul
dispatcher `switch`. Try-catch is environment-answered (callee never executes),
matching Yul's open-world calls exactly — no nested-execution semantics to
reconcile.
**Hinders.** `broke`/`continued`/`returned`/`selfdestructed` as `Result` values
vs Yul's `Checkpoint`/`leave`/halt encoding is a control-encoding translation,
but a routine one (Solidus already relates structured control to label jumps).
With the internal-call boundary now preserved in the core (2a), this is routine
throughout; the only residual erasure is inlined modifiers.

### 2f. Events / errors
**Helps.** `Event.toLogEntry` already produces the EVM-observable
`{address, topics, data}`; a lowering emits Yul `log0..log4` and must show the
same topics/data — the encoding is already computed here with real keccak.
**Hinders-R.** `RevertData` as a *structured* sum must be related to Yul revert
*bytes*. The encoder exists (`encodeRevertData?`), so the done-relation is
"decode the source `RevertData`, ABI-encode, compare to Yul returndata" — fine,
but it means the public done-relation touches the ABI encoder. Keeping
`RevertData` structured is the right call for the source semantics (readable,
matches solc's error model); the lowering just carries the encode step. No
change recommended.

### 2g. Gas / fuel / truncation
**Helps.** `gasleft` is an ambient constant and the alphabet already reserves
`Query.resource gas`; Yul's `gas()` is `Query.resource .gas`, so un-deferring is
additive on both sides. Fuel exhaustion is `SolidityFailure.outOfFuel`
(a distinguished, reflectable outcome, landed), which is exactly what
`ForwardRel.trans`'s `hReflect` needs (§0). **This is the correct shape** — do
not let it regress to `Option`.
**Recorded residue (not to fix now):** `requestedGas` gas-key erasure (no-gas vs
`{gas: gasleft}` indistinguishable), and create `initCode` being source-canonical
(name-encoded) rather than compiled bytecode. Both are transcript-level
mismatches that resolve *at* the lowering (when creates carry real initCode and
gas is un-deferred) — they are correctly logged deferrals, and a lowering proof
would quantify over them or discharge them then.

---

## 3. The Solidity→Yul lowering as a stratified tower of intermediate IRs

**Correction to an earlier draft of this section.** A prior version proposed a
single new refinement layer ("elaborated `CoreContract` ⊑ Yul") for the whole
lowering. That badly understates the work and is not how Solidus is built. The
**composition seam** into `compile_correct` is indeed one new spine segment
(Solidity-source ⊑ Yul, chained by `ForwardRel.trans`), but the **proof** of
that segment must itself be a tower of intermediate IRs, each its own adjacent
`ForwardRel`, to be tractable — exactly as Solidus decomposes the *smaller*
Yul⊑EVM gap.

### What Solidus actually does for the smaller (Yul→EVM) gap

Verified by reading `../evm-compiler/EvmCompiler/`: `compile_correct`
(`Correctness.lean:99`) is **not** a Yul⊑EVM one-step proof. It is the transitive
composition (`ForwardRel.trans`, `Interaction.lean:2244`) of a chain of
per-IR refinements, one directory each:

```
Yul (canonical)                Yul/InteractionSemantics.lean
  ⊑ Functions                  Functions/Interaction*Preservation.lean   (hoist fns; stack-alloc layout)
  ⊑ Locals                     Locals/InteractionPreservation.lean        (named locals → stack slots)
  ⊑ Expressions                Expressions/InteractionPreservation.lean   (nested exprs → flat stack code)
  ⊑ Structured                 Structured/Interaction*Preservation.lean   (block/branch/loop/switch → labels)
  ⊑ TypedCfg                   TypedCfg/InteractionPreservation.lean       (structured → CFG + labels)
  ⊑ Assembly                   Assembly/InteractionPreservation.lean       (CFG → instruction list; + gasless→gasful bridge)
  ⊑ Bytecode / EVM.X           Assembly/InteractionBytecode.lean, GasfulBridge
```

~7 intermediate IRs for a gap where **Yul already provides** words, memory,
storage, keccak, and calls as primitives. Two structural lessons for us:
- **Each seam introduces exactly one abstraction** and carries its **own
  done-relation**, which grows more machine-specific downward: `Functions`
  `StateOutcomeRel layout suffix` (stack layout appears), `Locals`/`Expressions`
  `OutcomeRel baseStack`/locals-`Ctx`-keyed (stack slots appear), `TypedCfg`
  `SegmentDoneRel` over CFG exit tokens (labels appear). The high, abstract
  done-relations near the top compare *values*; the low ones compare *stacks and
  layouts*. Same transcript throughout (`Query` alphabet is invariant).
- Truncation (`OutOfFuel`) is threaded through every seam and reflected by each
  `trans`'s `hReflect` — the discipline is uniform, one instrument per layer.

### Why Solidity→Yul is a *larger* gap, and its tower is *taller*

Solidity is much higher-level than Yul. Yul is not the problem to *implement*
(it already has memory/storage/keccak/call builtins); the job is to **lay out
high-level constructs onto those builtins** — and that layout decomposes into
several independent abstractions, each of which wants its own IR and its own
refinement to stay tractable. The elaborated `CoreContract` is **not the top of
one short hop**; it is a partly-collapsed IR that a real tower would *un-collapse*
into distinct layers. The realistic tower, top-down from `CoreContract` to a Yul
object:

```
        (frontend, trusted or separately-verified — NOT the lowering spine)
        Surface AST → TypeCheck (acceptance) → Elaboration → CoreContract

  ── the new lowering spine: Solidity-source ⊑ Yul, decomposed ──

  Sd  DISPATCH / OBJECT layer     CoreContract (flat FunctionDef list + selector table,
                                   storage/event/error decls, immutables)
      abstracts: the contract-as-callable — one public entry answering calldata.
      seam Sd→Sc: selector table → Yul dispatcher `switch`; public fns → external
                  entry wrappers (ABI decode args / encode returns around the call);
                  receive/fallback arms; constructor → creation object.
      done-rel: OpenWorld + exact output/revert bytes + logs (the TOP relation,
                = the composition seam's done-rel; compares observable values, no layout).
      size: MEDIUM. Mostly a table→switch structural map; the ABI wrappers are
            shared with Sb. Hardest part is receive/fallback/constructor corner cases.

  Sc  CALLING-CONVENTION / FUNCTION layer   functions with internal calls + params/returns
      abstracts: the internal-function boundary and internal (possibly recursive) calls.
      seam Sc→Sb: each Solidity internal function → a real Yul function; internal
                  call → Yul function call; named returns / multiple returns → Yul
                  return-var convention; modifier wrappers → caller/callee split.
      done-rel: OpenWorld + return values (as words/memory refs) + control outcome
                (normal/return/revert), quantified over the call graph by induction
                on source fuel / the evaluation derivation.
      size: LARGE and still the HARDEST proof (induction on source fuel over
            the call graph) — but since the boundary-completion arc it HAS a
            source IR to refine: internal functions are `FunctionTable` entries,
            call sites are `Stmt.internalCall`/`internalCallPtr` core nodes, and
            recursion is representable (D1 resolved). Residual: modifiers are
            still inlined at elaboration, so this seam sees post-modifier
            function bodies — a stated, shallow fragment worth naming in the
            theorem, not a structural break.

  Sm  MEMORY-LAYOUT layer         structural values (tuple/array/bytes/string, memoryRef)
      abstracts: aggregate values as regions of a flat byte memory.
      seam Sm→(word/byte ops): structs/arrays → head/tail + length-prefix layout on
                  Yul memory; free-memory-pointer discipline (the FMP word lives
                  at 0x40 and initially points to 0x80, the start of free memory);
                  memoryRef →
                  concrete offset; copy/allocation → mstore/mload sequences.
      done-rel: value ≅ (region of the flat `ByteArray` memory) under a memory
                invariant; final `memory`/`activeWords` match the Yul done-rel's
                memory fields.
      size: LARGE. Full translation layer — the interpreter's object-heap memory
            (List (Nat × Value) with aliasing) does NOT correspond to Yul memory
            at all, and the byte-shadow that would is DEAD (§4 hinder-M). New model,
            new invariant, per-type layout proofs. Deliberately roadmap-deferred.

  Sy  STORAGE-LAYOUT layer        typed storage paths (mappings/arrays/packing)
      abstracts: typed field/mapping/array access as slot arithmetic + keccak.
      seam Sy→(sload/sstore): storagePathRef → slot via the materialized encoding E
                  (keccak(key‖slot), keccak(slot)+i, packed bit-ranges, short/long
                  bytes); read/write/deep-clear → word ops.
      done-rel: typed storage state ≅ word storage under E; = the OpenWorld storage
                field. NEAR-IDENTITY on our side — storage is already word-addressed,
                E already computed (needs materializing, P1).
      size: SMALL–MEDIUM, the CHEAPEST seam. Our representation already lives at
            the target. Mostly: lift E out (P1) + prove the per-access path = E.

  Sx  ABI-CODEC layer             encode/decode of args/returns/revert/events
      abstracts: values ↔ ABI byte strings (head/tail, dynamic offsets, selectors).
      seam Sx→(byte/memory ops): encodeValues/decodeArgs → Yul ABI encode/decode
                  builtins over memory; RevertData → error/panic/custom bytes;
                  event fields → topics + data bytes.
      done-rel: produced bytes byte-identical to Yul's; already computed here over
                List Byte (bridge to ByteArray). Interlocks with Sm (codec writes
                to the memory model) and Sd (dispatch uses the codec).
      size: MEDIUM. The spec logic exists and is faithful; the work is relating it
            to Yul's codec over the concrete memory model (so it rides on Sm).

  Sk  ARITHMETIC / CONTROL layer  checked/unchecked word ops; if/for/while; require/revert
      abstracts: (almost nothing — this is where we already ARE at Yul level).
      seam Sk→Yul: BinaryOp → Yul builtin; checked guard → Yul overflow-check
                  snippet + Panic; *Cleanup → Yul cleanup fn; structured control →
                  Yul if/for/switch/break/continue/leave; Result(broke/continued/
                  returned) → Yul control encoding.
      done-rel: word-for-word equality; structured-control outcome match.
      size: SMALLEST, near-1:1. Word ops are DEFINITIONALLY EvmYul.UInt256 (§2c);
            checked = wrapping-builtin + explicit Panic = solc's own Yul shape;
            control shapes line up with Yul's (and with Solidus's Structured layer).
```

These are not a strict linear stack — `Sm`, `Sy`, `Sx`, `Sk` are **largely
orthogonal abstractions** that a real compiler applies together, and a proof
engineer would sequence them as independent refinements (or bundle memory+ABI,
since ABI encoding *targets* the memory model). `Sd`/`Sc` are the genuinely
*vertical* ones (contract→functions→function bodies). A plausible ordering that
keeps each adjacent theorem to one abstraction: **Sy (storage) and Sk
(arith/control) first — cheap, our IR is already there — then Sx+Sm together
(codec on memory), then Sc (calling convention), then Sd (dispatch/object) on
top.** The composition seam's done-relation is `Sd`'s top relation (observable
`OpenWorld` + bytes + logs); the internal seams' done-relations are progressively
more concrete (memory offsets, slot arithmetic, stack-free but layout-explicit).

### Where the elaborated CoreContract actually sits

**Not at the top of a short hop — mid-tower, with some layers already
collapsed.** (First draft: "and one prematurely destroyed" — no longer true;
the Sc source has been restored.) Concretely:
- CoreContract has **already applied Sy-input and Sk-input shape**: storage
  access is explicit typed paths (good — Sy's source), arithmetic is explicit
  word ops with cleanup nodes (good — Sk's source). For these seams the core is
  a clean, aligned top IR.
- CoreContract has **already partly collapsed Sm**: values are still structural
  (`tuple/array/bytes`), so Sm's *source* is present — but memory is an object
  heap, so there is representation work, not just a layout choice.
- CoreContract now **carries Sc's source** (boundary-completion arc): internal
  functions are `FunctionTable` entries, call sites are `Stmt.internalCall`/
  `internalCallPtr`, function pointers have dispatch IDs, and recursion is
  representable. The remaining collapse is modifiers-inlined-at-elaboration —
  a stated fragment, not a missing layer.
- CoreContract **is** roughly Sd's source (flat function list + selector table),
  so the dispatch layer sits naturally on it.

So the honest picture: the current core is a good **Sy/Sk/Sd/Sc** anchor
(Sc modulo the stated modifier-inlining fragment) and an
**adequate-but-heap-mismatched Sm/Sx** anchor.

### Hardest seams (ranked)

1. **Sc (calling convention / function boundary)** — hardest *proof* (the
   induction-on-source-fuel/derivation over the call graph — the one place the
   skill insists you must not use an "all callees preserve" oracle), but no
   longer blocked: the source IR exists (D1 resolved; `FunctionTable` +
   `internalCall`/`internalCallPtr`, recursion representable). Residual stated
   fragment: modifiers inlined.
2. **Sm (memory layout)** — full translation layer; the object-heap memory has
   no correspondence to Yul's flat bytes (the old dead byte-shadow is deleted,
   so the byte model is built fresh here). New model + invariant + per-type
   layout proofs. Interlocks with Sx.
3. **Sx (ABI codec) on the memory model** — faithful spec exists, but relating
   it to Yul's codec over concrete memory rides on Sm and touches the public
   done-relation (revert/return bytes).

Cheapest, by contrast: **Sy (storage)** and **Sk (arithmetic/control)** — our
representation already lives at the Yul level for both.

---

## 4. Findings ledger (help / hinder / vestigial)

- **help-A (arithmetic)** — word ops are definitionally `UInt256`; checked =
  wrapping-builtin + explicit Panic guard = solc's Yul shape. Near-1:1 lowering.
- **help-S (storage)** — word-addressed, solc-exact, real keccak; storage
  done-relation is near-direct. Best-positioned seam.
- **help-O (order)** — deterministic right-to-left `yulCompatible` evaluation
  already chosen and load-bearing; makes the query transcript well-defined.
- **help-G (fuel/gas)** — `outOfFuel` distinguished outcome matches
  `ForwardRel.trans` `hReflect`; `Query.resource gas` reserved on both sides.
- **help-C (control)** — structured control + flat selector dispatch +
  environment-answered try-catch line up with Yul's structured control and
  open-world calls.
- **neither-S (layout artifact)** — `E` exists but is re-derived per access, not
  a materialized spec-owned function. → **P1**.
- **hinder-D1 (function boundary)** — **RESOLVED** (boundary-completion arc):
  internal calls/pointer-calls are core constructs over a `FunctionTable`,
  recursion representable, inline-splice deleted. Residual stated fragment:
  modifiers still inlined. → **D1** (now a record of the resolution).
- **hinder-M (memory)** — live memory is an object heap unlike Yul's flat
  bytes. The dead byte-shadow is **deleted** (N2 done); the real byte model is
  a lowering-project artifact. Still the biggest representation gap.
- **hinder-I (immutables)** — name-keyed typed values, no code-substitution
  model; abstract vs EVM code-embedded immutables. Lowering-era concern; note only.
- **hinder-R (revert)** — structured `RevertData` vs Yul bytes; encoder exists,
  done-rel carries the encode. Keep structured; note only.
- **hinder-E (exp)** — `checkedExp` O(exponent) loop; lower to Yul `exp`, prove
  equal. Cheaper against a closed-form. Note only.
- **vestigial-1** — the ~14 dead observation-era classifier enums
  (`LowLevelCallEvaluationStatus`, `ShortCircuitDecision`, …) — **DELETED** (N1 done).
- **vestigial-2** — the dead byte-memory shadow — **DELETED** (N2 done).
- **vestigial-3** — the unspecified-order quantification scaffolding —
  **DELETED** (V3 done, 2026-07-08): order pinned to `yulCompatible` forever;
  the two-order evaluator and its left/right witnesses are kept as
  order-sensitivity pins.
- **vestigial-4** — the end-of-file example/witness defs — **MOVED** to
  `SolidCore/Witness/InterpreterExamples.lean` (N3 done).
- **clean** — zero `partial`/`sorry`/`axiom` in `Interpreter.lean`; no
  nondeterminism (single deterministic evaluation order); rollback purely
  functional and pinned by a theorem.

---

## 5. Recommended prep refactorings

Separated into "worth doing now" and "defer to the lowering project."

### Do now (cheap, and now beats later) — ALL DONE as of 2026-07-08

**N1 — Delete the ~14 dead observation-era classifier enums (vestigial-1).**
**DONE** — deleted; no non-definition references remained.

**N2 — Retire the dead byte-memory shadow (hinder-M / V2).**
**DONE** — `memoryByteMap`/`memoryFreePointer`/readers deleted from `Runtime`;
the future memory-refinement layer builds the real byte model from scratch.

**N3 — Move the in-file example defs to `Witness/` (V4).**
**DONE** — now `SolidCore/Witness/InterpreterExamples.lean`.

**N4 — Fix the coarse import edge (`Ast.lean` → `ABI.lean`).**
**DONE** — `Ast.lean` now imports only `SolidCore.Solidity.Shared.Precompile`
and `SolidCore.Solidity.Shared.Word`.

### Consider now (higher value, higher care — flag for the orchestrator)

**P1 — Lift the storage-layout encoding `E` into a standalone spec-owned
function (neither-S).** *Rationale:* the lowering's storage seam needs a single
named total `CoreContract →ᴱ (storage path → word slot + packing)` with a checked
constructor (the skill's "compiler-generated evidence must be constructed").
Today the logic lives inside `resolveStoragePathSlot` (`:3985`) and the
elaboration-side slot assignment (`toCoreStorageFieldsFromSlot` `Interface.lean:17611`),
re-derived per access. Extracting it now — as a definition the interpreter
*uses* (proving the per-access path equals `E`) rather than a parallel copy —
both cleans the semantics and pre-builds the lowering's most important artifact.
*Cost:* 1–2 days; must be behavior-preserving (corpus is the arbiter).
*Now-vs-later:* genuinely optional now; the
logic is correct and present. Do it now only if the orchestrator wants the
storage seam de-risked early; otherwise it is a clean early task for the lowering
project. Recommend: **flag, lean toward deferring** unless storage is the first
lowering layer.

**D1 — The function-boundary gap. RESOLVED (boundary-completion arc).**
The first draft identified this as the tower's structural break: elaboration
inlined internal calls and modifiers away (fuel 64) before `CoreContract`
existed, so the calling-convention layer Sc had nothing to refine and recursion
was unrepresentable. The resolution took option (b)-in-place: the core IR now
**preserves the function boundary** — internal functions live in a
`FunctionTable` (projected from the flat `FunctionDef` list by
`Contract.table`), call sites elaborate to `Stmt.internalCall` /
`Stmt.internalCallPtr` (function pointers via `dispatchId?` words), the
inline-splice path is deleted, and recursion depth is bounded only by the
interpreter's statement fuel. `defaultInternalCallInlineFuel` survives only as
the nested-call-argument hoisting bound in elaboration's termination measure.
*Residual:* modifiers are still inlined by placeholder substitution — a
stated, shallow fragment to name in the Sc theorem, not a structural break.

**V3 — Collapse the `unspecifiedOrders` scaffolding (vestigial-3). DONE
(2026-07-08).** The decision was made to pin the evaluation order to
`ChildEvalOrder.yulCompatible` permanently; all quantification machinery
(`unspecifiedOrders`, `withUnspecifiedChildEvalOrders`,
`callUnspecifiedResults`/`CallsUnspecified`, the ABI
`callCalldataAtFromUnspecifiedResults`/`CalldataCallUnspecified`/transaction
variant, the Checked wrappers, and the three consuming witnesses) is deleted.
The two-order evaluator (`ChildEvalOrder`, `withChildEvalOrder`) and the
left/right witness pairs are retained as order-sensitivity pins.

### Defer to the lowering project (do NOT build now)

- **Memory-refinement layer** (structural values / `bytes` → flat Yul memory +
  free-memory-pointer). Deliberately deferred per roadmap (memory layout is not
  spec-owned). Build the real byte model *in the lowering*, not now.
- **`RevertData` → bytes done-relation** (hinder-R): the encoder exists; the
  relation is a lowering-proof artifact.
- **`checkedExp` → Yul `exp`** equality (hinder-E): lowering-proof artifact;
  possibly simplify the source to a closed form *then*.
- **Immutables code-substitution model** (hinder-I): lowering-era; the
  name-keyed abstraction is fine for the source semantics.
- **Un-deferring `gasleft` / real create initCode**: recorded gaps; resolve at
  the lowering when gas/creation transcripts must align byte-for-byte with Yul.
- **Elaboration correctness** (surface → core): either a separate obligation or
  surface-as-trusted-input (matching how Solidus treats solc's Yul emission).
  Not a source-semantics cleanup task.
- **Stack-too-deep spilling (verified Yul→Yul pass)**: Solidus's backend is
  stack-only (`memoryguard(size) = size`, fail-closed headroom certificate —
  no StackLimitEvader analogue), so wide functions/ABI wrappers will make
  `compile?` return `none` on real contracts. Plan: a Yul→Yul local-demotion
  pass in the lowering project — same frozen Yul semantics on both sides,
  one `ForwardRel` seam chained by `trans`; spilled locals become one-word
  memory slots folded into the reserved region below the memoryguard value
  (per-activation spill frames for recursive functions), unobservable at the
  seam. Policy (pressure heuristic + fail-closed retry against `compile?`)
  is untrusted; only the transformation carries a theorem. Sequence after Sk
  lands, before declaring the executable pipeline corpus-complete. See
  `docs/memory-layer-design.md` for the memory-model fit. Completeness-only:
  without it nothing is unsound, contracts just fail to compile.

---

## 6. Summary

**Layer map (§3):** import Solidus's Yul→bytecode tower (frozen) — we emit a Yul
object and inherit ~7 verified IRs below it. The Solidity→Yul gap is a **single
composition seam** (Solidity-source ⊑ Yul, chained into `compile_correct` by
`ForwardRel.trans`) whose **proof is its own stratified tower**, because
Solidity→Yul is a *larger* semantic distance than the Yul→EVM gap Solidus itself
decomposed into ~7 IRs. Ordered intermediate IRs (top-down from the elaborated
core to Yul), each an adjacent `ForwardRel` with its own done-relation:
- **Sd — dispatch/object**: selector table → Yul dispatcher `switch`. done-rel:
  `OpenWorld` + output/revert bytes + logs (this *is* the composition seam's
  top done-relation — observable values, no layout). MEDIUM.
- **Sc — calling convention / function boundary**: internal fns → Yul functions,
  internal calls → Yul calls. done-rel: `OpenWorld` + return values + control
  outcome, by induction on source fuel. **LARGE, HARDEST proof — but the source
  IR now exists** (`FunctionTable` + `internalCall`/`internalCallPtr`, recursion
  representable; D1 resolved). Stated fragment: modifiers inlined.
- **Sm — memory layout**: structural values/`bytes` → flat Yul memory + FMP +
  head/tail. done-rel: value ≅ memory region under an invariant; final
  `memory`/`activeWords` match. LARGE — full translation layer (our memory is an
  object heap; the byte model is built fresh here).
- **Sx — ABI codec**: encode/decode/dispatch → byte/memory ops. done-rel:
  byte-identical bytes. MEDIUM, rides on Sm.
- **Sy — storage layout**: typed paths/mappings/arrays/packing → slot arithmetic
  via keccak (the materialized `E`). done-rel: typed store ≅ word store under `E`
  = `OpenWorld` storage. SMALL–MEDIUM, near-identity on our side.
- **Sk — arithmetic/control**: checked ops+Panic → Yul overflow snippets;
  structured control → Yul control. done-rel: word equality + control match.
  SMALLEST, near-1:1.
The transcript is the shared `Query` alphabet at every seam; fuel exhaustion is
the reflectable `outOfFuel` outcome each `trans` `hReflect` needs.

**Which tower layers are already cheap vs face a full translation layer.** The
earlier "well-positioned" framing was too flat — position varies sharply *by
layer*:
- **Cheap / already at the Yul level (aligned representation):** *Sy (storage)* —
  storage is word-addressed, solc-exact, real keccak; *Sk (arithmetic/control)* —
  word ops definitionally `EvmYul.UInt256`, checked = wrapping-builtin + explicit
  Panic = solc's own Yul shape, structured control lines up. Deterministic
  Yul-compatible evaluation order and the `outOfFuel` outcome make the shared
  parts of *every* seam (transcript, truncation) well-defined. These are the
  expensive-to-get-right primitives, and they are right.
- **Full translation layer (representation mismatch):** *Sm (memory)* — the
  object-heap memory has no correspondence to Yul's flat bytes (a new model,
  invariant, and per-type layout proofs); *Sx (ABI)* rides on it. *Sd
  (dispatch)* is a moderate structural map.
- **Hardest proof, source now in place:** *Sc (calling convention)* — the
  function boundary is preserved in the core (boundary-completion arc) and
  recursion is representable; what remains is the genuinely hard call-graph
  induction, plus the stated modifiers-inlined fragment.

So the current core is a strong **Sy/Sk/Sd/Sc** anchor (Sc modulo the modifier
fragment) and an adequate-but-mismatched **Sm/Sx** anchor — mid-tower, not the
top of a single short hop, but with no structural break remaining.

**The "do it now" refactorings (N1–N4) are all DONE**, and **D1 is resolved**
in the source (boundary-completion arc). Still open from this study's ledger:
**P1** (materialize the storage-layout `E`, the Sy artifact — optional early
de-risking, lean toward deferring), **V3** (`unspecifiedOrders` scaffolding),
and the deliberately-deferred lowering-era items below.

Everything genuinely lowering-shaped (memory layout, revert-bytes relation, exp,
immutables, gas/initCode alignment, elaboration correctness) is deferred, per the
roadmap's "no new speculative interfaces" — the current phase only needs to leave
the source semantics clean, and it is close.

*Deliverable written (uncommitted) at `docs/compile-to-yul-readiness.md`.*
