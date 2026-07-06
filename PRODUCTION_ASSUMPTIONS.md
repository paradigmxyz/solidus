# Production Assumptions

This document states the trust and model boundary of the stack-only optimized
Yul backend. Its primary question is compiler preservation: whether execution
of the declared Yul source semantics is preserved by execution of the emitted
bytes in the declared EVM semantics. Transaction processing, external-program
correctness, artifact compatibility, deployability policy, and toolchain trust
are recorded separately; they are not silently counted as compiler-preservation
obligations.

This file and `ROADMAP.md` are the only authoritative current gap descriptions.
`PROGRESS_LOG.md` is append-only history; oracle contexts, Aristotle prompts,
proof requests, and archived roadmap files describe the checkpoint at which
they were written and must not be read as current status.

## Which Theorem Should I Rely On?

Every entry below is a checked Lean theorem on the supported raw-solc spine.
The sections after this one state exact hypotheses and caveats; this list only
routes a claim to its endpoint.

- Raw finite-prefix preservation:
  `RawAst.optimizedRawSolcIrToRawBytecode`
  (`EvmCompiler/Solidity/RawAstEndToEnd.lean`) relates execution of the
  selected raw solc `irOptimizedAst` object to the emitted byte image in the
  gas-free open semantics, from compile success alone.
- Gasful frame refinement:
  `RawAst.optimizedRawSolcIrToGasfulRawBytecode` (same file) adds the
  recursive gasful `EVM.X` frame refinement; its only runtime premise is the
  initial `GasfulBridge.OpenStateRel`.
- Gasful claims with no escape branch:
  `Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeTotal` (+ `FinishedTotal`,
  `TerminalTotal`, `TotalWithCodeSuffix`;
  `EvmCompiler/Yul/GasfulCrown.lean`) is the crown for artifacts that carry a
  stack-headroom certificate: the charged run completes in refinement,
  collapses an exceptional child frame in step, or halts out-of-gas with the
  committal rollback semantics; `OutOfFuel`, `StackOverflow`, and
  `BadJumpDestination` are excluded outright.
- Creation frames with constructor arguments:
  `RawAst.optimizedRawSolcIrToRawBytecodeWithCodeSuffix` and
  `RawAst.optimizedRawSolcIrToGasfulRawBytecodeWithCodeSuffix`
  (`EvmCompiler/Solidity/RawAstEndToEnd.lean`) install `image ++ suffix`
  uniformly on both sides, covering solc's appended ABI-encoded constructor
  arguments.
- Creation-to-runtime image linkage:
  `Object.creationImage_embeds_deployedRuntimeImage`
  (`EvmCompiler/Solidity/CreationRuntimeImage.lean`) proves, for the
  standard single-runtime-child creation shape, that the compiled runtime
  child image is embedded verbatim at its planned layout offset inside the
  creation image.
- Deploy-time immutable patching:
  `Object.patchImmutables_image_compileWithImmutableValues?_ofCompile`
  (`EvmCompiler/Solidity/ImmutablePatch.lean`) proves patching the compiled
  image's immutable windows equals a fresh compile with those values, from
  compile success alone.
- Unlinked libraries:
  `Object.patchImmutablesAndLibraries_image_ofCompileUnlinked` and
  `Object.compileVerifiedStackObjectArtifactUnlinked?_withValues_resolvesOriginal`
  (`EvmCompiler/Solidity/LibraryPatch.lean`) prove that writing the 20
  address bytes at the exported `linkReferences` offsets of an unlinked
  compile reproduces the pipeline's own compile with those addresses
  resolved (see "Unlinked Libraries" for the placeholder-byte caveat).

## Public Theorem

The primary raw-input theorem is
`RawAst.optimizedRawSolcIrToRawBytecode`. Its only explicit hypothesis is:

1. `hCompile`: running the checked raw Standard JSON compiler produced the
   named artifact.

Its conclusion identifies the parsed JSON, selected `irOptimizedAst` object,
and object-builtin context, then relates execution of that raw object to the
emitted byte image. The adjacent theorem
`Yul.EndToEnd.optimizedSolcYulToRawBytecode` remains available when the declared
source is already canonical ordered Yul.

`hCompile` is the graph equation of an executable partial compiler, not
externally supplied proof evidence. The theorem names an `artifact`, so the
equation ties that value to the exact result computed from `rawJson` and
`selection`; an arbitrary artifact cannot satisfy it. A caller obtains the
equation directly by evaluating and case-splitting on the compiler:

```lean
match hCompile :
    compileArtifactFromRawSolcIr? rawJson selection with
| none => -- checked rejection; there is no artifact to execute
| some artifact =>
    RawAst.optimizedRawSolcIrToRawBytecode hCompile
```

The equation cannot be derived for every input because the checked compiler is
intentionally fail-closed: malformed, unsupported, or unschedulable inputs
return `none`. An unconditional theorem returning an artifact for every object
would incorrectly assert compiler totality. A theorem stated by matching on the
compiler result could hide `hCompile` syntactically, but would have exactly the
same logical content.

The primary raw and canonical theorems have no `hFinished`, `hTerminal`, or
source-completion premise. For every source semantic-fuel bound they preserve
the exact ordered interaction prefix up to source `OutOfFuel`; at truncation
they make no claim about the target suffix. The derived theorem
`Yul.EndToEnd.optimizedSolcYulToRawBytecodeFinished` accepts `hFinished` only
when a caller wants to upgrade that prefix result to a related final outcome.
There `hFinished` is an execution fact saying every open-world branch reaches a
genuine halt or supported runtime error without exhausting the chosen source
semantic fuel. It is not an assumption of primary compiler correctness, and
arbitrary recursive Yul cannot satisfy it uniformly.

Malformed-source exclusion is not hidden in these theorems:
`truncated_iff_outOfFuel` proves that public truncation is exactly source
`OutOfFuel`, while checked validation and scoped preservation derive
missing-name, arity, expression, and contract/function facts internally.

## Derived Facts

Successful artifact construction internally derives all of the following:

- optimized-Yul validation, source well-formedness, scoping, and supported
  primitive checks;
- primitive availability for the bridge-declared London, Paris, Shanghai,
  Cancun, Prague/Pectra, or Osaka/Fusaka target, propagated through every
  recursive frontend object;
- Functions normalization and its preservation theorem;
- liveness, symbolic layouts, schedules, joins, dormant frames, symbolic stack
  depth, and top-16 accessibility; these compile-time facts alone are not a
  global proof of the real EVM's 1024-word stack headroom — that bound is
  discharged separately, for artifacts that carry one, by the fail-closed
  stack-headroom certificate (see "Completed Compiler-Preservation Chain");
- stack-only lowering with no compiler memory access or scratch reservation;
- `memoryguard(size) = size` for the stack-only backend;
- canonical Yul-to-Functions and Functions-to-Expressions initial relations;
- exact installation of the compiled byte image for `CODESIZE`/`CODECOPY`
  (with `WithCodeSuffix` variants installing `image ++ suffix` uniformly on
  both sides for creation frames; see "Creation Frames And Constructor
  Arguments" below);
- target-fuel bounds preserving every source-visible prefix, plus exclusion of
  compiler-introduced structural `OutOfFuel` in the derived all-finished result;
- TypedCfg generation, certification, assembly acceptance, compact relocation,
  byte decoding, the code/data `INVALID` sentinel, child-object layout, linker
  substitution, and the exact final image.

None of these appears as a premise of the canonical public theorem. The
architecture gate rejects regressions that reintroduce initial-state, scratch
safety, generated-context, certificate, or oracle premises. It also fails when
any built `.lake` object lacks a matching source module, so deleted Lean API
cannot silently keep resolving from orphaned build artifacts after a refactor.

## State Relation

The theorem does not merely compare return values. Regular execution relates
the mutable code-erased open world exactly: account nonce, balance, storage,
transient storage, executable code bytes, substate/logs, and created accounts.
It also relates memory, active memory words, environment, calldata, and the
active code image. Compiler control data such as PC, structural execution
counters, stack layouts, and private locals is related at its owning layer.

At a terminal halt, the relation intentionally omits scratch return-data
bookkeeping and dead control/stack data that no continuation can observe. It
retains output, memory, active words, the execution environment, and the open
world. The canonical open semantics carries a parameterized available-gas
field; the gasful bridge instead relates the concrete target after erasing its
target-only gas/control bookkeeping. Therefore the claim is observational
state equivalence, not literal equality of every record field.

## Source Boundary And Frontend

The production raw entry point accepts Standard JSON containing solc's selected
optimized-Yul `irOptimizedAst`. Its execution-side source is the independently
interpreted raw Yul object, before frontend elaboration. The canonical ordered
Yul contract retained in the artifact is an internal adjacent boundary.

The raw entry point decodes and elaborates selected Standard JSON
`irOptimizedAst` in Lean and then invokes the same checked compiler. Python may
invoke solc, transport JSON, and run differential tests, but it no longer
constructs the raw theorem's `Solidity.Frontend.Program`. The legacy normalized
bridge and standalone-Yul recovery paths still use Python and are not the raw
theorem boundary.

For a Yul-to-EVM claim, Solidity-to-Yul lowering, source/remapping selection,
and correctness of solc itself are upstream of the declared source language.
They matter only for a broader Solidity-to-EVM or textual-toolchain claim. The
requested fork and linker values remain compilation inputs, while successful
Lean compilation checks their structural consequences: missing metadata is
rejected, and an object containing instructions unavailable in its declared
fork cannot produce an artifact.

`RawAst.Raw.SourcePreservation.optimizedRawSolcIrToRawSourceBytecode` composes
the complete raw frontend path. It covers lexical scope resolution,
nested-function hoisting and alpha-renaming through recursive caller/control
contexts, generated `clz` expansion, object/data ordering and builtins,
memoryguard inference, top-level function-table construction, and empty-code
objects. No generated-name, layout, replay, or preservation certificate is a
public premise.

The raw frontend additionally checks solc's `difficulty()`/`prevrandao()` split
before both spellings lower to opcode `0x44`; successful conversion derives
that check internally.

## Fork Surface

The solc-facing CLI accepts canonical `evmVersion` spellings London, Paris,
Shanghai, Cancun, Prague, and Osaka. The Lean raw and bridge decoders also
accept Pectra as an alias for Prague and Fusaka as an alias for Osaka, so
metadata transported from fork-family terminology still reaches the same
checked dialect profile. Unknown future names fail closed.

Closed native frame execution is governed by the EVMYulLean commit selected in
`lakefile.lean`. This compiler repo currently pins
`3c5c44a62f4e7964bd1bc648caa708a111664c84` (branch `djtotal`), which includes
native `CLZ`, execution-side EIP-7702 delegated-code lookup, Fusaka MODEXP
gas/size rules, and a total Nat-indexed jumpdest scanner `D_J_aux`
(`termination_by c.size - n`) with unfolding lemmas
(`D_J_aux_out_of_bounds`/`D_J_aux_step`/`D_J_def`); `D_J`'s signature and
values are unchanged, but the scanner is no longer opaque, which is what lets
this repo prove jumpdest-scan membership instead of gating on the runtime
`jumpdestCorrect?` check. The raw solc `clz` builtin is supported through the
verified generated-helper lowering before Osaka and through native opcode
emission from Osaka onward. EIP-7702 transaction authorization-list processing
remains outside this frame-level compiler theorem.

Solc-emitted precompile use is different: it reaches the compiler as ordinary
`CALL`/`STATICCALL` to an address. That includes existing `ecrecover` lowering,
BN254/MODEXP calls, Prague BLS12-381 addresses `0x0b` through `0x11`, and Osaka
P256VERIFY at `0x100`. The compiler theorem preserves those calls through the
open external-boundary response model; it does not require a verified
cryptographic implementation of the precompile body. Concrete closed execution
of new precompiles remains an EVMYulLean/model-backend concern, not a compiler
preservation gap.

EIP-2935 history storage does not change this compiler theorem boundary: it is
pre-block/prestate system-contract setup plus ordinary external account state.
Likewise transaction admission, authorization-list processing, system calls,
receipts, and finalization stay outside the frame-level compiler theorem unless
a future EVMYulLean frame rule exposes them as parent-frame execution.

## Open World

`GAS` and `MSIZE` are ordered resource queries. CALL- and CREATE-family
operations are ordered open effects. Logs, storage writes, and other local
world effects update the shared `OpenWorld`, so their order is visible in the
next request and in terminal outcomes. The theorem preserves requests,
answers, state updates, and interleaving for every related open world. External
accounts carry executable bytes and mutable account data, not Yul ASTs or
compiler provenance.

Universal quantification over a shared response is the intended compiler
semantics, not an unfinished implementation of external contracts. A real
callee, reentrant contract, or precompile can instantiate the same response;
the compiler does not need to verify that external program. The checked
recursive `EVM.X` frame refinement decomposes gasful CALL/CREATE execution into
these requests and responses while preserving the caller's observable result.

## Completed Compiler-Preservation Chain

There is no known unfinished compiler pass in the finite-prefix theorem chain.
`RawAst.optimizedRawSolcIrToGasfulRawBytecode` packages both:

- raw selected-object execution to emitted open-bytecode forward preservation;
- recursive gasful `EVM.X` frame refinement to that same open-bytecode run at
  the compiler-derived budget and transcript.

Its only runtime premise is `GasfulBridge.OpenStateRel` for the concrete initial
frame. It has no `hFinished`, response oracle, replay, generated-name, layout, or
certificate premise. The result is intentionally frame-level and finite-prefix:
source semantic fuel may truncate an unobserved suffix, while transaction and
chain finalization remain outside the declared theorem boundary.

The bridge's out-of-gas branch is committal, not merely a transcript-prefix
fact. `Assembly.GasfulBridge.RunRefinesOpenCommittal` and the endpoints
concluding it
(`Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeGasBoundedCommittal`,
`...TerminalGasBounded`, and the `Total` family via
`RunRefinesOpenTotal.toRunRefinesOpenCommittal`) carry
`Assembly.GasfulBridge.OutOfGasFrameSemantics` on that branch: the charged
`EVM.X` run is exactly `.error .OutOfGass`, a code-execution boundary `Ξ`
entered at that run reports the same exceptional halt, and a message-call
boundary `Θ` built on it commits to the canonical exceptional-halt collapse —
caller world and substate restored to the checkpoint, zero returned gas,
failure flag set, empty output.

The bad-jump branch is now excluded outright for compiled artifacts when the
jump table is the interpreter's own jumpdest scan of the installed image —
exactly the table `Ξ`/`Θ` install (`EVM.X f (D_J code 0)`). The compact
compiler emits fixed-label branches only; every label destination lowers to a
located `JUMPDEST`, and `Assembly.Compact.D_J_contains_of_decodingCorrect`
proves EVMYulLean's scanner lists each of them over the artifact image
(suffix-tolerantly, so creation frames with appended constructor arguments
are covered). `Assembly.GasfulBridge.x_ne_badJumpDestination_of_frame` turns
this into `EVM.X fuel validJumps s ≠ .error BadJumpDestination` with no
stack certificate, and the endpoints
`Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_badJumpDestination`
(+ `_withCodeSuffix`) and `...runRefinesOpen_noBadJump` (+ `_withCodeSuffix`)
prune the `badJumpDestination` constructor from any `RunRefinesOpen` witness
(`Assembly.GasfulBridge.RunRefinesOpenNoBadJump`). The stack-overflow
branch is excluded separately by the fail-closed stack-headroom certificate
(`VerifiedStackObjectArtifact.stackHeadroomCert?`,
`...x_ne_stackOverflow` + `_withCodeSuffix`,
`RunRefinesOpenNoStackOverflow`); the `RunRefinesOpen` constructors are
retained additively as intermediate views.

These prunings are composed into a single crown at the gasful boundary. For
a compiled artifact that carries a stack-headroom certificate
(`stackHeadroomCert? = some cert`), the endpoints
`Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeTotal`
(+ `FinishedTotal`, `TerminalTotal`, and `TotalWithCodeSuffix` for creation
frames) conclude `Assembly.GasfulBridge.RunRefinesOpenTotal` at the
gas-derived fuel `max budget (gasAvailable + 6)` against the interpreter's
own jumpdest scan of the installed image, from compile success and
`OpenStateRel` for the concrete initial frame alone. `RunRefinesOpenTotal`
has no escape constructor: the charged run either completes in refinement
with the source-related open run, collapses an exceptional child frame in
step with the open run per EVM frame semantics (with the charged label
provably none of `OutOfFuel`, `StackOverflow`, `BadJumpDestination`), or
halts out-of-gas with the committal `OutOfGasFrameSemantics` rollback pinned
above — nothing else. `outOfFuel` is discharged structurally by the
gas-derived fuel bound
(`Assembly.GasfulFuelBound.x_ne_outOfFuel_of_gas_lt_fuel`), not by a
per-execution hypothesis.

Honest caveats on the crown: gas charging, the derived fuel bound, and the
out-of-gas boundary follow the gas schedule of the EVMYulLean commit pinned
in `lakefile.lean` (see "Fork Surface"); CALL/CREATE-family effects remain
open request/response exchanges (see "Open World"), so the crown does not
verify external programs; and genuinely recursive programs, whose operand
stacks are input-unbounded, fail the stack-headroom certificate closed and
keep the committal endpoints instead.

## Creation Frames And Constructor Arguments

Creation frames execute the checked image with the caller's ABI-encoded
constructor arguments appended: `executionEnv.code = image ++ args`. The
suffix-tolerant endpoints
`RawAst.optimizedRawSolcIrToRawBytecodeWithCodeSuffix` and
`RawAst.optimizedRawSolcIrToGasfulRawBytecodeWithCodeSuffix` (and the
canonical `Yul.EndToEnd.optimizedSolcYulToRawBytecodeWithCodeSuffix`,
`...FinishedWithCodeSuffix`, `...TerminalWithCodeSuffix`, and
`...ToGasfulRawBytecodeOfRecursiveFrameBridgeWithCodeSuffix`) quantify over an
arbitrary appended byte suffix and install `image ++ suffix` uniformly on both
sides, so source `CODESIZE`/`CODECOPY` observe exactly the code decoded by the
target machine — the mechanism solc constructors use to read their arguments.
The gasful variant enters at `EVM.X f (D_J (image ++ suffix) 0) initial`,
matching EvmYul's real creation-frame entry: jump-destination validity is
computed over the full installed code, and covered-path jump targets still
come from the compact layout inside the checked image. With the jumpdest-scan
membership theorems, that entry table provably lists every compiled label
destination even with the suffix appended, so the bad-jump branch is
refutable for these frames
(`VerifiedStackObjectArtifact.x_ne_badJumpDestination_withCodeSuffix`); the
out-of-gas outcome branch of the bridge relation is unchanged.
The exact-image theorems are the `suffix := []` instances (up to
`List.append_nil`), and remain the published runtime-code endpoints.

## Unlinked Libraries

The unlinked pipeline (`Program.compileArtifactUnlinked?`,
`RawAst.compileArtifactUnlinkedFromRawSolcIr?`) compiles `linkersymbol` names
without provided addresses by rewriting them into `loadimmutable` markers, so
unlinked bytecode carries zero-filled PUSH32 windows rather than solc's
`__$hash$__` placeholder text. The exported `linkReferences` offsets
(`start := window + 12`, `length := 20`) and the linked result follow the solc
linking contract — a linker that writes the 20 address bytes at each exported
offset produces exactly the bytes of the pipeline's own compile with those
addresses resolved
(`Object.patchImmutablesAndLibraries_image_ofCompileUnlinked`,
`Object.compileVerifiedStackObjectArtifactUnlinked?_withValues_resolvesOriginal`)
— but byte identity of UNLINKED objects with solc's unlinked output is not
claimed, and a fresh fully-linked compile may legitimately choose shorter
pushes for the same addresses. The patch endpoint covers the selected object's
own code windows; creation-side link references over the embedded runtime
payload are exported for solc compatibility and covered by running the same
endpoint with the runtime selector.

## Not Compiler-Preservation Gaps

The following may matter for a larger product, chain-integration, language-
coverage, or trusted-specification claim, but they are not prerequisites for a
formally verified lowering from the declared Yul AST semantics to the declared
EVM frame semantics:

- implementing or verifying external contracts and Ethereum precompile bodies;
- top-level intrinsic gas, fees, sender-nonce processing, transaction receipts,
  refund settlement, transaction-final transient-storage clearing, and final
  `SELFDESTRUCT` processing;
- source maps, ABI/metadata compatibility, deployment-size optimization, and
  EIP-170/EIP-3860 admission checks;
- compiler totality, acceptance of every valid Yul program, support for every
  fork or dialect, and optimization quality;
- verification of solc's upstream Solidity-to-Yul transformation when Yul is
  the declared source boundary;
- adequacy of the chosen EVM model to an external prose specification,
  host-memory/cryptographic/FFI implementation trust, and the ordinary Lean,
  native-code, OS, and hardware trusted computing base;
- a backward-equivalence theorem or a transaction-wrapper theorem
  when the claimed result is forward preservation of frame execution.

`Assembly.OutOfGasPolicyAssumption` and
`Assembly.CurrentContractProjectionAssumption` are documentation markers with
`True` fields. They are not used to discharge or inflate the raw, canonical, or
gasful end-to-end theorems.

## Release Evidence

Tests are evidence of implementation coverage, not substitutes for theorem
scope. The release gates currently include both supported solc pins, generated
pressure and semantic surfaces, executable local/external code inspection,
constructor success/revert/rollback and CREATE2 collision, delegated proxy
state/reentrancy/rollback/upgrade execution, exact Permit2, linked Aave Pool,
linked PoolManager creation/runtime, full pinned Safe and ERC-4337 EntryPoint
creation/runtime, and fourteen pinned real-repository suites. Differential
execution gates additionally deploy full-solc and Lean-backend bytecode for the
example-contract corpus and pinned Aave v3 math fixtures in one Foundry VM and
replay identical calls against both, requiring the same success flags, return
data hashes, and logs, including revert paths. Permit2 remains an
exact solc-0.8.17 legacy/version-boundary gate because that compiler emits no
structured `irOptimizedAst`; the raw compiler rejects its missing AST. Safe and
EntryPoint are compile gates; only cases for which solc emits a reference image
are counted as differential execution tests. The kernel proof gate replays
`#print axioms` for the primary raw and gasful theorems and the canonical
`Yul.EndToEnd` theorems — including the gasful Total crown endpoints and the
immutable/library patch theorems — and fails unless every report is exactly
`propext`, `Classical.choice`, and `Quot.sound`.
The supported-version matrix also compiles honest London and Cancun fixtures
and rejects Cancun-only `MCOPY`/transient-storage syntax relabeled as London.
It separately compiles London `difficulty()` and Paris `prevrandao()`, then
rejects both cross-fork relabelings. Focused metadata tests cover Prague/Osaka
canonical acceptance, Pectra/Fusaka bridge aliases, unknown-fork rejection,
pre-Osaka generated-helper lowering for raw `clz`, and Osaka native raw `clz`
emission.
