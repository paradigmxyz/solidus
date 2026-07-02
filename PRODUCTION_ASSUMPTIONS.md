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
  depth, and top-16 accessibility; this is not yet a global proof of the real
  EVM's 1024-word stack headroom on every recursive trace;
- stack-only lowering with no compiler memory access or scratch reservation;
- `memoryguard(size) = size` for the stack-only backend;
- canonical Yul-to-Functions and Functions-to-Expressions initial relations;
- exact installation of the compiled byte image for `CODESIZE`/`CODECOPY`;
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
`8b610d524898f9bc7d451b017e0df6057cc88cd9`, which includes native `CLZ`,
execution-side EIP-7702 delegated-code lookup, and Fusaka MODEXP gas/size
rules. The raw solc `clz` builtin is still supported through the verified
generated-helper lowering, so the compiler does not need to emit the native
opcode. EIP-7702 transaction authorization-list processing remains outside this
frame-level compiler theorem.

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
`Yul.EndToEnd` theorems, and fails unless every report is exactly `propext`,
`Classical.choice`, and `Quot.sound`.
The supported-version matrix also compiles honest London and Cancun fixtures
and rejects Cancun-only `MCOPY`/transient-storage syntax relabeled as London.
It separately compiles London `difficulty()` and Paris `prevrandao()`, then
rejects both cross-fork relabelings. Focused metadata tests cover Prague/Osaka
canonical acceptance, Pectra/Fusaka bridge aliases, unknown-fork rejection, and
the existing generated-helper lowering path for raw `clz`.
