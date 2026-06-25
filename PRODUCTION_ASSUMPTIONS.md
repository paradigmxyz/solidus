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

The primary theorem is
`Yul.EndToEnd.optimizedSolcYulToRawBytecode`. Its only explicit hypothesis is:

1. `hObject`: running the checked recursive object compiler produced the named
   artifact.

`hObject` is the graph equation of an executable partial compiler, not
externally supplied proof evidence. The theorem names an `artifact`, so the
equation ties that value to the exact result computed from `object` and
`linkerSymbols`; an arbitrary artifact cannot satisfy it. A caller obtains the
equation directly by evaluating and case-splitting on the compiler:

```lean
match hCompile :
    object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
      linkerSymbols with
| none => -- checked rejection; there is no artifact to execute
| some artifact =>
    Yul.EndToEnd.optimizedSolcYulToRawBytecode hCompile
```

The equation cannot be derived for every input because the checked compiler is
intentionally fail-closed: malformed, unsupported, or unschedulable inputs
return `none`. An unconditional theorem returning an artifact for every object
would incorrectly assert compiler totality. A theorem stated by matching on the
compiler result could hide `hObject` syntactically, but would have exactly the
same logical content.

The primary theorem has no `hFinished`, `hTerminal`, or source-completion
premise. For every source semantic-fuel bound it preserves the exact ordered
interaction prefix up to source `OutOfFuel`; at truncation it makes no claim
about the target suffix. The derived theorem
`Yul.EndToEnd.optimizedSolcYulToRawBytecodeFinished` accepts `hFinished` only
when a caller wants to upgrade that prefix result to a related final outcome.
There `hFinished` is an execution fact saying every open-world branch reaches a
genuine halt or supported runtime error without exhausting the chosen source
semantic fuel. It is not an assumption of primary compiler correctness, and
arbitrary recursive Yul cannot satisfy it uniformly.

Malformed-source exclusion is not hidden in either theorem:
`truncated_iff_outOfFuel` proves that public truncation is exactly source
`OutOfFuel`, while checked validation and scoped preservation derive
missing-name, arity, expression, and contract/function facts internally.

## Derived Facts

Successful artifact construction internally derives all of the following:

- optimized-Yul validation, source well-formedness, scoping, and supported
  primitive checks;
- primitive availability for the bridge-declared London, Paris, Shanghai, or
  Cancun target, propagated through every recursive frontend object;
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
safety, generated-context, certificate, or oracle premises.

## State Relation

The theorem does not merely compare return values. Regular execution relates
the mutable code-erased open world exactly: account nonce, balance, storage,
transient storage, executable code bytes, substate/logs, and created accounts.
It also relates memory, active memory words, environment, calldata, and the
active code image. Compiler control data such as PC, structural execution
counters, stack layouts, and private locals is related at its owning layer.

At a terminal halt, the relation intentionally omits scratch return-data
bookkeeping and dead control/stack data that no continuation can observe. It
retains output, memory, active words, the available-gas field in the
parameterized model, the execution environment, and the open world. This does
not claim that the field has been updated by gasful EVM charging. Therefore the
claim is observational state equivalence, not literal equality of every record
field.

## Source Boundary And Frontend

The normalized entry point accepts a checked `Solidity.Frontend.Object`. Its
execution-side source in the public theorem is the canonical ordered Yul
contract retained in the successful artifact. The backend preservation spine
from that ordered Yul program through emitted bytes is checked.

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

One compiler-preservation obligation remains if the claimed source is the raw
selected Yul AST rather than the canonical ordered Yul program: the local
decoding/elaboration facts, especially nested-function hoisting and
alpha-renaming through complete caller/control contexts, must be composed into
a whole-source same-observation theorem. The current raw theorem executes the
elaborated ordered source; successful raw decoding by itself is not that
semantic bridge.

The raw frontend additionally checks solc's `difficulty()`/`prevrandao()` split
before both spellings lower to opcode `0x44`; successful conversion derives
that check internally.

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
the compiler does not need to verify that external program. What remains is a
target-side contextual/refinement theorem showing that a gasful EVM frame can
be decomposed into these requests and responses while preserving the caller's
observable result.

## Remaining Compiler-Preservation Obligations

Only the following are current gaps in a preservation theorem from the claimed
Yul source to the actual gasful EVM runner:

1. **Source-facing frontend preservation, when that is the declared source.**
   Complete and compose the remaining raw-Yul elaboration and object-resolution
   preservation facts so the theorem starts from execution of the selected
   source AST rather than only execution of its elaborated ordered program. The
   known active frontier is nested-function hoisting/alpha-renaming through full
   caller and control contexts.
2. **Gasful target refinement.** Relate EVMYulLean's gasful execution of the
   emitted byte image to the public open bytecode interaction after erasing
   target-only gas/control data. This bridge must:
   - use the gasful run's actual `GAS` and `MSIZE` observations to resolve the
     already-matched resource queries;
   - relate runner fuel, byte decoding, PC advance, termination, the supplied
     valid-jump table, and the decoder-window representation bound;
   - account for ordinary and dynamic charging, including memory expansion,
     warm/cold account and storage access, copy/log/hash/storage/create costs,
     EIP-150 effective forwarding, stipends, and returned gas, without adding a
     cost semantics to Yul;
   - treat out-of-gas and real EVM exceptional conditions, including stack
     underflow/overflow, invalid opcodes/jumps, return-data copy bounds, static
     restrictions, and intrinsic CALL/CREATE failures, either through an
     honest outcome relation or explicit source-facing resource premises;
   - decompose successful CALL/CREATE execution, including caller-local
     memory/returndata/gas effects and child commit/revert selection, through
     the existing shared external strategy rather than requiring verified
     external programs or precompiles.
3. **Public composition.** Compose that target refinement with
   `optimizedSolcYulToRawBytecode` so the final theorem names the actual gasful
   EVM runner and contains no compiler-generated oracle or certificate premise.

For the deliberately narrower source boundary consisting of the already-
elaborated canonical ordered Yul contract, item 1 is out of scope and item 2 is
the only missing semantic bridge. A claim beginning at the selected raw Yul
object requires both items.

The existing open theorem has already completed the compiler-side part of
target-derived gas observations: for every answer, source and target expose the
same resource query and use the same value. The missing theorem proves that the
gasful target execution supplies the answers and related outcome.

## Not Compiler-Preservation Gaps

The following may matter for a larger product, chain-integration, language-
coverage, or trusted-specification claim, but they are not prerequisites for a
formally verified lowering from the declared Yul AST semantics to the declared
EVM frame semantics:

- implementing or verifying external contracts and Ethereum precompiles;
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
`True` fields. They do not discharge the gasful target-refinement obligation
and are not used to inflate the optimized-Yul end-to-end theorem.

## Release Evidence

Tests are evidence of implementation coverage, not substitutes for theorem
scope. The release gates currently include both supported solc pins, generated
pressure and semantic surfaces, executable local/external code inspection,
constructor success/revert/rollback and CREATE2 collision, delegated proxy
state/reentrancy/rollback/upgrade execution, exact Permit2, linked Aave Pool,
linked PoolManager creation/runtime, full pinned Safe and ERC-4337 EntryPoint
creation/runtime, and fourteen pinned real-repository suites. Safe and
EntryPoint are compile gates; only cases for which solc emits a reference image
are counted as differential execution tests. The kernel proof gate reports
only `propext`, `Classical.choice`, and `Quot.sound` for the public theorem.
The supported-version matrix also compiles honest London and Cancun fixtures
and rejects Cancun-only `MCOPY`/transient-storage syntax relabeled as London.
It separately compiles London `difficulty()` and Paris `prevrandao()`, then
rejects both cross-fork relabelings.
