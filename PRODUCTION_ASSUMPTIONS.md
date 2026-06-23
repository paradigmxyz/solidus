# Production Assumptions

This document states the trust and model boundary of the stack-only optimized
Yul backend. It distinguishes facts computed by the checked compiler from
conditions on an execution and from semantics that are not yet refined to a
full production EVM.

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
- liveness, symbolic layouts, schedules, joins, dormant frames, stack depth,
  and top-16 accessibility;
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
retains output, memory, active words, available gas in the parameterized model,
the execution environment, and the open world. Therefore the claim is
observational state equivalence, not literal equality of every record field.

## Trusted Frontend

The theorem starts at the parsed optimized Yul object. The following remain
trusted:

- the selected pinned solc binary and its Solidity-to-optimized-Yul lowering;
- Standard JSON handling and `irOptimizedAst` production by solc;
- the Python adapter that normalizes solc JSON into checked bridge JSON;
- source-file, remapping, linker-symbol, and requested-fork inputs supplied to
  that adapter.

The Lean frontend validates the normalized object and fails closed, but there
is not yet a proof that the Python normalization preserves arbitrary solc JSON.
The requested fork is therefore still an external compilation input, but its
consequences are checked rather than trusted: missing metadata is rejected, and
an object containing instructions unavailable in its declared fork cannot
produce a checked artifact.
The raw frontend additionally checks solc's `difficulty()`/`prevrandao()` split
before both spellings lower to opcode `0x44`; successful conversion derives
that check internally.

## Open World

`GAS` and `MSIZE` are ordered resource queries. CALL-, CREATE-, and LOG-family
operations are ordered open effects. The theorem preserves their arguments,
answers, state updates, and interleaving for every related open world. External
accounts carry executable bytes and mutable account data, not Yul ASTs or
compiler provenance.

This does not verify an implementation of external contracts or Ethereum
precompiles. The corpus executes real precompiles and self-reentrant calls as
differential tests, while the formal theorem quantifies over their related open
responses.

## Unfinished Full-EVM Refinements

The following are deliberately outside the current theorem and must be closed
before describing the backend as a drop-in, fork-accurate solc replacement:

- instruction gas charging, EIP-150 forwarding, refunds, and out-of-gas
  interruption;
- a theorem connecting ordered `GAS`/`MSIZE` answers to a concrete gas-metered
  EVM run;
- concrete nested call/create execution, precompile implementations, and
  transaction-level commit/revert refinement;
- proof that the host-bounded memory representation agrees with every relevant
  mathematical EVM memory access;
- validation beyond the explicitly accepted London, Paris, Shanghai, and
  Cancun targets;
- cryptographic/FFI and any remaining imported EVM implementation trust;
- standard solc artifact compatibility such as source maps and metadata.

`Assembly.OutOfGasPolicyAssumption` and
`Assembly.CurrentContractProjectionAssumption` are documentation markers with
`True` fields. They do not discharge these refinements and are not used to
inflate the optimized-Yul end-to-end theorem.

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
