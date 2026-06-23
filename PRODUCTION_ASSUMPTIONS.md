# Production Assumptions

This document states the trust and model boundary of the stack-only optimized
Yul backend. It distinguishes facts computed by the checked compiler from
conditions on an execution and from semantics that are not yet refined to a
full production EVM.

## Public Theorem

The primary theorem is
`Yul.EndToEnd.optimizedSolcYulToRawBytecodeFinished`. Its explicit hypotheses
are:

1. `hObject`: running the checked recursive object compiler produced the named
   artifact.
2. `hFinished`: the canonical parameterized Yul execution reached only genuine
   terminal or runtime-error leaves, rather than a structurally truncated
   source-semantics leaf.

`hObject` is an executable compiler equation, not externally supplied proof
evidence. `hFinished` is an execution condition. Arbitrary recursive Yul need
not terminate, so no sound compiler can derive it uniformly from syntax.
At present `SourceFinished` also excludes malformed source-interpreter failures.
Checked validation and scoped-state invariants have begun deriving those cases
internally (including deferred and direct pure variable lookup), but a complete
accepted-Yul validation/progress theorem has not yet separated them from the
public execution condition.

## Derived Facts

Successful artifact construction internally derives all of the following:

- optimized-Yul validation, source well-formedness, scoping, and supported
  primitive checks;
- Functions normalization and its preservation theorem;
- liveness, symbolic layouts, schedules, joins, dormant frames, stack depth,
  and top-16 accessibility;
- stack-only lowering with no compiler memory access or scratch reservation;
- `memoryguard(size) = size` for the stack-only backend;
- canonical Yul-to-Functions and Functions-to-Expressions initial relations;
- exact installation of the compiled byte image for `CODESIZE`/`CODECOPY`;
- target-fuel bounds and exclusion of compiler-introduced structural
  `OutOfFuel` whenever the source run is finished;
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
constructor success/revert/rollback and CREATE2 collision, exact Permit2,
linked Aave Pool, linked PoolManager creation/runtime, and fourteen pinned
real-repository suites. The kernel proof gate reports only `propext`,
`Classical.choice`, and `Quot.sound` for the public theorem.
