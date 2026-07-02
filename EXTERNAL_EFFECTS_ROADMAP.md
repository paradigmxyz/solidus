# Open Effects Architecture

Status: complete; retained as an architectural summary. Both the compiler-side
migration and the gasful target refinement described below are finished and
composed into the published theorems. Current status is tracked in
[`ROADMAP.md`](ROADMAP.md), and the exact claim boundary is maintained in
[`PRODUCTION_ASSUMPTIONS.md`](PRODUCTION_ASSUMPTIONS.md).

## Completed Compiler Boundary

The production theorem uses one ordered `Simulation.Interaction` tree across
the compiler:

- `GAS` and `MSIZE` suspend at resource queries;
- CALL, CALLCODE, DELEGATECALL, STATICCALL, CREATE, and CREATE2 suspend at
  normalized external requests;
- the request contains the exact caller-visible pre-world and opcode operands;
- the same dependent answer is supplied to source and target continuations;
- logs, storage, transient storage, balances, account data, memory, returndata,
  and terminal outcomes remain related around those suspensions;
- every compiler pass preserves the same request order through the emitted raw
  byte image.

This universal open-world theorem is the intended compiler semantics. It proves
preservation for every shared external strategy, including strategies realized
by reentrant contracts, contract creation, or precompiles. The compiler need
not implement or verify those external programs.

## Target-Derived Resource Observations

Yul does not need an instruction-cost semantics. Its `gas()` and `msize()`
operations are parameterized observations:

```text
for every resource transcript t,
  Yul(open, t) is related to emitted-bytecode(open, t)
```

EVMYulLean already contains a gasful EVM runner that charges instructions,
computes memory expansion and EIP-150 forwarding, returns unused call gas, and
detects out-of-gas. The gasful target theorem — completed and published as
`optimizedRawSolcIrToGasfulRawBytecode` via `Assembly.GasfulBridge` — does all
of the following:

1. relate that gasful run to the open bytecode run after erasing target-only
   gas/control data;
2. extract the actual `GAS` and `MSIZE` values from the gasful run;
3. use those values to resolve the target interaction and, by the existing
   compiler theorem, the source interaction;
4. relate runner fuel, decoding, PC/termination, the valid-jump table, and the
   decoder-window representation bound;
5. relate ordinary and dynamic charges, including memory expansion, warm/cold
   access, storage/account/copy/log/hash/create costs, and EIP-150 call gas;
6. handle out-of-gas and stack, opcode/jump, returndata, static-mode, and
   intrinsic CALL/CREATE exceptions through an explicit outcome relation or
   source-facing resource premises;
7. decompose successful CALL/CREATE through the same external-strategy
   interface while retaining target-internal effective/returned gas and
   caller-local memory/returndata effects.

The final composition names the actual gasful EVM runner and does not add a
target trace, response oracle, replay certificate, or compiler-generated
resource certificate as a public premise.

## Deliberately Outside Compiler Preservation

The following are not missing steps in preservation from Yul frame execution to
EVM frame execution:

- verification of external contract or precompile implementations;
- top-level transaction intrinsic gas, fees, nonce processing, receipts,
  refund settlement, transient-storage clearing, or final `SELFDESTRUCT`
  processing;
- source maps, ABI/metadata compatibility, deployment-size policy, compiler
  totality, optimization quality, or support for every fork/dialect;
- adequacy of the chosen EVM model, cryptographic/FFI code, or the ordinary Lean
  and native trusted computing base.

Those may be separate product, coverage, chain-integration, or specification-
trust goals. They must not be presented as blockers to the compiler's open-
world preservation theorem.
