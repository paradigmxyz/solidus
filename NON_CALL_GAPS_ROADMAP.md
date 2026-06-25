# Archived Non-CALL Gas-Aware Roadmap

This file formerly tracked the deleted no-CALL `Assembly.GasAware` /
`Yul.NoCallRuntime` proof route. Its target-side premise packages and theorem
names are historical and are not the current compiler boundary.

The production proof now preserves GAS/MSIZE and CALL/CREATE together through
one open interaction semantics. Current work is tracked in
[`ROADMAP.md`](ROADMAP.md), with the exact boundary in
[`PRODUCTION_ASSUMPTIONS.md`](PRODUCTION_ASSUMPTIONS.md).

The surviving lesson from the old route is still relevant: successful execution
in the gas-erased target does not by itself imply safety for the gasful EVM.
Stack overflow, jump validity, static restrictions, and out-of-gas must be
derived for the actual compiled trace or exposed as honest source-facing
resource premises. That obligation now belongs to the single gasful-target
refinement theorem, not to a separate no-CALL compiler corridor.

External contract behavior, precompile implementation, transaction processing,
artifact compatibility, and deployability policy are not compiler-preservation
gaps and are intentionally absent from this roadmap.
