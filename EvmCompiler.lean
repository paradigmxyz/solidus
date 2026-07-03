import EvmCompiler.Compiler
import EvmCompiler.Simulation.Outcome
import EvmCompiler.TypedCfg
import EvmCompiler.Solidity.RawAstPublic

/-!
Stable compiler API.

Proof-bearing implementation modules are checked through
`EvmCompiler.Verification`; importing the stable compiler root keeps that
verification surface out of downstream runtime builds.
-/
