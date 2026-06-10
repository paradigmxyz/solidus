import EvmCompiler.Compiler
import EvmCompiler.Simulation.Outcome
import EvmCompiler.TypedCfg
import EvmCompiler.Public

/-!
Stable compiler API.

Historical theorem corridors and runtime-specific audit aliases are available
through `EvmCompiler.Legacy`; importing the root compiler no longer pulls those
large compatibility modules into downstream builds.
-/
