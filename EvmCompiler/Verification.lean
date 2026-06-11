import EvmCompiler.Public
import EvmCompiler.PublicVerification
import EvmCompiler.Compiler.AllocatedTypedCfg
import EvmCompiler.Functions.ScratchFrameSpill
import EvmCompiler.Locals.EffectSemantics
import EvmCompiler.Structured.TypedCfgPreservation
import EvmCompiler.TypedCfg.Preservation
import EvmCompiler.Yul.EffectSemantics
import EvmCompiler.Yul.ObjectSemantics
import EvmCompiler.Yul.ObserverOracle

/-!
Stable verification aggregate.

This root checks the proof-bearing components used by the public compiler
without restoring the retired replay runtimes, parallel allocation backends,
or audit-alias corridor.
-/
