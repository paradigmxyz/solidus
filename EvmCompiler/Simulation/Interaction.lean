/-
Re-export stub: the Simulation alphabet is single-sourced from the pinned
`evm-interaction` package (module `EvmInteraction.Simulation.Interaction`; the
declaration namespaces remain `EvmCompiler.Simulation.*`, so every frozen
theorem statement is textually unchanged). This stub keeps the historical
module name importable so frozen files' import lines stay byte-identical.
-/
import EvmInteraction.Simulation.Interaction
