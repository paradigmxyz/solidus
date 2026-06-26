import EvmCompiler.Yul.EndToEnd
import EvmCompiler.Assembly.GasfulBridgeDecode

namespace EvmCompiler
namespace Yul
namespace EndToEnd

/-!
Gasful optimized-Yul composition.

`EndToEnd` stays as the short public open-bytecode spine.  This sibling module
adds the gasful target boundary by composing that spine with the explicit
`EVM.X`-to-open-bytecode bridge relation.
-/

/-- Composition point for a concrete gasful target run.  The source theorem
remains cost-model-free: `GAS` and `MSIZE` are open observations in the emitted
bytecode semantics, while `hGasful` supplies the concrete charged `EVM.X` run
that resolves those observations and accounts for out-of-gas and external
CALL/CREATE boundaries. -/
theorem optimizedSolcYulToGasfulRawBytecodeOfOpenRunBridge
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel gasFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hGasful :
      ∀ structuredFuel,
        Assembly.GasfulBridge.RunRefinesOpen
          (EvmYul.EVM.X gasFuel
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpen
          (EvmYul.EVM.X gasFuel
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, hAccepted, hForward⟩ :=
    optimizedSolcYulToRawBytecode (sourceFuel := sourceFuel)
      (baseSource := baseSource) hObject
  exact ⟨structuredFuel, hAccepted, hForward, hGasful structuredFuel⟩

end EndToEnd
end Yul
end EvmCompiler
