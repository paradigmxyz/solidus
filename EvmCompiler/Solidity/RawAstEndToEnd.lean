import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Yul.EndToEnd

/-!
Raw solc Standard JSON to bytecode theorem composition.

The raw decoder/elaborator and artifact wrapper stay Solidity-owned. This
module is only the thin public composition that feeds their checked artifact
result into the existing optimized-Yul end-to-end theorem.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst

/-- Primary raw-solc theorem. A successful checked compilation from raw solc
Standard JSON internally decodes the selected `irOptimizedAst`, elaborates it to
`Solidity.Frontend`, extracts linker metadata, and preserves every finite
ordered open-world prefix to the emitted raw bytecode image. -/
theorem optimizedRawSolcIrToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
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
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  exact
    Yul.EndToEnd.optimizedSolcYulToRawBytecode
      (object := program.object)
      (linkerSymbols := linkerSymbols)
      (artifact := artifact)
      (sourceFuel := sourceFuel)
      (baseSource := baseSource)
      hProgramCompile

/-- Finished-source corollary for the raw-solc theorem. This retains the
unconditional theorem as primary; the source-finished premise is only used to
upgrade finite-prefix preservation to a full open-world relation. -/
theorem optimizedRawSolcIrToRawBytecodeFinished
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (Yul.EndToEnd.installedSourceState artifact baseSource))) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
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
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  exact
    Yul.EndToEnd.optimizedSolcYulToRawBytecodeFinished
      (object := program.object)
      (linkerSymbols := linkerSymbols)
      (artifact := artifact)
      (sourceFuel := sourceFuel)
      (baseSource := baseSource)
      hProgramCompile
      hFinished

end RawAst
end Solidity
end EvmCompiler
