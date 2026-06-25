import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Yul.EndToEnd

/-!
End-to-end wrappers for the raw solc frontend.

These theorems keep Python out of the theorem source-program boundary: the
premise is successful checked compilation from raw solc Standard JSON, and the
proof composes through the existing optimized-Yul finished theorem.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_finished
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
          linkerSymbols =
        some artifact)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (Yul.EndToEnd.installedSourceState artifact baseSource))) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              (Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  unfold compileArtifactFromRawSolcIrWithLinkerSymbols? at hCompile
  cases hDecode : decodeAndElaborateSolcIr? rawJson selection with
  | none =>
      simp [hDecode] at hCompile
  | some program =>
      have hObject :
          program.object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
              linkerSymbols =
            some artifact := by
        simpa [hDecode, Frontend.Program.compileArtifactWithLinkerSymbols?]
          using hCompile
      exact
        Yul.EndToEnd.optimizedSolcYulToRawBytecodeFinished
          hObject hFinished

theorem compileArtifactFromRawSolcIr?_finished
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
          (Compiler.OpenInteractionComposition.VerifiedStackObjectDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              (Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  exact
    Yul.EndToEnd.optimizedSolcYulToRawBytecodeFinished
      hProgramCompile hFinished

end RawAst
end Solidity
end EvmCompiler
