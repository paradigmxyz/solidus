import EvmCompiler.Solidity.RawAst
import EvmCompiler.Solidity.Public

/-!
Checked artifact-facing wrappers for the raw solc frontend.

The raw decoder/elaborator itself stays in `Solidity.RawAst` and stops at
`Solidity.Frontend.Program`.  This module is the narrow integration point with
the existing checked stack-object artifact API.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst

def compileArtifactFromRawSolcIrWithLinkerSymbols? (rawJson : String)
    (selection : Selection)
    (linkerSymbols : List (Frontend.Name × Frontend.Word)) :
    Option Frontend.Program.Artifact := do
  let program ← decodeAndElaborateSolcIr? rawJson selection
  program.compileArtifactWithLinkerSymbols? linkerSymbols

def compileArtifactFromRawSolcIr? (rawJson : String)
    (selection : Selection) : Option Frontend.Program.Artifact :=
  compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection []

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_valid
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ program : Frontend.Program,
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact := by
  unfold compileArtifactFromRawSolcIrWithLinkerSymbols? at hCompile
  cases hDecode : decodeAndElaborateSolcIr? rawJson selection with
  | none =>
      simp [hDecode] at hCompile
  | some program =>
      have hValid :=
        Frontend.Program.compileArtifactWithLinkerSymbols?_valid
          (program := program) (linkerSymbols := linkerSymbols)
          (artifact := artifact)
      have hProgramCompile :
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact := by
        simpa [hDecode] using hCompile
      exact ⟨program, rfl, hValid hProgramCompile⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_decodingCorrect
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    Assembly.Compact.DecodingCorrect
      artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList artifact.image.bytes) := by
  unfold compileArtifactFromRawSolcIrWithLinkerSymbols? at hCompile
  cases hDecode : decodeAndElaborateSolcIr? rawJson selection with
  | none =>
      simp [hDecode] at hCompile
  | some program =>
      have hCorrect :=
        Frontend.Program.compileArtifactWithLinkerSymbols?_decodingCorrect
          (program := program) (linkerSymbols := linkerSymbols)
          (artifact := artifact)
      have hProgramCompile :
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact := by
        simpa [hDecode] using hCompile
      exact hCorrect hProgramCompile

end RawAst
end Solidity
end EvmCompiler
