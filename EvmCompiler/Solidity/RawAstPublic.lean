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
  match Lean.Json.parse rawJson with
  | .error _ => none
  | .ok json =>
      match decodeAndElaborateSolcIrJson json selection with
      | .error _ => none
      | .ok program =>
          match decodeLinkerSymbolsJson json selection with
          | .error _ => none
          | .ok linkerSymbols =>
              program.compileArtifactWithLinkerSymbols? linkerSymbols

theorem compileArtifactFromRawSolcIr?_decoded
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact := by
  unfold compileArtifactFromRawSolcIr? at hCompile
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hCompile
  | ok json =>
      cases hDecode : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hDecode] at hCompile
      | ok program =>
          cases hLinker : decodeLinkerSymbolsJson json selection with
          | error err =>
              simp [hParse, hDecode, hLinker] at hCompile
          | ok linkerSymbols =>
              have hProgramCompile :
                  program.compileArtifactWithLinkerSymbols? linkerSymbols =
                    some artifact := by
                simpa [hParse, hDecode, hLinker] using hCompile
              refine ⟨program, linkerSymbols, ?_, ?_, hProgramCompile⟩
              · simp [decodeAndElaborateSolcIr?, hParse, hDecode]
              · simp [decodeLinkerSymbols?, hParse, hLinker]

theorem compileArtifactFromRawSolcIr?_valid
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeAndElaborateSolcIrJson json selection = .ok program ∧
          decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
            Frontend.Object.VerifiedStackObjectArtifact.ValidFor
              linkerSymbols program.object artifact := by
  unfold compileArtifactFromRawSolcIr? at hCompile
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hCompile
  | ok json =>
      cases hDecode : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hDecode] at hCompile
      | ok program =>
          cases hLinker : decodeLinkerSymbolsJson json selection with
          | error err =>
              simp [hParse, hDecode, hLinker] at hCompile
          | ok linkerSymbols =>
              have hProgramCompile :
                  program.compileArtifactWithLinkerSymbols? linkerSymbols =
                    some artifact := by
                simpa [hParse, hDecode, hLinker] using hCompile
              refine ⟨json, program, linkerSymbols, ?_, ?_, ?_, ?_⟩
              · simp [hParse]
              · simp [hDecode]
              · simp [hLinker]
              · exact
                  Frontend.Program.compileArtifactWithLinkerSymbols?_valid
                    (program := program) (linkerSymbols := linkerSymbols)
                    (artifact := artifact) hProgramCompile

theorem compileArtifactFromRawSolcIr?_decodingCorrect
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    Assembly.Compact.DecodingCorrect
      artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList artifact.image.bytes) := by
  unfold compileArtifactFromRawSolcIr? at hCompile
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hCompile
  | ok json =>
      cases hDecode : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hDecode] at hCompile
      | ok program =>
          cases hLinker : decodeLinkerSymbolsJson json selection with
          | error err =>
              simp [hParse, hDecode, hLinker] at hCompile
          | ok linkerSymbols =>
              have hProgramCompile :
                  program.compileArtifactWithLinkerSymbols? linkerSymbols =
                    some artifact := by
                simpa [hParse, hDecode, hLinker] using hCompile
              exact
                Frontend.Program.compileArtifactWithLinkerSymbols?_decodingCorrect
                  (program := program) (linkerSymbols := linkerSymbols)
                  (artifact := artifact) hProgramCompile

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
