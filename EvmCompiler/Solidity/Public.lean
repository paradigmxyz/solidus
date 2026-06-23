import EvmCompiler.Solidity.VerifiedStackObjectArtifact

namespace EvmCompiler
namespace Solidity
namespace Frontend
namespace Program

abbrev Artifact := VerifiedStackObjectArtifact

def compileArtifactWithLinkerSymbols? (program : Program)
    (linkerSymbols : List (Name × Word)) : Option Artifact :=
  program.object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
    linkerSymbols

def compileArtifact? (program : Program) : Option Artifact :=
  program.compileArtifactWithLinkerSymbols? []

def compileImageWithLinkerSymbols? (program : Program)
    (linkerSymbols : List (Name × Word)) : Option ObjectImage := do
  let artifact ← program.compileArtifactWithLinkerSymbols? linkerSymbols
  some artifact.image

def compileImage? (program : Program) : Option ObjectImage :=
  program.compileImageWithLinkerSymbols? []

theorem compileArtifactWithLinkerSymbols?_valid
    {program : Program} {linkerSymbols : List (Name × Word)}
    {artifact : Artifact}
    (hCompile :
      program.compileArtifactWithLinkerSymbols? linkerSymbols = some artifact) :
    Object.VerifiedStackObjectArtifact.ValidFor
      linkerSymbols program.object artifact := by
  exact
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_valid
      program.object linkerSymbols artifact hCompile

theorem compileArtifactWithLinkerSymbols?_decodingCorrect
    {program : Program} {linkerSymbols : List (Name × Word)}
    {artifact : Artifact}
    (hCompile :
      program.compileArtifactWithLinkerSymbols? linkerSymbols = some artifact) :
    Assembly.Compact.DecodingCorrect artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList artifact.image.bytes) :=
  Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
    hCompile

end Program
end Frontend
end Solidity
end EvmCompiler
