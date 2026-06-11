import EvmCompiler.Public
import EvmCompiler.Solidity.Frontend

namespace EvmCompiler
namespace Solidity
namespace Frontend
namespace Program

def toPublicSource? (program : Program) : Option Public.Source := do
  let objects ← program.toObjectsUnchecked?
  some (.objects objects)

noncomputable def compileArtifactWithPolicy?
    (policy : Public.BackendPolicy) (program : Program) :
    Option Public.Artifact := do
  let source ← program.toPublicSource?
  Public.compileArtifactWithPolicy? policy .ordinary source

noncomputable def compileArtifact? (program : Program) :
    Option Public.Artifact :=
  program.compileArtifactWithPolicy? Objects.Program.defaultBackendPolicy

noncomputable def compile? (program : Program) :
    Option Assembly.TargetProgram :=
  Compiler.Artifact.target? program.compileArtifact?

end Program
end Frontend
end Solidity
end EvmCompiler
