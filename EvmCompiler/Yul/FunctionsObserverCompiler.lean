import EvmCompiler.Yul.FunctionsCompilerArtifact

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCompiler

/-! Compatibility exports for the historical observer proof modules. New
Yul-to-Functions proofs import `FunctionsCompilerArtifact` directly. -/

export FunctionsCompilerArtifact
  (Decomposition decomposition_of_toObjectsWithObservers?
    memoryContract_of_toObjectsWithObservers?)

namespace Decomposition

export FunctionsCompilerArtifact.Decomposition
  (findFunction findFunction_parts)

end Decomposition

end FunctionsObserverCompiler
end Yul
end EvmCompiler
