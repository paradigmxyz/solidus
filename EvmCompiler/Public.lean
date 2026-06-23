import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Public

/-!
Stable stack-only backend API.

The trusted production frontend supplies optimized Yul. The backend computes
pressure normalization and a physical stack schedule, and fails closed when
that schedule cannot be lowered. It performs no compiler-owned memory access.
-/

abbrev Source := Yul.Program
abbrev Artifact := Compiler.StackArtifact.Artifact

noncomputable def compileArtifact? (source : Source) : Option Artifact :=
  source.compileArtifact?

noncomputable def compile? (source : Source) :
    Option Assembly.TargetProgram :=
  (compileArtifact? source).map (fun artifact => artifact.target)

def SourceAccepted (source : Source) : Prop :=
  ∃ lower : Objects.Program,
    source.toObjects? = some lower ∧ lower.toFunctions.SourceAccepted

def ArtifactValid (source : Source) (artifact : Artifact) : Prop :=
  compileArtifact? source = some artifact

theorem compile?_target {source : Source} {artifact : Artifact}
    (hCompile : compileArtifact? source = some artifact) :
    compile? source = some artifact.target := by
  simp [compile?, hCompile]

theorem compileArtifact?_valid
    {source : Source} {artifact : Artifact}
    (hCompile : compileArtifact? source = some artifact) :
    ArtifactValid source artifact :=
  hCompile

theorem compileArtifact?_sourceAccepted
    {source : Source} {artifact : Artifact}
    (hCompile : compileArtifact? source = some artifact) :
    SourceAccepted source := by
  unfold compileArtifact? at hCompile
  unfold Yul.Program.compileArtifact? at hCompile
  cases hLower : source.toObjects? with
  | none => simp [hLower] at hCompile
  | some lower =>
      have hArtifact :
          Compiler.StackArtifact.compile? lower.toFunctions = some artifact := by
        simpa [hLower] using hCompile
      have hAccepted :=
        Compiler.StackArtifact.compile?_sourceAccepted hArtifact
      exact ⟨lower, hLower, hAccepted⟩

end Public
end EvmCompiler
