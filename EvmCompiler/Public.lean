import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Public

inductive Source where
  | objects (program : Objects.Program)
  | yul (program : Yul.Program)

inductive SemanticMode where
  | ordinary
  | resourceObservers
  deriving DecidableEq, Repr

abbrev BackendPolicy := Objects.Program.BackendPolicy
abbrev Artifact := Objects.Program.CompileArtifact

noncomputable def Source.toObjects? (mode : SemanticMode) :
    Source → Option Objects.Program
  | .objects program => some program
  | .yul program =>
      match mode with
      | .ordinary => program.toObjects?
      | .resourceObservers => program.toObjectsWithObservers?

noncomputable def compileArtifactWithPolicy?
    (policy : BackendPolicy) (mode : SemanticMode)
    (source : Source) : Option Artifact := do
  let objects ← source.toObjects? mode
  Objects.Program.compileArtifactWithPolicy? policy objects

noncomputable def compileArtifact? (mode : SemanticMode)
    (source : Source) : Option Artifact :=
  compileArtifactWithPolicy? Objects.Program.defaultBackendPolicy mode source

noncomputable def compile? (mode : SemanticMode)
    (source : Source) : Option Assembly.TargetProgram :=
  Compiler.Artifact.target? (compileArtifact? mode source)

def SourceAccepted (mode : SemanticMode) (source : Source) : Prop :=
  ∃ objects,
    source.toObjects? mode = some objects ∧
      Objects.Program.SourceAccepted objects

def ArtifactValid (policy : BackendPolicy) (mode : SemanticMode)
    (source : Source) (artifact : Artifact) : Prop :=
  ∃ objects,
    source.toObjects? mode = some objects ∧
      Objects.Program.CompileArtifact.Valid policy objects artifact

noncomputable def compilePass (policy : BackendPolicy)
    (mode : SemanticMode) :
    Compiler.Pass Source Assembly.TargetProgram
      Objects.Program.CompileMetadata where
  compile? := compileArtifactWithPolicy? policy mode

noncomputable def compileContract (policy : BackendPolicy)
    (mode : SemanticMode) :
    Compiler.PassContract Source Assembly.TargetProgram
      Objects.Program.CompileMetadata where
  pass := compilePass policy mode
  Accepted := SourceAccepted mode
  MetaValid := ArtifactValid policy mode

theorem compileArtifactWithPolicy?_objects
    (policy : BackendPolicy) (mode : SemanticMode)
    (program : Objects.Program) :
    compileArtifactWithPolicy? policy mode (.objects program) =
      Objects.Program.compileArtifactWithPolicy? policy program := by
  rfl

theorem compile?_target {mode : SemanticMode} {source : Source}
    {artifact : Artifact}
    (hCompile : compileArtifact? mode source = some artifact) :
    compile? mode source = some artifact.target := by
  simp [compile?, hCompile]

theorem compileArtifactWithPolicy?_metadataValid
    {policy : BackendPolicy} {mode : SemanticMode} {source : Source}
    {artifact : Artifact}
    (hCompile :
      compileArtifactWithPolicy? policy mode source = some artifact) :
    artifact.metadata.Valid policy := by
  unfold compileArtifactWithPolicy? at hCompile
  cases hObjects : source.toObjects? mode with
  | none =>
      simp [hObjects] at hCompile
  | some objects =>
      simp [hObjects] at hCompile
      exact
        Objects.Program.compileArtifactWithPolicy?_metadataValid hCompile

theorem compileArtifactWithPolicy?_valid
    {policy : BackendPolicy} {mode : SemanticMode} {source : Source}
    {artifact : Artifact}
    (hCompile :
      compileArtifactWithPolicy? policy mode source = some artifact) :
    ArtifactValid policy mode source artifact := by
  unfold compileArtifactWithPolicy? at hCompile
  cases hObjects : source.toObjects? mode with
  | none =>
      simp [hObjects] at hCompile
  | some objects =>
      simp [hObjects] at hCompile
      exact
        ⟨objects, hObjects,
          Objects.Program.compileArtifactWithPolicy?_valid hCompile⟩

theorem compileArtifactWithPolicy?_checked
    {policy : BackendPolicy} {mode : SemanticMode} {source : Source}
    {artifact : Artifact}
    (hAccepted : SourceAccepted mode source)
    (hCompile :
      compileArtifactWithPolicy? policy mode source = some artifact) :
    Compiler.PassContract.Checked (compileContract policy mode)
      source artifact := by
  exact
    { accepted := hAccepted
      compiles := hCompile
      metadataValid :=
        compileArtifactWithPolicy?_valid hCompile }

end Public
end EvmCompiler
