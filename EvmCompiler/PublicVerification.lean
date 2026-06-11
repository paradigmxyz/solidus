import EvmCompiler.Public
import EvmCompiler.Assembly.Preservation
import EvmCompiler.Compiler.AllocatedTypedCfg

namespace EvmCompiler
namespace Public

namespace Artifact

def atEntry (initial : Assembly.EVMState) (entryPc : Nat) :
    Assembly.EVMState :=
  { initial with pc := EvmYul.UInt256.ofNat entryPc }

/--
One public semantic relation for compiled blocks.

The generated Assembly program and its entry-PC witness are owned by the
artifact relation. Callers provide only the public artifact, a CFG label, and
an initial EVM state.
-/
def BlockSimulation (artifact : Artifact)
    (label : Assembly.Label) (initial : Assembly.EVMState) : Prop :=
  ∃ assembly : Assembly.Program, ∃ block : TypedCfg.Block, ∃ entryPc : Nat,
    artifact.metadata.typedCfg.findBlock? label = some block ∧
      assembly.labelPc label = some entryPc ∧
      Assembly.compileExecutable? assembly = some artifact.target ∧
      Assembly.Source.Eventually assembly (atEntry initial entryPc)
        (TypedCfg.Preservation.Block.RunSimulates assembly
          (artifact.metadata.typedCfg.step label
            (atEntry initial entryPc).incrPC)) ∧
      ∀ {fuel : Nat} {result : Assembly.StepResult},
        Assembly.Source.runNResult assembly fuel (atEntry initial entryPc) =
            .ok result →
          Assembly.Preservation.BlockTraceResult assembly artifact.target fuel
            (atEntry initial entryPc) result

abbrev EntrySimulation (artifact : Artifact)
    (initial : Assembly.EVMState) : Prop :=
  BlockSimulation artifact artifact.metadata.typedCfg.entry initial

theorem blockSimulation_of_loweredFrom
    {artifact : Artifact} {source : Functions.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {initial : Assembly.EVMState}
    (hLowered : artifact.LoweredFrom source)
    (hFind :
      artifact.metadata.typedCfg.findBlock? label = some block) :
    artifact.BlockSimulation label initial := by
  rcases hLowered with
    ⟨expressions, compiled, hExpressions, hCfg, hCompile, hExecutable,
      hCertificate⟩
  rcases
      Compiler.AllocatedTypedCfg.Program.compileCertified?_labelPc_exists
        hCompile hFind with
    ⟨entryPc, hLabelPc⟩
  have hEventually :=
    Compiler.AllocatedTypedCfg.Program.compileCertified?_step_eventually
      hCompile hFind hLabelPc
        (show (atEntry initial entryPc).pc =
            EvmYul.UInt256.ofNat entryPc by
          rfl)
  have hTargetCompile :
      Assembly.compile? compiled.target = some artifact.target := by
    rw [← Assembly.compileExecutable?_eq_compile?]
    exact hExecutable
  exact
    ⟨compiled.target, block, entryPc, hFind, hLabelPc, hExecutable,
      hEventually, by
        intro fuel result hRun
        exact
          (Assembly.Preservation.compile_runN_result_block_trace_sound
            hTargetCompile hRun).2⟩

end Artifact

theorem compileArtifactWithPolicy?_blockSimulation
    {policy : BackendPolicy} {mode : SemanticMode} {source : Source}
    {artifact : Artifact} {label : Assembly.Label}
    {block : TypedCfg.Block} {initial : Assembly.EVMState}
    (hCompile :
      compileArtifactWithPolicy? policy mode source = some artifact)
    (hFind :
      artifact.metadata.typedCfg.findBlock? label = some block) :
    artifact.BlockSimulation label initial := by
  rcases compileArtifactWithPolicy?_valid hCompile with
    ⟨objects, hObjects, hValid⟩
  exact
    Artifact.blockSimulation_of_loweredFrom hValid.2 hFind

theorem compileArtifactWithPolicy?_entrySimulation
    {policy : BackendPolicy} {mode : SemanticMode} {source : Source}
    {artifact : Artifact} {initial : Assembly.EVMState}
    (hCompile :
      compileArtifactWithPolicy? policy mode source = some artifact) :
    artifact.EntrySimulation initial := by
  rcases compileArtifactWithPolicy?_valid hCompile with
    ⟨objects, hObjects, hValid⟩
  rcases hValid.1 with
    ⟨hBackend, hAllocation, hTypedCfg⟩
  have hWellTyped : artifact.metadata.typedCfg.WellTyped :=
    hTypedCfg.2.1
  cases hFind :
      artifact.metadata.typedCfg.findBlock?
        artifact.metadata.typedCfg.entry with
  | none =>
      exact False.elim (hWellTyped.2.2.1 hFind)
  | some block =>
      exact
        Artifact.blockSimulation_of_loweredFrom hValid.2 hFind

end Public
end EvmCompiler
