import EvmCompiler.Public
import EvmCompiler.Assembly.Preservation
import EvmCompiler.Compiler.AllocatedTypedCfg
import EvmCompiler.Structured.TypedCfgPreservation

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

def plannedFor (artifact : Artifact)
    (source : Functions.Program) : Objects.Program.PlannedProgram :=
  { source := source
    allocation := artifact.metadata.allocation }

/--
A checked evaluation of the hidden Structured program selected by a public
artifact's allocation-aware lowering path.
-/
def StructuredEvaluation (artifact : Artifact)
    (source : Functions.Program) (fuel : Nat)
    (initial : Assembly.EVMState)
    (outcome : Structured.Outcome) : Prop :=
  ∃ expressions,
    (plannedFor artifact source).lowerWithAllocation? =
        some expressions ∧
      expressions.toStructured.WF ∧
      expressions.toStructured.FrameSafe ∧
      Structured.Block.Eval expressions.toStructured fuel
        expressions.toStructured.body
        (Structured.Program.initialState initial) outcome

/--
The public source-to-Assembly artifact relation at the generated entry.

The complete source evaluation is related to a finite TypedCfg path, while the
same hidden entry-PC witness starts the checked Assembly execution of the
path's first block. This is the honest composition boundary for the current
gas-erasing TypedCfg-to-Assembly contract; it does not claim a flattened
multi-block Assembly trace.
-/
def StructuredEntrySimulation (artifact : Artifact)
    (sourceProgram : Structured.Program)
    (initial : Assembly.EVMState)
    (outcome : Structured.Outcome) : Prop :=
  ∃ assembly : Assembly.Program, ∃ block : TypedCfg.Block,
    ∃ entryPc : Nat, ∃ targetOutcome : TypedCfg.Outcome,
      artifact.metadata.typedCfg.findBlock?
          artifact.metadata.typedCfg.entry =
        some block ∧
      assembly.labelPc artifact.metadata.typedCfg.entry = some entryPc ∧
      Assembly.compileExecutable? assembly = some artifact.target ∧
      artifact.metadata.typedCfg.Eventually
        artifact.metadata.typedCfg.entry
        (atEntry initial entryPc).incrPC targetOutcome ∧
      Structured.TypedCfgPreservation.OutcomeSimulation.Rel
        (Structured.TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          { procs := sourceProgram.procs }
            Structured.ProcLabel.programEnd)
        [] outcome targetOutcome ∧
      Assembly.Source.Eventually assembly (atEntry initial entryPc)
        (TypedCfg.Preservation.Block.RunSimulates assembly
          (artifact.metadata.typedCfg.step
            artifact.metadata.typedCfg.entry
            (atEntry initial entryPc).incrPC)) ∧
      ∀ {fuel : Nat} {result : Assembly.StepResult},
        Assembly.Source.runNResult assembly fuel
            (atEntry initial entryPc) =
            .ok result →
          Assembly.Preservation.BlockTraceResult assembly artifact.target fuel
            (atEntry initial entryPc) result

def StructuredSimulation (artifact : Artifact)
    (initial : Assembly.EVMState)
    (outcome : Structured.Outcome) : Prop :=
  ∃ sourceProgram,
    StructuredEntrySimulation artifact sourceProgram initial outcome

theorem blockSimulation_of_loweredFrom
    {artifact : Artifact} {source : Functions.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {initial : Assembly.EVMState}
    (hLowered : artifact.LoweredFrom source)
    (hFind :
      artifact.metadata.typedCfg.findBlock? label = some block) :
    artifact.BlockSimulation label initial := by
  rcases hLowered with
    ⟨expressions, compiled, _hCompatible, _hMemoryAuthorized,
      hExpressions, _hSourceWF, hCfg, hCompile, hExecutable, hCertificate⟩
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

theorem structuredSimulation_of_loweredFrom
    {artifact : Artifact} {source : Functions.Program}
    {fuel : Nat} {initial : Assembly.EVMState}
    {outcome : Structured.Outcome}
    (hLowered : artifact.LoweredFrom source)
    (hEvaluation :
      artifact.StructuredEvaluation source fuel initial outcome) :
    artifact.StructuredSimulation initial outcome := by
  have hLoweredCopy := hLowered
  rcases hLowered with
    ⟨loweredExpressions, compiled, _hCompatible, _hMemoryAuthorized,
      hExpressions, _hSourceWF, hCfg, hCompile, hExecutable, hCertificate⟩
  rcases hEvaluation with
    ⟨evaluatedExpressions, hEvaluatedExpressions, hWF, hFrameSafe, hEval⟩
  have hExpressionsEq : evaluatedExpressions = loweredExpressions := by
    unfold plannedFor at hEvaluatedExpressions
    rw [hExpressions] at hEvaluatedExpressions
    exact (Option.some.inj hEvaluatedExpressions).symm
  subst evaluatedExpressions
  rcases
      Objects.Program.PlannedProgram.lowerTypedCfg?_sourceArtifact hCfg with
    ⟨entryShapes, sourceArtifact, hEntryShapes, hSourceArtifact,
      hSourceCfg⟩
  have hSourcePath :=
    Structured.TypedCfgPreservation.Program.path_of_artifactWithProcEntryShapes?_and_eval
      hSourceArtifact hWF hFrameSafe hEval
  have hSourcePath' :
      Structured.TypedCfgPreservation.OutcomeSimulation.Path
        artifact.metadata.typedCfg
        Structured.TypedCfgCompiler.entryLabel
        (Structured.TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            { procs := loweredExpressions.toStructured.procs }
            Structured.ProcLabel.programEnd)
        (Structured.Program.initialState initial) outcome [] := by
    simpa [hSourceCfg] using hSourcePath
  have hWellTyped : artifact.metadata.typedCfg.WellTyped :=
    (Compiler.AllocatedTypedCfg.Program.compileCertified?_certificateValid
      hCompile).2.2.2.2.1
  have hEntry :
      artifact.metadata.typedCfg.entry =
        Structured.TypedCfgCompiler.entryLabel := by
    rw [← hSourceCfg]
    exact
      Structured.TypedCfgCompiler.artifactWithProcEntryShapes?_entry
        hSourceArtifact
  cases hFind :
      artifact.metadata.typedCfg.findBlock?
        artifact.metadata.typedCfg.entry with
  | none =>
      exact False.elim (hWellTyped.2.2.1 hFind)
  | some entryBlock =>
      rcases
          blockSimulation_of_loweredFrom hLoweredCopy hFind with
        ⟨assembly, block, entryPc, hBlockFind, hLabelPc, hTarget,
          hAssembly, hTrace⟩
      have hInitialRel :
          Structured.TypedCfgPreservation.StateRel
            (Structured.Program.initialState initial) []
            (atEntry initial entryPc).incrPC := by
        apply
          Structured.TypedCfgPreservation.StateRel.targetCongr
            ?_
            (Structured.TypedCfgPreservation.StateRel.initial initial)
        cases initial
        rfl
      rcases hSourcePath' _ hInitialRel with
        ⟨targetOutcome, hCfgEventually, hOutcomeRel⟩
      have hCfgEventually' :
          artifact.metadata.typedCfg.Eventually
            artifact.metadata.typedCfg.entry
            (atEntry initial entryPc).incrPC targetOutcome := by
        simpa [hEntry] using hCfgEventually
      exact
        ⟨loweredExpressions.toStructured, assembly, block, entryPc,
          targetOutcome, hBlockFind, hLabelPc, hTarget, hCfgEventually',
          hOutcomeRel, hAssembly, hTrace⟩

end Artifact

def StructuredEvaluation
    (mode : SemanticMode) (source : Source) (artifact : Artifact)
    (fuel : Nat) (initial : Assembly.EVMState)
    (outcome : Structured.Outcome) : Prop :=
  ∃ objects,
    source.toObjects? mode = some objects ∧
      artifact.StructuredEvaluation objects.toFunctions fuel initial outcome

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
    hTypedCfg.2.2.2.2.1
  cases hFind :
      artifact.metadata.typedCfg.findBlock?
        artifact.metadata.typedCfg.entry with
  | none =>
      exact False.elim (hWellTyped.2.2.1 hFind)
  | some block =>
      exact
        Artifact.blockSimulation_of_loweredFrom hValid.2 hFind

theorem compileArtifactWithPolicy?_structuredSimulation
    {policy : BackendPolicy} {mode : SemanticMode} {source : Source}
    {artifact : Artifact} {fuel : Nat}
    {initial : Assembly.EVMState} {outcome : Structured.Outcome}
    (hCompile :
      compileArtifactWithPolicy? policy mode source = some artifact)
    (hEvaluation :
      StructuredEvaluation mode source artifact fuel initial outcome) :
    artifact.StructuredSimulation initial outcome := by
  rcases compileArtifactWithPolicy?_valid hCompile with
    ⟨objects, hObjects, hValid⟩
  rcases hEvaluation with
    ⟨evaluatedObjects, hEvaluatedObjects, hStructuredEval⟩
  rw [hObjects] at hEvaluatedObjects
  cases hEvaluatedObjects
  exact
    Artifact.structuredSimulation_of_loweredFrom
      hValid.2 hStructuredEval

end Public
end EvmCompiler
