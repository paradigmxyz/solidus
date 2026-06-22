import EvmCompiler.Public.ObserverComposition
import EvmCompiler.Yul.FunctionsObserverResourceSafety
import EvmCompiler.Compiler.OpenInteractionComposition

namespace EvmCompiler
namespace Yul
namespace EndToEnd

/-!
The public statement boundary for resource-observing Yul compilation.

The first theorem is deliberately restricted to checked artifacts without
external calls or creates and to target runs that reach an explicit EVM halt.
Ordinary Yul fallthrough needs a separate completion boundary because the
current generated CFG represents program end with an invalid terminator.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev SourceResult := ObserverSemantics.SourceReplay.Result
abbrev SourceExecutionResourceSafe :=
  FunctionsObserverResourceSafety.SourceExecutionResourceSafe

namespace State

def Rel (codeRel : StateRelation.CodeRel)
    (source : EvmYul.Yul.State) (target : Assembly.EVMState) : Prop :=
  ∃ shared vars,
    source = .Ok shared vars ∧
      StateRelation.Shared.Rel codeRel shared target.toSharedState

structure InitialRel (codeRel : StateRelation.CodeRel)
    (program : Yul.Program) (source : EvmYul.Yul.State)
    (target : Assembly.EVMState) : Prop where
  semantic :
    Rel codeRel
      (ObserverSemantics.SourceReplay.Program.installContract program
        (transcript := ([] : Trace)) { source := source }).source
      target
  target :
    Public.ObserverComposition.InitialConditions target

structure ObservableMachineRel
    (contract : MemoryContract.Contract)
    (source target : EvmYul.MachineState) : Prop where
  memory :
    match contract.scratch? with
    | none => source.memory = target.memory
    | some reservation =>
        Compiler.MemoryRelation.OutsideReservation
          reservation source.memory target.memory
  activeWords :
    match contract.scratch? with
    | none => source.activeWords = target.activeWords
    | some _reservation =>
        source.activeWords.toNat ≤ target.activeWords.toNat
  output : source.H_return = target.H_return

def TerminalRel (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (source : EvmYul.Yul.State) (target : Assembly.EVMState) : Prop :=
  ∃ shared : EvmYul.SharedState .Yul,
  ∃ vars : EvmYul.Yul.VarStore,
    source = .Ok shared vars ∧
      StateRelation.TerminalWorld.Rel codeRel
        shared.toState target.toSharedState.toState ∧
      ObservableMachineRel contract
        shared.toMachineState target.toMachineState

theorem TerminalRel.of_programTerminalStateRel
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {middle : Functions.ObserverSemantics.State transcript}
    {target : Assembly.Halt}
    (hSource :
      FunctionsObserverOutcome.ProgramTerminalStateRel
        codeRel source middle)
    (hTarget :
      Functions.AllocationObserverRelation.SharedRel contract
        middle.source.shared target.state.toSharedState)
    (hOutput :
      target.output =
        middle.source.shared.toMachineState.H_return) :
    TerminalRel contract codeRel source.source target.state ∧
      target.output =
        source.source.sharedState.toMachineState.H_return := by
  rcases hSource with
    ⟨_hCursor, sourceShared, sourceVars, hSourceEq, hTerminal⟩
  have hMachine :
      ObservableMachineRel contract
        sourceShared.toMachineState target.state.toMachineState := by
    refine ⟨?_, ?_, ?_⟩
    · cases hReservation : contract.scratch? with
      | none =>
          simpa [hReservation, hTerminal.machine.memory] using
            hTarget.machine.memory
      | some reservation =>
          simpa [hReservation, hTerminal.machine.memory] using
            hTarget.machine.memory
    · cases hReservation : contract.scratch? with
      | none =>
          simpa [hReservation, hTerminal.machine.activeWords] using
            hTarget.machine.activeWords
      | some reservation =>
          simpa [hReservation, hTerminal.machine.activeWords] using
            hTarget.machine.activeWords
    · exact hTerminal.machine.output.trans hTarget.machine.output
  have hWorld :
      StateRelation.TerminalWorld.Rel codeRel
        sourceShared.toState target.state.toSharedState.toState := by
    rw [← hTarget.world]
    exact hTerminal.world
  refine
    ⟨⟨sourceShared, sourceVars, hSourceEq, hWorld, hMachine⟩,
      ?_⟩
  calc
    target.output =
        middle.source.shared.toMachineState.H_return :=
      hOutput
    _ = sourceShared.toMachineState.H_return :=
      hTerminal.machine.output.symm
    _ = source.source.sharedState.toMachineState.H_return := by
      rw [hSourceEq]
      rfl

end State

namespace Result

def IsSuccessfulHalt : Assembly.Halt → Prop
  | { kind := .stop, .. } => True
  | { kind := .return, .. } => True
  | { kind := .selfdestruct, .. } => True
  | { kind := .revert, .. } => False

def Rel {transcript : Trace} (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel) :
    SourceResult transcript → Assembly.StepResult → Prop
  | .regular _, _ => False
  | .yulHalt source _value, .running _ => False
  | .yulHalt source _value, .halted halt =>
      IsSuccessfulHalt halt ∧
        State.TerminalRel contract codeRel source.source halt.state ∧
        halt.output =
          source.source.sharedState.toMachineState.H_return
  | .revert source, .running _ => False
  | .revert source, .halted halt =>
      halt.kind = .revert ∧
        State.TerminalRel contract codeRel source.source halt.state ∧
        halt.output =
          source.source.sharedState.toMachineState.H_return

theorem target_terminal {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {contract : MemoryContract.Contract}
    {source : SourceResult transcript} {target : Assembly.StepResult}
    (hRel : Rel contract codeRel source target) :
    target.IsTerminal := by
  cases source <;> cases target <;>
    simp_all [Rel, Assembly.StepResult.IsTerminal]

theorem of_adjacent_relations
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {source : SourceResult transcript}
    {middle :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {target : Assembly.Halt}
    (hSource :
      FunctionsObserverOutcome.ProgramOutcomeRel
        codeRel source middle)
    (hTarget :
      Public.ObserverComposition.TerminalOutcomeRel
        contract middle target) :
    Rel contract codeRel source (.halted target) := by
  rcases hTarget with
    ⟨kind, hMode, hKind, hShared, hOutput⟩
  cases hSource with
  | regular state =>
      simp at hMode
  | stop state =>
      simp at hMode
      subst kind
      rcases
          State.TerminalRel.of_programTerminalStateRel
            state hShared hOutput with
        ⟨hTerminal, hSourceOutput⟩
      exact
        ⟨by
            cases target
            cases hMode
            trivial,
          hTerminal, hSourceOutput⟩
  | «return» state =>
      simp at hMode
      subst kind
      rcases
          State.TerminalRel.of_programTerminalStateRel
            state hShared hOutput with
        ⟨hTerminal, hSourceOutput⟩
      exact
        ⟨by
            cases target
            cases hMode
            trivial,
          hTerminal, hSourceOutput⟩
  | selfdestruct state =>
      simp at hMode
      subst kind
      rcases
          State.TerminalRel.of_programTerminalStateRel
            state hShared hOutput with
        ⟨hTerminal, hSourceOutput⟩
      exact
        ⟨by
            cases target
            cases hMode
            trivial,
          hTerminal, hSourceOutput⟩
  | revert state =>
      simp at hMode
      subst kind
      rcases
          State.TerminalRel.of_programTerminalStateRel
            state hShared hOutput with
        ⟨hTerminal, hSourceOutput⟩
      exact ⟨hMode.symm, hTerminal, hSourceOutput⟩

end Result

structure ClosedArtifact (policy : Public.BackendPolicy)
    (program : Yul.Program) (artifact : Public.Artifact) : Prop where
  accepted :
    Public.SourceAccepted .resourceObservers (.yul program)
  compiled :
    Public.compileArtifactWithPolicy? policy
      .resourceObservers (.yul program) = some artifact
  noExternalEffects :
    Public.Observer.NoExternalEffects artifact

theorem ClosedArtifact.valid
    {policy : Public.BackendPolicy} {program : Yul.Program}
    {artifact : Public.Artifact}
    (hArtifact : ClosedArtifact policy program artifact) :
    Public.ArtifactValid policy .resourceObservers
      (.yul program) artifact :=
  Public.compileArtifactWithPolicy?_valid hArtifact.compiled

theorem ClosedArtifact.observerReplay
    {policy : Public.BackendPolicy} {program : Yul.Program}
    {artifact : Public.Artifact} {fuel : Nat}
    {initial : Assembly.EVMState} {target : Assembly.StepResult}
    {transcript : Trace}
    (hArtifact : ClosedArtifact policy program artifact)
    (hRun :
      Public.Observer.TerminalRun artifact fuel
        initial target transcript) :
    Public.Observer.ExactReplay artifact fuel initial
      target transcript :=
  hRun.exactReplay

/--
The corrected public proposition for closed resource-observing compilation.

Scratch-backed compilation reserves source memory for compiler spill frames.
Consequently, acceptedness and target execution alone are insufficient: the
caller must provide the source-facing guarded execution fact for the concrete
transcript. This premise is stated over canonical Yul semantics and the
program's memory contract; it contains no generated code, allocation
certificate, or target artifact evidence.
-/
def ClosedResourceCorrect : Prop :=
  ∀ (policy : Public.BackendPolicy) (program : Yul.Program)
    (artifact : Public.Artifact) (codeRel : StateRelation.CodeRel)
    (profile : SolcValidation.DialectProfile)
    (source : EvmYul.Yul.State) (initial : Assembly.EVMState)
    (fuel : Nat) (target : Assembly.StepResult) (transcript : Trace),
    ClosedArtifact policy program artifact →
    SolcValidation.ProgramOkWith? profile program = true →
    State.InitialRel codeRel program source initial →
    SourceExecutionResourceSafe program source transcript →
    Public.Observer.TerminalRun artifact fuel
      initial target transcript →
    ∃ sourceResult : SourceResult transcript,
      ObserverSemantics.SourceReplay.Program.ExactTerminates
        program source transcript sourceResult ∧
      Result.Rel program.memoryContract codeRel sourceResult target

/--
Checked compiler-selected end-to-end observer replay.

The proof is intentionally only a composition of adjacent public interfaces:
bounded Yul-to-Functions forward preservation, source-facing reservation
safety, trace adequacy, and the ordinary
allocation/Structured/TypedCfg/Assembly/bytecode terminal composition theorem.
-/
theorem closedResourceCorrect : ClosedResourceCorrect := by
  intro policy program artifact codeRel profile source initial fuel
    target transcript hArtifact hProgramOk hInitial hSafe hTarget
  rcases hArtifact.valid with
    ⟨targetProgram, hObjects, hValid⟩
  change
    Program.toObjectsWithObservers? program = some targetProgram
      at hObjects
  rcases hArtifact.accepted with
    ⟨acceptedProgram, hAcceptedObjects, hAccepted⟩
  change
    Program.toObjectsWithObservers? program = some acceptedProgram
      at hAcceptedObjects
  rw [hObjects] at hAcceptedObjects
  cases hAcceptedObjects
  have hContract :
      targetProgram.toFunctions.memoryContract =
        program.memoryContract :=
    FunctionsObserverCompiler.memoryContract_of_toObjectsWithObservers?
      hObjects
  let functionsInitial :
      Functions.ObserverSemantics.State transcript :=
    Locals.ObserverSemantics.Program.initialState initial transcript
  rcases hInitial.semantic with
    ⟨sourceShared, sourceVars, hInstalled, hInitialShared⟩
  have hInput :
      FunctionsObserverOutcome.ProgramInputRel codeRel
        (ObserverSemantics.SourceReplay.Program.installContract
          program { source := source })
        functionsInitial := by
    refine
      .intro rfl sourceShared sourceVars ?_ ?_ rfl
    · simpa using hInstalled
    · simpa [functionsInitial] using hInitialShared
  have hTraceSafe :
    FunctionsObserverTraceAdequacy.SourceExecutionSafe
        program source transcript :=
    FunctionsObserverResourceSafety.SourceExecutionResourceSafe.executionSafe
      hSafe
  rcases hSafe with
    ⟨safeResult, sourceFuel, hSourceRun, _hSourceBound,
      hReservationSafe⟩
  obtain
      ⟨functionsFuel, functionsOutcome,
        hFunctionsRun, _hForwardOutcome, hFunctionsFuel⟩ :=
    FunctionsObserverPreservation.compileProgramForwardProgramBounded
      hObjects hProgramOk hInput hSourceRun
  have hFuelSafe :
      (Functions.AllocationObserverProgram.selectedResourceMode
          artifact.metadata.allocation
          targetProgram.toFunctions).FuelSafe
        (Functions.AllocationObserverProgram.selectedMainSetupDepth
            artifact.metadata.allocation targetProgram.toFunctions +
          (functionsFuel + 1)) :=
    FunctionsObserverResourceSafety.SourceReservationSafe.selectedFuelSafe
      hObjects hReservationSafe hFunctionsFuel
  obtain
      ⟨halt, hTargetEq, hExhausted, hTerminal⟩ :=
    Public.ObserverComposition.terminalWithResourceSafety
      hAccepted hValid.2 hArtifact.noExternalEffects
      hFuelSafe
      hInitial.target
      (by simpa [functionsInitial, hContract] using hFunctionsRun)
      hTarget
  obtain
      ⟨sourceResult, hExact, hSourceFunctions⟩ :=
    FunctionsObserverTraceAdequacy.compileProgramTraceAdequate
      hObjects hProgramOk hInput hTraceSafe
      (by simpa [functionsInitial] using hFunctionsRun)
      hExhausted
  refine ⟨sourceResult, hExact, ?_⟩
  rw [hTargetEq]
  apply Result.of_adjacent_relations hSourceFunctions
  simpa [hContract] using hTerminal

abbrev OpenWorldTerminalCorrect :=
  Compiler.OpenInteractionComposition.OpenWorldTerminalCorrect

/-- Public open-world terminal compiler correctness. The end-to-end module is
only a short alias of the designated horizontal composition theorem. -/
theorem openWorldTerminalCorrect : OpenWorldTerminalCorrect :=
  Compiler.OpenInteractionComposition.openWorldTerminalCorrect

/-- Exact recursive-object/raw-byte correctness with concrete resource
observations and universally open external effects. All proof work remains in
the horizontally composed compiler module. -/
abbrev compiledObjectRootToBytecode :=
  @Compiler.OpenInteractionComposition.compiledObjectRootToBytecode

/-- Exact recursive-object/raw-byte correctness for the checked stack
allocator and compact encoder used by the verified Solidity frontend. -/
abbrev compiledVerifiedStackObjectToRawBytecode :=
  @Compiler.OpenInteractionComposition.compiledVerifiedStackObjectToRawBytecode

end EndToEnd
end Yul
end EvmCompiler
