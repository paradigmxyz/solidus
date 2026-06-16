import EvmCompiler.Functions.AllocationObserverProgram
import EvmCompiler.Public.Observer
import EvmCompiler.Structured.ObserverProgramAdequacy
import EvmCompiler.TypedCfg.ObserverPreservation

namespace EvmCompiler
namespace Public
namespace ObserverComposition

abbrev Trace := Assembly.ResourceTrace

structure InitialConditions (initial : Assembly.EVMState) : Prop where
  pcZero : initial.pc = EvmYul.UInt256.ofNat 0
  stackEmpty : initial.stack = []
  activeNoWrap :
    initial.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size

def TerminalOutcomeRel
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (source :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript))
    (target : Assembly.Halt) : Prop :=
  ∃ kind,
    source.mode = .halt kind ∧
      target.kind = kind ∧
      Functions.AllocationObserverRelation.SharedRel contract
        source.state.source.shared target.state.toSharedState ∧
      target.output =
        source.state.source.shared.toMachineState.H_return

/--
Terminal observer composition from canonical Functions semantics to assembled
bytecode for the compiler-selected allocation mode.

Scratch-backed execution requires an explicit bound proving that the concrete
source run cannot exhaust the compiler-reserved frame region. The theorem
reconstructs only the concrete terminal execution needed for exact observer
replay; it does not expose generated CFG/Assembly evidence.
-/
theorem terminalWithResourceSafety
    {sourceProgram : Objects.Program}
    {artifact : Public.Artifact}
    {sourceFuel targetFuel : Nat}
    {transcript : Trace}
    {initial : Assembly.EVMState}
    {sourceOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetResult : Assembly.StepResult}
    (hAccepted : sourceProgram.SourceAccepted)
    (hLowered :
      artifact.LoweredFrom sourceProgram.toFunctions)
    (hNoExternal : Public.Observer.NoExternalEffects artifact)
    (hResourceSafe :
      (Functions.AllocationObserverProgram.selectedResourceMode
          artifact.metadata.allocation sourceProgram.toFunctions).FuelSafe
        (Functions.AllocationObserverProgram.selectedMainSetupDepth
            artifact.metadata.allocation sourceProgram.toFunctions +
          (sourceFuel + 1)))
    (hInitial : InitialConditions initial)
    (hSource :
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            sourceProgram.toFunctions.memoryContract transcript)
          sourceFuel sourceProgram.toFunctions
          (Locals.ObserverSemantics.Program.initialState
            initial transcript) =
        .ok sourceOutcome)
    (hTarget :
      Public.Observer.TerminalRun artifact targetFuel
        initial targetResult transcript) :
    ∃ halt,
      targetResult = .halted halt ∧
        sourceOutcome.state.remaining = [] ∧
        TerminalOutcomeRel
          sourceProgram.toFunctions.memoryContract sourceOutcome halt := by
  rcases Assembly.StepResult.terminal_iff_exists_halt.mp hTarget.2 with
    ⟨halt, rfl⟩
  rcases hLowered with
    ⟨expressions, compiled, _hCompatible, _hMemoryAuthorized,
      hExpressions, hStructuredWF, hCfg, hAllocated,
      hExecutable, _hCertificate⟩
  let planned : Objects.Program.PlannedProgram :=
    { source := sourceProgram.toFunctions
      allocation := artifact.metadata.allocation }
  have hLower :
      Functions.AllocationLowering.lowerExpressionsFromAllocation?
          artifact.metadata.allocation sourceProgram.toFunctions =
        some expressions := by
    unfold Objects.Program.PlannedProgram.lowerWithAllocation? at hExpressions
    cases hResult : planned.loweringResult? with
    | none =>
        simp [planned, hResult] at hExpressions
    | some result =>
        rcases result with ⟨backend, loweredExpressions⟩
        simp [planned, hResult] at hExpressions
        subst loweredExpressions
        have hExact :=
          Objects.Program.PlannedProgram.loweringResult?_lowerer_exact
            (planned := planned)
            (backend := backend)
            (expressions := expressions)
            hResult
        simpa [Functions.AllocationLowering.allocationLowerer,
          planned] using hExact
  have hCfgCompile :=
    Compiler.AllocatedTypedCfg.Program.compileCertified?_cfg hAllocated
  have hCfgWellTyped : artifact.metadata.typedCfg.WellTyped :=
    TypedCfg.Program.compileCertified?_wellTyped hCfgCompile
  have hCfgSafe : artifact.metadata.typedCfg.ReplaySafe :=
    TypedCfg.Program.replaySafe_of_independent_noExternal
      (Objects.Program.PlannedProgram.lowerTypedCfg?_programCounterIndependent
        hCfg)
      hNoExternal
  have hAssemblyLower :
      artifact.metadata.typedCfg.lower? = some compiled.target :=
    TypedCfg.Program.compileCertified?_target hCfgCompile
  have hEntryPc :
      compiled.target.labelPc artifact.metadata.typedCfg.entry = some 0 := by
    simpa using TypedCfg.Program.lower?_entry_labelPc_zero hAssemblyLower
  have hAt :
      Assembly.Program.instrAtPc compiled.target initial.pc.toNat =
        some (0, .label artifact.metadata.typedCfg.entry) := by
    rw [hInitial.pcZero]
    simpa using Assembly.Program.instrAtPc_of_labelPc hEntryPc
  have hByteLength :
      compiled.target.byteLength < EvmYul.UInt256.size := by
    have hFits := TypedCfg.Program.compileCertified?_pcFits hCfgCompile
    have hWordLt :
        compiled.target.pcAfter.toNat < EvmYul.UInt256.size :=
      compiled.target.pcAfter.val.isLt
    rw [hFits] at hWordLt
    exact hWordLt
  have hAssemblyCompile :
      Assembly.compile? compiled.target = some artifact.target := by
    rw [← Assembly.compileExecutable?_eq_compile?]
    exact hExecutable
  have hExact := hTarget.exactReplay
  obtain ⟨assemblyFuel, hAssemblyRun⟩ :=
    Assembly.Preservation.compile_terminal_target_run_source_exists
      hAssemblyCompile hAt hByteLength hExact.2
  have hEntryRun :
      TypedCfg.ObserverPreservation.Program.EntryTerminalRun
          artifact.metadata.typedCfg
          { target := compiled.target
            metadata := compiled.metadata.cfg }
          assemblyFuel initial transcript [] halt := by
    refine ⟨0, hEntryPc, ?_⟩
    have hInitialEq :
        { initial with pc := EvmYul.UInt256.ofNat 0 } = initial := by
      cases initial
      simpa using hInitial.pcZero.symm
    rw [hInitialEq]
    exact hAssemblyRun
  obtain ⟨cfgFuel, cfgKind, cfgFinal, hCfgRun, hCfgHalt⟩ :=
    TypedCfg.ObserverPreservation.Program.compileCertified?_entry_terminal_backward
      hCfgCompile hCfgSafe
      (Assembly.SameRuntimeData.refl initial) hEntryRun
  rcases
      Objects.Program.PlannedProgram.lowerTypedCfg?_sourceArtifact hCfg with
    ⟨entryShapes, sourceArtifact, _hEntryShapes, hSourceArtifact,
      hSourceCfg⟩
  have hGenerate :
      Structured.TypedCfgCompiler.generateWithProcEntryShapes?
          expressions.toStructured entryShapes =
        some artifact.metadata.typedCfg := by
    have hGenerated :=
      Structured.TypedCfgCompiler.artifactWithProcEntryShapes?_generate
        hSourceArtifact
    simpa [hSourceCfg] using hGenerated
  have hStructuredInitial :
      Structured.ObserverPreservation.StateRel.At
        TypedCfg.Shape.caller
        (Structured.ObserverSemantics.Program.initialState
          (Structured.RunState.initial initial) transcript)
        [] initial transcript :=
    Structured.ObserverPreservation.StateRel.At.initial initial transcript
  obtain
      ⟨structuredFuel, structuredOutcome, hStructuredRun,
        hStructuredCfg⟩ :=
    Structured.ObserverAdequacy.Program.generateWithProcEntryShapes?_terminal_backward
      hGenerate hCfgWellTyped hStructuredWF hStructuredInitial hCfgRun
  let functionsInitial :
      Functions.ObserverSemantics.State transcript :=
    Locals.ObserverSemantics.Program.initialState initial transcript
  let structuredInitial :
      Structured.ObserverSemantics.State transcript :=
    Structured.ObserverSemantics.Program.initialState
      (Structured.RunState.initial initial) transcript
  have hAllocationInitial :
      Functions.AllocationObserverProgram.InitialRel
        sourceProgram.toFunctions.memoryContract
        functionsInitial structuredInitial := by
    refine
      { cursor := rfl
        shared := ?_
        stack := hInitial.stackEmpty
        activeNoWrap := hInitial.activeNoWrap }
    exact
      { machine :=
          Compiler.MemoryRelation.MachineRel.refl
            sourceProgram.toFunctions.memoryContract
            initial.toMachineState
        world := rfl }
  let fuelBound := sourceFuel + 1
  let maxDepth :=
    Functions.AllocationObserverProgram.selectedMainSetupDepth
        artifact.metadata.allocation sourceProgram.toFunctions +
      fuelBound
  have hFuelSafe :
      (Functions.AllocationObserverProgram.selectedResourceMode
          artifact.metadata.allocation sourceProgram.toFunctions).FuelSafe
        maxDepth := by
    simpa [maxDepth, fuelBound] using hResourceSafe
  have hDepthBound :
      Functions.AllocationObserverProgram.selectedMainSetupDepth
          artifact.metadata.allocation sourceProgram.toFunctions +
          fuelBound ≤
        maxDepth := by
    rfl
  have hSourceFuel : sourceFuel < fuelBound := by
    simp [fuelBound]
  have hAllocationOutcome :
      Functions.AllocationObserverProgram.OutcomeRel
        sourceProgram.toFunctions.memoryContract
        sourceOutcome structuredOutcome := by
    apply
      Functions.AllocationObserverProgram.mainTargetAgreement
        hLower hAccepted.2.2 hFuelSafe hDepthBound hSourceFuel
        hAllocationInitial
    · simpa [functionsInitial] using hSource
    · simpa [structuredInitial] using hStructuredRun
  cases hAllocationOutcome with
  | regular state stack =>
      simp [Structured.ObserverPreservation.OutcomeSimulation.Rel]
        at hStructuredCfg
  | brk state =>
      simp [Structured.ObserverPreservation.OutcomeSimulation.Rel]
        at hStructuredCfg
  | cont state =>
      simp [Structured.ObserverPreservation.OutcomeSimulation.Rel]
        at hStructuredCfg
  | leave state =>
      simp [Structured.ObserverPreservation.OutcomeSimulation.Rel]
        at hStructuredCfg
  | halt kind state =>
      rename_i sourceFinal targetFinal
      rcases
          Structured.ObserverPreservation.OutcomeSimulation.Rel.halt_iff.mp
            hStructuredCfg with
        ⟨hCfgKind, structuredFinal, hStructuredStep,
          structuredStateRel⟩
      rcases structuredStateRel with
        ⟨tokens, hStructuredState, hRemaining⟩
      rcases hStructuredState with
        ⟨realizedStack, _hRealize, hStructuredRuntime⟩
      rcases
          TypedCfg.ObserverPreservation.Outcome.HaltMatches.elim
            hCfgHalt with
        ⟨hHaltKind, simulated, hSimulatedRuntime,
          hSimulatedStep, hOutput⟩
      have hSimulatedStep' :
          Structured.Terminal.step kind simulated =
            .ok halt.state := by
        simpa [Structured.Terminal.step, hCfgKind] using hSimulatedStep
      have hTerminalRuntime :
          Assembly.SameRuntimeData halt.state structuredFinal := by
        have hCongruence :=
          Structured.Terminal.step_map_eraseRuntimeControl
            kind hSimulatedRuntime
        rw [hSimulatedStep', hStructuredStep] at hCongruence
        simpa [Except.map, Assembly.SameRuntimeData] using hCongruence
      have hFinalRuntime :
          Assembly.SameRuntimeData
            halt.state
            { targetFinal.source.evm with stack := realizedStack } :=
        Assembly.SameRuntimeData.trans
          hTerminalRuntime hStructuredRuntime
      have hSharedEq :
          halt.state.toSharedState =
            targetFinal.source.evm.toSharedState := by
        simpa using Assembly.SameRuntimeData.shared_eq hFinalRuntime
      have hShared :
          Functions.AllocationObserverRelation.SharedRel
            sourceProgram.toFunctions.memoryContract
            sourceFinal.source.shared halt.state.toSharedState := by
        rw [hSharedEq]
        exact state.shared
      have hSourceRemaining :
          sourceFinal.remaining = [] := by
        change transcript.drop sourceFinal.cursor = []
        rw [state.cursor]
        exact hRemaining
      have hOutputEq :
          halt.output =
            sourceFinal.source.shared.toMachineState.H_return := by
        calc
          halt.output =
              halt.state.toMachineState.H_return :=
            hOutput
          _ =
              targetFinal.source.evm.toMachineState.H_return := by
            exact congrArg
              (fun shared =>
                shared.toMachineState.H_return) hSharedEq
          _ =
              sourceFinal.source.shared.toMachineState.H_return :=
            state.shared.machine.output.symm
      refine
        ⟨halt, rfl, hSourceRemaining,
          ⟨kind, rfl, ?_, hShared, hOutputEq⟩⟩
      exact hHaltKind.trans hCfgKind

/--
Stack-only specialization of `terminalWithResourceSafety`.
-/
theorem terminalStackOnly
    {sourceProgram : Objects.Program}
    {artifact : Public.Artifact}
    {sourceFuel targetFuel : Nat}
    {transcript : Trace}
    {initial : Assembly.EVMState}
    {sourceOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetResult : Assembly.StepResult}
    (hAccepted : sourceProgram.SourceAccepted)
    (hLowered :
      artifact.LoweredFrom sourceProgram.toFunctions)
    (hNoExternal : Public.Observer.NoExternalEffects artifact)
    (hStackOnly :
      Functions.AllocationObserverProgram.selectedResourceMode
          artifact.metadata.allocation sourceProgram.toFunctions =
        .stackOnly)
    (hInitial : InitialConditions initial)
    (hSource :
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            sourceProgram.toFunctions.memoryContract transcript)
          sourceFuel sourceProgram.toFunctions
          (Locals.ObserverSemantics.Program.initialState
            initial transcript) =
        .ok sourceOutcome)
    (hTarget :
      Public.Observer.TerminalRun artifact targetFuel
        initial targetResult transcript) :
    ∃ halt,
      targetResult = .halted halt ∧
        sourceOutcome.state.remaining = [] ∧
        TerminalOutcomeRel
          sourceProgram.toFunctions.memoryContract sourceOutcome halt := by
  apply
    terminalWithResourceSafety hAccepted hLowered hNoExternal
      (hInitial := hInitial) (hSource := hSource) (hTarget := hTarget)
  rw [hStackOnly]
  trivial

end ObserverComposition
end Public
end EvmCompiler
