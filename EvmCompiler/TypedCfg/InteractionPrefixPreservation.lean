import EvmCompiler.TypedCfg.InteractionPreservation

namespace EvmCompiler
namespace TypedCfg
namespace InteractionPrefixPreservation

open InteractionPreservation

namespace Program

/-- Certified TypedCfg-to-Assembly preservation for every finite interaction
prefix. Structural CFG exhaustion preserves only the exact transcript prefix;
runtime errors and source-safe halts preserve their complete outcomes. -/
theorem compileCertified?_entry_openRunNPrefix_assembly_forward
    {program : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {targetState sourceState : EVMState} (fuel : Nat)
    (hCompile : program.compileCertified? = some artifact)
    (hIndependent : program.ProgramCounterIndependent)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat 0)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC)
    (hSafe : Simulation.Interaction.AllDone
      InteractionSemantics.Program.PrefixAssemblySafe
      (InteractionSemantics.Program.openRunNPrefix
        program fuel program.entry sourceState)) :
    Simulation.Interaction.ForwardRel
      InteractionSemantics.Program.PrefixTruncated
      (InteractionPreservation.OpenBlock.RunSimulates artifact.target)
      (InteractionSemantics.Program.openRunNPrefix
        program fuel program.entry sourceState)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.target
        (fuel * InteractionSemantics.CompiledProgram.fuelBudget program)
        targetState) := by
  have hLower : program.lower? = some artifact.target :=
    TypedCfg.Program.compileCertified?_target hCompile
  have hAccepted :=
    TypedCfg.Program.compileCertified?_targetAccepted hCompile
  have hFits := TypedCfg.Program.compileCertified?_pcFits hCompile
  have hTyped := TypedCfg.Program.compileCertified?_wellTyped hCompile
  have hLabelPc := TypedCfg.Program.lower?_entry_labelPc_zero hLower
  have hBlocks :=
    InteractionPreservation.Program.compileCertified?_entry_openRunN_rel fuel
      hCompile hIndependent hPc hRuntime
  apply Simulation.Interaction.ForwardRel.of_executes_or_follows
  intro transcript sourceDone hSourceExec
  have hSafeDone :=
    Simulation.Interaction.AllDone.property_of_executes hSafe hSourceExec
  unfold InteractionSemantics.Program.openRunNPrefix at hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    hRunError | hRunOk
  · rcases hRunError with ⟨sourceError, hDone, hRun⟩
    subst sourceDone
    obtain ⟨usedFuel, hUsedFuel, hAssemblyExec⟩ :=
      InteractionPreservation.Program.lower?_openRunN_error_executes_source_bounded
        hLower hAccepted hFits hTyped hIndependent hLabelPc hPc hRuntime hRun
    by_cases hTruncated :
        InteractionSemantics.Program.PrefixTruncated sourceError
    · exact .inl
        ⟨sourceError, rfl, hTruncated,
          Assembly.InteractionSemantics.Source.openRunNResult_follows_of_executes_of_le
            hUsedFuel hAssemblyExec⟩
    · let extra :=
        fuel * InteractionSemantics.CompiledProgram.fuelBudget program -
          usedFuel
      have hFuel :
          usedFuel + extra =
            fuel * InteractionSemantics.CompiledProgram.fuelBudget program :=
        Nat.add_sub_of_le hUsedFuel
      have hPadded :=
        Assembly.InteractionSemantics.Source.openRunNResult_error_add_executes
          (extra := extra) hAssemblyExec
      rw [hFuel] at hPadded
      exact .inr ⟨.error sourceError, hPadded, rfl⟩
  · rcases hRunOk with
      ⟨sourceOutcome, headTranscript, restTranscript,
        hTranscript, hRun, hFinish⟩
    subst transcript
    cases sourceOutcome with
    | halt kind sourceFinal =>
        cases hFinish
        obtain ⟨targetDone, hTargetExec, hSim⟩ :=
          Simulation.Interaction.Rel.executes hBlocks hRun
        have hSourceSafe :
            InteractionSemantics.Program.AssemblySafeHalted
              (.ok (.halt kind sourceFinal)) := by
          exact hSafeDone
        have hTerminal :=
          InteractionPreservation.OpenBlock.terminal_of_assemblySafeHalted
            hSourceSafe hSim
        cases targetDone with
        | error targetError => cases hTerminal
        | ok targetResult =>
            cases targetResult with
            | running targetAfter => cases hTerminal
            | halted halt =>
                obtain ⟨usedFuel, hUsedFuel, hAssemblyExec⟩ :=
                  InteractionSemantics.CompiledProgram.openRunN_executes_source_bounded
                    hTargetExec
                let extra :=
                  fuel * InteractionSemantics.CompiledProgram.fuelBudget program -
                    usedFuel
                have hFuel :
                    usedFuel + extra =
                      fuel *
                        InteractionSemantics.CompiledProgram.fuelBudget program :=
                  Nat.add_sub_of_le hUsedFuel
                have hPadded :=
                  Assembly.InteractionSemantics.Source.openRunNResult_halted_add_executes
                    (extra := extra) hAssemblyExec
                rw [hFuel] at hPadded
                exact .inr
                  ⟨.ok (.halted halt), by simpa using hPadded, hSim⟩
    | jump label sourceFinal =>
        cases hFinish
        obtain ⟨targetDone, hTargetExec, _hSim⟩ :=
          Simulation.Interaction.Rel.executes hBlocks hRun
        obtain ⟨usedFuel, hUsedFuel, hAssemblyFollow⟩ :=
          InteractionSemantics.CompiledProgram.openRunN_follows_source_bounded
            hLower hTargetExec
        exact .inl
          ⟨.OutOfFuel, rfl, by trivial,
            by simpa using
              Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
                hUsedFuel hAssemblyFollow⟩
    | fallthrough sourceFinal =>
        cases hFinish
        obtain ⟨targetDone, hTargetExec, _hSim⟩ :=
          Simulation.Interaction.Rel.executes hBlocks hRun
        obtain ⟨usedFuel, hUsedFuel, hAssemblyFollow⟩ :=
          InteractionSemantics.CompiledProgram.openRunN_follows_source_bounded
            hLower hTargetExec
        exact .inl
          ⟨.OutOfFuel, rfl, by trivial,
            by simpa using
              Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
                hUsedFuel hAssemblyFollow⟩
    | returnDispatch sourceFinal =>
        cases hFinish
        obtain ⟨targetDone, hTargetExec, _hSim⟩ :=
          Simulation.Interaction.Rel.executes hBlocks hRun
        obtain ⟨usedFuel, hUsedFuel, hAssemblyFollow⟩ :=
          InteractionSemantics.CompiledProgram.openRunN_follows_source_bounded
            hLower hTargetExec
        exact .inl
          ⟨.OutOfFuel, rfl, by trivial,
            by simpa using
              Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
                hUsedFuel hAssemblyFollow⟩
    | invalid sourceFinal =>
        cases hFinish
        obtain ⟨targetDone, hTargetExec, _hSim⟩ :=
          Simulation.Interaction.Rel.executes hBlocks hRun
        obtain ⟨usedFuel, hUsedFuel, hAssemblyFollow⟩ :=
          InteractionSemantics.CompiledProgram.openRunN_follows_source_bounded
            hLower hTargetExec
        exact .inl
          ⟨.OutOfFuel, rfl, by trivial,
            by simpa using
              Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
                hUsedFuel hAssemblyFollow⟩

end Program
end InteractionPrefixPreservation
end TypedCfg
end EvmCompiler
