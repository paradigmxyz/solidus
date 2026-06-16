import EvmCompiler.Functions.EffectSemanticsDeterminism
import EvmCompiler.Yul.FunctionsObserverPreservation

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTraceAdequacy

/-!
Narrow reverse reasoning for the adjacent Yul-to-Functions observer boundary.

The source-facing premise states only that the guarded canonical Yul semantics
terminates on the concrete transcript. Ordinary forward preservation
constructs a Functions run; semantic uniqueness aligns that run with the
concrete target execution, whose exhausted cursor proves that the source also
consumed the transcript exactly. No general target-to-source interpreter,
compiler certificate, or call oracle is involved.
-/

abbrev Trace := Assembly.ResourceTrace

def SourceExecutionSafe
    (program : Yul.Program) (source : EvmYul.Yul.State)
    (transcript : Trace) : Prop :=
  ∃ result : ObserverSemantics.SourceReplay.Result transcript,
    ∃ fuel,
      ObserverSafety.SafeSemantics.Program.run
          program.memoryContract fuel program source transcript =
        .ok result ∧
      result.state.cursor ≤ transcript.length

theorem compileProgramTraceAdequate
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {source : EvmYul.Yul.State}
    {target : Functions.ObserverSemantics.State transcript}
    {targetFuel : Nat}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hLower :
      Program.toObjectsWithObservers? sourceProgram =
        some targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hInput :
      FunctionsObserverOutcome.ProgramInputRel codeRel
        (ObserverSemantics.SourceReplay.Program.installContract
          sourceProgram { source := source })
        target)
    (hSafe :
      SourceExecutionSafe sourceProgram source transcript)
    (hTarget :
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            sourceProgram.memoryContract transcript)
          targetFuel targetProgram.toFunctions target =
        .ok targetOutcome)
    (hTargetExhausted : targetOutcome.state.remaining = []) :
    ∃ sourceResult : ObserverSemantics.SourceReplay.Result transcript,
      ObserverSemantics.SourceReplay.Program.ExactTerminates
          sourceProgram source transcript sourceResult ∧
        FunctionsObserverOutcome.ProgramOutcomeRel codeRel
          sourceResult targetOutcome := by
  rcases hSafe with
    ⟨sourceResult, sourceFuel, hSourceRun, hSourceBound⟩
  obtain
      ⟨forwardFuel, forwardOutcome, hForward, hOutcome⟩ :=
    FunctionsObserverPreservation.compileProgramForward
      hLower hProgramOk hInput hSourceRun
  have hOutcomeEq : forwardOutcome = targetOutcome :=
    Functions.Source.Effectful.Program.runState_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        sourceProgram.memoryContract transcript)
      targetProgram.toFunctions hForward hTarget
  rw [hOutcomeEq] at hOutcome
  have hTargetBound :
      targetOutcome.state.cursor ≤ transcript.length := by
    rw [← FunctionsObserverOutcome.ProgramOutcomeRel.cursor_eq hOutcome]
    exact hSourceBound
  have hTranscriptBound :
      transcript.length ≤ targetOutcome.state.cursor := by
    exact List.drop_eq_nil_iff.mp hTargetExhausted
  have hTargetConsumed : targetOutcome.state.ConsumedExactly := by
    exact Nat.le_antisymm hTargetBound hTranscriptBound
  have hSourceConsumed : sourceResult.ConsumedExactly :=
    (FunctionsObserverOutcome.ProgramOutcomeRel.consumedExactly_iff
      hOutcome).mpr hTargetConsumed
  exact
    ⟨sourceResult,
      ObserverSafety.SafeSemantics.Program.ExactTerminates.observerTerminates
        ⟨sourceFuel, hSourceRun, hSourceConsumed⟩,
      hOutcome⟩

end FunctionsObserverTraceAdequacy
end Yul
end EvmCompiler
