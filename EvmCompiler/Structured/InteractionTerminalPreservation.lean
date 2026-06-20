import EvmCompiler.Structured.InteractionBoundedOwnerPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionTerminalPreservation
namespace OpenOutcome

open InteractionControlPreservation.OpenOutcome

/-- Every open-world source branch terminates through a Yul/EVM halt. -/
def SourceHalted : Except EVMException Structured.Outcome -> Prop
  | .ok { mode := .halt _ , .. } => True
  | _ => False

namespace SourceHalted

theorem successful
    {run : Simulation.Interaction EVMException Structured.Outcome}
    (hHalted : Simulation.Interaction.AllDone SourceHalted run) :
    Simulation.Interaction.Successful run := by
  apply Simulation.Interaction.AllDone.mono hHalted
  intro outcome hOutcome
  cases outcome with
  | error error => cases hOutcome
  | ok sourceOutcome => trivial

end SourceHalted

theorem assemblySafeHalted_of_related
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Except EVMException Structured.Outcome}
    {target : Except EVMException TypedCfg.Outcome}
    (hRel : OutcomeDoneRel result ctx regular returns tokens source target)
    (hSourceHalted : SourceHalted source) :
    TypedCfg.InteractionSemantics.Program.AssemblySafeHalted target := by
  cases source with
  | error sourceError => cases hSourceHalted
  | ok sourceOutcome =>
      cases target with
      | error targetError => cases hRel
      | ok targetOutcome =>
          cases hRel with
          | ok hOutcome =>
              rcases sourceOutcome with ⟨sourceState, sourceMode⟩
              cases sourceMode with
              | regular | brk | cont | leave => cases hSourceHalted
              | halt kind =>
                  obtain ⟨targetState, targetFinal, hTarget, hStep,
                      _hFinal⟩ :=
                    TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim
                      hOutcome.1
                  subst targetOutcome
                  exact ⟨targetFinal, hStep⟩

/-- A terminal Structured-to-TypedCfg relation supplies the source-facing
safety needed to execute the adjacent Assembly halt instruction. -/
theorem allDone_assemblySafeHalted
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {sourceRun : Simulation.Interaction EVMException Structured.Outcome}
    {targetRun : Simulation.Interaction EVMException TypedCfg.Outcome}
    (hRel : Simulation.Interaction.Rel
      (OutcomeDoneRel result ctx regular returns tokens)
      sourceRun targetRun)
    (hSourceHalted :
      Simulation.Interaction.AllDone SourceHalted sourceRun) :
    Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeHalted
      targetRun := by
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left hRel hSourceHalted
  apply Simulation.Interaction.Rel.allDone_right hStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hSourceDone⟩
  exact assemblySafeHalted_of_related hRelated hSourceDone

namespace PreservesUnder

/-- Erase the residual-fuel tag from a checked Structured fragment run. -/
theorem outcomes
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    {regularExit : RegularExit}
    (hPreserves :
      InteractionControlPreservation.OpenOutcome.PreservesUnder
        result cfg entry ctx regular regularExit source tokens
        sourceRun targetFuel policy)
    (target : EVMState)
    (hStateRel : TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel
      (OutcomeDoneRel result ctx regular source.returns tokens)
      sourceRun
      (TypedCfg.InteractionSemantics.Program.openRunNWithStop
        policy cfg targetFuel entry target) := by
  have hRunRel := hPreserves target hStateRel
  have hMapped :
      Simulation.Interaction.Rel
        (OutcomeDoneRel result ctx regular source.returns tokens)
        (Simulation.Interaction.bind sourceRun
          Simulation.Interaction.pure)
        (Simulation.Interaction.map
          TypedCfg.InteractionSemantics.Program.runResultOutcome
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            policy cfg targetFuel entry target)) := by
    apply Simulation.Interaction.Rel.bind_custom hRunRel
    intro sourceDone targetDone hDone
    cases sourceDone with
    | error sourceError =>
        cases targetDone with
        | error targetError =>
            exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error trivial)
        | ok targetResult => cases hDone
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError => cases hDone
        | ok targetResult =>
            cases hDone with
            | ok hRun =>
                cases targetResult with
                | exhausted label targetState =>
                    exact False.elim hRun
                | stopped remaining targetOutcome =>
                    exact Simulation.Interaction.Rel.done
                      (Simulation.Interaction.ExceptRel.ok hRun)
  rw [
    TypedCfg.InteractionSemantics.Program.map_openRunNResultWithStop_runResultOutcome]
    at hMapped
  simpa [Simulation.Interaction.bind_pure] using hMapped

/-- On universally halting source runs, a fragment stop policy is inert. -/
theorem terminal
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    {regularExit : RegularExit}
    (hPreserves :
      InteractionControlPreservation.OpenOutcome.PreservesUnder
        result cfg entry ctx regular regularExit source tokens
        sourceRun targetFuel policy)
    (hSourceHalted :
      Simulation.Interaction.AllDone SourceHalted sourceRun)
    (target : EVMState)
    (hStateRel : TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel
      (OutcomeDoneRel result ctx regular source.returns tokens)
      sourceRun
      (TypedCfg.InteractionSemantics.Program.openRunN
        cfg targetFuel entry target) := by
  have hOutcomes := outcomes hPreserves target hStateRel
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left
      hOutcomes hSourceHalted
  have hTargetHalted :
      Simulation.Interaction.AllDone
        TypedCfg.InteractionSemantics.Program.Halted
        (TypedCfg.InteractionSemantics.Program.openRunNWithStop
          policy cfg targetFuel entry target) := by
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone targetDone hDone
    rcases hDone with ⟨hRelated, hSourceDone⟩
    cases sourceDone with
    | error sourceError => cases hSourceDone
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError => cases hRelated
        | ok targetOutcome =>
            cases hRelated with
            | ok hOutcome =>
                rcases sourceOutcome with ⟨sourceState, sourceMode⟩
                cases sourceMode with
                | regular | brk | cont | leave => cases hSourceDone
                | halt kind =>
                    obtain ⟨targetState, targetFinal, hTarget, _hStep,
                        _hFinal⟩ :=
                      TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim
                        hOutcome.1
                    subst targetOutcome
                    trivial
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNWithStop_eq_openRunN_of_allDone_halted
      policy cfg targetFuel entry target hTargetHalted]
    at hOutcomes
  exact hOutcomes

end PreservesUnder

namespace GeneratedProgram

/-- Checked terminal Structured-to-TypedCfg preservation at the ordinary CFG
runner. The generated context is selected internally from compilation. -/
theorem generateWithProcEntryShapes?_main_terminal
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? program entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState)
    (hSourceHalted : Simulation.Interaction.AllDone SourceHalted
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)) :
    exists generated :
        TypedCfgPreservation.Program.GeneratedContext
          program entryShapes cfg,
      forall target,
        TypedCfgPreservation.StateRel source [] target ->
          Simulation.Interaction.Rel
            (OutcomeDoneRel generated.main
              { procs := program.procs } ProcLabel.programEnd
              source.returns [])
            (InteractionSemantics.Block.openRun
              program sourceFuel program.body source)
            (TypedCfg.InteractionSemantics.Program.openRunN cfg
              (InteractionStaticCost.blockBudget
                program sourceFuel program.body)
              TypedCfgCompiler.entryLabel target) := by
  obtain ⟨generated, hPreserves⟩ :=
    InteractionBoundedOwnerPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_preserves
      hGenerate hWellTyped hProgramWF hProgramFrameSafe sourceFuel source
        (SourceHalted.successful hSourceHalted)
  refine ⟨generated, ?_⟩
  intro target hStateRel
  exact PreservesUnder.terminal
    hPreserves hSourceHalted target hStateRel

end GeneratedProgram

end OpenOutcome
end InteractionTerminalPreservation
end Structured
end EvmCompiler
