import EvmCompiler.Structured.ObserverGeneratedAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace Program

private def Terminal : TypedCfg.Outcome → Prop
  | .halt _ _ => True
  | _ => False

private def TopBoundary {transcript : Trace}
    (source : ObserverSemantics.State transcript)
    (endShape : TypedCfg.Shape) : TypedCfg.Outcome → Prop :=
  OutcomeSimulation.JumpAt source [] ProcLabel.programEnd endShape Terminal

/-- Whole-program outcomes discharge the generated regular continuation by
executing its `STOP` block. Explicit source terminals retain the ordinary
adjacent-pass terminal relation. -/
def TopRel {transcript : Trace}
    (source : ObserverSemantics.Outcome (transcript := transcript))
    (target : TypedCfg.Outcome) (trace : Trace) : Prop :=
  match source.mode, target with
  | .regular, .halt .stop target =>
      ObserverPreservation.StateRel source.state [] target trace
  | .halt kind, .halt targetKind target =>
      targetKind = kind ∧
        ∃ targetFinal,
          Structured.Terminal.step kind target = .ok targetFinal ∧
            ObserverPreservation.OutcomeSimulation.HaltStateRel
              source.state targetFinal trace
  | _, _ => False

namespace GeneratedProgram

theorem programEndShape
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg) :
    OutcomeSimulation.LabelShape cfg ProcLabel.programEnd
      (generated.main.fallthrough?.getD TypedCfg.Shape.caller) := by
  refine
    ⟨{ label := ProcLabel.programEnd
       input := generated.main.fallthrough?.getD TypedCfg.Shape.caller
       body := []
       output := generated.main.fallthrough?.getD TypedCfg.Shape.caller
       term := .halt .stop },
      generated.programEndBlock, rfl⟩

theorem programEnd_step
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (state : EVMState) (trace : Trace) :
    TypedCfg.ObserverSemantics.Program.step
        cfg ProcLabel.programEnd state trace =
      .ok (.halt .stop state, trace) := by
  simp [TypedCfg.ObserverSemantics.Program.step,
    generated.programEndBlock, TypedCfg.ObserverSemantics.Block.run,
    TypedCfg.Block.runTerm, Bind.bind, Except.bind]

theorem programEnd_runN_succ
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (fuel : Nat) (state : EVMState) (trace : Trace) :
    TypedCfg.ObserverSemantics.Program.runN
        cfg (fuel + 1) ProcLabel.programEnd state trace =
      .ok (.halt .stop state, trace) := by
  rw [TypedCfg.ObserverSemantics.Program.runN_succ,
    programEnd_step generated]

end GeneratedProgram

/--
Whole-program target-to-source adequacy for the generated Structured CFG.

The theorem consumes only successful generation, checked source/target inputs,
and a concrete terminal target run. Recursive compiler artifacts stay private
to the adjacent Structured-to-TypedCfg pass.
-/
theorem generateWithProcEntryShapes?_terminal_backward
    {transcript : Trace}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {initial final : EVMState}
    {initialTrace finalTrace : Trace}
    {fuel : Nat} {kind : Assembly.HaltKind}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? program entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hWF : program.WF)
    (hRel :
      ObserverPreservation.StateRel.At
        TypedCfg.Shape.caller source [] initial initialTrace)
    (hRun :
      TypedCfg.ObserverSemantics.Program.runN
          cfg fuel cfg.entry initial initialTrace =
        .ok (.halt kind final, finalTrace)) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval
          program sourceFuel program.body source sourceOutcome ∧
        TopRel sourceOutcome (.halt kind final) finalTrace := by
  let generated :=
    TypedCfgPreservation.Program.GeneratedContext.of_generate
      hGenerate hWellTyped
  let endShape :=
    generated.main.fallthrough?.getD TypedCfg.Shape.caller
  let accept := TopBoundary source endShape
  have hRunEntry :
      TypedCfg.ObserverSemantics.Program.runN
          cfg fuel TypedCfgCompiler.entryLabel initial initialTrace =
        .ok (.halt kind final, finalTrace) := by
    simpa [generated.entry_eq] using hRun
  have hTerminalAccepted :
      accept (.halt kind final) := by
    simp [accept, TopBoundary, Terminal,
      OutcomeSimulation.JumpAt]
  obtain
      ⟨prefixFuel, prefixOutcome, prefixTrace, hPrefixLe, hPrefix⟩ :=
    OutcomeSimulation.FirstReaches.exists_of_run
      hRunEntry hTerminalAccepted
  have hEntryNotAccepted :
      ¬ accept (.jump TypedCfgCompiler.entryLabel initial) := by
    simp [accept, TopBoundary, Terminal,
      OutcomeSimulation.JumpAt, TypedCfgCompiler.entryLabel,
      ProcLabel.programEnd]
  have hPrefixPos :=
    hPrefix.fuel_pos_of_entry_not_accepted hEntryNotAccepted
  cases prefixFuel with
  | zero =>
      omega
  | succ targetFuel =>
      have hContext :
          SourceContext program { procs := program.procs } []
            false false false :=
        { supports :=
            { breakLabel := by simp
              continueLabel := by simp
              leaveLabel := by simp }
          procs := rfl
          leaveTokens := by simp }
      have hEndShape :
          OutcomeSimulation.LabelShape cfg ProcLabel.programEnd endShape := by
        simpa [endShape] using
          GeneratedProgram.programEndShape generated
      have hTerminalOwned :
          OutcomeSimulation.ActivationOwned cfg source [] Terminal := by
        intro label target hAccepted
        simp [Terminal] at hAccepted
      have hTerminalFresh :
          OutcomeSimulation.GeneratedFresh Terminal 0 := by
        intro scope tag target hScope hAccepted
        simp [Terminal] at hAccepted
      have hBoundary :
          OutcomeSimulation.RecursiveBoundary
            cfg source [] accept 0 ProcLabel.programEnd :=
        { ownership :=
            (OutcomeSimulation.ActivationProtected.of_owned
              hTerminalOwned).jumpAt hEndShape
          fresh :=
            OutcomeSimulation.ActivationFreshExcept.of_generated
              hTerminalFresh.jumpAt }
      have hEntryRejected :
          OutcomeSimulation.EntryRejected
            cfg source [] accept TypedCfgCompiler.entryLabel
              TypedCfg.Shape.caller := by
        intro target hShape hFrame hAccepted
        rcases hAccepted with hEnd | hTerminal
        · exact
            (by
              simpa [TypedCfgCompiler.entryLabel,
                ProcLabel.programEnd] using hEnd.1)
        · simpa [Terminal] using hTerminal
      have hMainCompile :
          TypedCfgCompiler.compileBlockFuel?
              (TypedCfgCompiler.blockFuel program.body + 1)
              program.body { procs := program.procs }
              0 TypedCfgCompiler.entryLabel TypedCfg.Shape.caller
              ProcLabel.programEnd =
            some generated.main := by
        simpa [TypedCfgCompiler.compileBlock?] using
          generated.mainCompile
      have hAccept :
          ∀ sourceFuel sourceOutcome targetOutcome trace,
            ObserverSemantics.Block.Eval
                program sourceFuel program.body source sourceOutcome →
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  { procs := program.procs } ProcLabel.programEnd)
                [] sourceOutcome targetOutcome trace →
              OutcomeSimulation.OutcomeArtifact
                generated.main { procs := program.procs } sourceOutcome →
              accept targetOutcome := by
        intro sourceFuel sourceOutcome targetOutcome trace
          hEval hOutcome hArtifact
        rcases sourceOutcome with ⟨sourceFinal, mode⟩
        cases mode with
        | regular =>
            obtain ⟨target, rfl, hState⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.regular_elim
                hOutcome
            obtain ⟨output, hOutput, hFits⟩ := hArtifact
            apply Or.inl
            refine ⟨rfl, ?_⟩
            apply OutcomeSimulation.FrameMatches.of_rel
            · exact
                ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
                  hEval (by simp [ObserverSemantics.Outcome.Nonhalting])
            · exact hState
            · simpa [endShape, hOutput] using hFits
        | brk =>
            obtain ⟨label, target, hLabel, rfl, hState⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.brk_elim hOutcome
            simp [TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
              at hLabel
        | cont =>
            obtain ⟨label, target, hLabel, rfl, hState⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.cont_elim hOutcome
            simp [TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
              at hLabel
        | leave =>
            obtain ⟨label, target, hLabel, rfl, hState⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.leave_elim hOutcome
            simp [TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
              at hLabel
        | halt haltKind =>
            obtain ⟨target, targetFinal, rfl, hStep, hState⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.halt_elim hOutcome
            simp [accept, TopBoundary, Terminal,
              OutcomeSimulation.JumpAt]
      obtain ⟨sourceFuel, sourceOutcome, hEval, hOutcome, hArtifact⟩ :=
        Generated.adequateWithinFuel_block
          generated hWF hContext hWF.2.2.2.2
          (OutcomeSimulation.ActivationInput.top _)
          (by simp [
            OutcomeSimulation.LabelBeforeSupply,
            TypedCfgCompilerFacts.LabelBeforeSupply,
            TypedCfgCompiler.entryLabel])
          (by simp [
            OutcomeSimulation.LabelBeforeSupply,
            TypedCfgCompilerFacts.LabelBeforeSupply,
            ProcLabel.programEnd])
          hBoundary hEntryRejected hMainCompile
          generated.mainBlocks generated.mainCalls
          (targetFuel := targetFuel)
          hAccept hRel (by simpa using hPrefix)
      cases prefixOutcome with
      | jump label middle =>
          rcases hPrefix.boundary with hEnd | hTerminal
          · rcases hEnd with ⟨rfl, hFrame⟩
            have hRemaining :=
              OutcomeSimulation.FirstReaches.remaining_run_of_jump
                hRunEntry hPrefix hPrefixLe
            cases hRemainingFuel : fuel - (targetFuel + 1) with
            | zero =>
                rw [hRemainingFuel] at hRemaining
                simp at hRemaining
            | succ remainingFuel =>
                rw [hRemainingFuel,
                  GeneratedProgram.programEnd_runN_succ generated] at hRemaining
                have hPair := Except.ok.inj hRemaining
                have hOutcomeEq := congrArg Prod.fst hPair
                have hTraceEq := congrArg Prod.snd hPair
                injection hOutcomeEq with hKind hFinal
                subst kind
                subst final
                change prefixTrace = finalTrace at hTraceEq
                subst finalTrace
                refine ⟨sourceFuel, sourceOutcome, hEval, ?_⟩
                rcases sourceOutcome with ⟨sourceFinal, sourceMode⟩
                cases sourceMode with
                | regular =>
                    exact
                      (ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mp
                        hOutcome).2
                | brk =>
                    simp [ObserverPreservation.OutcomeSimulation.Rel,
                      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                      at hOutcome
                | cont =>
                    simp [ObserverPreservation.OutcomeSimulation.Rel,
                      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                      at hOutcome
                | leave =>
                    simp [ObserverPreservation.OutcomeSimulation.Rel,
                      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                      at hOutcome
                | halt sourceKind =>
                    simp [ObserverPreservation.OutcomeSimulation.Rel] at hOutcome
          · simp [Terminal] at hTerminal
      | halt prefixKind prefixFinal =>
          have hExtended :=
            TypedCfg.ObserverSemantics.Program.runN_add_of_halt
              (restFuel := fuel - (targetFuel + 1)) hPrefix.run
          have hFuel :
              targetFuel + 1 + (fuel - (targetFuel + 1)) = fuel := by
            omega
          have hOkEq :
              (.ok (.halt prefixKind prefixFinal, prefixTrace) :
                  Except TypedCfg.EVMException
                    (TypedCfg.Outcome × Trace)) =
                .ok (.halt kind final, finalTrace) := by
            calc
              _ = TypedCfg.ObserverSemantics.Program.runN
                    cfg (targetFuel + 1 + (fuel - (targetFuel + 1)))
                    TypedCfgCompiler.entryLabel initial initialTrace :=
                  hExtended.symm
              _ = TypedCfg.ObserverSemantics.Program.runN
                    cfg fuel TypedCfgCompiler.entryLabel
                    initial initialTrace := by rw [hFuel]
              _ = _ := hRunEntry
          have hPair := Except.ok.inj hOkEq
          have hOutcomeEq := congrArg Prod.fst hPair
          have hTraceEq := congrArg Prod.snd hPair
          injection hOutcomeEq with hKind hFinal
          subst prefixKind
          subst prefixFinal
          change prefixTrace = finalTrace at hTraceEq
          subst prefixTrace
          exact
            ⟨sourceFuel, sourceOutcome, hEval,
              by
                rcases sourceOutcome with ⟨sourceFinal, sourceMode⟩
                cases sourceMode <;>
                  simpa [TopRel,
                    ObserverPreservation.OutcomeSimulation.Rel] using hOutcome⟩
      | fallthrough state =>
          have hImpossible := hPrefix.boundary
          simp [accept, TopBoundary, Terminal,
            OutcomeSimulation.JumpAt] at hImpossible
      | returnDispatch state =>
          have hImpossible := hPrefix.boundary
          simp [accept, TopBoundary, Terminal,
            OutcomeSimulation.JumpAt] at hImpossible
      | invalid state =>
          have hImpossible := hPrefix.boundary
          simp [accept, TopBoundary, Terminal,
            OutcomeSimulation.JumpAt] at hImpossible

end Program
end ObserverAdequacy
end Structured
end EvmCompiler
