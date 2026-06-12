import EvmCompiler.Structured.ObserverAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace Stmt

/--
A well-typed TypedCfg halt cannot obtain missing operands from compiler-owned
return data. The shape-indexed relation therefore reconstructs the
corresponding observer-aware Structured terminal evaluation.
-/
theorem terminal_of_wellTyped_halt
    {transcript : Trace} {program : Structured.Program}
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {kind : Assembly.HaltKind}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {fuel : Nat}
    (hTyped : block.WellTyped cfg)
    (hTerm : block.term = .halt kind)
    (hSourceArity :
      kind.argCount ≤
        TypedCfgCompiler.Shape.sourceLength block.output)
    (hRel :
      ObserverPreservation.StateRel.At
        block.output source tokens target trace) :
    ∃ finalEVM,
      Structured.Terminal.step kind source.source.evm =
          .ok finalEVM ∧
        ObserverSemantics.Stmt.Eval program fuel
          (.terminal kind) source
          (Structured.OutcomeT.halt kind
            (source.withSource
              (source.source.withEVM finalEVM))) := by
  have hAritySource :
      kind.argCount ≤ source.source.evm.stack.length :=
    Nat.le_trans hSourceArity hRel.sourceStack
  obtain ⟨finalEVM, hStep⟩ :=
    Structured.Terminal.exists_step_of_argCount_le
      kind source.source.evm hAritySource
  exact
    ⟨finalEVM, hStep,
      Structured.EffectSemantics.Stmt.Eval.terminal hStep⟩

/--
The terminal backward leaf also reconstructs the post-terminal target relation.
This is the outcome-indexed fact needed by the recursive statement adequacy
proof; no terminal-safety premise remains at the boundary.
-/
theorem terminal_outcome_of_wellTyped_halt
    {transcript : Trace} {program : Structured.Program}
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {kind : Assembly.HaltKind}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {fuel : Nat}
    (hTyped : block.WellTyped cfg)
    (hTerm : block.term = .halt kind)
    (hSourceArity :
      kind.argCount ≤
        TypedCfgCompiler.Shape.sourceLength block.output)
    (hRel :
      ObserverPreservation.StateRel.At
        block.output source tokens target trace) :
    ∃ sourceFinal targetFinal,
      Structured.Terminal.step kind source.source.evm =
          .ok sourceFinal ∧
        Structured.Terminal.step kind target =
          .ok targetFinal ∧
        ObserverSemantics.Stmt.Eval program fuel
          (.terminal kind) source
          (Structured.OutcomeT.halt kind
            (source.withSource
              (source.source.withEVM sourceFinal))) ∧
        ObserverPreservation.StateRel
          (source.withSource
            (source.source.withEVM sourceFinal))
          tokens targetFinal trace := by
  obtain ⟨sourceFinal, hSourceStep, hEval⟩ :=
    terminal_of_wellTyped_halt hTyped hTerm hSourceArity hRel
  obtain ⟨targetFinal, hTargetStep, hFinalRel⟩ :=
    ObserverPreservation.StateRel.terminal hRel.rel hSourceStep
  exact
    ⟨sourceFinal, targetFinal, hSourceStep, hTargetStep,
      hEval, hFinalRel⟩

/--
Compiler-facing backward adequacy for a terminal statement.

The checked compiler block and ambient CFG typing construct all target evidence
internally. The public inputs are the existing compiler result, its generated
block inclusion, and the adjacent shape-indexed state relation.
-/
theorem outcome_terminal_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hWellTyped : cfg.WellTyped)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace) :
    ∃ sourceFinal targetFinal,
      ObserverSemantics.Stmt.Eval program fuel
          (.terminal kind) source
          (Structured.OutcomeT.halt kind
            (source.withSource
              (source.source.withEVM sourceFinal))) ∧
        TypedCfg.ObserverSemantics.Program.Eventually
          cfg entry target trace (.halt kind target) trace ∧
        Structured.Terminal.step kind target =
          .ok targetFinal ∧
        ObserverPreservation.StateRel
          (source.withSource
            (source.source.withEVM sourceFinal))
          tokens targetFinal trace := by
  obtain ⟨hSourceWords, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal
      hCompile
  have hSourceArity :
      kind.argCount ≤ TypedCfgCompiler.Shape.sourceLength input :=
    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
      hSourceWords
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .halt kind }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hMem : generated ∈ cfg.blocks := by
    unfold TypedCfg.Program.findBlock? at hFind
    exact List.mem_of_find?_eq_some hFind
  have hTyped : generated.WellTyped cfg :=
    (List.forall_iff_forall_mem.mp hWellTyped.2.1) generated hMem
  obtain
      ⟨sourceFinal, targetFinal, _hSourceStep,
        hTargetStep, hEval, hFinalRel⟩ :=
    terminal_outcome_of_wellTyped_halt
      (fuel := fuel) hTyped (by rfl) hSourceArity hRel
  have hRun :
      TypedCfg.ObserverSemantics.Block.run
          generated target trace =
        .ok (.halt kind target, trace) := by
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hEventually :=
    ObserverPreservation.BlocksInProgram.eventually_of_run
      hBlocks (block := generated) (by simp [generated]) hRun
  exact
    ⟨sourceFinal, targetFinal, hEval, hEventually,
      hTargetStep, hFinalRel⟩

/--
Stable backward-adequacy interface for terminal statements.
-/
theorem adequateWithin_terminal_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hWellTyped : cfg.WellTyped) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.terminal kind) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  obtain
      ⟨sourceFinal, targetFinal, hEval, _hEventually,
        hTargetStep, hFinalRel⟩ :=
    outcome_terminal_of_compileStmtFuel?
      (program := program)
      hCompile hBlocks hWellTyped hRel
  have hCompile' := hCompile
  obtain ⟨_hSourceWords, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal
      hCompile'
  subst result
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .halt kind }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.halt kind target, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFind]
    simp [generated, TypedCfg.ObserverSemantics.Block.run,
      TypedCfg.ObserverSemantics.Block.runBody_nil,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]
  have hBoundary :
      OutcomeSimulation.TargetBoundary continuations
        (.halt kind target) := by
    trivial
  let final :
      ObserverSemantics.State transcript :=
    source.withSource
      (source.source.withEVM sourceFinal)
  have hSourceEval :
      ObserverSemantics.Stmt.Eval
        program compilerFuel (.terminal kind) source
          (Structured.OutcomeT.halt kind final) := by
    simpa [final] using hEval
  have hOutcomeRel :
      ObserverPreservation.OutcomeSimulation.Rel
        continuations tokens
        (Structured.OutcomeT.halt kind final)
        (.halt kind target) trace :=
    ObserverPreservation.OutcomeSimulation.Rel.halt_iff.mpr
      ⟨rfl, targetFinal, hTargetStep, ⟨tokens, hFinalRel⟩⟩
  obtain ⟨hOutcomeEq, hTraceEq⟩ :=
    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
      hReach hStep
        (hAccept compilerFuel _ _ _ hSourceEval hOutcomeRel trivial)
  subst targetOutcome
  subst traceFinal
  exact
    ⟨compilerFuel, Structured.OutcomeT.halt kind final,
      hSourceEval,
      hOutcomeRel,
      trivial⟩

end Stmt
end ObserverAdequacy
end Structured
end EvmCompiler
