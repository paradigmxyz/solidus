import EvmCompiler.Structured.InteractionControlPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionLeafPreservation

namespace Stmt

private theorem target_openStep_empty_jump
    {cfg : TypedCfg.Program}
    {entry exitLabel : Assembly.Label} {input : TypedCfg.Shape}
    {targetState : EVMState}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .jump exitLabel }) :
    TypedCfg.InteractionSemantics.Program.openStep
        cfg entry targetState =
      Simulation.Interaction.pure
        (TypedCfg.Outcome.jump exitLabel targetState) := by
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind,
    TypedCfg.InteractionSemantics.Block.openRun,
    TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody,
    TypedCfg.Block.runTerm]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.done
          (Except.ok (targetState, input)))
        (fun result =>
          if result.2 = input then
            Simulation.Interaction.done
              (Except.ok
                (TypedCfg.Outcome.jump exitLabel result.1))
          else
            Simulation.Interaction.done
              (Except.error
                (.InvalidInstruction : EVMException))) =
      Simulation.Interaction.done
        (Except.ok
          (TypedCfg.Outcome.jump exitLabel targetState))
  simp [Simulation.Interaction.bind]

private theorem target_openStep_empty_halt
    {cfg : TypedCfg.Program}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    {kind : Assembly.HaltKind} {targetState : EVMState}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .halt kind })
    (hAllowed : kind = .selfdestruct →
      targetState.executionEnv.perm = true) :
    TypedCfg.InteractionSemantics.Program.openStep
        cfg entry targetState =
      Simulation.Interaction.pure
        (TypedCfg.Outcome.halt kind targetState) := by
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind,
    TypedCfg.InteractionSemantics.Block.openRun,
    TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody,
    TypedCfg.Block.runTerm]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.done
          (Except.ok (targetState, input)))
        (fun result =>
          if result.2 = input then
            match TypedCfg.Block.runTermChecked
                input (.halt kind) result.1 with
            | .ok outcome => Simulation.Interaction.pure outcome
            | .error err => Simulation.Interaction.error err
          else
            Simulation.Interaction.done
              (Except.error
                (.InvalidInstruction : EVMException))) =
      Simulation.Interaction.done
        (Except.ok
          (TypedCfg.Outcome.halt kind targetState))
  simp [Simulation.Interaction.bind,
    TypedCfg.Block.runTermChecked_halt_of_allowed _ _ _ hAllowed]
  rfl

private theorem target_openStep_empty_selfdestruct_static
    {cfg : TypedCfg.Program}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    {targetState : EVMState}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .halt .selfdestruct })
    (hPermission : targetState.executionEnv.perm = false) :
    TypedCfg.InteractionSemantics.Program.openStep
        cfg entry targetState =
      .done (.error .StaticModeViolation) := by
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind,
    TypedCfg.InteractionSemantics.Block.openRun,
    TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody,
    TypedCfg.Block.runTerm]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.done
          (Except.ok (targetState, input)))
        (fun result =>
          if result.2 = input then
            match TypedCfg.Block.runTermChecked
                input (.halt .selfdestruct) result.1 with
            | .ok outcome => Simulation.Interaction.pure outcome
            | .error err => Simulation.Interaction.error err
          else
            Simulation.Interaction.error
              (.InvalidInstruction : EVMException)) =
      .done (.error .StaticModeViolation)
  simp [Simulation.Interaction.bind,
    TypedCfg.Block.runTermChecked_selfdestruct_of_static _ _ hPermission]
  rfl

/--
Compiled `break` performs one effect-free TypedCfg jump while preserving the
complete open outcome relation.
-/
theorem openStep_brk_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {targetState : EVMState}
    (hExit : ctx.breakLabel? = some exitLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStateRel :
      TypedCfgPreservation.StateRel source tokens targetState) :
    Simulation.Interaction.Rel
      (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
        result ctx regular source.returns tokens)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .brk source)
      (TypedCfg.InteractionSemantics.Program.openStep
        cfg entry targetState) := by
  obtain ⟨hBreakShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_brk
      hExit hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump exitLabel }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  have hTargetRun :
      TypedCfg.InteractionSemantics.Program.openStep
          cfg entry targetState =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump exitLabel targetState) := by
    apply target_openStep_empty_jump
    simpa [generated] using hFind
  have hRelated :
      InteractionControlPreservation.OpenOutcome.Rel
        { blocks := [generated]
          next := supply + 1
          calls := []
          fallthrough? := none }
        ctx regular source.returns tokens
        (Structured.Outcome.brk source)
        (.jump exitLabel targetState) := by
    constructor
    · exact
        TypedCfgPreservation.OutcomeSimulation.Rel.brk_iff.mpr
          ⟨hExit, hStateRel⟩
    · exact
        ⟨⟨input, hBreakShape, hFits⟩, rfl⟩
  rw [hTargetRun]
  simpa [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    generated] using
    Simulation.Interaction.Rel.done
      (Simulation.Interaction.ExceptRel.ok hRelated)

/--
`break` is boundary-parametric because it has no regular outcome.
-/
theorem openRun_brk_within_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular boundaryRegular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    (hExit : ctx.breakLabel? = some exitLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result boundaryResult cfg entry ctx regular boundaryRegular
      regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .brk source)
      1 := by
  obtain ⟨_hBreakShape, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_brk
      hExit hCompile
  have hNoFallthrough : result.fallthrough? = none := by
    simp [hResult]
  apply
    InteractionControlPreservation.OpenOutcome.PreservesWithin.of_openStep
  · intro targetState hStateRel
    exact
      openStep_brk_of_compileStmtFuel?
        hExit hCompile hBlocks hFits hStateRel
  · intro final targetState hRel
    exact False.elim
      (InteractionControlPreservation.OpenOutcome.Rel.not_regular_of_fallthrough_none
        hNoFallthrough hRel)

/--
`break` preserves under any active policy that stops nonregular outcomes.
-/
theorem openRun_brk_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hExit : ctx.breakLabel? = some exitLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hNonregularStops :
      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular
        policy ctx source.returns tokens) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      result cfg entry ctx regular regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .brk source)
      1 policy := by
  obtain ⟨_hBreakShape, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_brk
      hExit hCompile
  apply
    InteractionControlPreservation.OpenOutcome.PreservesUnder.of_openStep_no_fallthrough
      (by simp [hResult])
  · intro targetState hStateRel
    exact
      openStep_brk_of_compileStmtFuel?
        hExit hCompile hBlocks hFits hStateRel
  · exact hNonregularStops

/--
Compiled `continue` performs the context-owned continue jump and preserves the
same open outcome relation.
-/
theorem openStep_cont_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {targetState : EVMState}
    (hExit : ctx.continueLabel? = some exitLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStateRel :
      TypedCfgPreservation.StateRel source tokens targetState) :
    Simulation.Interaction.Rel
      (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
        result ctx regular source.returns tokens)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .cont source)
      (TypedCfg.InteractionSemantics.Program.openStep
        cfg entry targetState) := by
  obtain ⟨hContinueShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_cont
      hExit hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump exitLabel }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  have hTargetRun :
      TypedCfg.InteractionSemantics.Program.openStep
          cfg entry targetState =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump exitLabel targetState) := by
    apply target_openStep_empty_jump
    simpa [generated] using hFind
  have hRelated :
      InteractionControlPreservation.OpenOutcome.Rel
        { blocks := [generated]
          next := supply + 1
          calls := []
          fallthrough? := none }
        ctx regular source.returns tokens
        (Structured.Outcome.cont source)
        (.jump exitLabel targetState) := by
    constructor
    · exact
        TypedCfgPreservation.OutcomeSimulation.Rel.cont_iff.mpr
          ⟨hExit, hStateRel⟩
    · exact
        ⟨⟨input, hContinueShape, hFits⟩, rfl⟩
  rw [hTargetRun]
  simpa [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    generated] using
    Simulation.Interaction.Rel.done
      (Simulation.Interaction.ExceptRel.ok hRelated)

/--
`continue` is boundary-parametric because it has no regular outcome.
-/
theorem openRun_cont_within_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular boundaryRegular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    (hExit : ctx.continueLabel? = some exitLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result boundaryResult cfg entry ctx regular boundaryRegular
      regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .cont source)
      1 := by
  obtain ⟨_hContinueShape, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_cont
      hExit hCompile
  have hNoFallthrough : result.fallthrough? = none := by
    simp [hResult]
  apply
    InteractionControlPreservation.OpenOutcome.PreservesWithin.of_openStep
  · intro targetState hStateRel
    exact
      openStep_cont_of_compileStmtFuel?
        hExit hCompile hBlocks hFits hStateRel
  · intro final targetState hRel
    exact False.elim
      (InteractionControlPreservation.OpenOutcome.Rel.not_regular_of_fallthrough_none
        hNoFallthrough hRel)

/--
`continue` preserves under any active policy that stops nonregular outcomes.
-/
theorem openRun_cont_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hExit : ctx.continueLabel? = some exitLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hNonregularStops :
      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular
        policy ctx source.returns tokens) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      result cfg entry ctx regular regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .cont source)
      1 policy := by
  obtain ⟨_hContinueShape, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_cont
      hExit hCompile
  apply
    InteractionControlPreservation.OpenOutcome.PreservesUnder.of_openStep_no_fallthrough
      (by simp [hResult])
  · intro targetState hStateRel
    exact
      openStep_cont_of_compileStmtFuel?
        hExit hCompile hBlocks hFits hStateRel
  · exact hNonregularStops

/--
Compiled `leave` performs the procedure-exit jump. The explicit return-frame
premise is source-facing: without an active procedure activation, ordinary
Structured semantics rejects `leave`.
-/
theorem openStep_leave_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {targetState : EVMState}
    {frame : ReturnDest} {restReturns : List ReturnDest}
    (hExit : ctx.leaveLabel? = some exitLabel)
    (hReturns : source.returns = frame :: restReturns)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStateRel :
      TypedCfgPreservation.StateRel source tokens targetState) :
    Simulation.Interaction.Rel
      (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
        result ctx regular source.returns tokens)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .leave source)
      (TypedCfg.InteractionSemantics.Program.openStep
        cfg entry targetState) := by
  obtain ⟨hLeaveShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_leave
      hExit hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump exitLabel }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  have hTargetRun :
      TypedCfg.InteractionSemantics.Program.openStep
          cfg entry targetState =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump exitLabel targetState) := by
    apply target_openStep_empty_jump
    simpa [generated] using hFind
  have hRelated :
      InteractionControlPreservation.OpenOutcome.Rel
        { blocks := [generated]
          next := supply + 1
          calls := []
          fallthrough? := none }
        ctx regular source.returns tokens
        (Structured.Outcome.leave source)
        (.jump exitLabel targetState) := by
    constructor
    · exact
        TypedCfgPreservation.OutcomeSimulation.Rel.leave_iff.mpr
          ⟨hExit, hStateRel⟩
    · exact
        ⟨⟨input, hLeaveShape, hFits⟩, rfl⟩
  rw [hTargetRun]
  simpa [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    hReturns, generated] using
    Simulation.Interaction.Rel.done
      (Simulation.Interaction.ExceptRel.ok hRelated)

/--
`leave` is boundary-parametric because it has no regular outcome.
-/
theorem openRun_leave_within_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular boundaryRegular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {frame : ReturnDest} {restReturns : List ReturnDest}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    (hExit : ctx.leaveLabel? = some exitLabel)
    (hReturns : source.returns = frame :: restReturns)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result boundaryResult cfg entry ctx regular boundaryRegular
      regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .leave source)
      1 := by
  obtain ⟨_hLeaveShape, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_leave
      hExit hCompile
  have hNoFallthrough : result.fallthrough? = none := by
    simp [hResult]
  apply
    InteractionControlPreservation.OpenOutcome.PreservesWithin.of_openStep
  · intro targetState hStateRel
    exact
      openStep_leave_of_compileStmtFuel?
        hExit hReturns hCompile hBlocks hFits hStateRel
  · intro final targetState hRel
    exact False.elim
      (InteractionControlPreservation.OpenOutcome.Rel.not_regular_of_fallthrough_none
        hNoFallthrough hRel)

/--
`leave` preserves under any active policy that stops nonregular outcomes.
-/
theorem openRun_leave_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry exitLabel regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {frame : ReturnDest} {restReturns : List ReturnDest}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hExit : ctx.leaveLabel? = some exitLabel)
    (hReturns : source.returns = frame :: restReturns)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hNonregularStops :
      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular
        policy ctx source.returns tokens) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      result cfg entry ctx regular regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel .leave source)
      1 policy := by
  obtain ⟨_hLeaveShape, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_leave
      hExit hCompile
  apply
    InteractionControlPreservation.OpenOutcome.PreservesUnder.of_openStep_no_fallthrough
      (by simp [hResult])
  · intro targetState hStateRel
    exact
      openStep_leave_of_compileStmtFuel?
        hExit hReturns hCompile hBlocks hFits hStateRel
  · exact hNonregularStops

/--
Compiled terminal statements preserve the open terminal step and relate the
post-terminal source state to the TypedCfg halt marker's pre-terminal state.
-/
theorem openStep_terminal_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {targetState : EVMState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStateRel :
      TypedCfgPreservation.StateRel source tokens targetState) :
    Simulation.Interaction.Rel
      (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
        result ctx regular source.returns tokens)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.terminal kind) source)
      (TypedCfg.InteractionSemantics.Program.openStep
        cfg entry targetState) := by
  obtain ⟨hSourceWords, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal
      hCompile
  have hSourceArity :
      kind.argCount ≤ TypedCfgCompiler.Shape.sourceLength input :=
    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
      hSourceWords
  have hStackArity :
      kind.argCount ≤ source.evm.stack.length :=
    Nat.le_trans hSourceArity hFits.1
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .halt kind }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  by_cases hAllowed : Structured.Terminal.Allowed kind source.evm
  swap
  · rcases Structured.Terminal.not_allowed_iff.mp hAllowed with
      ⟨rfl, hSourcePermission⟩
    have hTargetShared :
        targetState.toSharedState = source.evm.toSharedState := by
      rcases hStateRel with ⟨_realized, _hRealize, hSame⟩
      simpa using Assembly.SameRuntimeData.shared_eq hSame
    have hTargetPermission :
        targetState.executionEnv.perm = false := by
      change targetState.toSharedState.executionEnv.perm = false
      rw [hTargetShared]
      exact hSourcePermission
    have hSourceTerminal :
        InteractionSemantics.Terminal.openStep .selfdestruct source =
          .done (.error .StaticModeViolation) := by
      have hPrimitive :
          Assembly.PrimOp.selfdestruct.step source.evm =
            .error .StaticModeViolation :=
        Assembly.PrimOp.step_selfdestruct_of_static
          source.evm hSourcePermission
      unfold InteractionSemantics.Terminal.openStep
      rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
        (by rfl) (by decide) (by decide)]
      change
        Simulation.Interaction.map source.withEVM
            (.done (Assembly.PrimOp.selfdestruct.step source.evm)) = _
      rw [hPrimitive]
      rfl
    have hTargetRun :
        TypedCfg.InteractionSemantics.Program.openStep
            cfg entry targetState =
          .done (.error .StaticModeViolation) := by
      apply target_openStep_empty_selfdestruct_static
      · simpa [generated] using hFind
      · exact hTargetPermission
    have hDone :
        Simulation.Interaction.Rel
          (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
            { blocks := [generated]
              next := supply + 1
              calls := []
              fallthrough? := none }
            ctx regular source.returns tokens)
          (.done (.error .StaticModeViolation))
          (.done (.error .StaticModeViolation)) :=
      Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.error trivial)
    rw [hTargetRun]
    simpa [InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Stmt.run,
      InteractionSemantics.handler, hSourceTerminal, generated] using hDone
  obtain ⟨sourceFinal, hSourceStep⟩ :=
    Structured.Terminal.exists_step_of_argCount_le
      kind source.evm hStackArity hAllowed
  obtain ⟨targetFinal, hTargetStep, hFinalStateRel⟩ :=
    TypedCfgPreservation.StateRel.terminal
      hStateRel hSourceStep
  have hTargetRun :
      TypedCfg.InteractionSemantics.Program.openStep
          cfg entry targetState =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.halt kind targetState) := by
    apply target_openStep_empty_halt
    · simpa [generated] using hFind
    · exact Structured.Terminal.allowed_of_step hTargetStep
  have hRelated :
      InteractionControlPreservation.OpenOutcome.Rel
        { blocks := [generated]
          next := supply + 1
          calls := []
          fallthrough? := none }
        ctx regular source.returns tokens
        (Structured.Outcome.halt kind
          (source.withEVM sourceFinal))
        (.halt kind targetState) := by
    constructor
    · exact
        TypedCfgPreservation.OutcomeSimulation.Rel.halt_iff.mpr
          ⟨rfl, targetFinal, hTargetStep,
            ⟨tokens, hFinalStateRel⟩⟩
    · exact ⟨trivial, trivial⟩
  have hDone :
      Simulation.Interaction.Rel
        (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
          { blocks := [generated]
            next := supply + 1
            calls := []
            fallthrough? := none }
          ctx regular source.returns tokens)
        (Simulation.Interaction.pure
          (Structured.Outcome.halt kind
            (source.withEVM sourceFinal)))
        (Simulation.Interaction.pure
          (TypedCfg.Outcome.halt kind targetState)) :=
    Simulation.Interaction.Rel.done
      (Simulation.Interaction.ExceptRel.ok hRelated)
  have hTerminalRun :
      InteractionSemantics.Terminal.openStep kind source =
        Simulation.Interaction.pure
          (source.withEVM sourceFinal) := by
    have hExternal :
        Simulation.ExternalKind.ofEVMOperation?
            kind.toPrimOp.toEVM = none := by
      cases kind <;> rfl
    have hGas : kind.toPrimOp ≠ .gas := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    have hMsize : kind.toPrimOp ≠ .msize := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    have hPrimitiveStep :
        kind.toPrimOp.step source.evm = .ok sourceFinal := by
      simpa [Structured.Terminal.step] using hSourceStep
    unfold InteractionSemantics.Terminal.openStep
    rw [
      Assembly.InteractionSemantics.PrimOp.openStep_closed
        hExternal hGas hMsize]
    simp [Simulation.Interaction.map, hPrimitiveStep]
  rw [hTargetRun]
  simpa [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    InteractionSemantics.handler,
    hTerminalRun, generated] using hDone

/--
Terminal statements are boundary-parametric because they cannot return
regularly.
-/
theorem openRun_terminal_within_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular boundaryRegular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result boundaryResult cfg entry ctx regular boundaryRegular
      regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.terminal kind) source)
      1 := by
  obtain ⟨_hSourceWords, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal
      hCompile
  have hNoFallthrough : result.fallthrough? = none := by
    simp [hResult]
  apply
    InteractionControlPreservation.OpenOutcome.PreservesWithin.of_openStep
  · intro targetState hStateRel
    exact
      openStep_terminal_of_compileStmtFuel?
        hCompile hBlocks hFits hStateRel
  · intro final targetState hRel
    exact False.elim
      (InteractionControlPreservation.OpenOutcome.Rel.not_regular_of_fallthrough_none
        hNoFallthrough hRel)

/--
Terminals preserve under any active policy that stops nonregular outcomes.
-/
theorem openRun_terminal_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hNonregularStops :
      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular
        policy ctx source.returns tokens) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      result cfg entry ctx regular regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.terminal kind) source)
      1 policy := by
  obtain ⟨_hSourceWords, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal
      hCompile
  apply
    InteractionControlPreservation.OpenOutcome.PreservesUnder.of_openStep_no_fallthrough
      (by simp [hResult])
  · intro targetState hStateRel
    exact
      openStep_terminal_of_compileStmtFuel?
        hCompile hBlocks hFits hStateRel
  · exact hNonregularStops

end Stmt

end InteractionLeafPreservation
end Structured
end EvmCompiler
