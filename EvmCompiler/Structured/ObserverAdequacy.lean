import EvmCompiler.Structured.ObserverPreservation

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy

/-!
Backward adequacy for the adjacent Structured-to-TypedCfg pass.

This module consumes only the existing Structured compiler, its TypedCfg
typing facts, the shared observer semantics, and the pass-owned state relation.
It does not reason about Assembly or bytecode execution.
-/

abbrev Trace := Assembly.ResourceTrace

namespace Code

/--
Backward straight-line adequacy at a source boundary with no active ghost
return frames. This is the top-level case used by the first closed-program
theorem; recursive procedure frames require the stronger shape-indexed
induction still under construction.
-/
theorem run_of_runBody_toCfg_noFrames
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel
        source [] target trace)
    (hRun :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetFinal, output), traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.run code source = .ok final ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  rcases hRel.1 with ⟨realized, hRealize, hSame⟩
  simp [hReturns, TypedCfgPreservation.realizeStack] at hRealize
  subst realized
  let targetState : ObserverSemantics.State transcript :=
    source.withSource (source.source.withEVM target)
  have hReplay :
      ObserverPreservation.ReplayStateRel targetState source := by
    exact
      ⟨rfl, by simp [targetState], by simpa [targetState] using hSame⟩
  have hTargetBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input
          targetState.source.evm targetState.remaining =
        .ok ((targetFinal, output), traceFinal) := by
    simpa [targetState, hRel.2] using hRun
  obtain
      ⟨targetFinalState, hTargetCode, hTargetEVM, hTargetTrace⟩ :=
    ObserverPreservation.Code.run_of_runBody_toCfg
      hType hTargetBody
  obtain ⟨final, hSourceCode, hFinalReplay⟩ :=
    ObserverPreservation.Code.run_of_rel hReplay hTargetCode
  have hFinalReturns : final.source.returns = [] := by
    rw [ObserverSemantics.Code.run_returns_eq hSourceCode, hReturns]
  refine ⟨final, hSourceCode, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨final.source.evm.stack, ?_, ?_⟩
    · simp [hFinalReturns, TypedCfgPreservation.realizeStack]
    · rw [← hTargetEVM]
      simpa using hFinalReplay.source.2
  · rw [← hTargetTrace]
    exact
      (ObserverPreservation.ReplayStateRel.remaining_eq
        hFinalReplay).symm

/--
Backward adequacy for a compiled condition at a no-frame boundary.
-/
theorem runCondition_of_runBody_toCfg_noFrames
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {target targetAfter targetFinal : EVMState}
    {trace traceFinal : Trace} {cond : Bool}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel
        source [] target trace)
    (hBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetAfter, output), traceFinal))
    (hPop :
      Structured.Code.popCondition targetAfter =
        .ok (targetFinal, cond)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.runCondition code source =
          .ok (final, cond) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  obtain ⟨after, hSourceCode, hAfterRel⟩ :=
    run_of_runBody_toCfg_noFrames
      hType hReturns hRel hBody
  have hAfterReturns : after.source.returns = [] := by
    rw [ObserverSemantics.Code.run_returns_eq hSourceCode, hReturns]
  rcases hAfterRel.1 with ⟨realized, hRealize, hSame⟩
  simp [hAfterReturns, TypedCfgPreservation.realizeStack] at hRealize
  subst realized
  have hStack :
      targetAfter.stack = after.source.evm.stack :=
    Assembly.SameRuntimeData.stack_eq hSame
  unfold Structured.Code.popCondition
    EffectSemantics.Code.popCondition at hPop
  cases hTargetStack : targetAfter.stack with
  | nil =>
      simp [hTargetStack, EvmYul.Stack.pop] at hPop
  | cons value stack =>
      simp [hTargetStack, EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      have hSourceStack :
          after.source.evm.stack = value :: stack := by
        rw [← hStack, hTargetStack]
      let final : ObserverSemantics.State transcript :=
        after.withSource
          (after.source.withEVM
            { after.source.evm with stack := stack })
      refine ⟨final, ?_, ?_⟩
      · unfold ObserverSemantics.Code.runCondition
          EffectSemantics.Code.runCondition
        have hEffectRun :
            EffectSemantics.Code.run
                (ObserverSemantics.stateModel transcript)
                (ObserverSemantics.handler transcript)
                code source =
              .ok after :=
          hSourceCode
        rw [hEffectRun]
        simp only [Bind.bind, Except.bind]
        unfold EffectSemantics.Code.popCondition
        simp only [ObserverSemantics.stateModel_evm,
          ObserverSemantics.stateModel_withEVM]
        rw [hSourceStack]
        rfl
      · refine ⟨?_, ?_⟩
        · refine ⟨stack, ?_, ?_⟩
          · simp [final, hAfterReturns,
              TypedCfgPreservation.realizeStack]
          · simpa [final] using
              Assembly.SameRuntimeData.replaceStack hSame
                (targetStack := stack)
                (sourceStack := stack) rfl
        · simpa [final] using hAfterRel.2

end Code

namespace Stmt

/--
Compiler-facing backward adequacy for a straight-line statement at a boundary
with no active procedure frames.
-/
theorem outcome_code_of_compileStmtFuel?_and_step_noFrames
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel.At
        input source [] target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program fuel
          (.code code) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated :=
        hBlocks generated (by simp [generated])
      unfold TypedCfg.ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      change
        TypedCfg.ObserverSemantics.Block.run generated target trace =
          .ok (.jump regular targetFinal, traceFinal) at hStep
      unfold TypedCfg.ObserverSemantics.Block.run at hStep
      dsimp [generated] at hStep
      cases hBody :
          TypedCfg.ObserverSemantics.Block.runBody
            (TypedCfgCompiler.Code.toCfg code) input target trace with
      | error err =>
          rw [hBody] at hStep
          simp [generated, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with ⟨⟨bodyFinal, bodyOutput⟩, bodyTrace⟩
          rw [hBody] at hStep
          simp only [Bind.bind, Except.bind] at hStep
          by_cases hOutput : bodyOutput = output
          · simp [generated, hOutput] at hStep
            rcases hStep with ⟨hFinal, hTrace⟩
            subst bodyOutput
            simp [TypedCfg.Block.runTerm] at hFinal
            subst targetFinal
            subst traceFinal
            obtain ⟨final, hSourceRun, hFinalRel⟩ :=
              Code.run_of_runBody_toCfg_noFrames
                (by simpa [TypedCfgCompiler.Code.type?] using hType)
                hReturns hRel.rel hBody
            exact
              ⟨final,
                Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
                hFinalRel⟩
          · simp [generated, hOutput] at hStep

/--
Backward adequacy for the false branch of a compiled conditional at a no-frame
boundary. Label distinctness is the local compiler-freshness fact; whole-program
generation will discharge it internally.
-/
theorem outcome_if_false_of_compileStmtFuel?_and_step_noFrames
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel.At
        input source [] target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program (fuel + 1)
          (.if_ cond body) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok (.jump regular targetFinal, traceFinal) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    unfold TypedCfg.Block.runTerm at hTerm
                    cases hStack : targetAfter.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hTerm
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          subst targetFinal
                          subst traceFinal
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                false := by
                            rw [hZero]
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_self
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    false) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg_noFrames
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hReturns hRel.rel hCondBody hPop
                          exact
                            ⟨final,
                              Structured.EffectSemantics.Stmt.Eval.if_false
                                hCond,
                              hFinalRel⟩
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          exact False.elim (hDistinct hTerm.1)
                  · simp [hOutput] at hStep

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
  have hArityShape :
      kind.argCount ≤ block.output.length :=
    TypedCfg.Block.halt_argCount_le_of_wellTyped hTyped hTerm
  have hAritySource :
      kind.argCount ≤ source.source.evm.stack.length :=
    Nat.le_trans hArityShape hRel.sourceStack
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
    terminal_of_wellTyped_halt hTyped hTerm hRel
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
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
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
      (fuel := fuel) hTyped (by rfl) hRel
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

end Stmt

end ObserverAdequacy
end Structured
end EvmCompiler
