import EvmCompiler.Structured.InteractionLeafPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionBranchPreservation

namespace Code

def JumpResultRel
    (label : Assembly.Label) (tokens : List Word)
    (output : TypedCfg.Shape)
    (source : RunState) (target : TypedCfg.Outcome) : Prop :=
  ∃ targetState,
    target = .jump label targetState ∧
      TypedCfgPreservation.StateRel source tokens targetState ∧
        TypedCfgCompiler.Shape.SourceFrameFits
          output source.evm.stack.length

abbrev JumpDoneRel
    (label : Assembly.Label) (tokens : List Word)
    (output : TypedCfg.Shape) :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError : EVMException => True)
    (JumpResultRel label tokens output)

/--
Straight-line open code followed by a compiler-selected unconditional jump
preserves the complete interaction tree and exposes the exact target label.
-/
theorem openRun_jump_toCfg
    {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {entry label : Assembly.Label}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hType :
      TypedCfgCompiler.Code.type? code input = some output)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel
      (JumpDoneRel label tokens output)
      (InteractionSemantics.Code.openRun code source)
      (TypedCfg.InteractionSemantics.Block.openRun
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump label }
        target) := by
  have hCode :=
    InteractionPreservation.Code.openRun_toCfg
      hType hFits hRel
  have hComposed :
      Simulation.Interaction.Rel
        (JumpDoneRel label tokens output)
        (Simulation.Interaction.bind
          (InteractionSemantics.Code.openRun code source)
          Simulation.Interaction.pure)
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Block.openRunBody
            (TypedCfgCompiler.Code.toCfg code) input target)
          (fun result =>
            if result.2 = output then
              Simulation.Interaction.pure
                (TypedCfg.Block.runTerm output
                  (.jump label) result.1)
            else
              Simulation.Interaction.error .InvalidInstruction)) := by
    apply Simulation.Interaction.Rel.bind hCode
    intro sourceFinal targetAfterCode hAfterCode
    rcases hAfterCode with
      ⟨hOutput, hStateRel, hFinalFits⟩
    rcases targetAfterCode with
      ⟨targetAfterCode, targetShape⟩
    change targetShape = output at hOutput
    subst targetShape
    simp only [Prod.snd, if_pos rfl, if_true]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      ⟨targetAfterCode, by simp [TypedCfg.Block.runTerm],
        hStateRel, hFinalFits⟩
  simpa [
    Simulation.Interaction.bind_pure,
    TypedCfg.InteractionSemantics.Block.openRun,
    TypedCfg.Control.Block.run, hType] using hComposed

end Code

namespace Condition

def ResultRel
    (trueLabel falseLabel : Assembly.Label)
    (tokens : List Word) (restShape : TypedCfg.Shape)
    (source : RunState × Bool) (target : TypedCfg.Outcome) : Prop :=
  ∃ targetState,
    target =
        .jump
          (if source.2 then trueLabel else falseLabel)
          targetState ∧
      TypedCfgPreservation.StateRel source.1 tokens targetState ∧
        TypedCfgCompiler.Shape.SourceFrameFits
          restShape source.1.evm.stack.length

abbrev DoneRel
    (trueLabel falseLabel : Assembly.Label)
    (tokens : List Word) (restShape : TypedCfg.Shape) :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError : EVMException => True)
    (ResultRel trueLabel falseLabel tokens restShape)

/--
Straight-line open condition evaluation, its source-visible stack pop, and the
generated TypedCfg `jumpi` expose the same branch for every external answer.
-/
theorem openRunCondition_jumpi_toCfg
    {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {entry trueLabel falseLabel : Assembly.Label}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hType :
      TypedCfgCompiler.Code.type? code input = some output)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 output = some ())
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel
      (DoneRel trueLabel falseLabel tokens
        { output with slots := output.slots.tail })
      (InteractionSemantics.Code.openRunCondition code source)
      (TypedCfg.InteractionSemantics.Block.openRun
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jumpi trueLabel falseLabel }
        target) := by
  have hCode :=
    InteractionPreservation.Code.openRun_toCfg
      hType hFits hRel
  have hComposed :
      Simulation.Interaction.Rel
        (DoneRel trueLabel falseLabel tokens
          { output with slots := output.slots.tail })
        (Simulation.Interaction.bind
          (InteractionSemantics.Code.openRun code source)
          InteractionSemantics.Code.openPopCondition)
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Block.openRunBody
            (TypedCfgCompiler.Code.toCfg code) input target)
          (fun result =>
            if result.2 = output then
              Simulation.Interaction.pure
                (TypedCfg.Block.runTerm output
                  (.jumpi trueLabel falseLabel) result.1)
            else
              Simulation.Interaction.error .InvalidInstruction)) := by
    apply Simulation.Interaction.Rel.bind hCode
    intro sourceAfterCode targetAfterCode hAfterCode
    rcases hAfterCode with
      ⟨hOutput, hStateRel, hAfterFits⟩
    rcases targetAfterCode with
      ⟨targetAfterCode, targetShape⟩
    change targetShape = output at hOutput
    subst targetShape
    simp only [Prod.snd, if_pos rfl, if_true]
    cases hStack : sourceAfterCode.evm.stack with
    | nil =>
        have hSourceCount :
            1 ≤ TypedCfgCompiler.Shape.sourceLength output :=
          TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
            hSource
        have hStackBound := hAfterFits.1
        simp [hStack] at hStackBound
        omega
    | cons value stack =>
        have hPop :
            sourceAfterCode.evm.stack.pop = some (stack, value) := by
          simp [hStack, EvmYul.Stack.pop]
        obtain ⟨realizedTail, _hTailRealize, hTargetStack⟩ :=
          TypedCfgPreservation.StateRel.stackView_of_pop
            hStateRel hPop
        have hTargetStack' :
            targetAfterCode.stack = value :: realizedTail := by
          simpa using hTargetStack
        obtain ⟨targetFinal, hTargetPop, hFinalRel⟩ :=
          TypedCfgPreservation.StateRel.popCondition
            hStateRel hPop
        have hTargetPopExpected :
            Structured.Code.popCondition targetAfterCode =
              .ok
                ({ targetAfterCode with stack := realizedTail },
                  value != EvmYul.UInt256.ofNat 0) := by
          simp [
            Structured.Code.popCondition,
            EffectSemantics.Code.popCondition,
            EffectSemantics.Control.Code.popCondition,
            hTargetStack', EvmYul.Stack.pop]
        rw [hTargetPopExpected] at hTargetPop
        cases hTargetPop
        have hSourceCount :
            1 ≤ TypedCfgCompiler.Shape.sourceLength output :=
          TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
            hSource
        have hFinalFits :
            TypedCfgCompiler.Shape.SourceFrameFits
              { output with slots := output.slots.tail }
              stack.length := by
          have hPopped :=
            TypedCfgCompilerFacts.Shape.sourceFrameFits_pop
              (shape := output) (stackLength := sourceAfterCode.evm.stack.length)
              (count := 1) hSourceCount hAfterFits
          simpa [TypedCfg.Shape.pop, hStack] using hPopped
        have hTargetRun :
            TypedCfg.Block.runTerm output
                (.jumpi trueLabel falseLabel) targetAfterCode =
              .jump
                (if value != EvmYul.UInt256.ofNat 0 then
                  trueLabel
                else
                  falseLabel)
                { targetAfterCode with stack := realizedTail } := by
          by_cases hZero : value = EvmYul.UInt256.ofNat 0
          · have hBne :
                (value != EvmYul.UInt256.ofNat 0) = false := by
              subst value
              exact TypedCfg.Preservation.uint256_bne_zero_self
            simp only [
              TypedCfg.Block.runTerm, hTargetStack',
              EvmYul.Stack.pop]
            rw [if_pos hZero, hBne]
            rfl
          · have hBne :
                (value != EvmYul.UInt256.ofNat 0) = true :=
              TypedCfg.Preservation.uint256_bne_zero_of_ne value hZero
            simp only [
              TypedCfg.Block.runTerm, hTargetStack',
              EvmYul.Stack.pop]
            rw [if_neg hZero, hBne]
            rfl
        have hSourcePop :
            InteractionSemantics.Code.openPopCondition sourceAfterCode =
              Simulation.Interaction.pure
                (sourceAfterCode.withEVM
                  { sourceAfterCode.evm with stack := stack },
                  value != EvmYul.UInt256.ofNat 0) := by
          simp [
            InteractionSemantics.Code.openPopCondition,
            EffectSemantics.Control.Code.popCondition,
            EffectSemantics.Ordinary.runStateModel_evm,
            EffectSemantics.Ordinary.runStateModel_withEVM,
            hPop]
          rfl
        rw [hTargetRun]
        rw [hSourcePop]
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        exact
          ⟨{ targetAfterCode with stack := realizedTail },
            rfl, hFinalRel,
            by simpa [RunState.withEVM, hStack] using hFinalFits⟩
  simpa [
    InteractionSemantics.Code.openRunCondition,
    EffectSemantics.Control.Code.runCondition,
    TypedCfg.InteractionSemantics.Block.openRun,
    TypedCfg.Control.Block.run, hType] using hComposed

/--
The compiler-owned `if` head exposes the generic open condition branch at its
actual program entry.
-/
theorem openStep_if_of_compileStmtFuel?
    {compilerFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target) :
    ∃ (output bodyInput : TypedCfg.Shape)
        (bodyResult : TypedCfgCompiler.Result),
      bodyInput =
        { output with slots := output.slots.tail } ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
          (supply + 1) (LabelSupply.label supply 0)
          bodyInput regular =
        some bodyResult ∧
      bodyResult.requireFallthrough?
          bodyInput =
        some () ∧
      result.fallthrough? =
        some bodyInput ∧
      Simulation.Interaction.Rel
        (DoneRel (LabelSupply.label supply 0) regular tokens
          bodyInput)
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg entry target) := by
  obtain
      ⟨output, _condition, bodyResult,
        hType, hSource, _hHead, hBody, hRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if
      hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg cond
      output := output
      term := .jumpi (LabelSupply.label supply 0) regular }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated, hResult])
  let bodyInput : TypedCfg.Shape :=
    { output with slots := output.slots.tail }
  refine
    ⟨output, bodyInput, bodyResult, rfl,
      by simpa [bodyInput] using hBody,
      by simpa [bodyInput] using hRequire,
      by simp [bodyInput, hResult], ?_⟩
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind]
  simpa [generated, bodyInput] using
    (openRunCondition_jumpi_toCfg
      (entry := entry)
      (trueLabel := LabelSupply.label supply 0)
      (falseLabel := regular)
      hType hSource hFits hRel)

end Condition

namespace Stmt

/--
A compiled conditional preserves the open interaction tree under any active
stop policy that accepts related final outcomes and rejects the generated body
entry. The recursively compiled body keeps its own result relation while using
the exact same policy.
-/
theorem openRun_if_under_of_compileStmtFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hBodyEntryNoStop :
      ∀ targetState,
        policy (LabelSupply.label supply 0) targetState = false)
    (hBody :
      ∀ {output : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : RunState},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            { output with slots := output.slots.tail } regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        afterCond.returns = source.returns →
        bodyResult.requireFallthrough?
            { output with slots := output.slots.tail } =
          some () →
        result.fallthrough? =
          some { output with slots := output.slots.tail } →
        InteractionControlPreservation.OpenOutcome.PreservesUnder
          bodyResult cfg (LabelSupply.label supply 0) ctx
          regular regularExit afterCond tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterCond)
          bodyTargetFuel policy) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      result cfg entry ctx regular regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.if_ cond body) source)
      (1 + bodyTargetFuel) policy := by
  intro target hStateRel
  obtain
      ⟨output, _condition, bodyResult,
        hType, hSource, _hHead, hBodyCompile,
        hBodyRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if
      hCompile
  let bodyInput : TypedCfg.Shape :=
    { output with slots := output.slots.tail }
  have hFallthrough :
      result.fallthrough? = some bodyInput := by
    simp [bodyInput, hResult]
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hResult, hMem]
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg cond
      output := output
      term := .jumpi (LabelSupply.label supply 0) regular }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated, hResult])
  have hHeadRel :
      Simulation.Interaction.Rel
        (Condition.DoneRel
          (LabelSupply.label supply 0) regular tokens bodyInput)
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg entry target) := by
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa [generated, bodyInput] using
      (Condition.openRunCondition_jumpi_toCfg
        (entry := entry)
        (trueLabel := LabelSupply.label supply 0)
        (falseLabel := regular)
        hType hSource hFits hStateRel)
  have hHeadWithReturns :=
    Simulation.Interaction.Rel.strengthen_left hHeadRel
      (InteractionSemantics.Code.openRunCondition_returns cond source)
  rw [show 1 + bodyTargetFuel = bodyTargetFuel + 1 by omega,
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  apply Simulation.Interaction.Rel.bind_custom hHeadWithReturns
  intro sourceDone targetDone hDone
  cases sourceDone with
  | error sourceError =>
      cases targetDone with
      | error targetError =>
          exact
            Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error trivial)
      | ok targetOutcome =>
          rcases hDone with ⟨hCondition, _hReturns⟩
          cases hCondition
  | ok conditionResult =>
      cases targetDone with
      | error targetError =>
          rcases hDone with ⟨hCondition, _hReturns⟩
          cases hCondition
      | ok targetOutcome =>
          rcases conditionResult with ⟨afterCond, condTrue⟩
          rcases hDone with
            ⟨hCondition, hReturns⟩
          cases hCondition with
          | ok hCondition =>
          rcases hCondition with
            ⟨targetAfterCond, hTargetOutcome,
              hAfterCondRel, hAfterCondFits⟩
          cases condTrue with
          | false =>
              simp only [if_false] at hTargetOutcome
              subst targetOutcome
              have hReturnsEq :
                  afterCond.returns = source.returns := by
                simpa [
                  InteractionSemantics.Code.ConditionReturnsEq]
                  using hReturns
              have hWholeRel :
                  InteractionControlPreservation.OpenOutcome.Rel
                    result ctx regular source.returns tokens
                    (Structured.Outcome.regular afterCond)
                    (.jump regular targetAfterCond) := by
                refine ⟨?_, ?_, ?_⟩
                · exact
                    TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                      ⟨rfl, hAfterCondRel⟩
                · exact
                    ⟨bodyInput,
                      hFallthrough, hAfterCondFits⟩
                · simpa [
                    InteractionControlPreservation.OpenOutcome.ActivationRestored]
                    using hReturnsEq
              exact
                InteractionControlPreservation.OpenOutcome.afterOpenStepResultWithPolicy_of_targetStopped
                  (cfg := cfg)
                  (regularExit := regularExit)
                  (fuel := bodyTargetFuel)
                  hWholeRel (hStops hWholeRel)
          | true =>
              simp only [if_true] at hTargetOutcome
              subst targetOutcome
              have hReturnsEq :
                  afterCond.returns = source.returns := by
                simpa [
                  InteractionSemantics.Code.ConditionReturnsEq]
                  using hReturns
              have hBodyPreserves :=
                hBody
                  (output := output)
                  (bodyResult := bodyResult)
                  (afterCond := afterCond)
                  hBodyCompile hBodyBlocks hReturnsEq
                  hBodyRequire hFallthrough
              have hBodyLifted :=
                InteractionControlPreservation.OpenOutcome.PreservesUnder.change_result_of_required_fallthrough
                  hBodyRequire hFallthrough hBodyPreserves
              have hBodyRel :=
                hBodyLifted targetAfterCond hAfterCondRel
              have hNoStop :=
                hBodyEntryNoStop targetAfterCond
              simp only [
                TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                hNoStop, if_false]
              simpa [hReturnsEq] using hBodyRel

/--
A compiled conditional preserves the open interaction tree until its own
regular boundary. The false branch stops after the generated head and remains
inert under the body budget; the true branch delegates only to the recursively
compiled body theorem.
-/
theorem openRun_if_within_stop_of_compileStmtFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (hBody :
      ∀ {output : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : RunState},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            { output with slots := output.slots.tail } regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        afterCond.returns = source.returns →
        InteractionControlPreservation.OpenOutcome.PreservesWithin
          bodyResult result cfg (LabelSupply.label supply 0) ctx
          regular regular .stop afterCond tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterCond)
          bodyTargetFuel) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result result cfg entry ctx regular regular .stop source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.if_ cond body) source)
      (1 + bodyTargetFuel) := by
  intro target hStateRel
  obtain
      ⟨output, _condition, bodyResult,
        hType, hSource, _hHead, hBodyCompile,
        hBodyRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if
      hCompile
  let bodyInput : TypedCfg.Shape :=
    { output with slots := output.slots.tail }
  have hFallthrough :
      result.fallthrough? = some bodyInput := by
    simp [bodyInput, hResult]
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hResult, hMem]
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg cond
      output := output
      term := .jumpi (LabelSupply.label supply 0) regular }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated, hResult])
  have hHeadRel :
      Simulation.Interaction.Rel
        (Condition.DoneRel
          (LabelSupply.label supply 0) regular tokens bodyInput)
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg entry target) := by
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa [generated, bodyInput] using
      (Condition.openRunCondition_jumpi_toCfg
        (entry := entry)
        (trueLabel := LabelSupply.label supply 0)
        (falseLabel := regular)
        hType hSource hFits hStateRel)
  have hHeadWithReturns :=
    Simulation.Interaction.Rel.strengthen_left hHeadRel
      (InteractionSemantics.Code.openRunCondition_returns cond source)
  rw [show 1 + bodyTargetFuel = bodyTargetFuel + 1 by omega,
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  apply Simulation.Interaction.Rel.bind_custom hHeadWithReturns
  intro sourceDone targetDone hDone
  cases sourceDone with
  | error sourceError =>
      cases targetDone with
      | error targetError =>
          exact
            Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error trivial)
      | ok targetOutcome =>
          rcases hDone with ⟨hCondition, _hReturns⟩
          cases hCondition
  | ok conditionResult =>
      cases targetDone with
      | error targetError =>
          rcases hDone with ⟨hCondition, _hReturns⟩
          cases hCondition
      | ok targetOutcome =>
          rcases conditionResult with ⟨afterCond, condTrue⟩
          rcases hDone with
            ⟨hCondition, hReturns⟩
          cases hCondition with
          | ok hCondition =>
          rcases hCondition with
            ⟨targetAfterCond, hTargetOutcome,
              hAfterCondRel, hAfterCondFits⟩
          cases condTrue with
          | false =>
              simp only [if_false] at hTargetOutcome
              subst targetOutcome
              have hReturnsEq :
                  afterCond.returns = source.returns := by
                simpa [
                  InteractionSemantics.Code.ConditionReturnsEq]
                  using hReturns
              have hFrame :=
                TypedCfgPreservation.ActivationFrameMatches.check_of_stateRel
                  hAfterCondRel hAfterCondFits
              have hStop :
                  InteractionControlPreservation.OpenOutcome.stopJump
                      result ctx regular source.returns tokens
                      regular targetAfterCond =
                    true := by
                apply
                  InteractionControlPreservation.OpenOutcome.stopJump_regular
                    ctx regular source.returns tokens
                    bodyInput
                    targetAfterCond
                · exact hFallthrough
                · simpa [hReturnsEq] using hFrame
              have hWholeRel :
                  InteractionControlPreservation.OpenOutcome.Rel
                    result ctx regular source.returns tokens
                    (Structured.Outcome.regular afterCond)
                    (.jump regular targetAfterCond) := by
                refine ⟨?_, ?_, ?_⟩
                · exact
                    TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                      ⟨rfl, hAfterCondRel⟩
                · exact
                    ⟨bodyInput,
                      hFallthrough, hAfterCondFits⟩
                · simpa [
                    InteractionControlPreservation.OpenOutcome.ActivationRestored]
                    using hReturnsEq
              have hWholeRun :
                  InteractionControlPreservation.OpenOutcome.SegmentRunRel
                    result ctx regular source.returns tokens .stop
                    (Structured.Outcome.regular afterCond)
                    (.stopped bodyTargetFuel
                      (.jump regular targetAfterCond)) := by
                simpa [
                  InteractionControlPreservation.OpenOutcome.SegmentRunRel]
                  using hWholeRel
              simp only [
                TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                InteractionControlPreservation.OpenOutcome.segmentStopJump,
                hStop, Bool.false_eq_true, if_false]
              exact
                Simulation.Interaction.Rel.done
                  (Simulation.Interaction.ExceptRel.ok hWholeRun)
          | true =>
              simp only [if_true] at hTargetOutcome
              subst targetOutcome
              have hReturnsEq :
                  afterCond.returns = source.returns := by
                simpa [
                  InteractionSemantics.Code.ConditionReturnsEq]
                  using hReturns
              have hNoStop :
                  InteractionControlPreservation.OpenOutcome.stopJump
                      result ctx regular source.returns tokens
                      (LabelSupply.label supply 0) targetAfterCond =
                    false := by
                exact
                  InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false
                    hBefore (Nat.le_refl supply)
                    source.returns tokens targetAfterCond
              have hBodyPreserves :=
                hBody
                  (output := output)
                  (bodyResult := bodyResult)
                  (afterCond := afterCond)
                  hBodyCompile hBodyBlocks hReturnsEq
              have hBodyRelBase :=
                hBodyPreserves targetAfterCond hAfterCondRel
              have hBodyRel :
                  Simulation.Interaction.Rel
                    (InteractionControlPreservation.OpenOutcome.SegmentDoneRel
                      bodyResult ctx regular source.returns tokens .stop)
                    (InteractionSemantics.Block.openRun
                      sourceProgram sourceFuel body afterCond)
                    (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                      (InteractionControlPreservation.OpenOutcome.stopJump
                        result ctx regular source.returns tokens)
                      cfg bodyTargetFuel
                      (LabelSupply.label supply 0) targetAfterCond) := by
                simpa [hReturnsEq] using hBodyRelBase
              simp only [
                TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                InteractionControlPreservation.OpenOutcome.segmentStopJump,
                hNoStop, Bool.true_eq, if_true, if_false]
              have hLifted :
                  Simulation.Interaction.Rel
                    (InteractionControlPreservation.OpenOutcome.SegmentDoneRel
                      result ctx regular source.returns tokens .stop)
                    (InteractionSemantics.Block.openRun
                      sourceProgram sourceFuel body afterCond)
                    (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                      (InteractionControlPreservation.OpenOutcome.stopJump
                        result ctx regular source.returns tokens)
                      cfg bodyTargetFuel
                      (LabelSupply.label supply 0) targetAfterCond) := by
                apply Simulation.Interaction.Rel.mono hBodyRel
                intro sourceFinal targetFinal hFinal
                cases sourceFinal with
                | error sourceError =>
                    cases targetFinal with
                    | error targetError =>
                        exact
                          Simulation.Interaction.ExceptRel.error trivial
                    | ok targetRun =>
                        cases hFinal
                | ok sourceOutcome =>
                    cases targetFinal with
                    | error targetError =>
                        cases hFinal
                    | ok targetRun =>
                        cases hFinal with
                        | ok hRun =>
                            cases targetRun with
                            | exhausted label targetState =>
                                exact False.elim hRun
                            | stopped _remaining targetOutcome =>
                                exact
                                  Simulation.Interaction.ExceptRel.ok
                                    (InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                                      (left := bodyResult)
                                      (right := result)
                                      hBodyRequire hFallthrough
                                      hRun)
              exact hLifted

end Stmt

end InteractionBranchPreservation
end Structured
end EvmCompiler
