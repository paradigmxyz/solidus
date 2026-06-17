import EvmCompiler.Structured.InteractionBranchPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionSwitchPreservation

namespace Switch

abbrev testOutput :=
  TypedCfgCompilerFacts.Switch.testOutput

abbrev nextTestLabel :=
  TypedCfgCompilerFacts.Switch.nextTestLabel

/--
One compiler-generated switch entry removes the retained scrutinee and jumps
to the selected body or regular continuation without exposing an open effect.
-/
theorem openStep_pop_jump
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {entry label : Assembly.Label}
    {input output : TypedCfg.Shape}
    {source : RunState} {tokens : List Word} {target : EVMState}
    {stack : EvmYul.Stack Word} {value : Word}
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump label } ∈ result.blocks)
    (hType :
      TypedCfg.Instr.type? .pop input = some output)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target)
    (hPop :
      source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      TypedCfg.InteractionSemantics.Program.openStep
          cfg entry target =
        .done (.ok (.jump label targetFinal)) ∧
      TypedCfgPreservation.StateRel
        (source.withEVM { source.evm with stack := stack })
        tokens targetFinal := by
  rcases
      TypedCfgPreservation.StateRel.pop
        (shape := input) hRel hPop with
    ⟨targetFinal, hRunPop, hFinalRel⟩
  have hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := [.pop]
            output := output
            term := .jump label } :=
    hBlocks _ hMem
  have hOpenPop :
      TypedCfg.InteractionSemantics.Instr.openRunAt
          .pop input target =
        .done (.ok (targetFinal, output)) := by
    unfold
      TypedCfg.InteractionSemantics.Instr.openRunAt
      TypedCfg.Control.Instr.runAt
    rw [hType]
    simp only [
      TypedCfg.InteractionSemantics.Instr.openRunState,
      hRunPop]
    rfl
  have hOpenPop' :
      TypedCfg.Control.Instr.runAt
          TypedCfg.InteractionSemantics.Instr.openRunState
          .pop input target =
        .done (.ok (targetFinal, output)) :=
    hOpenPop
  refine ⟨targetFinal, ?_, hFinalRel⟩
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind,
    TypedCfg.InteractionSemantics.Block.openRun,
    TypedCfg.Control.Block.run,
    TypedCfg.Control.Block.runBody]
  rw [hOpenPop']
  simp [
    Simulation.Interaction.instMonad,
    Simulation.Interaction.bind,
    Simulation.Interaction.pure,
    TypedCfg.Block.runTerm]

/--
One generated switch test retains the source scrutinee and selects the same
case-entry or next-test label as the source comparison.
-/
theorem openStep_test
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {testLabel caseLabel nextTest : Assembly.Label}
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue value : Word}
    {source : RunState} {tokens : List Word} {target : EVMState}
    {stack : EvmYul.Stack Word}
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := testLabel
        input := valueShape
        body := [.dup 0, .push caseValue, .prim .eq]
        output := testOutput valueShape
        term := .jumpi caseLabel nextTest } ∈ result.blocks)
    (hHead :
      valueShape.slots.head? = some slot)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target)
    (hPop :
      source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      TypedCfg.InteractionSemantics.Program.openStep
          cfg testLabel target =
        .done
          (.ok
            (.jump
              (if caseValue = value then caseLabel else nextTest)
              targetFinal)) ∧
      TypedCfgPreservation.StateRel source tokens targetFinal := by
  let dupShape : TypedCfg.Shape :=
    { valueShape with slots := slot :: valueShape.slots }
  let pushShape : TypedCfg.Shape :=
    { dupShape with slots := .literal caseValue :: dupShape.slots }
  have hGet :
      valueShape.get? 0 = some slot := by
    rw [TypedCfg.Shape.get?, ← List.head?_eq_getElem?]
    exact hHead
  have hDupType :
      TypedCfg.Instr.type? (.dup 0) valueShape = some dupShape := by
    simp [TypedCfg.Instr.type?, hGet, dupShape]
  have hPushType :
      TypedCfg.Instr.type? (.push caseValue) dupShape =
        some pushShape := by
    rfl
  have hEqType :
      TypedCfg.Instr.type? (.prim .eq) pushShape =
        some (testOutput valueShape) := by
    have hTestType :=
      TypedCfgCompilerFacts.Switch.testBody_type
        (caseValue := caseValue) hHead
    simp [TypedCfg.Block.bodyType?, hDupType, hPushType] at hTestType
    exact hTestType
  rcases
      TypedCfgPreservation.StateRel.stackView_of_pop
        hRel hPop with
    ⟨realizedTail, _hTailRealize, hTargetStack⟩
  let afterDup :=
    target.replaceStackAndIncrPC
      (value :: value :: realizedTail)
  let afterPush :=
    afterDup.replaceStackAndIncrPC
      (caseValue :: value :: value :: realizedTail) (pcΔ := 33)
  let afterEq :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq caseValue value :: value :: realizedTail)
  let targetFinal : EVMState :=
    { afterEq with stack := value :: realizedTail }
  have hFinalSame :
      Assembly.SameRuntimeData targetFinal target := by
    cases target
    simp [targetFinal, afterEq, afterPush, afterDup,
      Assembly.SameRuntimeData, Assembly.eraseRuntimeControl,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hTargetStack ⊢
    exact hTargetStack.symm
  have hDupRun :
      TypedCfg.Instr.runAt (.dup 0) valueShape target =
        .ok (afterDup, dupShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hDupType]
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.dup, hTargetStack, afterDup,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hPushRun :
      TypedCfg.Instr.runAt (.push caseValue) dupShape afterDup =
        .ok (afterPush, pushShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hPushType]
    simp [TypedCfg.Instr.runState, afterPush, afterDup, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hEqRun :
      TypedCfg.Instr.runAt (.prim .eq) pushShape afterPush =
        .ok (afterEq, testOutput valueShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hEqType]
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push,
      afterPush, afterDup, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
    rfl
  have hDupRunState :
      TypedCfg.Instr.runState (.dup 0) valueShape target =
        .ok afterDup := by
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.dup, hTargetStack, afterDup,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hPushRunState :
      TypedCfg.Instr.runState (.push caseValue) dupShape afterDup =
        .ok afterPush := by
    simp [TypedCfg.Instr.runState, afterPush, afterDup, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hEqRunState :
      TypedCfg.Instr.runState (.prim .eq) pushShape afterPush =
        .ok afterEq := by
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push,
      afterPush, afterDup, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
    rfl
  have hEqStep :
      Assembly.PrimOp.step .eq afterPush = .ok afterEq := by
    simpa [TypedCfg.Instr.runState] using hEqRunState
  have hDupOpen :
      TypedCfg.Control.Instr.runAt
          TypedCfg.InteractionSemantics.Instr.openRunState
          (.dup 0) valueShape target =
        .done (.ok (afterDup, dupShape)) := by
    unfold TypedCfg.Control.Instr.runAt
    rw [hDupType]
    simp only [
      TypedCfg.InteractionSemantics.Instr.openRunState,
      hDupRunState]
    rfl
  have hPushOpen :
      TypedCfg.Control.Instr.runAt
          TypedCfg.InteractionSemantics.Instr.openRunState
          (.push caseValue) dupShape afterDup =
        .done (.ok (afterPush, pushShape)) := by
    unfold TypedCfg.Control.Instr.runAt
    rw [hPushType]
    simp only [
      TypedCfg.InteractionSemantics.Instr.openRunState,
      hPushRunState]
    rfl
  have hEqOpen :
      TypedCfg.Control.Instr.runAt
          TypedCfg.InteractionSemantics.Instr.openRunState
          (.prim .eq) pushShape afterPush =
        .done (.ok (afterEq, testOutput valueShape)) := by
    unfold TypedCfg.Control.Instr.runAt
    rw [hEqType]
    simp only [
      TypedCfg.InteractionSemantics.Instr.openRunState]
    rw [
      Assembly.InteractionSemantics.PrimOp.openStep_closed
        (op := .eq) (by rfl) (by decide) (by decide),
      hEqStep]
    rfl
  have hOpenBody :
      TypedCfg.InteractionSemantics.Block.openRunBody
          [.dup 0, .push caseValue, .prim .eq]
          valueShape target =
        .done (.ok (afterEq, testOutput valueShape)) := by
    unfold TypedCfg.InteractionSemantics.Block.openRunBody
    unfold TypedCfg.Control.Block.runBody
    rw [hDupOpen]
    simp [Simulation.Interaction.instMonad,
      Simulation.Interaction.bind, Simulation.Interaction.pure]
    unfold TypedCfg.Control.Block.runBody
    rw [hPushOpen]
    simp [Simulation.Interaction.instMonad,
      Simulation.Interaction.bind, Simulation.Interaction.pure]
    unfold TypedCfg.Control.Block.runBody
    rw [hEqOpen]
    simp [Simulation.Interaction.instMonad,
      Simulation.Interaction.bind, Simulation.Interaction.pure]
    unfold TypedCfg.Control.Block.runBody
    rfl
  have hOpenBody' :
      TypedCfg.Control.Block.runBody
          TypedCfg.InteractionSemantics.Instr.openRunState
          [.dup 0, .push caseValue, .prim .eq]
          valueShape target =
        .done (.ok (afterEq, testOutput valueShape)) :=
    hOpenBody
  have hTargetRun :
      TypedCfg.Block.runTerm (testOutput valueShape)
          (.jumpi caseLabel nextTest) afterEq =
        .jump
          (if caseValue = value then caseLabel else nextTest)
          targetFinal := by
    have hOneNeZero :
        EvmYul.UInt256.ofNat 1 ≠ EvmYul.UInt256.ofNat 0 := by
      decide
    by_cases hEq : caseValue = value
    · simp [TypedCfg.Block.runTerm, EvmYul.Stack.pop,
        EvmYul.UInt256.eq, hEq, hOneNeZero,
        targetFinal, afterEq,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
    · simp [TypedCfg.Block.runTerm, EvmYul.Stack.pop,
        EvmYul.UInt256.eq, hEq,
        targetFinal, afterEq,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  have hFind :
      cfg.findBlock? testLabel =
        some
          { label := testLabel
            input := valueShape
            body := [.dup 0, .push caseValue, .prim .eq]
            output := testOutput valueShape
            term := .jumpi caseLabel nextTest } :=
    hBlocks _ hMem
  refine
    ⟨targetFinal, ?_,
      TypedCfgPreservation.StateRel.targetCongr hFinalSame hRel⟩
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind,
    TypedCfg.InteractionSemantics.Block.openRun,
    TypedCfg.Control.Block.run]
  rw [hOpenBody']
  simp [
    Simulation.Interaction.instMonad,
    Simulation.Interaction.bind,
    Simulation.Interaction.pure,
    hTargetRun]

/--
The empty default arm preserves under any active policy that accepts its
related regular outcome.
-/
theorem openRun_default_none_under_of_compileDefaultFuel?
    {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          none ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits bodyShape stack.length)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      result cfg entry ctx regular regularExit source tokens
      (Simulation.Interaction.pure
        (Structured.Outcome.regular
          (source.withEVM { source.evm with stack := stack })))
      1 policy := by
  have hResult :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_none
      hPopType hCompile
  subst result
  apply
    InteractionControlPreservation.OpenOutcome.PreservesUnder.of_openStep
  · intro target hStateRel
    rcases
        openStep_pop_jump
          (entry := entry) (label := regular)
          (input := valueShape) (output := bodyShape)
          hBlocks (by simp) hPopType hStateRel hPop with
      ⟨targetFinal, hTargetRun, hFinalRel⟩
    rw [hTargetRun]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    constructor
    · exact
        TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
          ⟨rfl, hFinalRel⟩
    · constructor
      · exact ⟨bodyShape, rfl, hFits⟩
      · rfl
  · exact hStops

/--
The empty default arm removes the retained scrutinee and returns through the
switch's regular continuation.
-/
theorem openRun_default_none_of_compileDefaultFuel?
    {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular boundaryRegular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          none ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits bodyShape stack.length)
    (hRegularPolicy :
      ∀ {final : RunState} {targetState : EVMState},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            (Structured.Outcome.regular final)
            (.jump regular targetState) →
          InteractionControlPreservation.OpenOutcome.stopJump
              boundaryResult ctx boundaryRegular source.returns tokens
              regular targetState =
            match regularExit with
            | .stop => true
            | .resume => false) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result boundaryResult cfg entry ctx regular boundaryRegular
      regularExit source tokens
      (Simulation.Interaction.pure
      (Structured.Outcome.regular
          (source.withEVM { source.evm with stack := stack })))
      1 := by
  have hResult :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_none
      hPopType hCompile
  subst result
  apply
    InteractionControlPreservation.OpenOutcome.PreservesWithin.of_openStep
  · intro target hStateRel
    rcases
        openStep_pop_jump
          (entry := entry) (label := regular)
          (input := valueShape) (output := bodyShape)
          hBlocks (by simp) hPopType hStateRel hPop with
      ⟨targetFinal, hTargetRun, hFinalRel⟩
    rw [hTargetRun]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    constructor
    · exact
        TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
          ⟨rfl, hFinalRel⟩
    · constructor
      · exact ⟨bodyShape, rfl, hFits⟩
      · rfl
  · exact hRegularPolicy

/--
A present default arm removes the retained scrutinee, enters its generated
body, and then reuses that body's adjacent preservation theorem.
-/
theorem openRun_default_some_of_compileDefaultFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular boundaryRegular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply)
    (hBody :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000)
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        InteractionControlPreservation.OpenOutcome.PreservesWithin
          bodyResult boundaryResult cfg (.generated supply 2000) ctx
          regular boundaryRegular .stop
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
            (source.withEVM { source.evm with stack := stack }))
          bodyTargetFuel) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result boundaryResult cfg entry ctx regular boundaryRegular .stop
      source tokens
      (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
        (source.withEVM { source.evm with stack := stack }))
      (bodyTargetFuel + 1) := by
  obtain ⟨bodyResult, hBodyCompile, hRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
      hPopType hCompile
  subst result
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hBodyPreserves :=
    hBody hBodyCompile hBodyBlocks
  have hBodyLifted :
      InteractionControlPreservation.OpenOutcome.PreservesWithin
        { blocks :=
            { label := entry
              input := valueShape
              body := [.pop]
              output := bodyShape
              term := .jump (.generated supply 2000) } ::
              bodyResult.blocks
          next := bodyResult.next
          calls := bodyResult.calls
          fallthrough? := some bodyShape }
        boundaryResult cfg (.generated supply 2000) ctx
        regular boundaryRegular .stop
        (source.withEVM { source.evm with stack := stack }) tokens
        (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
          (source.withEVM { source.evm with stack := stack }))
        bodyTargetFuel := by
    apply
      InteractionControlPreservation.OpenOutcome.PreservesWithin.change_result_of_required_fallthrough
          hRequire rfl hBodyPreserves
  apply
    InteractionControlPreservation.OpenOutcome.PreservesWithin.prepend_closed_jump
  · intro target hStateRel
    exact
      openStep_pop_jump
        (entry := entry) (label := .generated supply 2000)
        (input := valueShape) (output := bodyShape)
        hBlocks (by simp) hPopType hStateRel hPop
  · rfl
  · intro targetAfter _hAfterRel
    exact
      InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false
          hBefore (Nat.le_refl supply)
          source.returns tokens targetAfter
  · exact hBodyLifted

/--
A present default arm preserves under the current active policy. Its generated
entry is private compiler control and is required not to stop that policy.
-/
theorem openRun_default_some_under_of_compileDefaultFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hEnclosingFallthrough :
      enclosingResult.fallthrough? = some bodyShape)
    (hBodyEntryNoStop :
      ∀ targetAfter,
        policy (.generated supply 2000) targetAfter = false)
    (hBody :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000)
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        bodyResult.requireFallthrough? bodyShape = some () →
        enclosingResult.fallthrough? = some bodyShape →
        InteractionControlPreservation.OpenOutcome.PreservesUnder
          bodyResult cfg (.generated supply 2000) ctx regular
          regularExit
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
            (source.withEVM { source.evm with stack := stack }))
          bodyTargetFuel policy) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      enclosingResult cfg entry ctx regular regularExit source tokens
      (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
        (source.withEVM { source.evm with stack := stack }))
      (bodyTargetFuel + 1) policy := by
  obtain ⟨bodyResult, hBodyCompile, hRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
      hPopType hCompile
  subst result
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hBodyPreserves :=
    hBody hBodyCompile hBodyBlocks hRequire hEnclosingFallthrough
  have hBodyLifted :
      InteractionControlPreservation.OpenOutcome.PreservesUnder
        enclosingResult cfg (.generated supply 2000) ctx regular
        regularExit
        (source.withEVM { source.evm with stack := stack }) tokens
        (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
          (source.withEVM { source.evm with stack := stack }))
        bodyTargetFuel policy := by
    exact
      InteractionControlPreservation.OpenOutcome.PreservesUnder.change_result_of_required_fallthrough
        hRequire hEnclosingFallthrough hBodyPreserves
  apply
    InteractionControlPreservation.OpenOutcome.PreservesUnder.prepend_closed_jump
  · intro target hStateRel
    exact
      openStep_pop_jump
        (entry := entry) (label := .generated supply 2000)
        (input := valueShape) (output := bodyShape)
        hBlocks (by simp) hPopType hStateRel hPop
  · rfl
  · intro targetAfter _hAfterRel
    exact hBodyEntryNoStop targetAfter
  · exact hBodyLifted

/--
Every generated case-chain entry is internal to the switch and therefore
cannot satisfy an enclosing continuation stop policy.
-/
theorem stopJump_casesEntryLabel_eq_false
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular : Assembly.Label}
    {base idx : Nat}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular base)
    (returns : List ReturnDest) (tokens : List Word)
    (state : EVMState)
    (cases : List (Word × Structured.Block)) :
    InteractionControlPreservation.OpenOutcome.stopJump
        result ctx boundaryRegular returns tokens
        (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases)
        state =
      false := by
  cases cases with
  | nil =>
      simpa [
        TypedCfgCompilerFacts.Switch.casesEntryLabel,
        LabelSupply.label] using
        (InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false
            hBefore (Nat.le_refl base) returns tokens state
            (tag := 1))
  | cons head rest =>
      simpa [
        TypedCfgCompilerFacts.Switch.casesEntryLabel,
        TypedCfgCompiler.switchTestLabel] using
        (InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false
            hBefore (Nat.le_refl base) returns tokens state
            (tag := 6 * idx + 1001))

theorem stopPolicy_casesEntryLabel_eq_false
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    {regular : Assembly.Label} {base idx : Nat}
    (hFresh :
      InteractionControlPreservation.OpenOutcome.StopPolicy.FreshExceptAt
        policy regular base)
    (hRegular :
      TypedCfgCompilerFacts.RegularAtSupply regular base)
    (state : EVMState)
    (cases : List (Word × Structured.Block)) :
    policy
        (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases)
        state =
      false := by
  cases cases with
  | nil =>
      simpa [
        TypedCfgCompilerFacts.Switch.casesEntryLabel,
        LabelSupply.label] using
        hFresh base 1 state (Nat.le_refl base)
          (hRegular.current_generated_ne (by omega))
  | cons head rest =>
      simpa [
        TypedCfgCompilerFacts.Switch.casesEntryLabel,
        TypedCfgCompiler.switchTestLabel] using
        hFresh base (6 * idx + 1001) state (Nat.le_refl base)
          (hRegular.current_generated_ne (by omega))

/--
Policy-generic selected-case routing. Generated test, case, and body labels are
private compiler control; the selected body keeps the active enclosing policy.
-/
theorem openRun_cases_some_under_of_compileCasesFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat}
    {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead :
      valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody =
        some selected)
    (hEnclosingFallthrough :
      enclosingResult.fallthrough? = some bodyShape)
    (hFresh :
      InteractionControlPreservation.OpenOutcome.StopPolicy.FreshExceptAt
        policy regular base)
    (hRegular :
      TypedCfgCompilerFacts.RegularAtSupply regular base)
    (hCase :
      ∀ {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (TypedCfgCompiler.switchBodyLabel base caseIdx)
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        bodyResult.requireFallthrough? bodyShape = some () →
        enclosingResult.fallthrough? = some bodyShape →
        InteractionControlPreservation.OpenOutcome.PreservesUnder
          bodyResult cfg
          (TypedCfgCompiler.switchBodyLabel base caseIdx) ctx
          regular regularExit
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          bodyTargetFuel policy)
    (hDefault :
      defaultBody = some selected →
        InteractionControlPreservation.OpenOutcome.PreservesUnder
          enclosingResult cfg (LabelSupply.label base 1) ctx
          regular regularExit source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          (bodyTargetFuel + 1) policy) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      enclosingResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular regularExit source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram sourceFuel selected
        (source.withEVM { source.evm with stack := stack }))
      (bodyTargetFuel + cases.length + 1) policy := by
  induction cases generalizing compilerFuel supply idx result selected with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefaultSelected : defaultBody = some selected := by
            simpa [Structured.Switch.select] using hSelect
          simpa [
            TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hDefault hDefaultSelected
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          obtain
              ⟨bodyResult, tail, hBodyCompile, hRequire,
                hTailCompile, hResult⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPopType hCompile
          have hBodyBlocks :
              TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          by_cases hEq : caseValue = value
          · have hSelected : body = selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            subst selected
            have hBodyPreserves :=
              hCase hBodyCompile hBodyBlocks
                hRequire hEnclosingFallthrough
            have hBodyLifted :
                InteractionControlPreservation.OpenOutcome.PreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchBodyLabel base idx) ctx
                  regular regularExit
                  (source.withEVM { source.evm with stack := stack }) tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  bodyTargetFuel policy := by
              exact
                InteractionControlPreservation.OpenOutcome.PreservesUnder.change_result_of_required_fallthrough
                  hRequire hEnclosingFallthrough hBodyPreserves
            have hBodyPadded :=
              InteractionControlPreservation.OpenOutcome.PreservesUnder.pad
                hBodyLifted rest.length
            have hFromCase :
                InteractionControlPreservation.OpenOutcome.PreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchCaseLabel base idx) ctx
                  regular regularExit source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyTargetFuel + rest.length) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.PreservesUnder.prepend_closed_jump
              · intro target hStateRel
                exact
                  openStep_pop_jump
                    (entry := TypedCfgCompiler.switchCaseLabel base idx)
                    (label := TypedCfgCompiler.switchBodyLabel base idx)
                    (input := valueShape) (output := bodyShape)
                    hBlocks (by simp [hResult]) hPopType hStateRel hPop
              · rfl
              · intro targetAfter _hAfterRel
                simpa [TypedCfgCompiler.switchBodyLabel] using
                  hFresh base (6 * idx + 1005) targetAfter
                    (Nat.le_refl base)
                    (hRegular.current_generated_ne (by omega))
              · exact hBodyPadded
            have hFromTest :
                InteractionControlPreservation.OpenOutcome.PreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx
                  regular regularExit source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  (((bodyTargetFuel + rest.length) + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.PreservesUnder.prepend_closed_jump
              · intro target hStateRel
                rcases
                    openStep_test
                      (testLabel :=
                        TypedCfgCompiler.switchTestLabel base idx)
                      (caseLabel :=
                        TypedCfgCompiler.switchCaseLabel base idx)
                      (nextTest :=
                        TypedCfgCompilerFacts.Switch.nextTestLabel
                          base idx rest)
                      (caseValue := caseValue) (value := value)
                      hBlocks (by simp [hResult]) hHead hStateRel hPop with
                  ⟨targetAfter, hTargetRun, hAfterRel⟩
                refine ⟨targetAfter, ?_, hAfterRel⟩
                simpa [hEq] using hTargetRun
              · rfl
              · intro targetAfter _hAfterRel
                simpa [TypedCfgCompiler.switchCaseLabel] using
                  hFresh base (6 * idx + 1003) targetAfter
                    (Nat.le_refl base)
                    (hRegular.current_generated_ne (by omega))
              · exact hFromCase
            simpa [
              TypedCfgCompilerFacts.Switch.casesEntryLabel] using
              hFromTest
          · have hTailSelect :
                Structured.Switch.select value rest defaultBody =
                  some selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            have hTailPreserves :=
              ih hTailCompile hTailBlocks hTailSelect hCase hDefault
            have hSkipped :
                InteractionControlPreservation.OpenOutcome.PreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx
                  regular regularExit source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel selected
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyTargetFuel + rest.length + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.PreservesUnder.prepend_closed_jump
              · intro target hStateRel
                rcases
                    openStep_test
                      (testLabel :=
                        TypedCfgCompiler.switchTestLabel base idx)
                      (caseLabel :=
                        TypedCfgCompiler.switchCaseLabel base idx)
                      (nextTest :=
                        TypedCfgCompilerFacts.Switch.nextTestLabel
                          base idx rest)
                      (caseValue := caseValue) (value := value)
                      hBlocks (by simp [hResult]) hHead hStateRel hPop with
                  ⟨targetAfter, hTargetRun, hAfterRel⟩
                refine ⟨targetAfter, ?_, hAfterRel⟩
                simpa [hEq] using hTargetRun
              · rfl
              · intro targetAfter _hAfterRel
                simpa [
                  TypedCfgCompilerFacts.Switch.nextTestLabel] using
                  stopPolicy_casesEntryLabel_eq_false
                    hFresh hRegular targetAfter rest (idx := idx + 1)
              · simpa [
                  TypedCfgCompilerFacts.Switch.nextTestLabel] using
                  hTailPreserves
            simpa [
              TypedCfgCompilerFacts.Switch.casesEntryLabel] using
              hSkipped

/--
Policy-generic no-case routing. Every test misses, and the unchanged active
policy is carried to the empty default arm.
-/
theorem openRun_cases_none_under_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat}
    {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {regularExit :
      InteractionControlPreservation.OpenOutcome.RegularExit}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead :
      valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody = none)
    (hFresh :
      InteractionControlPreservation.OpenOutcome.StopPolicy.FreshExceptAt
        policy regular base)
    (hRegular :
      TypedCfgCompilerFacts.RegularAtSupply regular base)
    (hDefault :
      defaultBody = none →
        InteractionControlPreservation.OpenOutcome.PreservesUnder
          enclosingResult cfg (LabelSupply.label base 1) ctx
          regular regularExit source tokens
          (Simulation.Interaction.pure
            (Structured.Outcome.regular
              (source.withEVM { source.evm with stack := stack })))
          1 policy) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      enclosingResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular regularExit source tokens
      (Simulation.Interaction.pure
        (Structured.Outcome.regular
          (source.withEVM { source.evm with stack := stack })))
      (cases.length + 1) policy := by
  induction cases generalizing compilerFuel supply idx result with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefaultNone : defaultBody = none := by
            simpa [Structured.Switch.select] using hSelect
          simpa [
            TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hDefault hDefaultNone
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          obtain
              ⟨bodyResult, tail, _hBodyCompile, _hRequire,
                hTailCompile, hResult⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPopType hCompile
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          have hNe : caseValue ≠ value := by
            intro hEq
            simp [Structured.Switch.select, hEq] at hSelect
          have hTailSelect :
              Structured.Switch.select value rest defaultBody = none := by
            simpa [Structured.Switch.select, hNe] using hSelect
          have hTailPreserves :=
            ih hTailCompile hTailBlocks hTailSelect
          have hSkipped :
              InteractionControlPreservation.OpenOutcome.PreservesUnder
                enclosingResult cfg
                (TypedCfgCompiler.switchTestLabel base idx) ctx
                regular regularExit source tokens
                (Simulation.Interaction.pure
                  (Structured.Outcome.regular
                    (source.withEVM { source.evm with stack := stack })))
                ((rest.length + 1) + 1) policy := by
            apply
              InteractionControlPreservation.OpenOutcome.PreservesUnder.prepend_closed_jump
            · intro target hStateRel
              rcases
                  openStep_test
                    (testLabel :=
                      TypedCfgCompiler.switchTestLabel base idx)
                    (caseLabel :=
                      TypedCfgCompiler.switchCaseLabel base idx)
                    (nextTest :=
                      TypedCfgCompilerFacts.Switch.nextTestLabel
                        base idx rest)
                    (caseValue := caseValue) (value := value)
                    hBlocks (by simp [hResult]) hHead hStateRel hPop with
                ⟨targetAfter, hTargetRun, hAfterRel⟩
              refine ⟨targetAfter, ?_, hAfterRel⟩
              simpa [hNe] using hTargetRun
            · rfl
            · intro targetAfter _hAfterRel
              simpa [
                TypedCfgCompilerFacts.Switch.nextTestLabel] using
                stopPolicy_casesEntryLabel_eq_false
                  hFresh hRegular targetAfter rest (idx := idx + 1)
            · simpa [
                TypedCfgCompilerFacts.Switch.nextTestLabel] using
                hTailPreserves
          simpa [
            TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hSkipped

/--
If source selection chooses a body, the generated case chain reaches exactly
that body and preserves its open interaction tree. The fixed fuel bound counts
one test per case plus the selected entry pop.
-/
theorem openRun_cases_some_of_compileCasesFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat}
    {regular boundaryRegular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead :
      valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody =
        some selected)
    (hEnclosingFallthrough :
      enclosingResult.fallthrough? = some bodyShape)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular base)
    (hCase :
      ∀ {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (TypedCfgCompiler.switchBodyLabel base caseIdx)
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        InteractionControlPreservation.OpenOutcome.PreservesWithin
          bodyResult boundaryResult cfg
          (TypedCfgCompiler.switchBodyLabel base caseIdx) ctx
          regular boundaryRegular .stop
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          bodyTargetFuel)
    (hDefault :
      defaultBody = some selected →
        InteractionControlPreservation.OpenOutcome.PreservesWithin
          enclosingResult boundaryResult cfg
          (LabelSupply.label base 1) ctx
          regular boundaryRegular .stop source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          (bodyTargetFuel + 1)) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      enclosingResult boundaryResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular boundaryRegular .stop source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram sourceFuel selected
        (source.withEVM { source.evm with stack := stack }))
      (bodyTargetFuel + cases.length + 1) := by
  induction cases generalizing compilerFuel supply idx result selected with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefaultSelected : defaultBody = some selected := by
            simpa [Structured.Switch.select] using hSelect
          simpa [
            TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hDefault hDefaultSelected
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          obtain
              ⟨bodyResult, tail, hBodyCompile, hRequire,
                hTailCompile, hResult⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
                hHead hPopType hCompile
          have hBodyBlocks :
              TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          by_cases hEq : caseValue = value
          · have hSelected : body = selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            subst selected
            have hBodyPreserves :=
              hCase hBodyCompile hBodyBlocks
            have hBodyLifted :
                InteractionControlPreservation.OpenOutcome.PreservesWithin
                  enclosingResult boundaryResult cfg
                  (TypedCfgCompiler.switchBodyLabel base idx) ctx
                  regular boundaryRegular .stop
                  (source.withEVM { source.evm with stack := stack }) tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  bodyTargetFuel := by
              exact
                InteractionControlPreservation.OpenOutcome.PreservesWithin.change_result_of_required_fallthrough
                    hRequire hEnclosingFallthrough hBodyPreserves
            have hBodyPadded :=
              InteractionControlPreservation.OpenOutcome.PreservesWithin.pad_stop
                hBodyLifted rest.length
            have hFromCase :
                InteractionControlPreservation.OpenOutcome.PreservesWithin
                  enclosingResult boundaryResult cfg
                  (TypedCfgCompiler.switchCaseLabel base idx) ctx
                  regular boundaryRegular .stop source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyTargetFuel + rest.length) + 1) := by
              apply
                InteractionControlPreservation.OpenOutcome.PreservesWithin.prepend_closed_jump
              · intro target hStateRel
                exact
                  openStep_pop_jump
                    (entry := TypedCfgCompiler.switchCaseLabel base idx)
                    (label := TypedCfgCompiler.switchBodyLabel base idx)
                    (input := valueShape) (output := bodyShape)
                    hBlocks (by simp [hResult]) hPopType hStateRel hPop
              · rfl
              · intro targetAfter _hAfterRel
                exact
                  InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false
                      hBefore (Nat.le_refl base)
                      source.returns tokens targetAfter
              · exact hBodyPadded
            have hFromTest :
                InteractionControlPreservation.OpenOutcome.PreservesWithin
                  enclosingResult boundaryResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx
                  regular boundaryRegular .stop source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  (((bodyTargetFuel + rest.length) + 1) + 1) := by
              apply
                InteractionControlPreservation.OpenOutcome.PreservesWithin.prepend_closed_jump
              · intro target hStateRel
                rcases
                    openStep_test
                      (testLabel :=
                        TypedCfgCompiler.switchTestLabel base idx)
                      (caseLabel :=
                        TypedCfgCompiler.switchCaseLabel base idx)
                      (nextTest :=
                        TypedCfgCompilerFacts.Switch.nextTestLabel
                          base idx rest)
                      (caseValue := caseValue) (value := value)
                      hBlocks (by simp [hResult]) hHead hStateRel hPop with
                  ⟨targetAfter, hTargetRun, hAfterRel⟩
                refine ⟨targetAfter, ?_, hAfterRel⟩
                simpa [hEq] using hTargetRun
              · rfl
              · intro targetAfter _hAfterRel
                exact
                  InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false
                      hBefore (Nat.le_refl base)
                      source.returns tokens targetAfter
              · exact hFromCase
            simpa [
              TypedCfgCompilerFacts.Switch.casesEntryLabel] using
              hFromTest
          · have hTailSelect :
                Structured.Switch.select value rest defaultBody =
                  some selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            have hTailPreserves :=
              ih hTailCompile hTailBlocks hTailSelect hCase hDefault
            have hSkipped :
                InteractionControlPreservation.OpenOutcome.PreservesWithin
                  enclosingResult boundaryResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx
                  regular boundaryRegular .stop source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel selected
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyTargetFuel + rest.length + 1) + 1) := by
              apply
                InteractionControlPreservation.OpenOutcome.PreservesWithin.prepend_closed_jump
              · intro target hStateRel
                rcases
                    openStep_test
                      (testLabel :=
                        TypedCfgCompiler.switchTestLabel base idx)
                      (caseLabel :=
                        TypedCfgCompiler.switchCaseLabel base idx)
                      (nextTest :=
                        TypedCfgCompilerFacts.Switch.nextTestLabel
                          base idx rest)
                      (caseValue := caseValue) (value := value)
                      hBlocks (by simp [hResult]) hHead hStateRel hPop with
                  ⟨targetAfter, hTargetRun, hAfterRel⟩
                refine ⟨targetAfter, ?_, hAfterRel⟩
                simpa [hEq] using hTargetRun
              · rfl
              · intro targetAfter _hAfterRel
                simpa [
                  TypedCfgCompilerFacts.Switch.nextTestLabel] using
                  stopJump_casesEntryLabel_eq_false
                    (result := boundaryResult)
                    hBefore source.returns tokens targetAfter rest
                    (idx := idx + 1)
              · simpa [
                  TypedCfgCompilerFacts.Switch.nextTestLabel] using
                  hTailPreserves
            simpa [
              TypedCfgCompilerFacts.Switch.casesEntryLabel] using
              hSkipped

/--
If source selection finds no body, every generated test misses and the case
chain reaches the empty default entry, which removes the retained scrutinee
and returns regularly.
-/
theorem openRun_cases_none_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat}
    {regular boundaryRegular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead :
      valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop :
      source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody = none)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular base)
    (hDefault :
      defaultBody = none →
        InteractionControlPreservation.OpenOutcome.PreservesWithin
          enclosingResult boundaryResult cfg
          (LabelSupply.label base 1) ctx
          regular boundaryRegular .stop source tokens
          (Simulation.Interaction.pure
            (Structured.Outcome.regular
              (source.withEVM { source.evm with stack := stack })))
          1) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      enclosingResult boundaryResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular boundaryRegular .stop source tokens
      (Simulation.Interaction.pure
        (Structured.Outcome.regular
          (source.withEVM { source.evm with stack := stack })))
      (cases.length + 1) := by
  induction cases generalizing compilerFuel supply idx result with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefaultNone : defaultBody = none := by
            simpa [Structured.Switch.select] using hSelect
          simpa [
            TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hDefault hDefaultNone
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          obtain
              ⟨bodyResult, tail, _hBodyCompile, _hRequire,
                hTailCompile, hResult⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPopType hCompile
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          have hNe : caseValue ≠ value := by
            intro hEq
            simp [Structured.Switch.select, hEq] at hSelect
          have hTailSelect :
              Structured.Switch.select value rest defaultBody = none := by
            simpa [Structured.Switch.select, hNe] using hSelect
          have hTailPreserves :=
            ih hTailCompile hTailBlocks hTailSelect
          have hSkipped :
              InteractionControlPreservation.OpenOutcome.PreservesWithin
                enclosingResult boundaryResult cfg
                (TypedCfgCompiler.switchTestLabel base idx) ctx
                regular boundaryRegular .stop source tokens
                (Simulation.Interaction.pure
                  (Structured.Outcome.regular
                    (source.withEVM { source.evm with stack := stack })))
                ((rest.length + 1) + 1) := by
            apply
              InteractionControlPreservation.OpenOutcome.PreservesWithin.prepend_closed_jump
            · intro target hStateRel
              rcases
                  openStep_test
                    (testLabel :=
                      TypedCfgCompiler.switchTestLabel base idx)
                    (caseLabel :=
                      TypedCfgCompiler.switchCaseLabel base idx)
                    (nextTest :=
                      TypedCfgCompilerFacts.Switch.nextTestLabel
                        base idx rest)
                    (caseValue := caseValue) (value := value)
                    hBlocks (by simp [hResult]) hHead hStateRel hPop with
                ⟨targetAfter, hTargetRun, hAfterRel⟩
              refine ⟨targetAfter, ?_, hAfterRel⟩
              simpa [hNe] using hTargetRun
            · rfl
            · intro targetAfter _hAfterRel
              simpa [
                TypedCfgCompilerFacts.Switch.nextTestLabel] using
                stopJump_casesEntryLabel_eq_false
                  (result := boundaryResult)
                  hBefore source.returns tokens targetAfter rest
                  (idx := idx + 1)
            · simpa [
                TypedCfgCompilerFacts.Switch.nextTestLabel] using
                hTailPreserves
          simpa [
            TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hSkipped

end Switch

namespace Stmt

/--
A compiled switch preserves under an arbitrary active stop policy. Generated
tests and entry pops are private compiler control, while the selected source
body keeps the same policy and outcome-indexed relation.
-/
theorem openRun_switch_under_of_compileStmtFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
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
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hFresh :
      InteractionControlPreservation.OpenOutcome.StopPolicy.FreshExceptAt
        policy regular supply)
    (hRegular :
      TypedCfgCompilerFacts.RegularAtSupply regular supply)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hBody :
      ∀ {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label}
        {bodyInput : TypedCfg.Shape}
        {body : Structured.Block}
        {bodyResult : TypedCfgCompiler.Result}
        {afterPop : RunState},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
            bodySupply bodyEntry bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        afterPop.returns = source.returns →
        bodyResult.requireFallthrough? bodyInput = some () →
        result.fallthrough? = some bodyInput →
        InteractionControlPreservation.OpenOutcome.PreservesUnder
          bodyResult cfg bodyEntry ctx regular regularExit afterPop tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterPop)
          bodyTargetFuel policy) :
    InteractionControlPreservation.OpenOutcome.PreservesUnder
      result cfg entry ctx regular regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      (1 + (bodyTargetFuel + cases.length + 1)) policy := by
  intro target hStateRel
  obtain
      ⟨valueShape, valueSlot, caseResult, defaultResult,
        hType, hSource, hValue, hCasesCompileRaw,
        hDefaultCompileRaw, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch
      hCompile
  let bodyShape : TypedCfg.Shape :=
    { valueShape with slots := valueShape.slots.tail }
  have hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
    cases valueShape with
    | mk slots tail =>
        cases slots with
        | nil =>
            simp at hValue
        | cons slot rest =>
            simp [bodyShape, TypedCfg.Instr.type?]
  have hCasesCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          supply (supply + 1) 0 valueShape bodyShape regular =
        some caseResult := by
    simpa [bodyShape] using hCasesCompileRaw
  have hDefaultCompile :
      TypedCfgCompiler.compileDefaultFuel? compilerFuel defaultBody ctx
          caseResult.next (LabelSupply.label supply 1)
          valueShape bodyShape regular =
        some defaultResult := by
    simpa [bodyShape] using hDefaultCompileRaw
  cases compilerFuel with
  | zero =>
      simp [TypedCfgCompiler.compileCasesFuel?] at hCasesCompile
  | succ bodyCompilerFuel =>
      have hFallthrough :
          result.fallthrough? = some bodyShape := by
        simp [bodyShape, hResult]
      have hCaseBlocks :
          TypedCfgPreservation.BlocksInProgram caseResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hResult, hMem]
      have hDefaultBlocks :
          TypedCfgPreservation.BlocksInProgram defaultResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hResult, hMem]
      have hDefaultFallthrough :
          defaultResult.fallthrough? = some bodyShape :=
        TypedCfgCompilerFacts.Switch.fallthrough_of_compileDefaultFuel?
          hPopType hDefaultCompile
      have hDefaultRequire :
          defaultResult.requireFallthrough? bodyShape = some () :=
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
          (Or.inr hDefaultFallthrough)
      have hCasesNext :
          supply + 1 ≤ caseResult.next :=
        TypedCfgCompilerFacts.Supply.cases_next_ge
          hValue hPopType hCasesCompile
      have hFreshDefault :
          InteractionControlPreservation.OpenOutcome.StopPolicy.FreshAt
            policy caseResult.next :=
        (hFresh.mono
            (Nat.le_trans (Nat.le_succ supply) hCasesNext)).toFreshAt
          (hRegular.before_succ.mono hCasesNext)
      let firstTest :=
        TypedCfgCompilerFacts.Switch.casesEntryLabel supply 0 cases
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg scrutinee
          output := valueShape
          term := .jump firstTest }
      have hFind :
          cfg.findBlock? entry = some generated := by
        exact hBlocks generated (by simp [generated, firstTest, hResult])
      have hHeadRel :
          Simulation.Interaction.Rel
            (InteractionBranchPreservation.Code.JumpDoneRel
              firstTest tokens valueShape)
            (InteractionSemantics.Code.openRun scrutinee source)
            (TypedCfg.InteractionSemantics.Program.openStep
              cfg entry target) := by
        simp only [
          TypedCfg.InteractionSemantics.Program.openStep,
          TypedCfg.Control.Program.step, hFind]
        simpa [generated] using
          (InteractionBranchPreservation.Code.openRun_jump_toCfg
            (entry := entry) (label := firstTest)
            hType hFits hStateRel)
      have hHeadWithReturns :=
        Simulation.Interaction.Rel.strengthen_left hHeadRel
          (InteractionSemantics.Code.openRun_returns scrutinee source)
      rw [
        show
          1 + (bodyTargetFuel + cases.length + 1) =
            (bodyTargetFuel + cases.length + 1) + 1 by
          omega,
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
              rcases hDone with ⟨hHead, _hReturns⟩
              cases hHead
      | ok afterScrutinee =>
          cases targetDone with
          | error targetError =>
              rcases hDone with ⟨hHead, _hReturns⟩
              cases hHead
          | ok targetOutcome =>
              rcases hDone with ⟨hHead, hReturns⟩
              cases hHead with
              | ok hJump =>
                  rcases hJump with
                    ⟨targetAfterScrutinee, hTargetOutcome,
                      hAfterRel, hAfterFits⟩
                  subst targetOutcome
                  have hReturnsEq :
                      afterScrutinee.returns = source.returns := by
                    simpa using hReturns
                  have hSourceOne :
                      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape :=
                    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
                      hSource
                  have hStackOne :
                      1 ≤ afterScrutinee.evm.stack.length :=
                    Nat.le_trans hSourceOne hAfterFits.1
                  obtain ⟨stack, value, hPop⟩ :=
                    Assembly.PrimStep.Stack.exists_pop_of_one_le hStackOne
                  have hPopLength :
                      afterScrutinee.evm.stack.length =
                        stack.length + 1 := by
                    cases hStack : afterScrutinee.evm.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hPop
                    | cons head tail =>
                        simp [hStack, EvmYul.Stack.pop] at hPop
                        rcases hPop with ⟨rfl, rfl⟩
                        simp [hStack]
                  have hBodyFits :
                      TypedCfgCompiler.Shape.SourceFrameFits
                        bodyShape stack.length := by
                    have hTailFits :=
                      TypedCfgCompilerFacts.Shape.sourceFrameFits_tail
                        hSourceOne
                        (show
                          TypedCfgCompiler.Shape.SourceFrameFits valueShape
                            (stack.length + 1) by
                          simpa [hPopLength] using hAfterFits)
                    simpa [bodyShape] using hTailFits
                  have hNoStop :
                      policy firstTest targetAfterScrutinee = false := by
                    simpa [firstTest] using
                      Switch.stopPolicy_casesEntryLabel_eq_false
                        hFresh hRegular targetAfterScrutinee cases (idx := 0)
                  simp only [
                    TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                    hNoStop, if_false]
                  cases hSelect :
                      Structured.Switch.select value cases defaultBody with
                  | none =>
                      have hDefaultRoute
                          (hDefaultNone : defaultBody = none) :
                          InteractionControlPreservation.OpenOutcome.PreservesUnder
                            result cfg (LabelSupply.label supply 1) ctx
                            regular regularExit afterScrutinee tokens
                            (Simulation.Interaction.pure
                              (Structured.Outcome.regular
                                (afterScrutinee.withEVM
                                  { afterScrutinee.evm with
                                    stack := stack })))
                            1 policy := by
                        have hCompileNone :
                            TypedCfgCompiler.compileDefaultFuel?
                                (bodyCompilerFuel + 1) none ctx
                                caseResult.next
                                (LabelSupply.label supply 1)
                                valueShape bodyShape regular =
                              some defaultResult := by
                          simpa [hDefaultNone] using hDefaultCompile
                        have hBase :=
                          Switch.openRun_default_none_under_of_compileDefaultFuel?
                            (result := defaultResult)
                            (regularExit := regularExit)
                            (source := afterScrutinee)
                            (tokens := tokens)
                            (policy := policy)
                            hCompileNone hDefaultBlocks hPopType hPop
                            hBodyFits
                            (fun {sourceOutcome} {targetOutcome} hRel => by
                              have hWholeRel :=
                                InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                                  hDefaultRequire hFallthrough hRel
                              exact hStops (by
                                simpa [hReturnsEq] using hWholeRel))
                        exact
                          InteractionControlPreservation.OpenOutcome.PreservesUnder.change_result_of_required_fallthrough
                            hDefaultRequire hFallthrough hBase
                      have hCasesNone :=
                        Switch.openRun_cases_none_under_of_compileCasesFuel?
                          (enclosingResult := result)
                          hCasesCompile hCaseBlocks hValue hPopType hPop
                          hSelect hFresh hRegular hDefaultRoute
                      have hCasesPadded :=
                        InteractionControlPreservation.OpenOutcome.PreservesUnder.pad
                          hCasesNone bodyTargetFuel
                      have hRouteRel :=
                        hCasesPadded targetAfterScrutinee hAfterRel
                      simpa [
                        hReturnsEq, hPop, hSelect, firstTest,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        hRouteRel
                  | some selected =>
                      have hCaseRoute :
                          ∀ {caseBodyCompilerFuel caseSupply caseIdx : Nat}
                            {bodyResult : TypedCfgCompiler.Result},
                            TypedCfgCompiler.compileBlockFuel?
                                caseBodyCompilerFuel selected ctx
                                caseSupply
                                (TypedCfgCompiler.switchBodyLabel
                                  supply caseIdx)
                                bodyShape regular =
                              some bodyResult →
                            TypedCfgPreservation.BlocksInProgram
                              bodyResult cfg →
                            bodyResult.requireFallthrough? bodyShape =
                              some () →
                            result.fallthrough? = some bodyShape →
                            InteractionControlPreservation.OpenOutcome.PreservesUnder
                              bodyResult cfg
                              (TypedCfgCompiler.switchBodyLabel
                                supply caseIdx)
                              ctx regular regularExit
                              (afterScrutinee.withEVM
                                { afterScrutinee.evm with
                                  stack := stack })
                              tokens
                              (InteractionSemantics.Block.openRun
                                sourceProgram sourceFuel selected
                                (afterScrutinee.withEVM
                                  { afterScrutinee.evm with
                                    stack := stack }))
                              bodyTargetFuel policy := by
                        intro caseBodyCompilerFuel caseSupply caseIdx
                          bodyResult hBodyCompile hBodyBlocks
                          hBodyRequire hResultFallthrough
                        exact
                          hBody hBodyCompile hBodyBlocks (by
                              simpa [RunState.withEVM] using hReturnsEq)
                            hBodyRequire hResultFallthrough
                      have hDefaultRoute
                          (hDefaultSelected :
                            defaultBody = some selected) :
                          InteractionControlPreservation.OpenOutcome.PreservesUnder
                            result cfg (LabelSupply.label supply 1) ctx
                            regular regularExit afterScrutinee tokens
                            (InteractionSemantics.Block.openRun
                              sourceProgram sourceFuel selected
                              (afterScrutinee.withEVM
                                { afterScrutinee.evm with
                                  stack := stack }))
                            (bodyTargetFuel + 1) policy := by
                        have hCompileSome :
                            TypedCfgCompiler.compileDefaultFuel?
                                (bodyCompilerFuel + 1) (some selected) ctx
                                caseResult.next
                                (LabelSupply.label supply 1)
                                valueShape bodyShape regular =
                              some defaultResult := by
                          simpa [hDefaultSelected] using hDefaultCompile
                        exact
                          Switch.openRun_default_some_under_of_compileDefaultFuel?
                            (enclosingResult := result)
                            (regularExit := regularExit)
                            (policy := policy)
                            hCompileSome hDefaultBlocks hPopType hPop
                            hFallthrough
                            (fun targetAfter =>
                              hFreshDefault caseResult.next 2000
                                targetAfter (Nat.le_refl caseResult.next))
                            (fun hBodyCompile hBodyBlocks hBodyRequire
                                hResultFallthrough =>
                              hBody hBodyCompile hBodyBlocks (by
                                  simpa [RunState.withEVM] using
                                    hReturnsEq)
                                hBodyRequire hResultFallthrough)
                      have hCasesSome :=
                        Switch.openRun_cases_some_under_of_compileCasesFuel?
                          (enclosingResult := result)
                          hCasesCompile hCaseBlocks hValue hPopType hPop
                          hSelect hFallthrough hFresh hRegular
                          hCaseRoute hDefaultRoute
                      have hRouteRel :=
                        hCasesSome targetAfterScrutinee hAfterRel
                      simpa [hReturnsEq, hPop, hSelect, firstTest] using
                        hRouteRel

/--
A compiled switch preserves its complete open interaction tree until its own
regular boundary. Case tests and entry pops are private compiler control;
only the selected source block contributes open effects.
-/
theorem openRun_switch_within_stop_of_compileStmtFuel?
    {compilerFuel sourceFuel bodyTargetFuel : Nat}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
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
      ∀ {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label}
        {bodyInput : TypedCfg.Shape}
        {body : Structured.Block}
        {bodyResult : TypedCfgCompiler.Result}
        {afterPop : RunState},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
            bodySupply bodyEntry bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        afterPop.returns = source.returns →
        InteractionControlPreservation.OpenOutcome.PreservesWithin
          bodyResult result cfg bodyEntry ctx
          regular regular .stop afterPop tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterPop)
          bodyTargetFuel) :
    InteractionControlPreservation.OpenOutcome.PreservesWithin
      result result cfg entry ctx regular regular .stop source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      (1 + (bodyTargetFuel + cases.length + 1)) := by
  intro target hStateRel
  obtain
      ⟨valueShape, valueSlot, caseResult, defaultResult,
        hType, hSource, hValue, hCasesCompileRaw,
        hDefaultCompileRaw, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch
      hCompile
  let bodyShape : TypedCfg.Shape :=
    { valueShape with slots := valueShape.slots.tail }
  have hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
    cases valueShape with
    | mk slots tail =>
        cases slots with
        | nil =>
            simp at hValue
        | cons slot rest =>
            simp [bodyShape, TypedCfg.Instr.type?]
  have hCasesCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          supply (supply + 1) 0 valueShape bodyShape regular =
        some caseResult := by
    simpa [bodyShape] using hCasesCompileRaw
  have hDefaultCompile :
      TypedCfgCompiler.compileDefaultFuel? compilerFuel defaultBody ctx
          caseResult.next (LabelSupply.label supply 1)
          valueShape bodyShape regular =
        some defaultResult := by
    simpa [bodyShape] using hDefaultCompileRaw
  cases compilerFuel with
  | zero =>
      simp [TypedCfgCompiler.compileCasesFuel?] at hCasesCompile
  | succ bodyCompilerFuel =>
      have hFallthrough :
          result.fallthrough? = some bodyShape := by
        simp [bodyShape, hResult]
      have hCaseBlocks :
          TypedCfgPreservation.BlocksInProgram caseResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hResult, hMem]
      have hDefaultBlocks :
          TypedCfgPreservation.BlocksInProgram defaultResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hResult, hMem]
      have hDefaultFallthrough :
          defaultResult.fallthrough? = some bodyShape :=
        TypedCfgCompilerFacts.Switch.fallthrough_of_compileDefaultFuel?
          hPopType hDefaultCompile
      have hDefaultRequire :
          defaultResult.requireFallthrough? bodyShape = some () :=
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
          (Or.inr hDefaultFallthrough)
      have hCasesNext :
          supply + 1 ≤ caseResult.next :=
        TypedCfgCompilerFacts.Supply.cases_next_ge
          hValue hPopType hCasesCompile
      have hBeforeDefault :
          TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
            ctx regular caseResult.next :=
        hBefore.mono
          (Nat.le_trans (Nat.le_succ supply) hCasesNext)
      let firstTest :=
        TypedCfgCompilerFacts.Switch.casesEntryLabel supply 0 cases
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg scrutinee
          output := valueShape
          term := .jump firstTest }
      have hFind :
          cfg.findBlock? entry = some generated := by
        exact hBlocks generated (by simp [generated, firstTest, hResult])
      have hHeadRel :
          Simulation.Interaction.Rel
            (InteractionBranchPreservation.Code.JumpDoneRel
              firstTest tokens valueShape)
            (InteractionSemantics.Code.openRun scrutinee source)
            (TypedCfg.InteractionSemantics.Program.openStep
              cfg entry target) := by
        simp only [
          TypedCfg.InteractionSemantics.Program.openStep,
          TypedCfg.Control.Program.step, hFind]
        simpa [generated] using
          (InteractionBranchPreservation.Code.openRun_jump_toCfg
            (entry := entry) (label := firstTest)
            hType hFits hStateRel)
      have hHeadWithReturns :=
        Simulation.Interaction.Rel.strengthen_left hHeadRel
          (InteractionSemantics.Code.openRun_returns scrutinee source)
      rw [
        show
          1 + (bodyTargetFuel + cases.length + 1) =
            (bodyTargetFuel + cases.length + 1) + 1 by
          omega,
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
              rcases hDone with ⟨hHead, _hReturns⟩
              cases hHead
      | ok afterScrutinee =>
          cases targetDone with
          | error targetError =>
              rcases hDone with ⟨hHead, _hReturns⟩
              cases hHead
          | ok targetOutcome =>
              rcases hDone with ⟨hHead, hReturns⟩
              cases hHead with
              | ok hJump =>
                  rcases hJump with
                    ⟨targetAfterScrutinee, hTargetOutcome,
                      hAfterRel, hAfterFits⟩
                  subst targetOutcome
                  have hReturnsEq :
                      afterScrutinee.returns = source.returns := by
                    simpa using hReturns
                  have hSourceOne :
                      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape :=
                    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
                      hSource
                  have hStackOne :
                      1 ≤ afterScrutinee.evm.stack.length :=
                    Nat.le_trans hSourceOne hAfterFits.1
                  obtain ⟨stack, value, hPop⟩ :=
                    Assembly.PrimStep.Stack.exists_pop_of_one_le hStackOne
                  have hPopLength :
                      afterScrutinee.evm.stack.length =
                        stack.length + 1 := by
                    cases hStack : afterScrutinee.evm.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hPop
                    | cons head tail =>
                        simp [hStack, EvmYul.Stack.pop] at hPop
                        rcases hPop with ⟨rfl, rfl⟩
                        simp [hStack]
                  have hBodyFits :
                      TypedCfgCompiler.Shape.SourceFrameFits
                        bodyShape stack.length := by
                    have hTailFits :=
                      TypedCfgCompilerFacts.Shape.sourceFrameFits_tail
                        hSourceOne
                        (show
                          TypedCfgCompiler.Shape.SourceFrameFits valueShape
                            (stack.length + 1) by
                          simpa [hPopLength] using hAfterFits)
                    simpa [bodyShape] using hTailFits
                  have hNoStop :
                      InteractionControlPreservation.OpenOutcome.stopJump
                          result ctx regular source.returns tokens
                          firstTest targetAfterScrutinee =
                        false := by
                    simpa [firstTest] using
                      Switch.stopJump_casesEntryLabel_eq_false
                        (result := result)
                        hBefore source.returns tokens
                        targetAfterScrutinee cases
                        (idx := 0)
                  simp only [
                    TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                    InteractionControlPreservation.OpenOutcome.segmentStopJump,
                    hNoStop, Bool.true_eq, if_false]
                  cases hSelect :
                      Structured.Switch.select value cases defaultBody with
                  | none =>
                      have hDefaultRoute
                          (hDefaultNone : defaultBody = none) :
                          InteractionControlPreservation.OpenOutcome.PreservesWithin
                              result result cfg
                              (LabelSupply.label supply 1) ctx
                              regular regular .stop
                              afterScrutinee tokens
                              (Simulation.Interaction.pure
                                (Structured.Outcome.regular
                                  (afterScrutinee.withEVM
                                    { afterScrutinee.evm with
                                      stack := stack })))
                              1 := by
                        have hCompileNone :
                            TypedCfgCompiler.compileDefaultFuel?
                                (bodyCompilerFuel + 1) none ctx
                                caseResult.next
                                (LabelSupply.label supply 1)
                                valueShape bodyShape regular =
                              some defaultResult := by
                          simpa [hDefaultNone] using hDefaultCompile
                        have hBase :=
                          Switch.openRun_default_none_of_compileDefaultFuel?
                              (result := defaultResult)
                              (boundaryResult := result)
                              (boundaryRegular := regular)
                              (regularExit := .stop)
                              (source := afterScrutinee)
                              (tokens := tokens)
                              hCompileNone hDefaultBlocks hPopType hPop
                              hBodyFits
                              (fun {final} {targetState} hRel => by
                                have hWholeRel :=
                                  InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                                      hDefaultRequire hFallthrough hRel
                                simpa [
                                  InteractionControlPreservation.OpenOutcome.TargetStopped] using
                                  (InteractionControlPreservation.OpenOutcome.targetStopped_of_rel
                                    hWholeRel))
                        exact
                          InteractionControlPreservation.OpenOutcome.PreservesWithin.change_result_of_required_fallthrough
                              hDefaultRequire hFallthrough hBase
                      have hCasesNone :=
                        Switch.openRun_cases_none_of_compileCasesFuel?
                          (enclosingResult := result)
                          hCasesCompile hCaseBlocks hValue hPopType hPop
                          hSelect hBefore hDefaultRoute
                      have hCasesPadded :=
                        InteractionControlPreservation.OpenOutcome.PreservesWithin.pad_stop
                            hCasesNone bodyTargetFuel
                      have hRouteRel :=
                        hCasesPadded targetAfterScrutinee hAfterRel
                      simpa [
                        hReturnsEq, hPop, hSelect, firstTest,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        hRouteRel
                  | some selected =>
                      have hCaseRoute :
                          ∀ {caseBodyCompilerFuel caseSupply caseIdx : Nat}
                            {bodyResult : TypedCfgCompiler.Result},
                            TypedCfgCompiler.compileBlockFuel?
                                caseBodyCompilerFuel selected ctx
                                caseSupply
                                (TypedCfgCompiler.switchBodyLabel
                                  supply caseIdx)
                                bodyShape regular =
                              some bodyResult →
                            TypedCfgPreservation.BlocksInProgram
                                bodyResult cfg →
                            InteractionControlPreservation.OpenOutcome.PreservesWithin
                                bodyResult result cfg
                                (TypedCfgCompiler.switchBodyLabel
                                  supply caseIdx)
                                ctx regular regular .stop
                                (afterScrutinee.withEVM
                                  { afterScrutinee.evm with
                                    stack := stack })
                                tokens
                                (InteractionSemantics.Block.openRun
                                  sourceProgram sourceFuel selected
                                  (afterScrutinee.withEVM
                                    { afterScrutinee.evm with
                                      stack := stack }))
                                bodyTargetFuel := by
                        intro caseBodyCompilerFuel caseSupply caseIdx
                          bodyResult hBodyCompile hBodyBlocks
                        exact
                          hBody hBodyCompile hBodyBlocks (by
                            simpa [RunState.withEVM] using hReturnsEq)
                      have hDefaultRoute
                          (hDefaultSelected :
                            defaultBody = some selected) :
                          InteractionControlPreservation.OpenOutcome.PreservesWithin
                              result result cfg
                              (LabelSupply.label supply 1) ctx
                              regular regular .stop afterScrutinee tokens
                              (InteractionSemantics.Block.openRun
                                sourceProgram sourceFuel selected
                                (afterScrutinee.withEVM
                                  { afterScrutinee.evm with
                                    stack := stack }))
                              (bodyTargetFuel + 1) := by
                        have hCompileSome :
                            TypedCfgCompiler.compileDefaultFuel?
                                (bodyCompilerFuel + 1) (some selected) ctx
                                caseResult.next
                                (LabelSupply.label supply 1)
                                valueShape bodyShape regular =
                              some defaultResult := by
                          simpa [hDefaultSelected] using hDefaultCompile
                        have hBase :=
                          Switch.openRun_default_some_of_compileDefaultFuel?
                              hCompileSome hDefaultBlocks hPopType hPop
                              hBeforeDefault
                              (fun hBodyCompile hBodyBlocks =>
                                hBody hBodyCompile hBodyBlocks (by
                                  simpa [RunState.withEVM] using
                                    hReturnsEq))
                        exact
                          InteractionControlPreservation.OpenOutcome.PreservesWithin.change_result_of_required_fallthrough
                              hDefaultRequire hFallthrough hBase
                      have hCasesSome :=
                        Switch.openRun_cases_some_of_compileCasesFuel?
                          (enclosingResult := result)
                          hCasesCompile hCaseBlocks hValue hPopType hPop
                          hSelect hFallthrough hBefore
                          hCaseRoute hDefaultRoute
                      have hRouteRel :=
                        hCasesSome targetAfterScrutinee hAfterRel
                      simpa [hReturnsEq, hPop, hSelect, firstTest] using
                        hRouteRel

end Stmt

end InteractionSwitchPreservation
end Structured
end EvmCompiler
