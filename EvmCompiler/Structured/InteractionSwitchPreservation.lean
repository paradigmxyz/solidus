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

end Switch

end InteractionSwitchPreservation
end Structured
end EvmCompiler
