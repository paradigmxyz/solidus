import EvmCompiler.Functions.AllocationInteractionCleanupResource
import EvmCompiler.Functions.AllocationInteractionResource
import EvmCompiler.Functions.AllocationInteractionTerminal

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionTerminalResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionResource

namespace Invocation

/-- Canonical terminal execution exposes exactly its allocator-safe growth. -/
theorem forward_shared_allocator
    {contract : MemoryContract.Contract}
    {kind : Assembly.HaltKind} {values : List Word}
    {source : SourceState} {target : TargetState}
    {sourceSharedFinal : EvmYul.SharedState .EVM}
    {baseStack : List Word}
    (invocation : AllocationInteractionTerminal.Invocation contract kind values)
    (hShared : SharedRel contract source.shared target.evm.toSharedState)
    (hTargetNoWrap :
      target.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind source.shared values = .ok sourceSharedFinal)
    (hStack : target.evm.stack = values.reverse ++ baseStack) :
    ∃ sourceFinal targetFinal,
      Locals.InteractionSemantics.Primitive.openTerminal
          kind source values = .done (.ok sourceFinal) ∧
        Structured.InteractionSemantics.Terminal.openStep
          kind target = .done (.ok targetFinal) ∧
        targetFinal.evm.toMachineState.memory =
          target.evm.toMachineState.memory ∧
        target.evm.activeWords.toNat ≤ targetFinal.evm.activeWords.toNat ∧
        targetFinal.evm.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size := by
  obtain
      ⟨targetSharedFinal, hTargetEval, _hSharedRel,
        hMemory, hActive, hFinalNoWrap⟩ :=
    invocation.simulate hShared hTargetNoWrap hEval
  obtain
      ⟨targetEvmFinal, hTargetStep, hFinalShared,
        _isolated, _hIsolated, _hFinalStack⟩ :=
    Locals.Source.PrimitiveSemantics.structured_terminal_step_exists
      hTargetEval rfl hStack
  let sourceFinal := source.withShared sourceSharedFinal
  let targetFinal := target.withEVM targetEvmFinal
  have hSourceBound :
      kind.argCount ≤
        (Locals.InteractionSemantics.Primitive.isolated
          source values).stack.length := by
    simp [Locals.InteractionSemantics.Primitive.isolated,
      List.length_reverse, invocation.values_length]
  obtain ⟨sourceEvmFinal, hSourceStep⟩ :=
    Structured.Terminal.exists_step_of_argCount_le
      kind (Locals.InteractionSemantics.Primitive.isolated source values)
        hSourceBound
  have hSourceEval' :
      sourceEvmFinal.toSharedState = sourceSharedFinal := by
    unfold Locals.Source.PrimitiveSemantics.structured at hEval
    change
      (match
          Structured.Terminal.step kind
            (Locals.InteractionSemantics.Primitive.isolated source values)
        with
        | .ok state' => Except.ok state'.toSharedState
        | .error err => Except.error err) =
        .ok sourceSharedFinal at hEval
    rw [hSourceStep] at hEval
    exact Except.ok.inj hEval
  have hSourceOpen :
      Locals.InteractionSemantics.Primitive.openTerminal
          kind source values = .done (.ok sourceFinal) := by
    unfold Locals.InteractionSemantics.Primitive.openTerminal
      Simulation.Interaction.map
    change
      Simulation.Interaction.bind
          (.done
            (Structured.Terminal.step kind
              (Locals.InteractionSemantics.Primitive.isolated source values)))
          _ = _
    rw [hSourceStep]
    change
      Simulation.Interaction.done
          (.ok (source.withShared sourceEvmFinal.toSharedState)) =
        Simulation.Interaction.done (.ok sourceFinal)
    rw [hSourceEval']
  have hTargetOpenStep :
      Assembly.InteractionSemantics.PrimOp.openStep
          kind.toPrimOp target.evm = .done (.ok targetEvmFinal) := by
    have hExternal :
        Simulation.ExternalKind.ofEVMOperation? kind.toPrimOp.toEVM = none := by
      cases kind <;> rfl
    have hGas : kind.toPrimOp ≠ .gas := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    have hMsize : kind.toPrimOp ≠ .msize := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize]
    have hPrimitiveStep : kind.toPrimOp.step target.evm = .ok targetEvmFinal := by
      simpa [Structured.Terminal.step] using hTargetStep
    rw [hPrimitiveStep]
  have hTargetOpen :
      Structured.InteractionSemantics.Terminal.openStep
          kind target = .done (.ok targetFinal) := by
    unfold Structured.InteractionSemantics.Terminal.openStep
      Simulation.Interaction.map
    rw [hTargetOpenStep]
    rfl
  refine ⟨sourceFinal, targetFinal, hSourceOpen, hTargetOpen, ?_, ?_, ?_⟩
  · simpa [targetFinal, hFinalShared] using hMemory
  · simpa [targetFinal, hFinalShared] using hActive
  · simpa [targetFinal, hFinalShared] using hFinalNoWrap

end Invocation

/-- Plain terminal cleanup and terminal growth preserve activation resources. -/
theorem terminal_of_lower_compile
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns live : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode} {kind : Assembly.HaltKind}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hMemory : Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminal kind) = some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth mode target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.terminal kind) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 3) { stmts := compiledStmts } target) := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    AllocationInteractionTerminal.TerminalLeaf.compiler_shape hLower hCompile
  obtain
      ⟨targetAfterCleanup, hCleanupRun,
        hCleanupStack, hCleanupShared, _hCleanupReturns⟩ :=
    Locals.InteractionPreservation.Code.openRun_replicate_pop
      localsFinal.layout.length (by rw [hInvariant.stackLength])
  have hCleanupRun' :
      Structured.InteractionSemantics.Code.openRun
          localsFinal.cleanupAll target =
        .done (.ok targetAfterCleanup) := by
    simpa [Locals.Ctx.cleanupAll] using hCleanupRun
  have hAfterStack : targetAfterCleanup.evm.stack = [] := by
    rw [hCleanupStack, hInvariant.stackLength.symm]
    exact List.drop_length
  have hAfterShared :
      SharedRel contract source.shared targetAfterCleanup.evm.toSharedState := by
    rw [hCleanupShared]
    exact hInvariant.state.shared
  have hAfterNoWrap :
      targetAfterCleanup.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    rw [show targetAfterCleanup.evm.activeWords = target.evm.activeWords by
      exact congrArg
        (fun shared : EvmYul.SharedState .EVM =>
          shared.toMachineState.activeWords) hCleanupShared]
    exact hInvariant.state.activeNoWrap
  have hCleanupEffect :
      AllocatorEffect config allocatorDepth target targetAfterCleanup :=
    AllocatorEffect.of_machine_eq hReady
      (congrArg EvmYul.SharedState.toMachineState hCleanupShared)
  have invocation := AllocationInteractionTerminal.Invocation.of_memorySafe hMemory
  obtain ⟨sourceSharedFinal, hSourceEval⟩ :=
    invocation.eval_exists source.shared
  obtain
      ⟨sourceFinal, targetFinal, hSourceTerminal, hTargetTerminal,
        hTerminalMemory, hTerminalActive, hTerminalNoWrap⟩ :=
    Invocation.forward_shared_allocator invocation hAfterShared hAfterNoWrap
      hSourceEval (by simpa using hAfterStack)
  have hTerminalEffect :
      AllocatorEffect config allocatorDepth targetAfterCleanup targetFinal :=
    AllocatorEffect.of_memory_eq_active_growth hCleanupEffect.ready
      hTerminalMemory hTerminalActive hTerminalNoWrap
  have hSource :
      Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel (.terminal kind) source =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
              sourceCtx)) := by
    unfold Functions.InteractionSemantics.Stmt.openRun
      Functions.Source.Canonical.Stmt.run
    simp only [Functions.Source.Effectful.Control.Stmt.run]
    unfold Functions.InteractionSemantics.primitiveSemantics
    unfold Locals.InteractionSemantics.primitiveSemantics
    change
      Simulation.Interaction.bind
          (Locals.InteractionSemantics.Primitive.openTerminal kind source [])
          (fun state' =>
            Simulation.Interaction.pure
              (Functions.Source.Effectful.Outcome.halt kind state',
                sourceCtx)) =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
              sourceCtx))
    rw [hSourceTerminal]
    rfl
  have hTarget :
      Expressions.InteractionSemantics.Block.openRun
          targetProgram (targetExtra + 3)
          { stmts := [.code localsFinal.cleanupAll, .terminal kind] }
          target =
        .done
          (.ok (Structured.EffectSemantics.Outcome.halt kind targetFinal)) := by
    rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_terminal]
    rw [hCleanupRun']
    change
      Simulation.Interaction.bind
          (Structured.InteractionSemantics.Terminal.openStep
            kind targetAfterCleanup)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.EffectSemantics.Outcome.halt kind final)) =
        .done
          (.ok (Structured.EffectSemantics.Outcome.halt kind targetFinal))
    rw [hTargetTerminal]
    rfl
  have hTargetCompiled :
      Expressions.InteractionSemantics.Block.openRun
          targetProgram (targetExtra + 3)
          { stmts :=
              Locals.codeStmt localsFinal.cleanupAll ++ [.terminal kind] }
          target =
        .done
          (.ok (Structured.EffectSemantics.Outcome.halt kind targetFinal)) := by
    simpa [Locals.codeStmt] using hTarget
  rw [hSource, hTargetCompiled]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact ActivationEffect.of_allocatorEffect
    (hCleanupEffect.trans hTerminalEffect)

end AllocationInteractionTerminalResource
end Functions
end EvmCompiler
