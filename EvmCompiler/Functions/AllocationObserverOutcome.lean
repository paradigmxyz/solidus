import EvmCompiler.Functions.AllocationObserverStatement

namespace EvmCompiler
namespace Functions
namespace AllocationObserverOutcome

open AllocationObserverRelation

/--
For an abrupt statement outcome, the continuation live environment may be
re-indexed. Break, continue, and leave select their own destination live sets;
terminal halts erase local realization entirely.
-/
theorem reindex_outcomeLive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {returns beforeLive afterLive : List Functions.Name}
    {sourceCtx : Functions.Source.Ctx}
    {stackOffset frameBase : Nat}
    {finalMode : ActivationMode}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      ActivationOutcomeRel contract plan
        (outcomeLive returns beforeLive sourceCtx sourceOutcome.mode)
        stackOffset frameBase finalMode sourceOutcome targetOutcome)
    (hMode : sourceOutcome.mode ≠ .regular) :
    ActivationOutcomeRel contract plan
      (outcomeLive returns afterLive sourceCtx sourceOutcome.mode)
      stackOffset frameBase finalMode sourceOutcome targetOutcome := by
  cases hRel with
  | regular _ =>
      exact False.elim (hMode rfl)
  | brk hState =>
      exact .brk (by simpa [outcomeLive] using hState)
  | cont hState =>
      exact .cont (by simpa [outcomeLive] using hState)
  | leave hState =>
      exact .leave hState
  | halt kind hState =>
      exact .halt kind hState

namespace BlockRuntimeForward

/--
Transport an abrupt open-block result back to an enclosing allocation index
after an activation exit.

Only `leave` retains a live-name index, and callers prove that both indices are
the same ordered return list. Terminal halts expose neither plan nor locals.
-/
theorem transport_of_isExit
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {beforePlan afterPlan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {sourceBlock : Functions.Block}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {targetBlock : Structured.Block}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hForward :
      BlockRuntimeForward contract config allocatorDepth transcript
        beforePlan beforeLive frameBase initialMode finalMode sourceProgram
        sourceCtx sourceBlock source targetProgram targetBlock target
        sourceOutcome targetOutcome finalCtx)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceOutcome)
    (hLeaveLive :
      sourceOutcome.mode = .leave → beforeLive = afterLive) :
    BlockRuntimeForward contract config allocatorDepth transcript
      afterPlan afterLive frameBase initialMode finalMode sourceProgram
      sourceCtx sourceBlock source targetProgram targetBlock target
      sourceOutcome targetOutcome finalCtx := by
  rcases hForward with
    ⟨sourceFuel, targetFuel, hSource, hTarget, hRel, hSame, hEffect⟩
  exact
    ⟨sourceFuel, targetFuel, hSource, hTarget,
      hRel.transport_of_isExit hExit hLeaveLive, hSame, hEffect⟩

end BlockRuntimeForward

namespace ScopedBlockRuntimeForward

/--
Re-index a scoped block after an activation exit.
-/
theorem transport_of_isExit
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {beforePlan afterPlan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceBlock : Functions.Block}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {targetBlock : Structured.Block}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hForward :
      ScopedBlockRuntimeForward contract config allocatorDepth transcript
        beforePlan beforeLive frameBase initialMode finalMode sourceProgram
        sourceCtx sourceBlock source targetProgram targetBlock target
        sourceOutcome targetOutcome)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceOutcome)
    (hLeaveLive :
      sourceOutcome.mode = .leave → beforeLive = afterLive) :
    ScopedBlockRuntimeForward contract config allocatorDepth transcript
      afterPlan afterLive frameBase initialMode finalMode sourceProgram
      sourceCtx sourceBlock source targetProgram targetBlock target
      sourceOutcome targetOutcome := by
  rcases hForward with
    ⟨sourceFuel, targetFuel, hSource, hTarget,
      hRel, hSame, hEffect⟩
  exact
    ⟨sourceFuel, targetFuel, hSource, hTarget,
      hRel.transport_of_isExit hExit hLeaveLive, hSame, hEffect⟩

end ScopedBlockRuntimeForward

namespace NonregularStmtRuntimeForward

/--
Re-index an activation-exit statement result after the surrounding compiler
returns to its outer allocation plan.

`leave` observes only the ordered return live set and terminal halts observe no
locals. The source/target runs and allocator effect are unchanged.
-/
theorem transport_of_isExit
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {beforePlan afterPlan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiled : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hForward :
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        beforePlan beforeLive frameBase initialMode finalMode sourceProgram
        sourceCtx stmt source targetProgram target compiled sourceOutcome
        targetOutcome stmtCtx)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit sourceOutcome)
    (hLeaveLive :
      sourceOutcome.mode = .leave → beforeLive = afterLive) :
    NonregularStmtRuntimeForward contract config allocatorDepth transcript
      afterPlan afterLive frameBase initialMode finalMode sourceProgram
      sourceCtx stmt source targetProgram target compiled sourceOutcome
      targetOutcome stmtCtx := by
  rcases hForward with
    ⟨sourceFuel, targetFuel, hSource, hTarget, hMode,
      hRel, hSame, hEffect⟩
  exact
    ⟨sourceFuel, targetFuel, hSource, hTarget, hMode,
      hRel.transport_of_isExit hExit hLeaveLive, hSame, hEffect⟩

theorem of_runs
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {finalLive : List Locals.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {stmt : Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiled : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel stmt source =
        .ok (sourceOutcome, stmtCtx))
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel { stmts := compiled } target
          targetOutcome)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hRel :
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome)
    (hSame : SameFrame initialMode finalMode)
    (hEffect :
      Frame.ActivationEffect config allocatorDepth initialMode
        target targetOutcome.state) :
    NonregularStmtRuntimeForward contract config allocatorDepth transcript
      plan finalLive frameBase initialMode finalMode sourceProgram sourceCtx
      stmt source targetProgram target compiled sourceOutcome targetOutcome
      stmtCtx :=
  ⟨sourceFuel, targetFuel, hSource, hTarget, hMode, hRel, hSame,
    Frame.OutcomeEffect.of_activation hEffect⟩

/--
Change the regular continuation environment carried by an abrupt statement
result. This is the sequence-facing form of
`ActivationOutcomeRel.reindex_outcomeLive`.
-/
theorem reindex_regularLive
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {returns beforeLive afterLive : List Functions.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiled : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hForward :
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan (outcomeLive returns beforeLive sourceCtx sourceOutcome.mode)
        frameBase initialMode finalMode sourceProgram sourceCtx stmt source
        targetProgram target compiled sourceOutcome targetOutcome stmtCtx) :
    NonregularStmtRuntimeForward contract config allocatorDepth transcript
      plan (outcomeLive returns afterLive sourceCtx sourceOutcome.mode)
      frameBase initialMode finalMode sourceProgram sourceCtx stmt source
      targetProgram target compiled sourceOutcome targetOutcome stmtCtx := by
  rcases hForward with
    ⟨sourceFuel, targetFuel, hSource, hTarget, hMode, hRel, hSame, hEffect⟩
  exact
    ⟨sourceFuel, targetFuel, hSource, hTarget, hMode,
      AllocationObserverOutcome.reindex_outcomeLive hRel hMode,
      hSame, hEffect⟩

theorem leave_of_invariant
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns functionScope live : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {frameBase : Nat}
    {mode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hReturnsLive : ∀ name, name ∈ returns → name ∈ live)
    (hReturnsScope : ∀ name, name ∈ returns → name ∈ functionScope)
    (hTargetDepth : localsCtx.leaveDepth? = some 0)
    (hRetc : localsCtx.leaveRetc = returns.length)
    (hReturnFrame : target.source.returns ≠ [])
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        live frameBase mode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .leave =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan returns frameBase mode mode sourceProgram sourceCtx .leave source
        targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.leave
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            functionScope source))
        (Structured.EffectSemantics.Outcome.leave targetFinal)
        sourceCtx := by
  obtain ⟨values, hLookup⟩ :=
    lookupMany_of_liveDefined hInvariant.activation.defined hReturnsLive
  have hSafe :=
    AllocationObserverCleanup.ReturnValues.memorySafeEval
      (contract := contract) (transcript := transcript) hLookup
  have hScoped :=
    AllocationObserverCleanup.ReturnValues.returnExprsScoped hReturnsLive
  obtain
      ⟨loweredReturns, returnCode, cleanup,
        hLowerReturns, hLowerSeq, hReturnCode, hCleanup,
        rfl, rfl, rfl, rfl⟩ :=
    AllocationObserverCleanup.LeaveLeaf.compiler_shape
      hTargetDepth hRetc hLower hCompile
  obtain ⟨afterReturns, hReturnRun, hReturnRel, hReturnEffect⟩ :=
    AllocationObserverExpression.forwardExprSeqRuntime_with_effect
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hSafe hInvariant.activation.compiler hScoped hLowerSeq
      hReturnCode hInvariant.activation.state hInvariant.allocator
  obtain
      ⟨targetFinal, hCleanupRun, hCleanupCursor, hFinalStack,
        hCleanupShared, hCleanupReturns⟩ :=
    AllocationObserverCleanup.Preserving.forward_zero
      (values := values.reverse)
      (baseStack := target.source.evm.stack)
      hCleanup
      (by simpa [Functions.Source.Store.lookupMany_length hLookup])
      (by simpa [hInvariant.activation.stackLength])
      hReturnRel.stack
  have hAfterReturnsFrame : afterReturns.source.returns ≠ [] := by
    rw [Structured.ObserverSemantics.Code.run_returns_eq hReturnRun]
    exact hReturnFrame
  have hFinalFrame : targetFinal.source.returns ≠ [] := by
    rw [hCleanupReturns]
    exact hAfterReturnsFrame
  have hLeaveStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 .leave targetFinal
          (Structured.EffectSemantics.Outcome.leave targetFinal) :=
    Structured.EffectSemantics.Stmt.Eval.leave hFinalFrame
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 3
        { stmts :=
            [ Structured.Stmt.code returnCode,
              Structured.Stmt.code cleanup,
              Structured.Stmt.leave ] }
        target
        (Structured.EffectSemantics.Outcome.leave targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 2) hReturnRun)
      (Structured.EffectSemantics.Block.Eval.cons_regular
        (Structured.EffectSemantics.Stmt.Eval.code
          (fuel := 1) hCleanupRun)
        (Structured.EffectSemantics.Block.Eval.cons_leave hLeaveStmt))
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.leave
      (contract := contract) (transcript := transcript)
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      (source := source) hSourceScope).run_eq
  let sourceFinal :=
    (Functions.ObserverSemantics.stateModel transcript).restrictTo
      functionScope source
  have hLeaveRel :
      LeaveStateRel contract returns sourceFinal targetFinal := by
    refine ⟨?_, ?_, values, ?_, hFinalStack⟩
    · change source.cursor = targetFinal.cursor
      rw [hCleanupCursor]
      exact hReturnRel.state.base.cursor
    · change
        SharedRel contract source.source.shared
          targetFinal.source.evm.toSharedState
      rw [hCleanupShared]
      exact hReturnRel.state.base.core.shared
    · exact
        Functions.Source.Store.lookupMany_restrictTo_of_mem
          hReturnsScope hLookup
  have hCleanupMachine :
      targetFinal.source.evm.toMachineState =
        afterReturns.source.evm.toMachineState := by
    exact congrArg EvmYul.SharedState.toMachineState hCleanupShared
  have hEffect :
      Frame.ActivationEffect config allocatorDepth mode target targetFinal :=
    Frame.ActivationEffect.of_allocatorEffect
      (hReturnEffect.trans
        (Frame.AllocatorEffect.of_machine_eq
          hReturnEffect.ready hCleanupMachine))
  refine
    ⟨targetFinal, 0, 3, hSource, ?_, ?_, .leave hLeaveRel,
      SameFrame.refl mode, Frame.OutcomeEffect.of_activation hEffect⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget
  · intro hMode
    cases hMode

theorem terminalArgs_of_invariant
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source afterArgs sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hArgs :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript args source afterArgs values)
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe contract kind values)
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind afterArgs values =
        .ok sourceFinal)
    (hScoped : Functions.Scope.ExprSeqScoped live args)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        live frameBase mode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminalArgs kind args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan live frameBase mode mode sourceProgram sourceCtx
        (.terminalArgs kind args) source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx := by
  obtain
      ⟨lowered, code, hLowerArgs, hCompileCode,
        rfl, rfl, rfl, rfl⟩ :=
    AllocationObserverStatement.TerminalLeaf.args_compiler_shape
      hLower hCompile
  obtain ⟨targetAfterArgs, hArgsRun, hArgsRel, hArgsEffect⟩ :=
    AllocationObserverExpression.forwardExprSeqRuntime_with_effect
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hArgs hInvariant.activation.compiler hScoped
      hLowerArgs hCompileCode hInvariant.activation.state
      hInvariant.allocator
  obtain
      ⟨evmFinal, hStep, hHaltRel,
        hMemoryEq, hActive, hFinalNoWrap⟩ :=
    (AllocationObserverTerminal.Invocation.of_memorySafe hMemory).forward_observer
      hArgsRel.state hTerminal hArgsRel.stack
  let targetFinal : Structured.ObserverSemantics.State transcript :=
    targetAfterArgs.withSource
      (targetAfterArgs.source.withEVM evmFinal)
  have hTerminalStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 (.terminal kind) targetAfterArgs
          (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
    simpa [targetFinal,
      Structured.ObserverSemantics.stateModel_withEVM] using
        (Structured.EffectSemantics.Stmt.Eval.terminal
          (model := Structured.ObserverSemantics.stateModel transcript)
          (handler := Structured.ObserverSemantics.handler transcript)
          (program := targetProgram) (fuel := 0) hStep)
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts :=
            [Structured.Stmt.code code, Structured.Stmt.terminal kind] }
        target
        (Structured.EffectSemantics.Outcome.halt kind targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 1) hArgsRun)
      (Structured.EffectSemantics.Block.Eval.cons_halt hTerminalStmt)
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.terminalArgs
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      hArgs hMemory hTerminal).run_eq
  have hTerminalEffect :
      Frame.AllocatorEffect config allocatorDepth
        targetAfterArgs targetFinal :=
    Frame.AllocatorEffect.of_memory_eq_active_growth
      hArgsEffect.ready hMemoryEq hActive hFinalNoWrap
  refine
    ⟨targetFinal, 0, 2, hSource, ?_, ?_,
      .halt kind hHaltRel, SameFrame.refl mode,
      Frame.OutcomeEffect.of_activation
        (Frame.ActivationEffect.of_allocatorEffect
          (hArgsEffect.trans hTerminalEffect))⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget
  · intro hMode
    cases hMode

theorem terminal_of_invariant
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.HaltKind}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe contract kind [])
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind source [] =
        .ok sourceFinal)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        live frameBase mode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminal kind) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan live frameBase mode mode sourceProgram sourceCtx
        (.terminal kind) source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx := by
  obtain
      ⟨hLowered, _hLowerFinal, hCompiled, _hLocalsFinal⟩ :=
    AllocationObserverStatement.TerminalLeaf.compiler_shape
      hLower hCompile
  obtain
      ⟨targetAfterCleanup, hCleanupRun, hCleanupCursor,
        hCleanupStack, hCleanupShared, _hCleanupReturns⟩ :=
    AllocationObserverPreservation.ObserverCode.run_replicate_pop
      localsCtx.layout.length
      (by
        rw [hInvariant.activation.stackLength])
  have hAfterStack : targetAfterCleanup.source.evm.stack = [] := by
    rw [hCleanupStack,
      hInvariant.activation.stackLength.symm]
    exact List.drop_length
  have hAfterCursor : source.cursor = targetAfterCleanup.cursor :=
    hInvariant.activation.state.base.cursor.trans hCleanupCursor.symm
  have hAfterShared :
      SharedRel contract source.source.shared
        targetAfterCleanup.source.evm.toSharedState := by
    rw [hCleanupShared]
    exact hInvariant.activation.state.base.core.shared
  have hAfterNoWrap :
      targetAfterCleanup.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    rw [show
      targetAfterCleanup.source.evm.activeWords =
        target.source.evm.activeWords by
          exact
            congrArg
              (fun shared : EvmYul.SharedState .EVM =>
                shared.toMachineState.activeWords)
              hCleanupShared]
    exact hInvariant.activation.state.activeNoWrap
  obtain
      ⟨evmFinal, hStep, hHaltRel,
        hMemoryEq, hActive, hFinalNoWrap⟩ :=
    (AllocationObserverTerminal.Invocation.of_memorySafe hMemory)
      |>.forward_shared_observer
        (plan := plan) (baseStack := [])
        hAfterCursor hAfterShared hAfterNoWrap hTerminal
        (by simpa using hAfterStack)
  let targetFinal : Structured.ObserverSemantics.State transcript :=
    targetAfterCleanup.withSource
      (targetAfterCleanup.source.withEVM evmFinal)
  have hTerminalStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 (.terminal kind) targetAfterCleanup
          (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
    simpa [targetFinal,
      Structured.ObserverSemantics.stateModel_withEVM] using
        (Structured.EffectSemantics.Stmt.Eval.terminal
          (model := Structured.ObserverSemantics.stateModel transcript)
          (handler := Structured.ObserverSemantics.handler transcript)
          (program := targetProgram) (fuel := 0) hStep)
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts :=
            [Structured.Stmt.code localsCtx.cleanupAll,
              Structured.Stmt.terminal kind] }
        target
        (Structured.EffectSemantics.Outcome.halt kind targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 1) hCleanupRun)
      (Structured.EffectSemantics.Block.Eval.cons_halt hTerminalStmt)
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.terminal
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      hMemory hTerminal).run_eq
  have hCleanupMachine :
      targetAfterCleanup.source.evm.toMachineState =
        target.source.evm.toMachineState :=
    congrArg EvmYul.SharedState.toMachineState hCleanupShared
  have hCleanupEffect :
      Frame.AllocatorEffect config allocatorDepth
        target targetAfterCleanup :=
    Frame.AllocatorEffect.of_machine_eq
      hInvariant.allocator hCleanupMachine
  have hTerminalEffect :
      Frame.AllocatorEffect config allocatorDepth
        targetAfterCleanup targetFinal :=
    Frame.AllocatorEffect.of_memory_eq_active_growth
      hCleanupEffect.ready hMemoryEq hActive hFinalNoWrap
  refine
    ⟨targetFinal, 0, 2, hSource, ?_, ?_,
      .halt kind hHaltRel, SameFrame.refl mode,
      Frame.OutcomeEffect.of_activation
        (Frame.ActivationEffect.of_allocatorEffect
          (hCleanupEffect.trans hTerminalEffect))⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured, Locals.codeStmt, hCompiled,
      hLowered] using hTarget
  · intro hMode
    cases hMode

theorem brk_of_invariant_exact
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : localsCtx.breakDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition plan beforeLive afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        beforeLive frameBase beforeMode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .brk =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan afterLive frameBase beforeMode afterMode sourceProgram sourceCtx
        .brk source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.brk
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source))
        (Structured.EffectSemantics.Outcome.brk targetFinal)
        sourceCtx ∧
      ActivationStateRel contract plan afterLive 0 frameBase afterMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source)
        targetFinal ∧
      targetFinal.source.evm.stack.length = targetDepth ∧
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    AllocationObserverCleanup.BreakLeaf.compiler_shape
      hTargetDepth hLower hCompile
  obtain
      ⟨targetFinal, hCleanupRun, hFinalRel, hFinalStack,
        hMachine⟩ :=
    AllocationObserverCleanup.Plain.forward_exact
      hInvariant.activation.compiler hTransition
      hInvariant.activation.planWF hInvariant.activation.defined
      hInvariant.activation.state hInvariant.activation.stackLength
      hCleanup
  have hBreakStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 .brk targetFinal
          (Structured.EffectSemantics.Outcome.brk targetFinal) :=
    Structured.EffectSemantics.Stmt.Eval.brk
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := [Structured.Stmt.code cleanup, Structured.Stmt.brk] }
        target
        (Structured.EffectSemantics.Outcome.brk targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 1) hCleanupRun)
      (Structured.EffectSemantics.Block.Eval.cons_brk hBreakStmt)
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.brk
      (contract := contract) (transcript := transcript)
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      (source := source) hSourceScope).run_eq
  have hEffect :
      Frame.ActivationEffect config allocatorDepth beforeMode
        target targetFinal :=
    Frame.ActivationEffect.of_allocatorEffect
      (Frame.AllocatorEffect.of_machine_eq
        hInvariant.allocator hMachine)
  refine ⟨targetFinal, ?_, hFinalRel, hFinalStack, hMachine⟩
  refine
    ⟨0, 2, hSource, ?_, ?_, .brk hFinalRel,
      hTransition.sameFrame, Frame.OutcomeEffect.of_activation hEffect⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget
  · intro hMode
    cases hMode

theorem brk_of_invariant
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : localsCtx.breakDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition plan beforeLive afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        beforeLive frameBase beforeMode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .brk =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan afterLive frameBase beforeMode afterMode sourceProgram sourceCtx
        .brk source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.brk
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source))
        (Structured.EffectSemantics.Outcome.brk targetFinal)
        sourceCtx := by
  obtain ⟨targetFinal, hForward, _hState, _hStack, _hMachine⟩ :=
    brk_of_invariant_exact hSourceScope hTargetDepth hTransition hInvariant
      hLower hCompile
  exact ⟨targetFinal, hForward⟩

theorem cont_of_invariant_exact
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : localsCtx.continueDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition plan beforeLive afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        beforeLive frameBase beforeMode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .cont =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan afterLive frameBase beforeMode afterMode sourceProgram sourceCtx
        .cont source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.cont
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source))
        (Structured.EffectSemantics.Outcome.cont targetFinal)
        sourceCtx ∧
      ActivationStateRel contract plan afterLive 0 frameBase afterMode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source)
        targetFinal ∧
      targetFinal.source.evm.stack.length = targetDepth ∧
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    AllocationObserverCleanup.ContinueLeaf.compiler_shape
      hTargetDepth hLower hCompile
  obtain
      ⟨targetFinal, hCleanupRun, hFinalRel, hFinalStack,
        hMachine⟩ :=
    AllocationObserverCleanup.Plain.forward_exact
      hInvariant.activation.compiler hTransition
      hInvariant.activation.planWF hInvariant.activation.defined
      hInvariant.activation.state hInvariant.activation.stackLength
      hCleanup
  have hContinueStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 .cont targetFinal
          (Structured.EffectSemantics.Outcome.cont targetFinal) :=
    Structured.EffectSemantics.Stmt.Eval.cont
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := [Structured.Stmt.code cleanup, Structured.Stmt.cont] }
        target
        (Structured.EffectSemantics.Outcome.cont targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 1) hCleanupRun)
      (Structured.EffectSemantics.Block.Eval.cons_cont hContinueStmt)
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.cont
      (contract := contract) (transcript := transcript)
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      (source := source) hSourceScope).run_eq
  have hEffect :
      Frame.ActivationEffect config allocatorDepth beforeMode
        target targetFinal :=
    Frame.ActivationEffect.of_allocatorEffect
      (Frame.AllocatorEffect.of_machine_eq
        hInvariant.allocator hMachine)
  refine ⟨targetFinal, ?_, hFinalRel, hFinalStack, hMachine⟩
  refine
    ⟨0, 2, hSource, ?_, ?_, .cont hFinalRel,
      hTransition.sameFrame, Frame.OutcomeEffect.of_activation hEffect⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget
  · intro hMode
    cases hMode

theorem cont_of_invariant
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : localsCtx.continueDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition plan beforeLive afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        beforeLive frameBase beforeMode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .cont =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan afterLive frameBase beforeMode afterMode sourceProgram sourceCtx
        .cont source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.cont
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source))
        (Structured.EffectSemantics.Outcome.cont targetFinal)
        sourceCtx := by
  obtain ⟨targetFinal, hForward, _hState, _hStack, _hMachine⟩ :=
    cont_of_invariant_exact hSourceScope hTargetDepth hTransition hInvariant
      hLower hCompile
  exact ⟨targetFinal, hForward⟩

end NonregularStmtRuntimeForward

namespace BlockRuntimeForward

theorem nil
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        live frameBase mode source target) :
    BlockRuntimeForward contract config allocatorDepth transcript plan live
      frameBase mode mode sourceProgram sourceCtx { stmts := [] } source
      targetProgram { stmts := [] } target
      (Functions.Source.Effectful.Outcome.regular source)
      (Structured.EffectSemantics.Outcome.regular target) sourceCtx := by
  exact
    ⟨1, 1,
      by simp [Functions.Source.Effectful.Block.runOpen],
      Structured.EffectSemantics.Block.Eval.nil,
      ActivationOutcomeRel.regular hInvariant.activation.state,
      SameFrame.refl mode,
      Frame.OutcomeEffect.of_activation
        (Frame.ActivationEffect.refl hInvariant.allocator)⟩

theorem cons_regular
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {midState : AllocationLowering.State}
    {midLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {midLive finalLive : List Locals.Name}
    {frameBase : Nat}
    {initialMode midMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx midCtx finalCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {source sourceMid : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target targetMid : Structured.ObserverSemantics.State transcript}
    {compiledHead compiledTail : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hHead :
      AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
        contract config allocatorDepth transcript lowerCtx midState midLocals
        plan midLive frameBase initialMode midMode sourceProgram sourceCtx stmt
        source targetProgram target compiledHead sourceMid targetMid midCtx)
    (hTail :
      BlockRuntimeForward contract config allocatorDepth transcript plan
        finalLive frameBase midMode finalMode sourceProgram midCtx
        { stmts := rest } sourceMid targetProgram
        { stmts := compiledTail } targetMid sourceOutcome targetOutcome
        finalCtx) :
    BlockRuntimeForward contract config allocatorDepth transcript plan
      finalLive frameBase initialMode finalMode sourceProgram sourceCtx
      { stmts := stmt :: rest } source targetProgram
      { stmts := compiledHead ++ compiledTail } target sourceOutcome
      targetOutcome finalCtx := by
  rcases hHead with
    ⟨headSourceFuel, headTargetFuel, hHeadSource, hHeadTarget,
      _hHeadInvariant, hHeadSame, hHeadEffect⟩
  rcases hTail with
    ⟨tailSourceFuel, tailTargetFuel, hTailSource, hTailTarget,
      hTailRel, hTailSame, hTailEffect⟩
  obtain ⟨sourceFuel, hSourceRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hHeadSource hTailSource
  obtain ⟨targetFuel, hTargetRun⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hHeadTarget hTailTarget
  exact
    ⟨sourceFuel, targetFuel, hSourceRun, hTargetRun, hTailRel,
      hHeadSame.trans hTailSame,
      Frame.OutcomeEffect.prepend_activation
        hHeadEffect hHeadSame hTailEffect⟩

theorem cons_nonregular
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {finalLive : List Locals.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiledHead compiledTail : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hHead :
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan finalLive frameBase initialMode finalMode sourceProgram sourceCtx
        stmt source targetProgram target compiledHead sourceOutcome
        targetOutcome stmtCtx) :
    BlockRuntimeForward contract config allocatorDepth transcript plan
      finalLive frameBase initialMode finalMode sourceProgram sourceCtx
      { stmts := stmt :: rest } source targetProgram
      { stmts := compiledHead ++ compiledTail } target sourceOutcome
      targetOutcome sourceCtx := by
  rcases hHead with
    ⟨sourceFuel, targetFuel, hSource, hTarget, hSourceMode, hRel,
      hSame, hEffect⟩
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hRel.target_nonregular hSourceMode
  exact
    ⟨sourceFuel + 1, targetFuel,
      Functions.Source.Effectful.Block.runOpen_cons_nonregular
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSource hSourceMode,
      Structured.EffectSemantics.Block.Eval.append_nonregular
        hTarget hTargetMode,
      hRel, hSame, hEffect⟩

end BlockRuntimeForward

/--
Every source control destination visible at a recursive statement boundary is
contained in the currently live lexical environment.

The return fields also retain the two facts needed by source `leave`: return
names are live now, and the declared leave scope contains them. This is source
context data, not compiler-generated evidence.
-/
structure ControlScopesWithin
    (returns live : List Functions.Name)
    (ctx : Functions.Source.Ctx) : Prop where
  breakScope :
    ∀ scope,
      ctx.breakScope? = some scope →
        ∀ name, name ∈ scope → name ∈ live
  continueScope :
    ∀ scope,
      ctx.continueScope? = some scope →
        ∀ name, name ∈ scope → name ∈ live
  returnsLive :
    ∀ name, name ∈ returns → name ∈ live
  leaveScope :
    ∀ scope,
      ctx.leaveScope? = some scope →
        ∀ name, name ∈ returns → name ∈ scope

namespace ControlScopesWithin

theorem mono
    {returns beforeLive afterLive : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns beforeLive ctx)
    (hSubset :
      ∀ name, name ∈ beforeLive → name ∈ afterLive) :
    ControlScopesWithin returns afterLive ctx := by
  refine
    { breakScope := ?_
      continueScope := ?_
      returnsLive := ?_
      leaveScope := hControl.leaveScope }
  · intro scope hScope name hName
    exact hSubset name
      (hControl.breakScope scope hScope name hName)
  · intro scope hScope name hName
    exact hSubset name
      (hControl.continueScope scope hScope name hName)
  · intro name hName
    exact hSubset name (hControl.returnsLive name hName)

theorem outcomeLive_subset
    {returns live : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns live ctx)
    (mode : Locals.Source.Mode) :
    ∀ name,
      name ∈ outcomeLive returns live ctx mode →
        name ∈ live := by
  intro name hName
  cases mode with
  | regular =>
      exact hName
  | brk =>
      cases hBreak : ctx.breakScope? with
      | none =>
          simp [outcomeLive, hBreak] at hName
      | some scope =>
          exact
            hControl.breakScope scope hBreak name
              (by simpa [outcomeLive, hBreak] using hName)
  | cont =>
      cases hContinue : ctx.continueScope? with
      | none =>
          simp [outcomeLive, hContinue] at hName
      | some scope =>
          exact
            hControl.continueScope scope hContinue name
              (by simpa [outcomeLive, hContinue] using hName)
  | leave =>
      exact hControl.returnsLive name hName
  | halt kind =>
      exact hName

theorem push
    {returns live : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns live ctx)
    (name : Functions.Name) :
    ControlScopesWithin returns (name :: live)
      { ctx with scope := name :: ctx.scope } := by
  refine
    { breakScope := ?_
      continueScope := ?_
      returnsLive := ?_
      leaveScope := ?_ }
  · intro scope hScope localName hLocal
    exact List.mem_cons_of_mem name
      (hControl.breakScope scope hScope localName hLocal)
  · intro scope hScope localName hLocal
    exact List.mem_cons_of_mem name
      (hControl.continueScope scope hScope localName hLocal)
  · intro returnName hReturn
    exact List.mem_cons_of_mem name
      (hControl.returnsLive returnName hReturn)
  · exact hControl.leaveScope

theorem functionBody
    (fn : Functions.FunDef) :
    ControlScopesWithin fn.returns
      (fn.returns.reverse ++ fn.params.reverse)
      (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
  refine
    { breakScope := ?_
      continueScope := ?_
      returnsLive := ?_
      leaveScope := ?_ }
  · intro scope hScope
    simp [Functions.Source.Effectful.FunDef.bodyCtx,
      Functions.Source.Ctx.initial,
      Functions.Source.Ctx.withLeaveScope] at hScope
  · intro scope hScope
    simp [Functions.Source.Effectful.FunDef.bodyCtx,
      Functions.Source.Ctx.initial,
      Functions.Source.Ctx.withLeaveScope] at hScope
  · intro name hName
    apply List.mem_append_left
    simpa using hName
  · intro scope hScope name hName
    have hEq :
        scope = fn.returns ++ fn.params := by
      simpa [Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial,
        Functions.Source.Ctx.withLeaveScope] using hScope.symm
    rw [hEq]
    exact List.mem_append_left _ hName

/--
Disabling loop control preserves every source control-scope obligation.

The break and continue fields become unavailable, while return liveness and
the function leave scope are unchanged.
-/
theorem withoutLoopControl
    {returns live : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns live ctx) :
    ControlScopesWithin returns live ctx.withoutLoopControl := by
  refine
    { breakScope := ?_
      continueScope := ?_
      returnsLive := hControl.returnsLive
      leaveScope := ?_ }
  · intro scope hScope
    simp [Functions.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    simp [Functions.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope name hName
    exact
      hControl.leaveScope scope
        (by
          simpa [Functions.Source.Ctx.withoutLoopControl] using hScope)
        name hName

/--
Install the canonical loop-entry break and continue scopes.

Both loop-control destinations are the current live environment; function
return liveness and the enclosing leave scope are preserved.
-/
theorem withLoopControl
    {returns live : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns live ctx)
    (hSourceScope : ∀ name, name ∈ ctx.scope ↔ name ∈ live) :
    ControlScopesWithin returns live
      (ctx.withLoopControl ctx.scope ctx.scope) := by
  refine
    { breakScope := ?_
      continueScope := ?_
      returnsLive := hControl.returnsLive
      leaveScope := ?_ }
  · intro scope hScope name hName
    have hEq : scope = ctx.scope := by
      simpa [Functions.Source.Ctx.withLoopControl] using hScope.symm
    exact (hSourceScope name).mp (by simpa [hEq] using hName)
  · intro scope hScope name hName
    have hEq : scope = ctx.scope := by
      simpa [Functions.Source.Ctx.withLoopControl] using hScope.symm
    exact (hSourceScope name).mp (by simpa [hEq] using hName)
  · intro scope hScope name hName
    exact
      hControl.leaveScope scope
        (by
          simpa [Functions.Source.Ctx.withLoopControl] using hScope)
        name hName

end ControlScopesWithin

namespace SameControl

theorem outcomeLive_eq_of_nonregular
    {returns regularLive : List Functions.Name}
    {before after : Functions.Source.Ctx}
    {mode : Locals.Source.Mode}
    (hControl : SameControl before after)
    (hMode : mode ≠ .regular) :
    outcomeLive returns regularLive before mode =
      outcomeLive returns regularLive after mode := by
  cases mode with
  | regular => exact False.elim (hMode rfl)
  | brk => simp [outcomeLive, hControl.breakScope]
  | cont => simp [outcomeLive, hControl.continueScope]
  | leave => rfl
  | halt => rfl

theorem controlScopesWithin
    {returns live : List Functions.Name}
    {before after : Functions.Source.Ctx}
    (hControl : SameControl before after)
    (hWithin : ControlScopesWithin returns live before) :
    ControlScopesWithin returns live after := by
  refine
    { breakScope := ?_
      continueScope := ?_
      returnsLive := hWithin.returnsLive
      leaveScope := ?_ }
  · intro scope hScope name hName
    exact
      hWithin.breakScope scope
        (hControl.breakScope.trans hScope) name hName
  · intro scope hScope name hName
    exact
      hWithin.continueScope scope
        (hControl.continueScope.trans hScope) name hName
  · intro scope hScope name hName
    exact
      hWithin.leaveScope scope
        (hControl.leaveScope.trans hScope) name hName

theorem controlScopesWithin_outEnv
    {returns live : List Functions.Name}
    {before after : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    (hControl : SameControl before after)
    (hWithin : ControlScopesWithin returns live before) :
    ControlScopesWithin returns
      (Functions.Scope.Stmt.outEnv live stmt) after := by
  apply hControl.controlScopesWithin
  exact
    hWithin.mono
      (fun name hName =>
        Functions.Scope.Stmt.mem_outEnv hName)

end SameControl

/--
The two loop-control destinations tracked by the recursive Functions
dispatcher.
-/
inductive ControlKind where
  | brk
  | cont

namespace ControlKind

def sourceScope? :
    ControlKind → Functions.Source.Ctx → Option (List Functions.Name)
  | .brk, ctx => ctx.breakScope?
  | .cont, ctx => ctx.continueScope?

def targetDepth? :
    ControlKind → Locals.Ctx → Option Nat
  | .brk, ctx => ctx.breakDepth?
  | .cont, ctx => ctx.continueDepth?

end ControlKind

/--
Static allocation destination underlying one available `break` or `continue`.

The destination retains the adjacent compiler context rather than a cleanup
transition. Declarations and lexical scopes can therefore extend the current
state, and the exact transition is constructed only at the abrupt leaf through
`AllocationObserverCleanup.Plain.transition_of_stateExtends`.
-/
structure ControlDestination
    (lowerCtx : AllocationLowering.Ctx)
    (currentState : AllocationLowering.State)
    (currentPlan : Locals.Allocation.Plan)
    (currentLive : List Functions.Name)
    (currentMode : ActivationMode) where
  state : AllocationLowering.State
  locals : Locals.Ctx
  plan : Locals.Allocation.Plan
  live : List Functions.Name
  mode : ActivationMode
  compiler :
    AllocationObserverContext.ActivationExprContext
      lowerCtx state locals plan live mode
  planWF :
    plan.WellFormed
  subset :
    ∀ name, name ∈ live → name ∈ currentLive
  sameFrame : SameFrame currentMode mode
  stateExtends :
    AllocationLowering.StateExtends live state currentState

namespace ControlDestination

def transport
    {lowerCtx : AllocationLowering.Ctx}
    {currentState nextState : AllocationLowering.State}
    {currentPlan nextPlan : Locals.Allocation.Plan}
    {currentLive nextLive : List Functions.Name}
    {currentMode nextMode : ActivationMode}
    (hDestination :
      ControlDestination lowerCtx currentState currentPlan currentLive
        currentMode)
    (hState :
      AllocationLowering.StateExtends
        currentLive currentState nextState)
    (hLive :
      ∀ name, name ∈ currentLive → name ∈ nextLive)
    (hMode : SameFrame currentMode nextMode) :
    ControlDestination lowerCtx nextState nextPlan nextLive nextMode :=
  { state := hDestination.state
    locals := hDestination.locals
    plan := hDestination.plan
    live := hDestination.live
    mode := hDestination.mode
    compiler := hDestination.compiler
    planWF := hDestination.planWF
    subset := fun name hName =>
      hLive name (hDestination.subset name hName)
    sameFrame := hMode.symm.trans hDestination.sameFrame
    stateExtends :=
      hDestination.stateExtends.trans hState hDestination.subset }

theorem exists_transition
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive : List Functions.Name}
    {currentMode : ActivationMode}
    (hDestination :
      ControlDestination lowerCtx currentState currentPlan currentLive
        currentMode)
    (hCurrent :
      AllocationObserverContext.ActivationExprContext
        lowerCtx currentState currentLocals currentPlan currentLive currentMode) :
    ∃ hTransition :
        AllocationObserverCleanup.Transition currentPlan currentLive
          hDestination.live hDestination.locals.layout.length
          currentMode hDestination.mode,
      True := by
  obtain ⟨hTransition, _hLayout, _hSlots⟩ :=
    AllocationObserverCleanup.Plain.transition_of_stateExtends
      hCurrent hDestination.compiler hDestination.subset
      hDestination.sameFrame rfl hDestination.stateExtends
  exact ⟨hTransition, trivial⟩

end ControlDestination

/--
The exact pass-owned cleanup artifact selected by one available source control
destination.

The transition stays indexed by the destination's canonical live ordering.
Source semantics may present an extensionally equal ordering; abrupt statement
preservation reindexes the transition only at the leaf. `restoredCompiler` and
`planAgree` retain the facts needed to rebuild the destination runtime
invariant after that cleanup.
-/
structure ControlTransitionArtifact
    (kind : ControlKind)
    (lowerCtx : AllocationLowering.Ctx)
    (currentState : AllocationLowering.State)
    (currentLocals : Locals.Ctx)
    (currentPlan : Locals.Allocation.Plan)
    (currentLive : List Functions.Name)
    (currentMode : ActivationMode)
    (sourceCtx : Functions.Source.Ctx)
    (afterLive : List Functions.Name) where
  destination :
    ControlDestination lowerCtx currentState currentPlan currentLive
      currentMode
  sourceEquivalent :
    ∀ name, name ∈ afterLive ↔ name ∈ destination.live
  target :
    kind.targetDepth? currentLocals =
      some destination.locals.layout.length
  transition :
    AllocationObserverCleanup.Transition currentPlan currentLive
      destination.live destination.locals.layout.length currentMode
      destination.mode
  restoredCompiler :
    AllocationObserverContext.ActivationExprContext
      lowerCtx destination.state destination.locals currentPlan
      destination.live destination.mode
  planAgree :
    PlanAgreesOn currentPlan destination.plan destination.live

namespace ControlTransitionArtifact

/--
Rebuild the complete runtime invariant at a canonical control destination after
the compiler-emitted plain cleanup has run.

The target execution facts are exactly those proved by the cleanup owner:
outcome state relation, exact destination stack depth, and unchanged machine
state. The allocation artifact supplies the destination compiler context and
plan agreement.
-/
theorem runtimeInvariant
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive afterLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (artifact :
      ControlTransitionArtifact kind lowerCtx currentState currentLocals
        currentPlan currentLive currentMode sourceCtx afterLive)
    (hInitial :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx currentState currentLocals
        currentPlan currentLive frameBase currentMode source target)
    (hState :
      ActivationStateRel contract currentPlan afterLive 0 frameBase
        artifact.destination.mode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source)
        targetFinal)
    (hStack :
      targetFinal.source.evm.stack.length =
        artifact.destination.locals.layout.length)
    (hMachine :
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState) :
    AllocationObserverContext.ActivationRuntimeInvariant
      contract config allocatorDepth lowerCtx artifact.destination.state
      artifact.destination.locals artifact.destination.plan
      artifact.destination.live frameBase artifact.destination.mode
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        afterLive source)
      targetFinal := by
  have hRestrict :
      (Functions.ObserverSemantics.stateModel transcript).restrictTo
          artifact.destination.live source =
        (Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source :=
    Locals.Source.Effectful.StateModel.restrictTo_congr
      (Functions.ObserverSemantics.stateModel transcript)
      (fun name => (artifact.sourceEquivalent name).symm)
  have hDefined :
      LiveDefined artifact.destination.live
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source).source := by
    have hRestricted :=
      hInitial.activation.defined.restrictTo artifact.destination.subset
    have hRestrictSource :=
      congrArg
        (fun state : Functions.ObserverSemantics.State transcript =>
          state.source)
        hRestrict
    change
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          artifact.destination.live source).source =
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source).source at hRestrictSource
    rw [← hRestrictSource]
    exact hRestricted
  have hDestinationState :
      ActivationStateRel contract artifact.destination.plan
        artifact.destination.live 0 frameBase artifact.destination.mode
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source)
        targetFinal := by
    exact
      (hState.reindex_live
        (fun name => (artifact.sourceEquivalent name).symm)).transport_plan
          artifact.planAgree
  exact
    { activation :=
        { compiler :=
            artifact.restoredCompiler.transport_plan artifact.planAgree
          planWF := artifact.destination.planWF
          defined := hDefined
          state := hDestinationState
          stackLength := hStack }
      allocator := hInitial.allocator.of_machine_eq hMachine
      frame := hInitial.frame.sameFrame artifact.transition.sameFrame }

end ControlTransitionArtifact

/--
Source/Locals synchronization for one loop-control kind at a recursive
statement boundary.

Unavailable bindings prove that both semantics reject the abrupt statement.
Available bindings point to the pass-owned destination context from which the
exact cleanup transition is derived.
-/
inductive ControlBinding
    (kind : ControlKind)
    (lowerCtx : AllocationLowering.Ctx)
    (currentState : AllocationLowering.State)
    (currentLocals : Locals.Ctx)
    (currentPlan : Locals.Allocation.Plan)
    (currentLive : List Functions.Name)
    (currentMode : ActivationMode)
    (sourceCtx : Functions.Source.Ctx) : Type where
  | unavailable
      (source :
        kind.sourceScope? sourceCtx = none)
      (target :
        kind.targetDepth? currentLocals = none) :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx
  | available
      (destination :
        ControlDestination lowerCtx currentState currentPlan currentLive
          currentMode)
      (sourceLive : List Functions.Name)
      (source :
        kind.sourceScope? sourceCtx = some sourceLive)
      (sourceEquivalent :
        ∀ name, name ∈ sourceLive ↔ name ∈ destination.live)
      (target :
        kind.targetDepth? currentLocals =
          some destination.locals.layout.length) :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx

namespace ControlTransitionArtifact

def OwnedBy
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive afterLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    (artifact :
      ControlTransitionArtifact kind lowerCtx currentState currentLocals
        currentPlan currentLive currentMode sourceCtx afterLive)
    (binding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx) : Prop :=
  ∃ hSource : kind.sourceScope? sourceCtx = some afterLive,
    binding =
      .available artifact.destination afterLive hSource
        artifact.sourceEquivalent artifact.target

end ControlTransitionArtifact

namespace ControlBinding

/--
The complete runtime invariant at the canonical destination selected by one
available control binding.

Unavailable bindings reduce to `False`. Available bindings expose only the
destination owned by the adjacent allocation/Locals pass; no cleanup code or
target execution evidence is stored here.
-/
def DestinationRuntimeInvariant
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    (binding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx)
    (sourceFinal : Functions.ObserverSemantics.State transcript)
    (targetFinal : Structured.ObserverSemantics.State transcript) : Prop :=
  ∃ (destination :
        ControlDestination lowerCtx currentState currentPlan currentLive
          currentMode)
      (sourceLive : List Functions.Name)
      (source : kind.sourceScope? sourceCtx = some sourceLive)
      (sourceEquivalent :
        ∀ name, name ∈ sourceLive ↔ name ∈ destination.live)
      (target :
        kind.targetDepth? currentLocals =
          some destination.locals.layout.length),
    binding =
      .available destination sourceLive source sourceEquivalent target ∧
    AllocationObserverContext.ActivationRuntimeInvariant
      contract config allocatorDepth lowerCtx destination.state
      destination.locals destination.plan destination.live frameBase
      destination.mode sourceFinal targetFinal

/--
The canonical control destination under the compiler-selected resource mode.
-/
def DestinationResourceInvariant
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    (binding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx)
    (sourceFinal : Functions.ObserverSemantics.State transcript)
    (targetFinal : Structured.ObserverSemantics.State transcript) : Prop :=
  ∃ (destination :
        ControlDestination lowerCtx currentState currentPlan currentLive
          currentMode)
      (sourceLive : List Functions.Name)
      (source : kind.sourceScope? sourceCtx = some sourceLive)
      (sourceEquivalent :
        ∀ name, name ∈ sourceLive ↔ name ∈ destination.live)
      (target :
        kind.targetDepth? currentLocals =
          some destination.locals.layout.length),
    binding =
      .available destination sourceLive source sourceEquivalent target ∧
    AllocationObserverContext.ActivationResourceInvariant
      resource contract allocatorDepth lowerCtx destination.state
      destination.locals destination.plan destination.live frameBase
      destination.mode sourceFinal targetFinal

namespace DestinationRuntimeInvariant

/-- Lift the existing scratch-backed destination invariant. -/
theorem toResource
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {binding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx}
    {sourceFinal : Functions.ObserverSemantics.State transcript}
    {targetFinal : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      DestinationRuntimeInvariant
        (contract := contract) (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        binding sourceFinal targetFinal) :
    DestinationResourceInvariant
      (contract := contract) (resource := .scratch config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      binding sourceFinal targetFinal := by
  rcases hInvariant with
    ⟨destination, sourceLive, source, sourceEquivalent, target,
      hBinding, hRuntime⟩
  exact
    ⟨destination, sourceLive, source, sourceEquivalent, target, hBinding,
      AllocationObserverContext.ActivationResourceInvariant.scratch
        hRuntime⟩

theorem available
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    (destination :
      ControlDestination lowerCtx currentState currentPlan currentLive
        currentMode)
    (sourceLive : List Functions.Name)
    (source :
      kind.sourceScope? sourceCtx = some sourceLive)
    (sourceEquivalent :
      ∀ name, name ∈ sourceLive ↔ name ∈ destination.live)
    (target :
      kind.targetDepth? currentLocals =
        some destination.locals.layout.length)
    {sourceFinal : Functions.ObserverSemantics.State transcript}
    {targetFinal : Structured.ObserverSemantics.State transcript}
    (invariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx destination.state
        destination.locals destination.plan destination.live frameBase
        destination.mode sourceFinal targetFinal) :
    DestinationRuntimeInvariant
      (contract := contract) (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (.available destination sourceLive source sourceEquivalent target)
      sourceFinal targetFinal :=
  by
    exact
      ⟨destination, sourceLive, source, sourceEquivalent, target, rfl,
        invariant⟩

theorem of_artifact
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive afterLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {sourceFinal : Functions.ObserverSemantics.State transcript}
    {targetFinal : Structured.ObserverSemantics.State transcript}
    {binding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx}
    (artifact :
      ControlTransitionArtifact kind lowerCtx currentState currentLocals
        currentPlan currentLive currentMode sourceCtx afterLive)
    (hOwned : artifact.OwnedBy binding)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx artifact.destination.state
        artifact.destination.locals artifact.destination.plan
        artifact.destination.live frameBase artifact.destination.mode
        sourceFinal targetFinal) :
    DestinationRuntimeInvariant
      (contract := contract) (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      binding sourceFinal targetFinal := by
  obtain ⟨hSource, rfl⟩ := hOwned
  exact
    available artifact.destination afterLive hSource
      artifact.sourceEquivalent artifact.target hInvariant

end DestinationRuntimeInvariant

/--
Recover the canonical destination cleanup selected by a successful source
`break` or `continue`.

All compiler facts come from the adjacent allocation and Locals passes. The
artifact contains no target run or observer-specific generated code.
-/
theorem transitionArtifact_of_source
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive afterLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    (hBinding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx)
    (hCurrent :
      AllocationObserverContext.ActivationExprContext
        lowerCtx currentState currentLocals currentPlan currentLive
        currentMode)
    (hSource :
      kind.sourceScope? sourceCtx = some afterLive) :
    ∃ artifact :
        ControlTransitionArtifact kind lowerCtx currentState currentLocals
          currentPlan currentLive currentMode sourceCtx afterLive,
      artifact.OwnedBy hBinding := by
  cases hBinding with
  | unavailable hNone _hTarget =>
      rw [hNone] at hSource
      contradiction
  | available hDestination sourceLive hDestinationSource hEquivalent hTarget =>
      have hLive : afterLive = sourceLive :=
        Option.some.inj (hSource.symm.trans hDestinationSource)
      subst afterLive
      obtain ⟨hTransition, hLayout, hSlots⟩ :=
        AllocationObserverCleanup.Plain.transition_of_stateExtends
          hCurrent hDestination.compiler hDestination.subset
          hDestination.sameFrame rfl hDestination.stateExtends
      obtain ⟨hRestored, hPlanAgree⟩ :=
        AllocationObserverCleanup.Plain.restore_context
          hCurrent hDestination.compiler hTransition hLayout hSlots
      exact
        ⟨{ destination := hDestination
           sourceEquivalent := hEquivalent
           target := hTarget
           transition := hTransition
           restoredCompiler := hRestored
           planAgree := hPlanAgree },
          hDestinationSource, rfl⟩

theorem transition_of_source
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive afterLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    (hBinding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx)
    (hCurrent :
      AllocationObserverContext.ActivationExprContext
        lowerCtx currentState currentLocals currentPlan currentLive
        currentMode)
    (hSource :
      kind.sourceScope? sourceCtx = some afterLive) :
    ∃ targetDepth afterMode,
      kind.targetDepth? currentLocals = some targetDepth ∧
      ∃ hTransition :
          AllocationObserverCleanup.Transition currentPlan currentLive
            afterLive targetDepth currentMode afterMode,
        True := by
  cases hBinding with
  | unavailable hNone _hTarget =>
      rw [hNone] at hSource
      contradiction
  | available hDestination sourceLive hDestinationSource hEquivalent hTarget =>
      have hLive : afterLive = sourceLive :=
        Option.some.inj (hSource.symm.trans hDestinationSource)
      subst afterLive
      obtain ⟨hTransition, _hTrue⟩ :=
        hDestination.exists_transition hCurrent
      exact
        ⟨hDestination.locals.layout.length, hDestination.mode,
          hTarget,
          hTransition.reindex_after (fun name => (hEquivalent name).symm),
          trivial⟩

def transport
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState nextState : AllocationLowering.State}
    {currentLocals nextLocals : Locals.Ctx}
    {currentPlan nextPlan : Locals.Allocation.Plan}
    {currentLive nextLive : List Functions.Name}
    {currentMode nextMode : ActivationMode}
    {sourceCtx nextSourceCtx : Functions.Source.Ctx}
    (hBinding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx)
    (hSourceControl : SameControl sourceCtx nextSourceCtx)
    (hLocalsControl : Locals.Ctx.SameControl currentLocals nextLocals)
    (hState :
      AllocationLowering.StateExtends
        currentLive currentState nextState)
    (hLive :
      ∀ name, name ∈ currentLive → name ∈ nextLive)
    (hMode : SameFrame currentMode nextMode) :
    ControlBinding kind lowerCtx nextState nextLocals nextPlan
      nextLive nextMode nextSourceCtx := by
  cases kind with
  | brk =>
      cases hBinding with
      | unavailable hSource hTarget =>
          exact
            .unavailable
              (by
                change nextSourceCtx.breakScope? = none
                rw [← hSourceControl.breakScope]
                exact hSource)
              (by
                change nextLocals.breakDepth? = none
                rw [← hLocalsControl.breakDepth]
                exact hTarget)
      | available hDestination sourceLive hSource hEquivalent hTarget =>
        have hNextSource :
            nextSourceCtx.breakScope? =
                some sourceLive := by
          rw [← hSourceControl.breakScope]
          exact hSource
        have hNextTarget :
            nextLocals.breakDepth? =
              some hDestination.locals.layout.length := by
          rw [← hLocalsControl.breakDepth]
          exact hTarget
        exact
          .available
            (hDestination.transport hState hLive hMode)
            sourceLive
            (by
              simpa [ControlKind.sourceScope?,
                ControlDestination.transport] using hNextSource)
            hEquivalent
            (by
              simpa [ControlKind.targetDepth?,
                ControlDestination.transport] using hNextTarget)
  | cont =>
      cases hBinding with
      | unavailable hSource hTarget =>
          exact
            .unavailable
              (by
                change nextSourceCtx.continueScope? = none
                rw [← hSourceControl.continueScope]
                exact hSource)
              (by
                change nextLocals.continueDepth? = none
                rw [← hLocalsControl.continueDepth]
                exact hTarget)
      | available hDestination sourceLive hSource hEquivalent hTarget =>
        have hNextSource :
            nextSourceCtx.continueScope? =
                some sourceLive := by
          rw [← hSourceControl.continueScope]
          exact hSource
        have hNextTarget :
            nextLocals.continueDepth? =
              some hDestination.locals.layout.length := by
          rw [← hLocalsControl.continueDepth]
          exact hTarget
        exact
          .available
            (hDestination.transport hState hLive hMode)
            sourceLive
            (by
              simpa [ControlKind.sourceScope?,
                ControlDestination.transport] using hNextSource)
            hEquivalent
            (by
              simpa [ControlKind.targetDepth?,
                ControlDestination.transport] using hNextTarget)

namespace DestinationRuntimeInvariant

/--
Forget the current recursive statement context after a transported binding has
reached its unchanged canonical destination.

`ControlDestination.transport` changes only the current context used to derive
cleanup; the destination state, Locals context, plan, live set, and mode remain
definitionally the same.
-/
theorem of_transport
    {kind : ControlKind}
    {lowerCtx : AllocationLowering.Ctx}
    {currentState nextState : AllocationLowering.State}
    {currentLocals nextLocals : Locals.Ctx}
    {currentPlan nextPlan : Locals.Allocation.Plan}
    {currentLive nextLive : List Functions.Name}
    {currentMode nextMode : ActivationMode}
    {sourceCtx nextSourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {sourceFinal : Functions.ObserverSemantics.State transcript}
    {targetFinal : Structured.ObserverSemantics.State transcript}
    (binding :
      ControlBinding kind lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx)
    (hSourceControl : SameControl sourceCtx nextSourceCtx)
    (hLocalsControl : Locals.Ctx.SameControl currentLocals nextLocals)
    (hState :
      AllocationLowering.StateExtends currentLive currentState nextState)
    (hLive :
      ∀ name, name ∈ currentLive → name ∈ nextLive)
    (hMode : SameFrame currentMode nextMode)
    (hInvariant :
      DestinationRuntimeInvariant
        (contract := contract) (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (ControlBinding.transport
          (currentPlan := currentPlan) (nextPlan := nextPlan)
          binding hSourceControl hLocalsControl hState hLive hMode)
        sourceFinal targetFinal) :
    DestinationRuntimeInvariant
      (contract := contract) (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      binding sourceFinal targetFinal := by
  obtain
    ⟨transportedDestination, transportedSourceLive, transportedSource,
      transportedEquivalent, transportedTarget, hBinding, hDestinationInvariant⟩ :=
    hInvariant
  cases kind with
  | brk =>
      cases binding with
      | unavailable _ _ =>
          simp [ControlBinding.transport] at hBinding
      | available destination sourceLive source sourceEquivalent target =>
          have hDestination :
              destination.transport hState hLive hMode =
                transportedDestination := by
            injection hBinding
          subst transportedDestination
          exact
            available destination sourceLive source sourceEquivalent target
              (by
                simpa [ControlDestination.transport] using
                  hDestinationInvariant)
  | cont =>
      cases binding with
      | unavailable _ _ =>
          simp [ControlBinding.transport] at hBinding
      | available destination sourceLive source sourceEquivalent target =>
          have hDestination :
              destination.transport hState hLive hMode =
                transportedDestination := by
            injection hBinding
          subst transportedDestination
          exact
            available destination sourceLive source sourceEquivalent target
              (by
                simpa [ControlDestination.transport] using
                  hDestinationInvariant)

end DestinationRuntimeInvariant

end ControlBinding

/--
Both loop-control bindings threaded by source-fuel statement/block recursion.
-/
structure ControlDestinations
    (lowerCtx : AllocationLowering.Ctx)
    (currentState : AllocationLowering.State)
    (currentLocals : Locals.Ctx)
    (currentPlan : Locals.Allocation.Plan)
    (currentLive : List Functions.Name)
    (currentMode : ActivationMode)
    (sourceCtx : Functions.Source.Ctx) where
  brk :
    ControlBinding .brk lowerCtx currentState currentLocals currentPlan
      currentLive currentMode sourceCtx
  cont :
    ControlBinding .cont lowerCtx currentState currentLocals currentPlan
      currentLive currentMode sourceCtx

namespace ControlDestinations

def withoutLoopControl
    {lowerCtx : AllocationLowering.Ctx}
    {currentState : AllocationLowering.State}
    {currentLocals : Locals.Ctx}
    {currentPlan : Locals.Allocation.Plan}
    {currentLive : List Functions.Name}
    {currentMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx} :
    ControlDestinations lowerCtx currentState
      currentLocals.withoutLoopControl currentPlan currentLive currentMode
      sourceCtx.withoutLoopControl :=
  { brk := .unavailable rfl rfl
    cont := .unavailable rfl rfl }

/--
The loop body targets the activation immediately after the initializer.

Post lowering may advance the fresh-slot cursor, but scoped lowering restores
the loop-entry environment and layout. Both `break` and `continue` therefore
derive their cleanup from the same pass-owned activation context.
-/
def loopBody
    {lowerCtx : AllocationLowering.Ctx}
    {loopState currentState : AllocationLowering.State}
    {loopLocals : Locals.Ctx}
    {loopPlan : Locals.Allocation.Plan}
    {loopLive : List Functions.Name}
    {loopMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    (hCompiler :
      AllocationObserverContext.ActivationExprContext
        lowerCtx loopState loopLocals loopPlan loopLive loopMode)
    (hPlanWF : loopPlan.WellFormed)
    (hState :
      AllocationLowering.StateExtends loopLive loopState currentState)
    (hScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ loopLive) :
    ControlDestinations lowerCtx currentState
      (loopLocals.withLoopControl loopLocals.layout.length)
      loopPlan loopLive loopMode
      (sourceCtx.withLoopControl sourceCtx.scope sourceCtx.scope) := by
  let destination :
      ControlDestination lowerCtx currentState loopPlan loopLive loopMode :=
    { state := loopState
      locals := loopLocals
      plan := loopPlan
      live := loopLive
      mode := loopMode
      compiler := hCompiler
      planWF := hPlanWF
      subset := fun _ hName => hName
      sameFrame := SameFrame.refl loopMode
      stateExtends := hState }
  exact
    { brk := .available destination sourceCtx.scope rfl hScope rfl
      cont := .available destination sourceCtx.scope rfl hScope rfl }

/--
Eliminate the canonical `break` destination of a loop body.
-/
theorem loopBody_break_destination
    {lowerCtx : AllocationLowering.Ctx}
    {loopState currentState : AllocationLowering.State}
    {loopLocals : Locals.Ctx}
    {loopPlan : Locals.Allocation.Plan}
    {loopLive : List Functions.Name}
    {loopMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {sourceFinal : Functions.ObserverSemantics.State transcript}
    {targetFinal : Structured.ObserverSemantics.State transcript}
    (hCompiler :
      AllocationObserverContext.ActivationExprContext
        lowerCtx loopState loopLocals loopPlan loopLive loopMode)
    (hPlanWF : loopPlan.WellFormed)
    (hState :
      AllocationLowering.StateExtends loopLive loopState currentState)
    (hScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ loopLive)
    (hDestination :
      ControlBinding.DestinationRuntimeInvariant
        (contract := contract) (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (loopBody hCompiler hPlanWF hState hScope).brk
        sourceFinal targetFinal) :
    AllocationObserverContext.ActivationRuntimeInvariant
      contract config allocatorDepth lowerCtx loopState loopLocals
      loopPlan loopLive frameBase loopMode sourceFinal targetFinal := by
  simp [loopBody, ControlBinding.DestinationRuntimeInvariant] at hDestination
  exact hDestination.2.2.2

/--
Eliminate the canonical `continue` destination of a loop body.
-/
theorem loopBody_continue_destination
    {lowerCtx : AllocationLowering.Ctx}
    {loopState currentState : AllocationLowering.State}
    {loopLocals : Locals.Ctx}
    {loopPlan : Locals.Allocation.Plan}
    {loopLive : List Functions.Name}
    {loopMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {sourceFinal : Functions.ObserverSemantics.State transcript}
    {targetFinal : Structured.ObserverSemantics.State transcript}
    (hCompiler :
      AllocationObserverContext.ActivationExprContext
        lowerCtx loopState loopLocals loopPlan loopLive loopMode)
    (hPlanWF : loopPlan.WellFormed)
    (hState :
      AllocationLowering.StateExtends loopLive loopState currentState)
    (hScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ loopLive)
    (hDestination :
      ControlBinding.DestinationRuntimeInvariant
        (contract := contract) (config := config)
        (allocatorDepth := allocatorDepth) (frameBase := frameBase)
        (loopBody hCompiler hPlanWF hState hScope).cont
        sourceFinal targetFinal) :
    AllocationObserverContext.ActivationRuntimeInvariant
      contract config allocatorDepth lowerCtx loopState loopLocals
      loopPlan loopLive frameBase loopMode sourceFinal targetFinal := by
  simp [loopBody, ControlBinding.DestinationRuntimeInvariant] at hDestination
  exact hDestination.2.2.2

def transport
    {lowerCtx : AllocationLowering.Ctx}
    {currentState nextState : AllocationLowering.State}
    {currentLocals nextLocals : Locals.Ctx}
    {currentPlan nextPlan : Locals.Allocation.Plan}
    {currentLive nextLive : List Functions.Name}
    {currentMode nextMode : ActivationMode}
    {sourceCtx nextSourceCtx : Functions.Source.Ctx}
    (hDestinations :
      ControlDestinations lowerCtx currentState currentLocals currentPlan
        currentLive currentMode sourceCtx)
    (hSourceControl : SameControl sourceCtx nextSourceCtx)
    (hLocalsControl : Locals.Ctx.SameControl currentLocals nextLocals)
    (hState :
      AllocationLowering.StateExtends
        currentLive currentState nextState)
    (hLive :
      ∀ name, name ∈ currentLive → name ∈ nextLive)
    (hMode : SameFrame currentMode nextMode) :
    ControlDestinations lowerCtx nextState nextLocals nextPlan
      nextLive nextMode nextSourceCtx :=
  { brk :=
      hDestinations.brk.transport hSourceControl hLocalsControl
        hState hLive hMode
    cont :=
      hDestinations.cont.transport hSourceControl hLocalsControl
        hState hLive hMode }

end ControlDestinations

/--
Transport an abrupt activation outcome from a lexical body plan to its outer
plan.

Only break/continue destinations inspect locals, and `ControlScopesWithin`
places those destinations inside the outer live set. Leave and halt outcomes
do not depend on lexical-plan locations.
-/
theorem transport_nonregular_outcome_plan
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {bodyPlan outerPlan : Locals.Allocation.Plan}
    {returns bodyLive outerLive : List Functions.Name}
    {sourceCtx : Functions.Source.Ctx}
    {stackOffset frameBase : Nat}
    {finalMode : ActivationMode}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      ActivationOutcomeRel contract bodyPlan
        (outcomeLive returns bodyLive sourceCtx sourceOutcome.mode)
        stackOffset frameBase finalMode sourceOutcome targetOutcome)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hPlanAgree :
      PlanAgreesOn bodyPlan outerPlan outerLive)
    (hControl :
      ControlScopesWithin returns outerLive sourceCtx) :
    ActivationOutcomeRel contract outerPlan
      (outcomeLive returns outerLive sourceCtx sourceOutcome.mode)
      stackOffset frameBase finalMode sourceOutcome targetOutcome := by
  have hOutcomePlanAgree :
      PlanAgreesOn bodyPlan outerPlan
        (outcomeLive returns outerLive sourceCtx sourceOutcome.mode) :=
    hPlanAgree.mono
      (hControl.outcomeLive_subset sourceOutcome.mode)
  cases hRel with
  | regular _ =>
      exact False.elim (hMode rfl)
  | brk hState =>
      exact .brk
        (by
          simpa [outcomeLive] using
            hState.transport_plan hOutcomePlanAgree)
  | cont hState =>
      exact .cont
        (by
          simpa [outcomeLive] using
            hState.transport_plan hOutcomePlanAgree)
  | leave hState =>
      exact .leave hState
  | halt kind hState =>
      exact .halt kind
        { cursor := hState.cursor
          shared := hState.shared }

/--
Lift an abrupt open lexical-body result to the enclosing `.block` statement.

The compiler-emitted cleanup is unreachable on an abrupt target outcome. The
only nontrivial boundary change is from the lexical body plan back to the
outer plan; synchronized-cursor plan agreement transports exactly the live
control destination.
-/
theorem NonregularStmtRuntimeForward.block_of_runtime
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {bodyPlan outerPlan : Locals.Allocation.Plan}
    {returns bodyLive outerLive : List Functions.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {sourceBlock : Functions.Block}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {compiledBody : List Expressions.Stmt}
    {targetBlock : Expressions.Block}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    {outerLocals bodyLocals : Locals.Ctx}
    (hBody :
      BlockRuntimeForward contract config allocatorDepth transcript
        bodyPlan
        (outcomeLive returns bodyLive sourceCtx sourceOutcome.mode)
        frameBase initialMode finalMode sourceProgram sourceCtx sourceBlock
        source targetProgram
        { stmts := Expressions.StmtList.toStructured compiledBody }
        target sourceOutcome targetOutcome finalCtx)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hPlanAgree :
      PlanAgreesOn bodyPlan outerPlan outerLive)
    (hControl :
      ControlScopesWithin returns outerLive sourceCtx)
    (hFinish :
      Locals.finishScoped outerLocals bodyLocals compiledBody =
        some targetBlock) :
    NonregularStmtRuntimeForward contract config allocatorDepth transcript
      outerPlan
      (outcomeLive returns outerLive sourceCtx sourceOutcome.mode)
      frameBase initialMode finalMode sourceProgram sourceCtx
      (.block sourceBlock) source targetProgram target
      (Expressions.StmtList.toStructured targetBlock.stmts)
      sourceOutcome targetOutcome sourceCtx := by
  rcases hBody with
    ⟨sourceFuel, targetFuel, hSourceOpen, hTargetBody,
      hOutcomeRel, hSame, hEffect⟩
  have hSourceScoped :=
    Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hSourceOpen hMode
  have hSourceStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel (.block sourceBlock) source =
        .ok (sourceOutcome, sourceCtx) := by
    simp only [Functions.Source.Effectful.Stmt.run]
    rw [hSourceScoped]
    rfl
  obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
    AllocationObserverCleanup.Plain.finishScoped_shape hFinish
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hOutcomeRel.target_nonregular hMode
  have hTargetStmt :
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel
        { stmts :=
            Expressions.StmtList.toStructured targetBlock.stmts }
        target targetOutcome := by
    rw [hTargetShape]
    simpa [Expressions.StmtList.toStructured_append,
      Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using
      (Structured.EffectSemantics.Block.Eval.append_nonregular
        hTargetBody hTargetMode :
        Structured.ObserverSemantics.Block.Eval
          targetProgram targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledBody ++
                [Structured.Stmt.code cleanup] }
          target targetOutcome)
  have hOuterOutcomeRel :
      ActivationOutcomeRel contract outerPlan
        (outcomeLive returns outerLive sourceCtx sourceOutcome.mode)
        0 frameBase finalMode sourceOutcome targetOutcome := by
    exact
      transport_nonregular_outcome_plan
        hOutcomeRel hMode hPlanAgree hControl
  exact
    ⟨sourceFuel, targetFuel, hSourceStmt, hTargetStmt, hMode,
      hOuterOutcomeRel, hSame, hEffect⟩

/--
One statement's complete runtime-forward result.

The regular constructor retains the compiler's outgoing allocation and Locals
contexts. The abrupt constructor retains only the outcome-indexed state
relation, matching the fact that no source continuation observes the static
tail contexts.
-/
inductive StmtRuntimeResult
    (contract : MemoryContract.Contract)
    (config : Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerFinal : AllocationLowering.State)
    (localsFinal : Locals.Ctx)
    (plan : Locals.Allocation.Plan)
    (returns regularLive : List Functions.Name)
    (frameBase : Nat)
    (initialMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (stmt : Functions.Stmt)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (target : Structured.ObserverSemantics.State transcript)
    (compiled : List Structured.Stmt) :
    Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript) →
      Structured.ObserverSemantics.Outcome
        (transcript := transcript) →
      Functions.Source.Ctx → Prop where
  | regular
      {sourceFinal : Functions.ObserverSemantics.State transcript}
      {targetFinal : Structured.ObserverSemantics.State transcript}
      {finalMode : ActivationMode}
      {finalCtx : Functions.Source.Ctx}
      (forward :
        AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
          contract config allocatorDepth transcript lowerCtx lowerFinal
          localsFinal plan regularLive frameBase initialMode finalMode
          sourceProgram sourceCtx stmt source targetProgram target compiled
          sourceFinal targetFinal finalCtx)
      (control : SameControl sourceCtx finalCtx) :
      StmtRuntimeResult contract config allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx stmt source targetProgram target compiled
        (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) finalCtx
  | nonregular
      {sourceOutcome :
        Functions.ObserverSemantics.Outcome
          (Functions.ObserverSemantics.State transcript)}
      {targetOutcome :
        Structured.ObserverSemantics.Outcome
          (transcript := transcript)}
      {finalMode : ActivationMode}
      {stmtCtx : Functions.Source.Ctx}
      (forward :
        NonregularStmtRuntimeForward contract config allocatorDepth transcript
          plan (outcomeLive returns regularLive sourceCtx sourceOutcome.mode)
          frameBase initialMode finalMode sourceProgram sourceCtx stmt source
          targetProgram target compiled sourceOutcome targetOutcome stmtCtx) :
      StmtRuntimeResult contract config allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx stmt source targetProgram target compiled
        sourceOutcome targetOutcome stmtCtx

/--
One statement's complete forward result under the compiler-selected resource
mode.
-/
inductive StmtResourceResult
    (contract : MemoryContract.Contract)
    (resource : Frame.ResourceMode)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerFinal : AllocationLowering.State)
    (localsFinal : Locals.Ctx)
    (plan : Locals.Allocation.Plan)
    (returns regularLive : List Functions.Name)
    (frameBase : Nat)
    (initialMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (stmt : Functions.Stmt)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (target : Structured.ObserverSemantics.State transcript)
    (compiled : List Structured.Stmt) :
    Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript) →
      Structured.ObserverSemantics.Outcome
        (transcript := transcript) →
      Functions.Source.Ctx → Prop where
  | regular
      {sourceFinal : Functions.ObserverSemantics.State transcript}
      {targetFinal : Structured.ObserverSemantics.State transcript}
      {finalMode : ActivationMode}
      {finalCtx : Functions.Source.Ctx}
      (forward :
        AllocationObserverStatement.Sequence.RegularStmtResourceInvariantForward
          contract resource allocatorDepth transcript lowerCtx lowerFinal
          localsFinal plan regularLive frameBase initialMode finalMode
          sourceProgram sourceCtx stmt source targetProgram target compiled
          sourceFinal targetFinal finalCtx)
      (control : SameControl sourceCtx finalCtx) :
      StmtResourceResult contract resource allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx stmt source targetProgram target compiled
        (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) finalCtx
  | nonregular
      {sourceOutcome :
        Functions.ObserverSemantics.Outcome
          (Functions.ObserverSemantics.State transcript)}
      {targetOutcome :
        Structured.ObserverSemantics.Outcome
          (transcript := transcript)}
      {finalMode : ActivationMode}
      {stmtCtx : Functions.Source.Ctx}
      (forward :
        NonregularStmtResourceForward contract resource allocatorDepth
          transcript plan
          (outcomeLive returns regularLive sourceCtx sourceOutcome.mode)
          frameBase initialMode finalMode sourceProgram sourceCtx stmt source
          targetProgram target compiled sourceOutcome targetOutcome stmtCtx) :
      StmtResourceResult contract resource allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx stmt source targetProgram target compiled
        sourceOutcome targetOutcome stmtCtx

namespace StmtRuntimeResult

/-- Lift the existing scratch-backed statement result. -/
theorem toResource
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerFinal : AllocationLowering.State}
    {localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {returns regularLive : List Functions.Name}
    {frameBase : Nat}
    {initialMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiled : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hResult :
      StmtRuntimeResult contract config allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx stmt source targetProgram target compiled
        sourceOutcome targetOutcome finalCtx) :
    StmtResourceResult contract (.scratch config) allocatorDepth transcript
      lowerCtx lowerFinal localsFinal plan returns regularLive frameBase
      initialMode sourceProgram sourceCtx stmt source targetProgram target
      compiled sourceOutcome targetOutcome finalCtx := by
  cases hResult with
  | regular forward control =>
      exact .regular forward.toResource control
  | nonregular forward =>
      exact .nonregular forward.toResource

end StmtRuntimeResult

/--
Open-block counterpart of `StmtRuntimeResult`, used as the sole recursive
result of the source-fuel block dispatcher.
-/
inductive BlockRuntimeResult
    (contract : MemoryContract.Contract)
    (config : Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerFinal : AllocationLowering.State)
    (localsFinal : Locals.Ctx)
    (plan : Locals.Allocation.Plan)
    (returns regularLive : List Functions.Name)
    (frameBase : Nat)
    (initialMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (sourceBlock : Functions.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (targetBlock : Structured.Block)
    (target : Structured.ObserverSemantics.State transcript) :
    Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript) →
      Structured.ObserverSemantics.Outcome
        (transcript := transcript) →
      Functions.Source.Ctx → Prop where
  | regular
      {sourceFinal : Functions.ObserverSemantics.State transcript}
      {targetFinal : Structured.ObserverSemantics.State transcript}
      {finalMode : ActivationMode}
      {finalCtx : Functions.Source.Ctx}
      (forward :
        AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward
          contract config allocatorDepth transcript lowerCtx lowerFinal
          localsFinal plan regularLive frameBase initialMode finalMode
          sourceProgram sourceCtx sourceBlock source targetProgram targetBlock
          target sourceFinal targetFinal finalCtx)
      (control : SameControl sourceCtx finalCtx) :
      BlockRuntimeResult contract config allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx sourceBlock source targetProgram targetBlock
        target (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) finalCtx
  | nonregular
      {sourceOutcome :
        Functions.ObserverSemantics.Outcome
          (Functions.ObserverSemantics.State transcript)}
      {targetOutcome :
        Structured.ObserverSemantics.Outcome
          (transcript := transcript)}
      {finalMode : ActivationMode}
      {finalCtx : Functions.Source.Ctx}
      (sourceNonregular : sourceOutcome.mode ≠ .regular)
      (forward :
        BlockRuntimeForward contract config allocatorDepth transcript plan
          (outcomeLive returns regularLive sourceCtx sourceOutcome.mode)
          frameBase initialMode finalMode sourceProgram sourceCtx sourceBlock
          source targetProgram targetBlock target sourceOutcome targetOutcome
          finalCtx) :
      BlockRuntimeResult contract config allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx sourceBlock source targetProgram targetBlock
        target sourceOutcome targetOutcome finalCtx

/--
Open-block counterpart of `StmtResourceResult`.
-/
inductive BlockResourceResult
    (contract : MemoryContract.Contract)
    (resource : Frame.ResourceMode)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerFinal : AllocationLowering.State)
    (localsFinal : Locals.Ctx)
    (plan : Locals.Allocation.Plan)
    (returns regularLive : List Functions.Name)
    (frameBase : Nat)
    (initialMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (sourceBlock : Functions.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (targetBlock : Structured.Block)
    (target : Structured.ObserverSemantics.State transcript) :
    Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript) →
      Structured.ObserverSemantics.Outcome
        (transcript := transcript) →
      Functions.Source.Ctx → Prop where
  | regular
      {sourceFinal : Functions.ObserverSemantics.State transcript}
      {targetFinal : Structured.ObserverSemantics.State transcript}
      {finalMode : ActivationMode}
      {finalCtx : Functions.Source.Ctx}
      (forward :
        AllocationObserverStatement.Sequence.RegularBlockResourceInvariantForward
          contract resource allocatorDepth transcript lowerCtx lowerFinal
          localsFinal plan regularLive frameBase initialMode finalMode
          sourceProgram sourceCtx sourceBlock source targetProgram targetBlock
          target sourceFinal targetFinal finalCtx)
      (control : SameControl sourceCtx finalCtx) :
      BlockResourceResult contract resource allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx sourceBlock source targetProgram targetBlock
        target (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) finalCtx
  | nonregular
      {sourceOutcome :
        Functions.ObserverSemantics.Outcome
          (Functions.ObserverSemantics.State transcript)}
      {targetOutcome :
        Structured.ObserverSemantics.Outcome
          (transcript := transcript)}
      {finalMode : ActivationMode}
      {finalCtx : Functions.Source.Ctx}
      (sourceNonregular : sourceOutcome.mode ≠ .regular)
      (forward :
        BlockResourceForward contract resource allocatorDepth transcript plan
          (outcomeLive returns regularLive sourceCtx sourceOutcome.mode)
          frameBase initialMode finalMode sourceProgram sourceCtx sourceBlock
          source targetProgram targetBlock target sourceOutcome targetOutcome
          finalCtx) :
      BlockResourceResult contract resource allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx sourceBlock source targetProgram targetBlock
        target sourceOutcome targetOutcome finalCtx

namespace BlockRuntimeResult

/-- Lift the existing scratch-backed block result. -/
theorem toResource
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerFinal : AllocationLowering.State}
    {localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {returns regularLive : List Functions.Name}
    {frameBase : Nat}
    {initialMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {sourceBlock : Functions.Block}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {targetBlock : Structured.Block}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hResult :
      BlockRuntimeResult contract config allocatorDepth transcript lowerCtx
        lowerFinal localsFinal plan returns regularLive frameBase initialMode
        sourceProgram sourceCtx sourceBlock source targetProgram targetBlock
        target sourceOutcome targetOutcome finalCtx) :
    BlockResourceResult contract (.scratch config) allocatorDepth transcript
      lowerCtx lowerFinal localsFinal plan returns regularLive frameBase
      initialMode sourceProgram sourceCtx sourceBlock source targetProgram
      targetBlock target sourceOutcome targetOutcome finalCtx := by
  cases hResult with
  | regular forward control =>
      exact .regular forward.toResource control
  | nonregular sourceNonregular forward =>
      exact .nonregular sourceNonregular forward.toResource

end BlockRuntimeResult

namespace BlockRuntimeResult

theorem nil
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {returns live : List Functions.Name}
    {frameBase : Nat}
    {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx plan
        live frameBase mode source target) :
    BlockRuntimeResult contract config allocatorDepth transcript lowerCtx
      lowerState localsCtx plan returns live frameBase mode sourceProgram
      sourceCtx { stmts := [] } source targetProgram { stmts := [] } target
      (Functions.Source.Effectful.Outcome.regular source)
      (Structured.EffectSemantics.Outcome.regular target) sourceCtx :=
  .regular
    (AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward.nil
      hInvariant)
    (SameControl.refl sourceCtx)

theorem cons_regular
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {midState finalState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {returns midLive finalLive : List Functions.Name}
    {frameBase : Nat}
    {initialMode midMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx midCtx finalCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {source sourceMid : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target targetMid : Structured.ObserverSemantics.State transcript}
    {compiledHead compiledTail : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hHead :
      AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
        contract config allocatorDepth transcript lowerCtx midState midLocals
        plan midLive frameBase initialMode midMode sourceProgram sourceCtx stmt
        source targetProgram target compiledHead sourceMid targetMid midCtx)
    (hControl : SameControl sourceCtx midCtx)
    (hTail :
      BlockRuntimeResult contract config allocatorDepth transcript lowerCtx
        finalState finalLocals plan returns finalLive frameBase midMode
        sourceProgram midCtx { stmts := rest } sourceMid targetProgram
        { stmts := compiledTail } targetMid sourceOutcome targetOutcome
        finalCtx) :
    BlockRuntimeResult contract config allocatorDepth transcript lowerCtx
      finalState finalLocals plan returns finalLive frameBase initialMode
      sourceProgram sourceCtx { stmts := stmt :: rest } source targetProgram
      { stmts := compiledHead ++ compiledTail } target sourceOutcome
      targetOutcome finalCtx := by
  cases hTail with
  | regular hTailForward hTailControl =>
      exact
        .regular
          (AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward.cons_regular
            hHead hTailForward)
          (hControl.trans hTailControl)
  | nonregular hMode hTailForward =>
      have hLive :=
        SameControl.outcomeLive_eq_of_nonregular
          (returns := returns) (regularLive := finalLive)
          hControl hMode
      rw [← hLive] at hTailForward
      exact
        .nonregular hMode
          (BlockRuntimeForward.cons_regular hHead hTailForward)

theorem cons_nonregular
    {contract : MemoryContract.Contract}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {finalState : AllocationLowering.State}
    {finalLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {returns finalLive : List Functions.Name}
    {frameBase : Nat}
    {initialMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiledHead compiledTail : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hHead :
      NonregularStmtRuntimeForward contract config allocatorDepth transcript
        plan (outcomeLive returns finalLive sourceCtx sourceOutcome.mode)
        frameBase initialMode finalMode sourceProgram sourceCtx stmt source
        targetProgram target compiledHead sourceOutcome targetOutcome
        stmtCtx) :
    BlockRuntimeResult contract config allocatorDepth transcript lowerCtx
      finalState finalLocals plan returns finalLive frameBase initialMode
      sourceProgram sourceCtx { stmts := stmt :: rest } source targetProgram
      { stmts := compiledHead ++ compiledTail } target sourceOutcome
      targetOutcome sourceCtx := by
  have hForward := hHead
  rcases hHead with
    ⟨_sourceFuel, _targetFuel, _hSource, _hTarget, hMode,
      _hRel, _hSame, _hEffect⟩
  exact
    .nonregular hMode
      (BlockRuntimeForward.cons_nonregular hForward)

end BlockRuntimeResult

end AllocationObserverOutcome
end Functions
end EvmCompiler
