import EvmCompiler.Functions.AllocationObserverStatement

namespace EvmCompiler
namespace Functions
namespace AllocationObserverOutcome

open AllocationObserverRelation

abbrev Trace := Assembly.ResourceTrace

/--
Allocator-aware preservation for one source statement that exits nonregularly.

The final activation mode describes the related abrupt outcome. `SameFrame`
and `ActivationEffect` retain the representation and allocator facts needed by
the enclosing source-fuel recursion.
-/
def NonregularStmtRuntimeForward
    (contract : MemoryContract.Contract)
    (config : Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (finalLive : List Locals.Name)
    (frameBase : Nat)
    (initialMode finalMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (stmt : Functions.Stmt)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (target : Structured.ObserverSemantics.State transcript)
    (compiled : List Structured.Stmt)
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript))
    (stmtCtx : Functions.Source.Ctx) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel stmt source =
        .ok (sourceOutcome, stmtCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel { stmts := compiled } target
          targetOutcome ∧
      sourceOutcome.mode ≠ .regular ∧
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome ∧
      SameFrame initialMode finalMode ∧
      Frame.ActivationEffect config allocatorDepth initialMode
        target targetOutcome.state

namespace NonregularStmtRuntimeForward

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
  ⟨sourceFuel, targetFuel, hSource, hTarget, hMode, hRel, hSame, hEffect⟩

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
      SameFrame.refl mode, hEffect⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget
  · intro hMode
    cases hMode

end NonregularStmtRuntimeForward

/--
Outcome-indexed block preservation with the recursive allocator invariant.

This is the common result type of the mutual statement/block dispatcher. It
supports regular continuation and every abrupt outcome without duplicating the
source or target control interpreters.
-/
def BlockRuntimeForward
    (contract : MemoryContract.Contract)
    (config : Frame.Config)
    (allocatorDepth : Nat)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (finalLive : List Locals.Name)
    (frameBase : Nat)
    (initialMode finalMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (sourceBlock : Functions.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (targetBlock : Structured.Block)
    (target : Structured.ObserverSemantics.State transcript)
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript))
    (finalCtx : Functions.Source.Ctx) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel sourceBlock source =
        .ok (sourceOutcome, finalCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel targetBlock target targetOutcome ∧
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome ∧
      SameFrame initialMode finalMode ∧
      Frame.ActivationEffect config allocatorDepth initialMode
        target targetOutcome.state

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
      Frame.ActivationEffect.refl hInvariant.allocator⟩

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
      hHeadEffect.trans_of_sameFrame hHeadSame hTailEffect⟩

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

end AllocationObserverOutcome
end Functions
end EvmCompiler
