import EvmCompiler.Functions.AllocationObserverStatement

namespace EvmCompiler
namespace Functions
namespace AllocationObserverOutcome

open AllocationObserverRelation

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
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    AllocationObserverCleanup.BreakLeaf.compiler_shape
      hTargetDepth hLower hCompile
  obtain
      ⟨targetFinal, hCleanupRun, hFinalRel, _hFinalStack,
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
  refine
    ⟨targetFinal, 0, 2, hSource, ?_, ?_, .brk hFinalRel,
      hTransition.sameFrame, hEffect⟩
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
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    AllocationObserverCleanup.ContinueLeaf.compiler_shape
      hTargetDepth hLower hCompile
  obtain
      ⟨targetFinal, hCleanupRun, hFinalRel, _hFinalStack,
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
  refine
    ⟨targetFinal, 0, 2, hSource, ?_, ?_, .cont hFinalRel,
      hTransition.sameFrame, hEffect⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget
  · intro hMode
    cases hMode

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

end ControlScopesWithin

structure SameControl
    (before after : Functions.Source.Ctx) : Prop where
  breakScope : before.breakScope? = after.breakScope?
  continueScope : before.continueScope? = after.continueScope?
  leaveScope : before.leaveScope? = after.leaveScope?

namespace SameControl

theorem refl (ctx : Functions.Source.Ctx) : SameControl ctx ctx :=
  ⟨rfl, rfl, rfl⟩

theorem trans
    {first second third : Functions.Source.Ctx}
    (hFirst : SameControl first second)
    (hSecond : SameControl second third) :
    SameControl first third :=
  ⟨hFirst.breakScope.trans hSecond.breakScope,
    hFirst.continueScope.trans hSecond.continueScope,
    hFirst.leaveScope.trans hSecond.leaveScope⟩

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
