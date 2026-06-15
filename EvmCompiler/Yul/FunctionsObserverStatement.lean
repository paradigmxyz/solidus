import EvmCompiler.Yul.FunctionsObserverCall

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverStatement

/-!
Statement and block preservation owned by the adjacent Yul-to-Functions pass.

The first constructor is the empty function-body base case. Subsequent
constructors compose ordinary statement lowering with the expression and call
interfaces; this module does not define a compiler or a control interpreter.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

namespace ReturnedBody

theorem of_empty
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨compilerFuel, lowerStmts, _hCompilerFuel, hLowerList, hBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  obtain ⟨_previous, _hPrevious, hLowerStmts, _hAfter⟩ :=
    Stmt.List.toFunctionsUncheckedFuel?_nil_parts hLowerList
  subst lowerStmts
  have hFnBody : fn.body = { stmts := [] } := by
    simpa using hBody
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨_seqPrevious, _hSeqFuel, hStateAfterSeq⟩ :=
    Yul.Source.Effectful.execSeq_nil_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  subst stateAfterSeq
  let sourceEntry :=
    sourceCaller.withSource
      (EvmYul.Yul.State.mkOk
        (sourceCaller.source.initcall params returns args))
  let targetEntry :=
    targetCaller.withSource
      { shared := targetCaller.source.shared,
        vars :=
          Functions.Source.Store.initReturns fn.returns paramStore }
  obtain
      ⟨entryShared, entryVars, hEntrySource,
        _hEntryShared, _hEntryVars, _hEntryDomain⟩ :=
    hEntry.2
  have hRestrict :
      sourceEntry.source.restrictStoreTo sourceEntry.source.store =
        sourceEntry.source := by
    rw [hEntrySource]
    simp only [EvmYul.Yul.State.store,
      EvmYul.Yul.State.restrictStoreTo]
    rw [StateRelation.VarStore.restrict_self]
  have hSourceAfterBody : sourceAfterBody = sourceEntry := by
    rw [hSourceAfter]
    change
      sourceEntry.withSource
          (sourceEntry.source.restrictStoreTo sourceEntry.source.store) =
        sourceEntry
    rw [hRestrict]
    exact Simulation.ResourceReplay.State.withSource_self sourceEntry
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.regular targetEntry
  have hTargetRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          1 fn.body targetEntry =
        .ok
          (targetOutcome,
            Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    rw [hFnBody]
    exact
      Functions.Source.Effectful.Block.runOpen_nil
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions
        (Functions.Source.Effectful.FunDef.bodyCtx fn)
        0 targetEntry
  have hFinalRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
        targetOutcome.state := by
    have hRevive :
        sourceEntry.source.reviveJump = sourceEntry.source := by
      rw [hEntrySource]
      rfl
    rw [hSourceAfterBody]
    rw [hRevive]
    simpa [targetEntry, targetOutcome]
      using hEntry
  refine
    ⟨1, ⟨paramStore, targetOutcome,
      Functions.Source.Effectful.FunDef.bodyCtx fn,
      hParamStore, ?_, ?_, hFinalRel⟩⟩
  · simpa [targetEntry] using hTargetRun
  · exact Or.inl rfl

theorem of_leave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Leave] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Leave])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨hFnBody, _hAfter⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_leave_parts hLower
  let sourceEntry :=
    sourceCaller.withSource
      (EvmYul.Yul.State.mkOk
        (sourceCaller.source.initcall params returns args))
  let targetEntry :=
    targetCaller.withSource
      { shared := targetCaller.source.shared,
        vars :=
          Functions.Source.Store.initReturns fn.returns paramStore }
  obtain
      ⟨entryShared, entryVars, hEntrySource,
        _hEntryShared, _hEntryVars, _hEntryDomain⟩ :=
    hEntry.2
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨_seqPrevious, stateAfterLeave, _hSeqFuel,
        hLeaveRun, hSeqFinal⟩ :=
    Yul.Source.Effectful.execSeq_cons_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  obtain ⟨_leavePrevious, _hLeaveFuel, hStateAfterLeave⟩ :=
    Yul.Source.Effectful.exec_leave_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hLeaveRun
  let sourceLeave :=
    sourceEntry.withSource
      (EvmYul.Yul.State.setLeave sourceEntry.source)
  have hStateAfterLeave' : stateAfterLeave = sourceLeave := by
    simpa [sourceEntry, sourceLeave] using hStateAfterLeave
  have hSourceLeave :
      sourceLeave.source =
        .Checkpoint (.Leave entryShared entryVars) := by
    change
      EvmYul.Yul.State.setLeave sourceEntry.source =
        .Checkpoint (.Leave entryShared entryVars)
    rw [hEntrySource]
    rfl
  have hStateAfterSeq : stateAfterSeq = sourceLeave := by
    rw [hStateAfterLeave'] at hSeqFinal
    change
      (match sourceLeave.source with
      | .Ok _ _ =>
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              _ [] (some sourceProgram.contract) sourceLeave =
            .ok stateAfterSeq
      | .OutOfFuel | .Checkpoint _ =>
          stateAfterSeq = sourceLeave) at hSeqFinal
    rw [hSourceLeave] at hSeqFinal
    exact hSeqFinal
  have hRestrictedLeave :
      sourceLeave.source.restrictStoreTo sourceEntry.source.store =
        sourceLeave.source := by
    rw [hSourceLeave, hEntrySource]
    simp only [EvmYul.Yul.State.store,
      EvmYul.Yul.State.restrictStoreTo]
    rw [StateRelation.VarStore.restrict_self]
  have hSourceAfterBody : sourceAfterBody = sourceLeave := by
    rw [hSourceAfter, hStateAfterSeq]
    change
      sourceLeave.withSource
          (sourceLeave.source.restrictStoreTo sourceEntry.source.store) =
        sourceLeave
    rw [hRestrictedLeave]
    exact Simulation.ResourceReplay.State.withSource_self sourceLeave
  let targetLeave :=
    targetEntry.withSource (targetEntry.source.restrictTo
      (fn.returns ++ fn.params))
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.leave targetLeave
  have hLeaveScope :
      (Functions.Source.Effectful.FunDef.bodyCtx fn).leaveScope? =
        some (fn.returns ++ fn.params) := by
    rfl
  have hTargetStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          1 .leave targetEntry =
        .ok
          (targetOutcome,
            Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    simpa [targetLeave, targetOutcome] using
      Functions.Source.Effectful.Stmt.run_leave_of_scope
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hLeaveScope
  have hTargetRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          2 fn.body targetEntry =
        .ok
          (targetOutcome,
            Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    rw [hFnBody]
    exact
      Functions.Source.Effectful.Block.runOpen_cons_nonregular
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetStmt (by
          intro hMode
          cases hMode)
  have hRevived :
      sourceAfterBody.withSource sourceAfterBody.source.reviveJump =
        sourceEntry := by
    rw [hSourceAfterBody]
    change
      (sourceEntry.withSource
          (EvmYul.Yul.State.setLeave sourceEntry.source)).withSource
          (EvmYul.Yul.State.setLeave sourceEntry.source).reviveJump =
        sourceEntry
    rw [hEntrySource]
    change
      sourceEntry.withSource (.Ok entryShared entryVars) = sourceEntry
    rw [← hEntrySource]
    exact Simulation.ResourceReplay.State.withSource_self sourceEntry
  have hFinalRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
        targetOutcome.state := by
    rw [hRevived]
    simpa [targetEntry, targetLeave, targetOutcome] using
      StateRelation.Replay.scopedExact_restrict_target hEntry
  refine
    ⟨2, ⟨paramStore, targetOutcome,
      Functions.Source.Effectful.FunDef.bodyCtx fn,
      hParamStore, ?_, ?_, hFinalRel⟩⟩
  · simpa [targetEntry] using hTargetRun
  · exact Or.inr rfl

end ReturnedBody

end FunctionsObserverStatement
end Yul
end EvmCompiler
