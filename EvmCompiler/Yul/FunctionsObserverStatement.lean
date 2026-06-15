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

end ReturnedBody

end FunctionsObserverStatement
end Yul
end EvmCompiler
