import EvmCompiler.Yul.FunctionsObserverForward
import EvmCompiler.Yul.FunctionsObserverCallTerminal
import EvmCompiler.Yul.FunctionsObserverTerminal

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTerminalForward

/-!
Source-fuel composition for terminal outcomes at the adjacent
Yul-to-Functions boundary.

Successful prefixes are delegated to `FunctionsObserverForward`. Terminal
results retain only the canonical target execution and terminal observable
relation; lexical layouts are dead once the target has halted.
-/

abbrev Trace := Assembly.ResourceTrace

def RecursiveTerminalStmtForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool},
    sourceFuel < bound →
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave stmt =
        true →
      StateRelation.Vars.NamesWithin before.used (Stmt.names stmt) →
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before stmt =
        some (lower, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      StateRelation.Vars.NamesWithin before.used layout →
      FunctionsObserverForward.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt (some sourceProgram.contract) source =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        (FunctionsObserverTerminal.StatementResult
          contract codeRel targetProgram.toFunctions lower
          failure target ctx)

def RecursiveTerminalListForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {stmts : List AstStmt}
    {lower : List Functions.Stmt}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool},
    sourceFuel < bound →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave stmts =
        true →
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names stmts) →
      Stmt.List.toFunctionsUncheckedFuel? compilerFuel before stmts =
        some (lower, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      StateRelation.Vars.NamesWithin before.used layout →
      FunctionsObserverForward.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.execSeq
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmts (some sourceProgram.contract) source =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        (FunctionsObserverTerminal.StatementResult
          contract codeRel targetProgram.toFunctions lower
          failure target ctx)

def RecursiveTerminalBodyForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel : Nat} {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt} {fn : Functions.FunDef}
    {args : List Assembly.Word} {paramStore : Locals.Source.Store}
    {sourceCaller :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {targetCaller : Functions.ObserverSemantics.State transcript},
    sourceFuel < bound →
      Stmt.List.toBlockUncheckedFuel?
        (FunctionList.fuel
          (Contract.functionEntries sourceProgram.contract))
        before body =
      some (fn.body, after) →
      fn.params = identNames params →
      fn.returns = identNames returns →
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore →
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params) →
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true body =
        true →
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }) →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block body) (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        (FunctionsObserverCallTerminal.BodyResult
          contract codeRel targetProgram.toFunctions fn.body failure
          (targetCaller.withSource
            { shared := targetCaller.source.shared,
              vars :=
                Functions.Source.Store.initReturns
                  fn.returns paramStore })
          (Functions.Source.Effectful.FunDef.bodyCtx fn))

namespace RecursiveTerminalListForward

theorem ofStmt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularStmt :
      FunctionsObserverForward.RecursiveOpenStmtForward
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalStmt :
      RecursiveTerminalStmtForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveTerminalListForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmts
    lower source failure target ctx canBreak canContinue canLeave
    hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
    hRun hObservable
  cases stmts with
  | nil =>
      cases sourceFuel with
      | zero =>
          simp [Yul.Source.Effectful.execSeq,
            Yul.Source.Effectful.fail] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | succ previous =>
          simp [Yul.Source.Effectful.execSeq] at hRun
  | cons head tail =>
      obtain
          ⟨compilerPrevious, lowerHead, middle, lowerTail,
            _hCompilerFuel, hLowerHead, hLowerTail, hLowerAppend⟩ :=
        Stmt.List.toFunctionsUncheckedFuel?_cons_parts hLower
      subst lower
      rcases
          Yul.Source.Effectful.execSeq_cons_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hRun with hOuter | hPrevious
      · rcases hOuter with ⟨rfl, hFailure⟩
        rw [← hFailure] at hObservable
        simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      · rcases hPrevious with
          ⟨sourcePrevious, hSourceFuel, hFailureCase⟩
        have hPreviousBound : sourcePrevious < bound := by
          omega
        obtain ⟨hHeadOk, hTailOk⟩ :=
          SolcValidation.stmtsOk_cons_parts hOk
        have hHeadNames :
            StateRelation.Vars.NamesWithin before.used
              (Stmt.names head) := by
          intro name hMem
          exact hNames name (List.mem_append_left _ hMem)
        rcases hFailureCase with hHeadFailure | hTailFailure
        · obtain ⟨headResult⟩ :=
            hTerminalStmt hPreviousBound hHeadOk hHeadNames
              hLowerHead hRel hDomain hScope hLayout hControl
              hHeadFailure hObservable
          exact
            ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
              headResult lowerTail⟩
        · rcases hTailFailure with
            ⟨sourceAfterHead, shared, vars,
              hHeadRun, hSourceAfterHead, hTailRun⟩
          obtain ⟨headResult⟩ :=
            hRegularStmt hPreviousBound hHeadOk hHeadNames
              hLowerHead hRel hDomain hScope hLayout hControl hHeadRun
          have hSourceAfterHead' :
              sourceAfterHead.source = .Ok shared vars := by
            simpa [ObserverSemantics.SourceReplay.stateModel] using
              hSourceAfterHead
          have hHeadRegular :
              headResult.openResult.outcome.mode = .regular := by
            have hMode := headResult.openResult.relation.mode
            rw [hSourceAfterHead'] at hMode
            exact
              FunctionsObserverOutcome.ModeRel.source_ok_target_regular
                hMode
          have hHeadRel :
              StateRelation.Replay.ScopedExactRel codeRel
                headResult.openResult.finalLayout sourceAfterHead
                headResult.openResult.outcome.state := by
            have hRevived :
                sourceAfterHead.withSource
                    sourceAfterHead.source.reviveJump =
                  sourceAfterHead := by
              calc
                sourceAfterHead.withSource
                    sourceAfterHead.source.reviveJump =
                    sourceAfterHead.withSource
                      sourceAfterHead.source := by
                        rw [hSourceAfterHead']
                        rfl
                _ = sourceAfterHead :=
                  Simulation.ResourceReplay.State.withSource_self
                    sourceAfterHead
            have hExact :=
              headResult.openResult.relation.exact hHeadRegular
            rw [hRevived] at hExact
            exact hExact
          have hTailNames :
              StateRelation.Vars.NamesWithin middle.used
                (Stmt.List.names tail) := by
            intro name hMem
            exact
              headResult.openResult.freshExtends name
                (hNames name (List.mem_append_right _ hMem))
          have hHeadLayout :=
            headResult.regularLayout hHeadRegular
          have hTailOk' :
              SolcValidation.StmtsOk? profile sourceProgram.contract
                  ((Contract.functionEntries
                    sourceProgram.contract).map Prod.fst)
                  headResult.openResult.finalLayout
                  canBreak canContinue canLeave tail =
                true := by
            rw [hHeadLayout]
            exact hTailOk
          obtain ⟨tailResult⟩ :=
            hTerminalList
              (sourceFuel := sourcePrevious)
              (compilerFuel := compilerPrevious)
              (sourceControl := sourceControl)
              (before := middle) (after := after)
              (layout := headResult.openResult.finalLayout)
              (stmts := tail) (lower := lowerTail)
              (source := sourceAfterHead) (failure := failure)
              (target := headResult.openResult.outcome.state)
              (ctx := headResult.openResult.finalCtx)
              (canBreak := canBreak)
              (canContinue := canContinue) (canLeave := canLeave)
              hPreviousBound hTailOk' hTailNames hLowerTail hHeadRel
              headResult.openResult.domain
              headResult.openResult.scope
              headResult.openResult.layoutWithin
              (headResult.regularControl hHeadRegular)
              hTailRun hObservable
          exact
            ⟨FunctionsObserverTerminal.StatementResult.prependRegular
              headResult.openResult hHeadRegular tailResult⟩

end RecursiveTerminalListForward

namespace RecursiveTerminalBodyForward

theorem ofList
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hList :
      RecursiveTerminalListForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveTerminalBodyForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel before after params returns body fn args paramStore
    sourceCaller failure targetCaller hFuel hLower hParams hReturns
    hParamStore hReserved hBodyNames hBodyOk hEntry hRun hObservable
  let layout := fn.returns ++ fn.params
  let sourceEntry :=
    sourceCaller.withSource
      (EvmYul.Yul.State.mkOk
        (sourceCaller.source.initcall params returns args))
  let targetEntry :=
    targetCaller.withSource
      { shared := targetCaller.source.shared,
        vars :=
          Functions.Source.Store.initReturns fn.returns paramStore }
  obtain ⟨listCompilerFuel, lower, _hCompilerFuel,
      hLowerList, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  rcases
      Yul.Source.Effectful.exec_block_error_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun with hOuter | hBodyFailure
  · rcases hOuter with ⟨rfl, hFailure⟩
    rw [← hFailure] at hObservable
    simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  · rcases hBodyFailure with
      ⟨listSourceFuel, _hSourceFuel, hListRun⟩
    let sourceControl : FunctionsObserverOutcome.SourceControlScopes :=
      { breakScope? := none
        continueScope? := none
        leaveScope? := some layout }
    have hControl :
        FunctionsObserverForward.ControlContextRel
          sourceControl layout false false true
          (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
      refine
        { scope := ?_
          breakScope := ?_
          continueScope := ?_
          leaveScope := ?_ }
      · simp [layout, Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope,
          FunctionsObserverOutcome.LayoutWithinScope]
      · simp [sourceControl, FunctionsObserverForward.ScopeOptionWithin,
          Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope]
      · simp [sourceControl, FunctionsObserverForward.ScopeOptionWithin,
          Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope]
      · simp [sourceControl, FunctionsObserverForward.ScopeOptionWithin,
          Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope, layout]
    obtain ⟨result⟩ :=
      hList
        (sourceFuel := listSourceFuel)
        (compilerFuel := listCompilerFuel)
        (sourceControl := sourceControl)
        (before := before) (after := after)
        (layout := layout) (stmts := body) (lower := lower)
        (source := sourceEntry) (failure := failure)
        (target := targetEntry)
        (ctx := Functions.Source.Effectful.FunDef.bodyCtx fn)
        (canBreak := false) (canContinue := false) (canLeave := true)
        (by omega) hBodyOk hBodyNames hLowerList hEntry
        (by
          simpa [targetEntry] using
            FunctionsObserverForward.RecursiveBodyForward.entryTargetDomain
              hParamStore hReserved)
        (FunctionsObserverForward.RecursiveBodyForward.bodyScope
          hReserved)
        hReserved hControl hListRun hObservable
    exact
      ⟨FunctionsObserverCallTerminal.BodyResult.ofStatement
        hFnBody result⟩

end RecursiveTerminalBodyForward

namespace RecursiveTerminalStmtForward

theorem block
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hTerminalList :
      RecursiveTerminalListForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
      {before after : Fresh.State}
      {layout : List Name}
      {body : List AstStmt}
      {lower : List Functions.Stmt}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx}
      {canBreak canContinue canLeave : Bool},
      sourceFuel < bound + 1 →
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout canBreak canContinue canLeave (.Block body) =
          true →
        StateRelation.Vars.NamesWithin before.used
          (Stmt.names (.Block body)) →
        Stmt.toFunctionsListUncheckedFuel?
            compilerFuel before (.Block body) =
          some (lower, after) →
        StateRelation.Replay.ScopedExactRel codeRel layout source target →
        StateRelation.Vars.TargetDomainWithin
          before.used target.source.vars →
        StateRelation.Vars.NamesWithin before.used ctx.scope →
        StateRelation.Vars.NamesWithin before.used layout →
        FunctionsObserverForward.ControlContextRel sourceControl layout
          canBreak canContinue canLeave ctx →
        Yul.Source.Effectful.exec
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceFuel (.Block body) (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions lower
            failure target ctx) := by
  intro sourceFuel compilerFuel sourceControl before after layout body
    lower source failure target ctx canBreak canContinue canLeave
    hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
    hRun hObservable
  obtain ⟨compilerPrevious, lowerBody, _hCompilerFuel,
      hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_block_parts hLower
  subst lower
  obtain ⟨listCompilerFuel, lowerStmts, _hBlockFuel,
      hLowerList, hLowerBodyEq⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  subst lowerBody
  rcases
      Yul.Source.Effectful.exec_block_error_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun with hOuter | hBodyFailure
  · rcases hOuter with ⟨rfl, hFailure⟩
    rw [← hFailure] at hObservable
    simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  · rcases hBodyFailure with
      ⟨sourcePrevious, hSourceFuel, hBodyRun⟩
    have hBodyOk :
        SolcValidation.StmtsOk? profile sourceProgram.contract
            ((Contract.functionEntries
              sourceProgram.contract).map Prod.fst)
            layout canBreak canContinue canLeave body =
          true := by
      simpa [SolcValidation.StmtOk?] using hOk
    have hBodyNames :
        StateRelation.Vars.NamesWithin before.used
          (Stmt.List.names body) := by
      simpa [Stmt.names] using hNames
    obtain ⟨bodyResult⟩ :=
      hTerminalList
        (sourceFuel := sourcePrevious)
        (compilerFuel := listCompilerFuel)
        (sourceControl := sourceControl)
        (before := before) (after := after)
        (layout := layout) (stmts := body) (lower := lowerStmts)
        (source := source) (failure := failure)
        (target := target) (ctx := ctx)
        (canBreak := canBreak) (canContinue := canContinue)
        (canLeave := canLeave)
        (by omega) hBodyOk hBodyNames hLowerList hRel hDomain
        hScope hLayout hControl hBodyRun hObservable
    exact
      ⟨FunctionsObserverTerminal.StatementResult.block bodyResult⟩

end RecursiveTerminalStmtForward

end FunctionsObserverTerminalForward
end Yul
end EvmCompiler
