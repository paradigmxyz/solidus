import EvmCompiler.Yul.FunctionsObserverStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverForward

/-!
Fuel-bounded composition for the adjacent Yul-to-Functions observer proof.

This module assembles the expression, call, and statement-owned constructors.
It does not define a compiler or interpreter. Recursive premises are strictly
smaller source-fuel interfaces and remain private to this pass boundary.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

def ScopeOptionWithin (enabled : Bool)
    (scope? : Option (List Name)) (layout : List Name) : Prop :=
  if enabled then
    ∃ scope,
      scope? = some scope ∧
        ∀ name, name ∈ scope → name ∈ layout
  else
    scope? = none

structure ControlContextRel
    (layout : List Name)
    (canBreak canContinue canLeave : Bool)
    (ctx : Functions.Source.Ctx) : Prop where
  breakScope :
    ScopeOptionWithin canBreak ctx.breakScope? layout
  continueScope :
    ScopeOptionWithin canContinue ctx.continueScope? layout
  leaveScope :
    ScopeOptionWithin canLeave ctx.leaveScope? layout

structure ScopedStmtResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (stmt : AstStmt)
    (lower : List Functions.Stmt)
    (initial final : Fresh.State)
    (entryLayout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (canBreak canContinue canLeave : Bool) where
  openResult :
    FunctionsObserverOutcome.ScopedOpenResult
      contract codeRel program lower initial final entryLayout
      sourceFinal target ctx
  regularLayout :
    openResult.outcome.mode = .regular →
      openResult.finalLayout =
        SolcValidation.StmtOutVars entryLayout stmt
  regularControl :
    openResult.outcome.mode = .regular →
      ControlContextRel openResult.finalLayout
        canBreak canContinue canLeave openResult.finalCtx

structure ScopedListResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (stmts : List AstStmt)
    (lower : List Functions.Stmt)
    (initial final : Fresh.State)
    (entryLayout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (canBreak canContinue canLeave : Bool) where
  openResult :
    FunctionsObserverOutcome.ScopedOpenResult
      contract codeRel program lower initial final entryLayout
      sourceFinal target ctx
  regularLayout :
    openResult.outcome.mode = .regular →
      openResult.finalLayout =
        SolcValidation.StmtsOutVars entryLayout stmts
  regularControl :
    openResult.outcome.mode = .regular →
      ControlContextRel openResult.finalLayout
        canBreak canContinue canLeave openResult.finalCtx

def RecursiveOpenStmtForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
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
      ControlContextRel layout canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedStmtResult contract codeRel targetProgram.toFunctions
          stmt lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave)

def RecursiveOpenListForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {stmts : List AstStmt}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
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
      ControlContextRel layout canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.execSeq
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmts (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedListResult contract codeRel targetProgram.toFunctions
          stmts lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave)

namespace RecursiveOpenListForward

theorem ofStmt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hStmt :
      RecursiveOpenStmtForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveOpenListForward contract transcript codeRel
      sourceProgram targetProgram profile bound := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel before after layout stmts lower
        source sourceFinal target ctx canBreak canContinue canLeave
        hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
      cases stmts with
      | nil =>
          obtain ⟨_compilerPrevious, _hCompilerFuel,
              hLowerNil, hAfter⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_nil_parts hLower
          obtain ⟨_sourcePrevious, _hSourceFuel, hSourceFinal⟩ :=
            Yul.Source.Effectful.execSeq_nil_ok_parts
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hRun
          subst lower
          subst after
          subst sourceFinal
          let result :=
            FunctionsObserverOutcome.ScopedOpenResult.empty
              (contract := contract) (program := targetProgram.toFunctions)
              hRel hDomain hScope hLayout
          exact
            ⟨{ openResult := result
               regularLayout := by
                 intro _hRegular
                 rfl
               regularControl := by
                 intro _hRegular
                 exact hControl }⟩
      | cons head tail =>
          obtain
              ⟨compilerPrevious, lowerHead, middle, lowerTail,
                _hCompilerFuel, hLowerHead, hLowerTail, hLowerAppend⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_cons_parts hLower
          subst lower
          obtain
              ⟨sourcePrevious, sourceAfterHead,
                hSourceFuel, hHeadRun, hTailRun⟩ :=
            Yul.Source.Effectful.execSeq_cons_ok_parts
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hRun
          have hPreviousBound : sourcePrevious < bound := by
            omega
          obtain ⟨hHeadOk, hTailOk⟩ :=
            SolcValidation.stmtsOk_cons_parts hOk
          have hHeadNames :
              StateRelation.Vars.NamesWithin before.used
                (Stmt.names head) := by
            intro name hMem
            exact hNames name (List.mem_append_left _ hMem)
          obtain ⟨headResult⟩ :=
            hStmt hPreviousBound hHeadOk hHeadNames hLowerHead
              hRel hDomain hScope hLayout hControl hHeadRun
          by_cases hRegular :
              headResult.openResult.outcome.mode = .regular
          · obtain ⟨sourceShared, sourceVars, hSourceAfterHead⟩ :=
              FunctionsObserverOutcome.ModeRel.target_regular_source_ok
                headResult.openResult.relation.mode hRegular
            have hTailRun' :
                Yul.Source.Effectful.execSeq
                    (ObserverSemantics.SourceReplay.stateModel transcript)
                    (ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    sourcePrevious tail (some sourceProgram.contract)
                    sourceAfterHead =
                  .ok sourceFinal := by
              simpa [ObserverSemantics.SourceReplay.stateModel,
                hSourceAfterHead] using hTailRun
            have hHeadRel :
                StateRelation.Replay.ScopedExactRel codeRel
                  headResult.openResult.finalLayout sourceAfterHead
                  headResult.openResult.outcome.state := by
              have hRevived :
                  sourceAfterHead.withSource
                      sourceAfterHead.source.reviveJump =
                    sourceAfterHead := by
                rw [hSourceAfterHead]
                change
                  sourceAfterHead.withSource
                      (.Ok sourceShared sourceVars) =
                    sourceAfterHead
                rw [← hSourceAfterHead]
                exact
                  Simulation.ResourceReplay.State.withSource_self
                    sourceAfterHead
              have hExact :=
                headResult.openResult.relation.exact hRegular
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
              headResult.regularLayout hRegular
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
              ih sourcePrevious (by omega)
                (compilerFuel := compilerPrevious)
                (before := middle) (after := after)
                (layout := headResult.openResult.finalLayout)
                (stmts := tail) (lower := lowerTail)
                (source := sourceAfterHead) (sourceFinal := sourceFinal)
                (target := headResult.openResult.outcome.state)
                (ctx := headResult.openResult.finalCtx)
                (canBreak := canBreak)
                (canContinue := canContinue) (canLeave := canLeave)
                hPreviousBound hTailOk' hTailNames hLowerTail hHeadRel
                headResult.openResult.domain
                headResult.openResult.scope
                headResult.openResult.layoutWithin
                (headResult.regularControl hRegular)
                hTailRun'
            let result :=
              FunctionsObserverOutcome.ScopedOpenResult.appendRegular
                headResult.openResult hRegular tailResult.openResult
            exact
              ⟨{ openResult := result
                 regularLayout := by
                   intro hResultRegular
                   change
                     tailResult.openResult.finalLayout =
                       SolcValidation.StmtsOutVars layout (head :: tail)
                   rw [tailResult.regularLayout hResultRegular]
                   simpa [SolcValidation.StmtsOutVars] using
                     congrArg
                       (fun headLayout =>
                         SolcValidation.StmtsOutVars headLayout tail)
                       hHeadLayout
                 regularControl := by
                   intro hResultRegular
                   exact tailResult.regularControl hResultRegular }⟩
          · obtain ⟨jump, hSourceAfterHead⟩ :=
              FunctionsObserverOutcome.ModeRel.target_nonregular_source_checkpoint
                headResult.openResult.relation.mode hRegular
            have hSourceFinal : sourceFinal = sourceAfterHead := by
              simpa [ObserverSemantics.SourceReplay.stateModel,
                hSourceAfterHead] using hTailRun
            subst sourceFinal
            have hTailFresh : Fresh.Extends middle after :=
              Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerTail
            let result :=
              FunctionsObserverOutcome.ScopedOpenResult.appendNonregular
                (rightLower := lowerTail)
                headResult.openResult hRegular hTailFresh
            exact
              ⟨{ openResult := result
                 regularLayout := by
                   intro hResultRegular
                   exact (hRegular hResultRegular).elim
                 regularControl := by
                   intro hResultRegular
                   exact (hRegular hResultRegular).elim }⟩

end RecursiveOpenListForward

namespace RecursiveBodyForward

theorem ofEmpty
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
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
    (_hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names []))
    (_hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true [] =
        true)
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
          fn args targetFuel sourceAfterBody targetCaller) :=
  FunctionsObserverStatement.ReturnedBody.of_empty
    hLower hParams hReturns hParamStore hEntry hRun

theorem ofLeave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
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
    (_hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Leave]))
    (_hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true [.Leave] =
        true)
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
          fn args targetFuel sourceAfterBody targetCaller) :=
  FunctionsObserverStatement.ReturnedBody.of_leave
    hLower hParams hReturns hParamStore hEntry hRun

theorem ofLetNone
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
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
          before [.Let names none] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (_hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Let names none]))
    (_hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true [.Let names none] =
        true)
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
          sourceFuel (.Block [.Let names none])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) :=
  FunctionsObserverStatement.ReturnedBody.of_let_none
    hLower hParams hReturns hParamStore hEntry hRun

theorem entryTargetDomain
    {before : Fresh.State} {fn : Functions.FunDef}
    {args : List Word} {paramStore : Locals.Source.Store}
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params)) :
    StateRelation.Vars.TargetDomainWithin before.used
      (Functions.Source.Store.initReturns fn.returns paramStore) := by
  intro name value hLookup
  exact
    hReserved name
      (Functions.Source.Store.initReturns_insertMany_empty_apply_mem
        hParamStore hLookup)

theorem bodyScope
    {before : Fresh.State} {fn : Functions.FunDef}
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params)) :
    StateRelation.Vars.NamesWithin before.used
      (Functions.Source.Effectful.FunDef.bodyCtx fn).scope := by
  simpa [Functions.Source.Effectful.FunDef.bodyCtx] using hReserved

theorem ofLetOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Let [name] (some expr)] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Let [name] (some expr)]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Let [name] (some expr)] =
        true)
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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Let [name] (some expr)])
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
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  apply
    FunctionsObserverStatement.ReturnedBody.of_let_one
      hNotFunctionCall hExprOk hLower hParams hReturns hParamStore
      hEntry
  · simpa using entryTargetDomain hParamStore hReserved
  · exact bodyScope hReserved
  · exact hValue
  · exact hRun

theorem ofAssignOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Assign [name] expr] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Assign [name] expr]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Assign [name] expr] =
        true)
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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Assign [name] expr])
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
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  apply
    FunctionsObserverStatement.ReturnedBody.of_assign_one
      hNotFunctionCall hExprOk hLower hParams hReturns hParamStore
      hEntry
  · simpa using entryTargetDomain hParamStore hReserved
  · exact bodyScope hReserved
  · exact hValue
  · exact hRun

theorem ofAssignCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before
          [.Assign names (.Call (.inr functionName) callArgs)] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names
          [.Assign names (.Call (.inr functionName) callArgs)]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Assign names (.Call (.inr functionName) callArgs)] =
        true)
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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block
            [.Assign names
              (.Call (.inr functionName) callArgs)])
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
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_assign_call_parts hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  exact
    FunctionsObserverStatement.ReturnedBody.of_assign_call
      hDecomposition hArgsLowering hFnBody hExprOk hProgramOk
      hParams hReturns hParamStore hEntry
      (by simpa using entryTargetDomain hParamStore hReserved)
      (bodyScope hReserved)
      (FunctionsObserverCall.RecursiveScopedValueForward.expression hValue)
      hBody hRun

theorem ofLetCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before
          [.Let names (some (.Call (.inr functionName) callArgs))] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names
          [.Let names (some (.Call (.inr functionName) callArgs))]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Let names (some (.Call (.inr functionName) callArgs))] =
        true)
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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block
            [.Let names
              (some (.Call (.inr functionName) callArgs))])
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
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_let_call_parts hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  exact
    FunctionsObserverStatement.ReturnedBody.of_let_call
      hDecomposition hArgsLowering hFnBody hExprOk hProgramOk
      hParams hReturns hParamStore hEntry
      (by simpa using entryTargetDomain hParamStore hReserved)
      (bodyScope hReserved) hBodyNames
      (FunctionsObserverCall.RecursiveScopedValueForward.expression hValue)
      hBody hRun

end RecursiveBodyForward

namespace RecursiveScopedValueForward

theorem ofBody
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        bound) :
    FunctionsObserverCall.RecursiveScopedValueForward
      contract transcript codeRel sourceProgram targetProgram profile
      bound := by
  intro exprFuel
  induction exprFuel using Nat.strong_induction_on with
  | h exprFuel ih =>
      intro before after layout expr pre lower source source'
        target ctx values hFuel hOk hLower hRel hDomain hScope hRun
      have hSmallerValue :
          FunctionsObserverCall.RecursiveScopedValueForward
            contract transcript codeRel sourceProgram targetProgram
            profile exprFuel := by
        intro smallerFuel smallerBefore smallerAfter smallerLayout
          smallerExpr smallerPre smallerLower smallerSource
          smallerSource' smallerTarget smallerCtx smallerValues
          hSmaller hSmallerOk hSmallerLower hSmallerRel
          hSmallerDomain hSmallerScope hSmallerRun
        exact
          ih smallerFuel hSmaller
            (by omega) hSmallerOk hSmallerLower hSmallerRel
            hSmallerDomain hSmallerScope hSmallerRun
      have hSmallerExpr :
          FunctionsObserverCall.RecursiveScopedExpressionForward
            contract transcript codeRel sourceProgram targetProgram
            profile exprFuel :=
        FunctionsObserverCall.RecursiveScopedValueForward.expression
          hSmallerValue
      have hSmallerBody :
          FunctionsObserverCall.RecursiveBodyForward
            contract transcript codeRel sourceProgram targetProgram profile
            exprFuel := by
        intro sourceFuel bodyBefore bodyAfter params returns body fn
          args paramStore sourceCaller sourceAfterBody targetCaller
          hSourceFuel hBodyLower hParams hReturns hParamStore
          hReserved hBodyNames hBodyOk hEntry hBodyRun
        exact
          hBody (by omega) hBodyLower hParams hReturns hParamStore
            hReserved hBodyNames hBodyOk hEntry hBodyRun
      cases expr with
      | Lit value =>
          exact
            FunctionsObserverExpression.ScopedPreparedValue.ofLiteral
              hLower hRel hDomain hScope hRun
      | Var name =>
          exact
            FunctionsObserverExpression.ScopedPreparedValue.ofVariable
              hLower hRel hDomain hScope hRun
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hArgsOk :
                  SolcValidation.ExprsOk? profile
                      sourceProgram.contract layout args =
                    true :=
                SolcValidation.exprsOk_of_exprOk_primitive hOk
              exact
                FunctionsObserverExpression.ScopedPreparedValue.ofPrimitive
                  hLower
                  (fun candidate hMem =>
                    SolcValidation.exprOk_of_exprsOk_of_mem
                      hArgsOk hMem)
                  (fun hArgFuel hArgOk hArgLower hArgRel
                      hArgDomain hArgScope hArgRun =>
                    hSmallerExpr hArgFuel hArgOk hArgLower hArgRel
                      hArgDomain hArgScope hArgRun)
                  hRel hDomain hScope hRun
          | inr functionName =>
              cases hLookup :
                  sourceProgram.contract.functions.lookup functionName with
              | none =>
                  simp [SolcValidation.ExprOk?,
                    SolcValidation.lookupFunction?, hLookup] at hOk
              | some fnDef =>
                  cases fnDef with
                  | Def params returns body =>
                      obtain ⟨returnName, hReturns⟩ :=
                        SolcValidation.returns_singleton_of_exprOk_functionCall
                          hOk hLookup
                      have hLength :=
                        Yul.Source.Effectful.evalValues_function_ok_length
                          (ObserverSemantics.SourceReplay.stateModel transcript)
                          (ObserverSafety.SafeSemantics.primitiveSemantics
                            contract transcript)
                          hLookup hRun
                      rw [hReturns] at hLength
                      cases values with
                      | nil =>
                          simp at hLength
                      | cons value rest =>
                          cases rest with
                          | nil =>
                              have hEval :
                                  Yul.Source.Effectful.eval
                                      (ObserverSemantics.SourceReplay.stateModel
                                        transcript)
                                      (ObserverSafety.SafeSemantics.primitiveSemantics
                                        contract transcript)
                                      exprFuel
                                      (.Call (.inr functionName) args)
                                      (some sourceProgram.contract) source =
                                    .ok (source', value) :=
                                Yul.Source.Effectful.eval_of_evalValues_singleton
                                  (ObserverSemantics.SourceReplay.stateModel
                                    transcript)
                                  (ObserverSafety.SafeSemantics.primitiveSemantics
                                    contract transcript)
                                  hRun
                              exact
                                ⟨value, rfl,
                                  FunctionsObserverCall.ScopedPreparedValue.ofFunctionCall
                                      hDecomposition hLower hProgramOk hOk
                                      hSmallerExpr hSmallerBody hRel
                                      hDomain hScope hEval⟩
                          | cons next tail =>
                              simp at hLength

end RecursiveScopedValueForward

end FunctionsObserverForward
end Yul
end EvmCompiler
