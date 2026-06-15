import EvmCompiler.Yul.FunctionsObserverForward
import EvmCompiler.Yul.FunctionsObserverCallTerminal
import EvmCompiler.Yul.FunctionsObserverTerminal
import EvmCompiler.Yul.EffectRefinement.Failure

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

def RecursiveTerminalExpressionForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {exprFuel : Nat} {before after : Fresh.State}
    {layout : List Name}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx},
    exprFuel < bound →
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
        true →
      Expr.lower1Unchecked? before expr = some (pre, lower, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      Yul.Source.Effectful.eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          exprFuel expr (some sourceProgram.contract) source =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        (FunctionsObserverTerminal.StatementResult
          contract codeRel targetProgram.toFunctions pre failure target ctx)

theorem terminalArgsOfUncheckedLowering
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {initial final : Fresh.State}
    {layout : List Name}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel : Nat}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {Eligible : AstExpr → Prop}
    (hLowering :
      Expr.List.UncheckedBoundLowering
        initial args pre lowerArgs final)
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hRegularExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {lower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < fuel →
          Eligible expr →
          Expr.lower1Unchecked? before expr =
            some (exprPre, lower, after) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
            before.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin before.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            (FunctionsObserverExpression.ScopedPreparedValue
              contract transcript codeRel program exprPre lower after
              layout exprSource' exprTarget exprCtx value))
    (hTerminalExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {lower : Locals.Expr 1}
        {exprSource :
          ObserverSemantics.SourceReplay.State transcript}
        {exprFailure :
          Yul.Source.Effectful.Failure
            (ObserverSemantics.SourceReplay.State transcript)}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx},
        exprFuel < fuel →
          Eligible expr →
          Expr.lower1Unchecked? before expr =
            some (exprPre, lower, after) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
            before.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin before.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .error exprFailure →
          Yul.Source.Effectful.Exception.Observable
              exprFailure.exception →
          Nonempty
            (FunctionsObserverTerminal.StatementResult
              contract codeRel program exprPre exprFailure
              exprTarget exprCtx))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel args.reverse codeOverride source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel program pre failure target ctx) := by
  induction hLowering generalizing fuel source failure target ctx with
  | nil =>
      cases fuel with
      | zero =>
          simp [Yul.Source.Effectful.evalArgs,
            Yul.Source.Effectful.fail] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | succ previous =>
          simp [Yul.Source.Effectful.evalArgs] at hRun
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      rw [List.reverse_cons] at hRun
      rcases
          Yul.Source.Effectful.evalArgs_append_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hRun with hRestFailure | hHeadFailure
      · obtain ⟨restResult⟩ :=
          ih
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            hRegularExpr hTerminalExpr hRel hDomain hScope
            hRestFailure hObservable
        exact
          ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
            restResult preHead⟩
      · rcases hHeadFailure with
          ⟨middle, restValues, headFuel,
            hFuel, hRestRun, hHeadRun⟩
        obtain ⟨exprFuel, hExprFuel, hExprRun⟩ :=
          Yul.Source.Effectful.evalArgs_singleton_observable_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hHeadRun hObservable
        obtain ⟨restPrepared⟩ :=
          FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
            hRest
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                hArgScope hArgRun =>
              hRegularExpr (by omega) hArgOk hArgLower hArgRel
                hArgDomain hArgScope hArgRun)
            hRel hDomain hScope hRestRun
        obtain ⟨headResult⟩ :=
          hTerminalExpr (by omega) (hEligible expr (by simp)) hHead
            restPrepared.relation
            restPrepared.prepared.prepared.domain
            restPrepared.prepared.prepared.scope
            hExprRun hObservable
        exact
          ⟨FunctionsObserverTerminal.StatementResult.prependPrepared
            restPrepared.prepared.prepared headResult⟩
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      rw [List.reverse_cons] at hRun
      rcases
          Yul.Source.Effectful.evalArgs_append_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hRun with hRestFailure | hHeadFailure
      · obtain ⟨restResult⟩ :=
          ih
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            hRegularExpr hTerminalExpr hRel hDomain hScope
            hRestFailure hObservable
        let result :=
          FunctionsObserverTerminal.StatementResult.appendUnreachable
            restResult
            (preHead ++ [Functions.Stmt.let_ tmp lowerHead])
        exact ⟨by simpa [List.append_assoc] using result⟩
      · rcases hHeadFailure with
          ⟨middle, restValues, headFuel,
            hFuel, hRestRun, hHeadRun⟩
        obtain ⟨exprFuel, hExprFuel, hExprRun⟩ :=
          Yul.Source.Effectful.evalArgs_singleton_observable_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hHeadRun hObservable
        obtain ⟨restPrepared⟩ :=
          FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
            hRest
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                hArgScope hArgRun =>
              hRegularExpr (by omega) hArgOk hArgLower hArgRel
                hArgDomain hArgScope hArgRun)
            hRel hDomain hScope hRestRun
        obtain ⟨headResult⟩ :=
          hTerminalExpr (by omega) (hEligible expr (by simp)) hHead
            restPrepared.relation
            restPrepared.prepared.prepared.domain
            restPrepared.prepared.prepared.scope
            hExprRun hObservable
        exact
          ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
            (FunctionsObserverTerminal.StatementResult.prependPrepared
              restPrepared.prepared.prepared headResult)
            [Functions.Stmt.let_ tmp lowerHead]⟩

theorem selectedBodyOfCallFailure
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound expected argsFuel callFuel : Nat}
    {layout : List Name}
    {functionName : Name} {args : List AstExpr}
    {sourceBeforeArgs sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {reversedValues : List Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout expected
          (.Call (.inr functionName) args) =
        true)
    (hTerminalBody :
      RecursiveTerminalBodyForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hCallFuelBound : callFuel < bound)
    (hArgsRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          argsFuel args.reverse (some sourceProgram.contract)
          sourceBeforeArgs =
        .ok (sourceAfterArgs, reversedValues))
    (hCallRun :
      Yul.Source.Effectful.call
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          callFuel reversedValues.reverse (some functionName)
          (some sourceProgram.contract) sourceAfterArgs =
        .error failure)
    (hCallerRel :
      StateRelation.Replay.Rel codeRel sourceAfterArgs targetCaller)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    ∃ fn paramStore,
      Functions.Source.FunList.find? functionName
          targetProgram.toFunctions.functions =
        some fn ∧
      Functions.Source.Store.insertMany fn.params reversedValues.reverse
          Locals.Source.Store.empty =
        some paramStore ∧
      Nonempty
        (FunctionsObserverCallTerminal.BodyResult
          contract codeRel targetProgram.toFunctions fn.body failure
          (targetCaller.withSource
            { shared := targetCaller.source.shared,
              vars :=
                Functions.Source.Store.initReturns
                  fn.returns paramStore })
          (Functions.Source.Effectful.FunDef.bodyCtx fn)) := by
  obtain
      ⟨bodyFuel, _accountContract, params, returns, body,
        hCallFuel, _hAccount, hFunction, hBodyRun⟩ :=
    Yul.Source.Effectful.call_observable_error_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hCallRun hObservable
  have hLookup :
      sourceProgram.contract.functions.lookup functionName =
        some (.Def params returns body) := by
    simpa using hFunction
  obtain ⟨_hReturnCount, hArgCount, hSignature⟩ :=
    SolcValidation.programOkWith_functionCall_partsN
      hProgramOk hExprOk hLookup
  obtain
      ⟨before, after, fn, hPrefix, hFind, _hName,
        hParams, hFnReturns, hLowerBody, hReserved⟩ :=
    hDecomposition.findFunction_parts hLookup
  have hArgsLength :
      reversedValues.reverse.length = (identNames params).length := by
    have hEvaluatedLength :=
      Yul.Source.Effectful.evalArgs_ok_length
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hArgsRun
    simpa [identNames, hArgCount] using hEvaluatedLength
  obtain ⟨paramStore, hParamStore⟩ :=
    Functions.Source.Store.insertMany_exists_of_length
      (names := identNames params)
      (values := reversedValues.reverse)
      (store := Locals.Source.Store.empty)
      hArgsLength
  have hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceAfterArgs.withSource
          (EvmYul.Yul.State.mkOk
            (sourceAfterArgs.source.initcall
              params returns reversedValues.reverse)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore }) := by
    have hIdentParams : identNames params = params :=
      identNames_eq_self params
    have hIdentReturns : identNames returns = returns :=
      identNames_eq_self returns
    have hSignature' : (returns ++ params).Nodup := by
      rw [hIdentReturns, hIdentParams] at hSignature
      exact hSignature
    have hParamStore' :
        Functions.Source.Store.insertMany params reversedValues.reverse
            Locals.Source.Store.empty =
          some paramStore := by
      rw [hIdentParams] at hParamStore
      exact hParamStore
    have hParams' : fn.params = params :=
      hParams.trans hIdentParams
    have hFnReturns' : fn.returns = returns :=
      hFnReturns.trans hIdentReturns
    have hEntryBase :=
      StateRelation.Replay.scopedExact_initcall
        (params := params)
        (returns := returns)
        (args := reversedValues.reverse)
        (paramStore := paramStore)
        hCallerRel hSignature' hParamStore'
    simpa [hParams', hFnReturns'] using hEntryBase
  have hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries
            sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true body =
        true := by
    rw [hFnReturns, hParams]
    exact
      SolcValidation.programOkWith_function_bodyOk hProgramOk hLookup
  have hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) := by
    intro candidate hMem
    apply hPrefix candidate
    change candidate ∈ Contract.names sourceProgram.contract
    exact
      (Contract.function_names_mem_names_of_lookup hLookup).2 candidate
        (by simp [FunctionDefinition.names, hMem])
  obtain ⟨bodyResult⟩ :=
    hTerminalBody (by omega) hLowerBody hParams hFnReturns
      (by simpa [hParams] using hParamStore)
      hReserved hBodyNames hBodyOk hEntry hBodyRun hObservable
  exact
    ⟨fn, paramStore, hFind,
      by simpa [hParams] using hParamStore, ⟨bodyResult⟩⟩

namespace RecursiveTerminalExpressionForward

theorem ofFunctionCall
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
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {exprFuel : Nat} {before after : Fresh.State}
      {layout : List Name}
      {functionName : Name} {args : List AstExpr}
      {pre : List Functions.Stmt} {lower : Locals.Expr 1}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      exprFuel < bound + 1 →
        SolcValidation.ExprOk? profile sourceProgram.contract layout 1
            (.Call (.inr functionName) args) =
          true →
        Expr.lower1Unchecked? before
            (.Call (.inr functionName) args) =
          some (pre, lower, after) →
        StateRelation.Replay.ScopedExactRel codeRel layout source target →
        StateRelation.Vars.TargetDomainWithin
          before.used target.source.vars →
        StateRelation.Vars.NamesWithin before.used ctx.scope →
        Yul.Source.Effectful.eval
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            exprFuel (.Call (.inr functionName) args)
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            pre failure target ctx) := by
  intro exprFuel before after layout functionName args pre lower
    source failure target ctx hFuel hExprOk hLower hRel hDomain hScope
    hRun hObservable
  have hValuesRun :=
    Yul.Source.Effectful.eval_observable_error
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨callFuel, hExprFuel, hFailureCase⟩ :=
    Yul.Source.Effectful.evalValues_function_observable_error_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hValuesRun hObservable
  obtain
      ⟨argsFresh, tmp, preArgs, lowerArgs,
        hArgsLowering, hFresh, hPre, hLowerVar⟩ :=
    (Expr.uncheckedFunctionCallLowering_of_lower1Unchecked?
      hLower).parts
  subst pre
  subst lower
  have hLookupExists :
      ∃ params returns body,
        sourceProgram.contract.functions.lookup functionName =
          some (.Def params returns body) := by
    cases hLookup :
        sourceProgram.contract.functions.lookup functionName with
    | none =>
        simp [SolcValidation.ExprOk?,
          SolcValidation.lookupFunction?, hLookup] at hExprOk
    | some fn =>
        cases fn with
        | Def params returns body =>
            exact ⟨params, returns, body, rfl⟩
  rcases hLookupExists with ⟨lookupParams, lookupReturns, lookupBody,
      hLookup⟩
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_functionCall hExprOk hLookup
  rcases hFailureCase with hArgsFailure | hCallFailure
  · have hArgsTerminal :
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            preArgs failure target ctx) := by
      cases hArgsLowering with
      | empty =>
          cases callFuel with
          | zero =>
              simp [Yul.Source.Effectful.evalArgs,
                Yul.Source.Effectful.fail] at hArgsFailure
              rw [← hArgsFailure] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable]
                at hObservable
          | succ previous =>
              simp [Yul.Source.Effectful.evalArgs] at hArgsFailure
      | bound hNonempty hLowering =>
          exact
            terminalArgsOfUncheckedLowering hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                  hArgScope hArgRun =>
                hRegularExpr (by omega) hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun)
              (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                  hArgScope hArgRun hArgObservable =>
                hTerminalExpr (by omega) hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun hArgObservable)
              hRel hDomain hScope hArgsFailure hObservable
    obtain ⟨argsResult⟩ := hArgsTerminal
    let result :=
      FunctionsObserverTerminal.StatementResult.appendUnreachable
        argsResult
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
          Functions.Stmt.call [tmp] functionName lowerArgs]
    exact ⟨by simpa [List.append_assoc] using result⟩
  · rcases hCallFailure with
      ⟨sourceAfterArgs, reversedValues, hArgsRun, hCallRun⟩
    have hPreparedArgs :
        Nonempty
          (FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel targetProgram.toFunctions
            preArgs lowerArgs argsFresh layout sourceAfterArgs target ctx
            reversedValues.reverse) := by
      cases hArgsLowering with
      | empty =>
          cases callFuel with
          | zero =>
              simp [Yul.Source.Effectful.evalArgs,
                Yul.Source.Effectful.fail] at hArgsRun
          | succ previous =>
              simp [Yul.Source.Effectful.evalArgs] at hArgsRun
              rcases hArgsRun with ⟨rfl, rfl⟩
              exact
                ⟨FunctionsObserverExpression.PreparedArgs.empty
                    (StateRelation.Replay.rel_of_scopedExact hRel)
                    hDomain hScope,
                  hRel⟩
      | bound hNonempty hLowering =>
          exact
            FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
              hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                  hArgScope hArgRun =>
                hRegularExpr (by omega) hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun)
              hRel hDomain hScope hArgsRun
    obtain ⟨preparedArgs⟩ := hPreparedArgs
    have hNotMem : tmp ∉ argsFresh.used :=
      Fresh.not_mem_of_fresh? hFresh
    have hSourceHidden :
        sourceAfterArgs.source.lookup? tmp = none :=
      StateRelation.Replay.source_lookup_none_of_targetDomainWithin
        preparedArgs.prepared.prepared.rel
        preparedArgs.prepared.prepared.domain hNotMem
    let targetCaller :=
      preparedArgs.prepared.prepared.finalTarget.withSource
        (preparedArgs.prepared.prepared.finalTarget.source.insert
          tmp Functions.Source.zero)
    have hCallerRel :
        StateRelation.Replay.Rel codeRel sourceAfterArgs targetCaller := by
      dsimp [targetCaller]
      exact
        StateRelation.Replay.insert_target_hidden
          preparedArgs.prepared.prepared.rel hSourceHidden
    obtain ⟨fn, paramStore, hFind, hParamStore, bodyResult⟩ :=
      selectedBodyOfCallFailure
        hDecomposition hProgramOk hExprOk hTerminalBody
        (by omega) hArgsRun hCallRun hCallerRel hObservable
    obtain ⟨bodyResult⟩ := bodyResult
    exact
      FunctionsObserverCallTerminal.expressionOfPreparedArgs
        preparedArgs hFresh hFind hParamStore
        (by simpa [targetCaller] using bodyResult)

end RecursiveTerminalExpressionForward

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

theorem functionCall
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
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {functionName : Name} {args : List AstExpr}
      {lower : List Functions.Stmt}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      sourceFuel < bound + 1 →
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout false false false
            (.ExprStmtCall (.Call (.inr functionName) args)) =
          true →
        Stmt.toFunctionsListUncheckedFuel? compilerFuel before
            (.ExprStmtCall (.Call (.inr functionName) args)) =
          some (lower, after) →
        StateRelation.Replay.ScopedExactRel codeRel layout source target →
        StateRelation.Vars.TargetDomainWithin
          before.used target.source.vars →
        StateRelation.Vars.NamesWithin before.used ctx.scope →
        Yul.Source.Effectful.exec
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceFuel
            (.ExprStmtCall (.Call (.inr functionName) args))
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            lower failure target ctx) := by
  intro sourceFuel compilerFuel before after layout functionName args
    lower source failure target ctx hFuel hStmtOk hLower hRel hDomain
    hScope hRun hObservable
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 0
          (.Call (.inr functionName) args) =
        true := by
    simpa [SolcValidation.StmtOk?] using hStmtOk
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_call_parts hLower
  subst lower
  obtain ⟨argsFuel, hSourceFuel, hFailureCase⟩ :=
    Yul.Source.Effectful.exec_expr_function_observable_error_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun hObservable
  have hLookupExists :
      ∃ params returns body,
        sourceProgram.contract.functions.lookup functionName =
          some (.Def params returns body) := by
    cases hLookup :
        sourceProgram.contract.functions.lookup functionName with
    | none =>
        simp [SolcValidation.ExprOk?,
          SolcValidation.lookupFunction?, hLookup] at hExprOk
    | some fn =>
        cases fn with
        | Def params returns body =>
            exact ⟨params, returns, body, rfl⟩
  rcases hLookupExists with
    ⟨lookupParams, lookupReturns, lookupBody, hLookup⟩
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_functionCall hExprOk hLookup
  rcases hFailureCase with hArgsFailure | hCallFailure
  · have hArgsTerminal :
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            preArgs failure target ctx) := by
      cases hArgsLowering with
      | empty =>
          cases argsFuel with
          | zero =>
              simp [Yul.Source.Effectful.evalArgs,
                Yul.Source.Effectful.fail] at hArgsFailure
              rw [← hArgsFailure] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable]
                at hObservable
          | succ previous =>
              simp [Yul.Source.Effectful.evalArgs] at hArgsFailure
      | bound hNonempty hLowering =>
          exact
            terminalArgsOfUncheckedLowering hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                  hArgScope hArgRun =>
                hRegularExpr (by omega) hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun)
              (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                  hArgScope hArgRun hArgObservable =>
                hTerminalExpr (by omega) hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun hArgObservable)
              hRel hDomain hScope hArgsFailure hObservable
    obtain ⟨argsResult⟩ := hArgsTerminal
    exact
      ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
        argsResult
        [Functions.Stmt.call [] functionName lowerArgs]⟩
  · rcases hCallFailure with
      ⟨callFuel, sourceAfterArgs, reversedValues,
        hArgsFuel, hArgsRun, hCallRun⟩
    have hPreparedArgs :
        Nonempty
          (FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel targetProgram.toFunctions
            preArgs lowerArgs after layout sourceAfterArgs target ctx
            reversedValues.reverse) := by
      cases hArgsLowering with
      | empty =>
          cases argsFuel with
          | zero =>
              simp [Yul.Source.Effectful.evalArgs,
                Yul.Source.Effectful.fail] at hArgsRun
          | succ previous =>
              simp [Yul.Source.Effectful.evalArgs] at hArgsRun
              rcases hArgsRun with ⟨rfl, rfl⟩
              exact
                ⟨FunctionsObserverExpression.PreparedArgs.empty
                    (StateRelation.Replay.rel_of_scopedExact hRel)
                    hDomain hScope,
                  hRel⟩
      | bound hNonempty hLowering =>
          exact
            FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
              hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
                  hArgScope hArgRun =>
                hRegularExpr (by omega) hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun)
              hRel hDomain hScope hArgsRun
    obtain ⟨preparedArgs⟩ := hPreparedArgs
    obtain ⟨fn, paramStore, hFind, hParamStore, bodyResult⟩ :=
      selectedBodyOfCallFailure
        hDecomposition hProgramOk hExprOk hTerminalBody
        (by omega) hArgsRun hCallRun
        (StateRelation.Replay.rel_of_scopedExact preparedArgs.relation)
        hObservable
    obtain ⟨bodyResult⟩ := bodyResult
    exact
      FunctionsObserverCallTerminal.statementOfPreparedArgs
        preparedArgs (by simp) hFind hParamStore bodyResult

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
