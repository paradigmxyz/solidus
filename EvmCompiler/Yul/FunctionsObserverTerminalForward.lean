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

def RecursiveTerminalCompoundForward
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
    FunctionsObserverForward.CompoundStmt stmt →
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

def RecursiveTerminalLoopForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after afterCond afterPost : Fresh.State}
    {layout : List Name}
    {cond : AstExpr}
    {post body : List AstStmt}
    {preCond : List Functions.Stmt}
    {lowerCond : Locals.Expr 1}
    {lowerPost lowerBody : Functions.Block}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool},
    sourceFuel < bound →
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 1 cond =
        true →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout false false canLeave post =
        true →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout true true canLeave body =
        true →
      StateRelation.Vars.NamesWithin before.used
          (Expr.names cond) →
      StateRelation.Vars.NamesWithin before.used
          (Stmt.List.names post) →
      StateRelation.Vars.NamesWithin before.used
          (Stmt.List.names body) →
      Expr.lower1Unchecked? before cond =
        some (preCond, lowerCond, afterCond) →
      Stmt.List.toBlockUncheckedFuel?
          compilerFuel afterCond post =
        some (lowerPost, afterPost) →
      Stmt.List.toBlockUncheckedFuel?
          compilerFuel afterPost body =
        some (lowerBody, after) →
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
          sourceFuel (.For cond post body)
          (some sourceProgram.contract) source =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        (FunctionsObserverTerminal.ForLoopResult
          contract codeRel targetProgram.toFunctions lowerPost
          { stmts :=
              preCond ++
                .if_
                  (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                  { stmts := [.brk] } ::
                lowerBody.stmts }
          failure target ctx)

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

theorem terminalCallOfUncheckedLowering
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound expected fuel : Nat}
    {before after : Fresh.State}
    {layout targets : List Name}
    {functionName : Name} {args : List AstExpr}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout expected
          (.Call (.inr functionName) args) =
        true)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering before args
        preArgs lowerArgs after)
    (hTargets : targets.Nodup)
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hFuel : fuel < bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inr functionName) args)
          (some sourceProgram.contract) source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel targetProgram.toFunctions
        (preArgs ++
          [Functions.Stmt.call targets functionName lowerArgs])
        failure target ctx) := by
  obtain ⟨callFuel, hSourceFuel, hFailureCase⟩ :=
    Yul.Source.Effectful.evalValues_function_observable_error_parts
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
    exact
      ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
        argsResult
        [Functions.Stmt.call targets functionName lowerArgs]⟩
  · rcases hCallFailure with
      ⟨sourceAfterArgs, reversedValues, hArgsRun, hCallRun⟩
    have hPreparedArgs :
        Nonempty
          (FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel targetProgram.toFunctions
            preArgs lowerArgs after layout sourceAfterArgs target ctx
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
    obtain ⟨fn, paramStore, hFind, hParamStore, bodyResult⟩ :=
      selectedBodyOfCallFailure
        hDecomposition hProgramOk hExprOk hTerminalBody
        (by omega) hArgsRun hCallRun
        (StateRelation.Replay.rel_of_scopedExact preparedArgs.relation)
        hObservable
    obtain ⟨bodyResult⟩ := bodyResult
    exact
      FunctionsObserverCallTerminal.statementOfPreparedArgs
        preparedArgs hTargets hFind hParamStore bodyResult

theorem terminalPrimitiveOfLowering
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel results : Nat}
    {initial final : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr results}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {Eligible : AstExpr → Prop}
    (hLower :
      Expr.lowerUnchecked? results initial (.Call (.inl prim) args) =
        some (pre, lower, final))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hRegularExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < fuel →
          Eligible expr →
          Expr.lower1Unchecked? before expr =
            some (exprPre, exprLower, after) →
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
              contract transcript codeRel program exprPre exprLower after
              layout exprSource' exprTarget exprCtx value))
    (hTerminalExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
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
            some (exprPre, exprLower, after) →
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
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel program pre failure target ctx) := by
  obtain ⟨callFuel, _hFuel, hFailureCase⟩ :=
    Yul.Source.Effectful.evalValues_primitive_observable_error_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun hObservable
  cases Expr.uncheckedPrimitiveLowering_of_lowerUnchecked? hLower with
  | @direct _ _ op lowerArgs seq
      hDirect hOp hArgs hSeq hOutputs =>
      rcases hFailureCase with hArgsFailure | hPrimitiveFailure
      · have hArgsReverse :
            Expr.List.toLocals1? args.reverse =
              some lowerArgs.reverse :=
          Expr.List.toLocals1?_reverse hArgs
        exact False.elim
          ((FunctionsObserverExpression.directNoObservableFailureAt
              contract transcript codeRel codeOverride callFuel).evalArgs
            hArgsReverse
            (StateRelation.Replay.rel_of_scopedExact hRel)
            hArgsFailure hObservable)
      · rcases hPrimitiveFailure with
          ⟨sourceAfterArgs, reversedValues, hArgsRun, hPrimRun⟩
        have hArgsReverse :
            Expr.List.toLocals1? args.reverse =
              some lowerArgs.reverse :=
          Expr.List.toLocals1?_reverse hArgs
        obtain
            ⟨targetAfterArgs, hTargetArgList, hArgsRel, _hArgsStore⟩ :=
          (FunctionsObserverExpression.directAt
            contract transcript codeRel codeOverride callFuel).evalArgs
            hArgsReverse
            (StateRelation.Replay.rel_of_scopedExact hRel)
            hArgsRun
        have hSeq' :
            Expr.List.toSeq? lowerArgs.reverse
                (Expressions.Structured.BasicOp.inputs op) =
              some seq := by
          simpa [Expr.List.toStackSeq?] using hSeq
        have hArgLength :
            reversedValues.length = lowerArgs.reverse.length :=
          Functions.Source.Effectful.ArgList.eval_length
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hTargetArgList
        have hSeqLength :
            lowerArgs.reverse.length =
              Expressions.Structured.BasicOp.inputs op :=
          Expr.List.toSeq?_length hSeq'
        have hArity :
            reversedValues.reverse.length =
              Expressions.Structured.BasicOp.inputs op := by
          simpa [List.length_reverse, hArgLength] using hSeqLength
        exact False.elim
          (FunctionsObserverPrimitive.safeCompilerSelected_noObservableFailure
            (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
            hOp hArity hArgsRel hPrimRun hObservable)
  | @bound _ _ _ op _ lowerArgs seq
      hBound hOp hArgs hSeq hOutputs =>
      rcases hFailureCase with hArgsFailure | hPrimitiveFailure
      · exact
          terminalArgsOfUncheckedLowering hArgs hEligible
            (fun hExprFuel hExprEligible hExprLower hExprRel hExprDomain
                hExprScope hExprRun =>
              hRegularExpr (by omega) hExprEligible hExprLower hExprRel
                hExprDomain hExprScope hExprRun)
            (fun hExprFuel hExprEligible hExprLower hExprRel hExprDomain
                hExprScope hExprRun hExprObservable =>
              hTerminalExpr (by omega) hExprEligible hExprLower hExprRel
                hExprDomain hExprScope hExprRun hExprObservable)
            hRel hDomain hScope hArgsFailure hObservable
      · rcases hPrimitiveFailure with
          ⟨sourceAfterArgs, reversedValues, hArgsRun, hPrimRun⟩
        obtain ⟨argsPrepared⟩ :=
          FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
            hArgs hEligible
            (fun hExprFuel hExprEligible hExprLower hExprRel hExprDomain
                hExprScope hExprRun =>
              hRegularExpr (by omega) hExprEligible hExprLower hExprRel
                hExprDomain hExprScope hExprRun)
            hRel hDomain hScope hArgsRun
        let targetAfterArgs :=
          argsPrepared.prepared.prepared.finalTarget
        have hStackArgs :=
          argsPrepared.prepared.stackStable targetAfterArgs
            (StateRelation.Vars.TargetExtends.refl _)
        have hStackArgs' :
            Functions.Source.Effectful.ArgList.eval
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                lowerArgs.reverse targetAfterArgs =
              .ok (targetAfterArgs, reversedValues) := by
          simpa [targetAfterArgs] using hStackArgs
        have hSeq' :
            Expr.List.toSeq? lowerArgs.reverse
                (Expressions.Structured.BasicOp.inputs op) =
              some seq := by
          simpa [Expr.List.toStackSeq?] using hSeq
        have hArgLength :
            reversedValues.length = lowerArgs.reverse.length :=
          Functions.Source.Effectful.ArgList.eval_length
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hStackArgs'
        have hSeqLength :
            lowerArgs.reverse.length =
              Expressions.Structured.BasicOp.inputs op :=
          Expr.List.toSeq?_length hSeq'
        have hArity :
            reversedValues.reverse.length =
              Expressions.Structured.BasicOp.inputs op := by
          simpa [List.length_reverse, hArgLength] using hSeqLength
        exact False.elim
          (FunctionsObserverPrimitive.safeCompilerSelected_noObservableFailure
            (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
            hOp hArity
            (StateRelation.Replay.rel_of_scopedExact
              argsPrepared.relation)
            hPrimRun hObservable)

namespace RecursiveTerminalExpressionForward

theorem ofPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {exprFuel : Nat} {before after : Fresh.State}
      {layout : List Name}
      {prim : EvmYul.Operation .Yul} {args : List AstExpr}
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
            (.Call (.inl prim) args) =
          true →
        Expr.lower1Unchecked? before (.Call (.inl prim) args) =
          some (pre, lower, after) →
        StateRelation.Replay.ScopedExactRel codeRel layout source target →
        StateRelation.Vars.TargetDomainWithin
          before.used target.source.vars →
        StateRelation.Vars.NamesWithin before.used ctx.scope →
        Yul.Source.Effectful.eval
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            exprFuel (.Call (.inl prim) args)
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            pre failure target ctx) := by
  intro exprFuel before after layout prim args pre lower source failure
    target ctx hFuel hExprOk hLower hRel hDomain hScope hRun hObservable
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  apply
    terminalPrimitiveOfLowering
      (fuel := exprFuel)
      (Eligible := fun expr =>
        SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
          true)
      (by simpa [Expr.lower1Unchecked?] using hLower)
      (fun expr hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
      (fun hExprFuel hExprOk hExprLower hExprRel hExprDomain
          hExprScope hExprRun =>
        hRegularExpr (by omega) hExprOk hExprLower hExprRel
          hExprDomain hExprScope hExprRun)
      (fun hExprFuel hExprOk hExprLower hExprRel hExprDomain
          hExprScope hExprRun hExprObservable =>
        hTerminalExpr (by omega) hExprOk hExprLower hExprRel
          hExprDomain hExprScope hExprRun hExprObservable)
      hRel hDomain hScope
      (Yul.Source.Effectful.eval_observable_error
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun)
      hObservable

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

theorem ofComponents
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
    RecursiveTerminalExpressionForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro exprFuel before after layout expr pre lower source failure
    target ctx hFuel hExprOk hLower hRel hDomain hScope hRun hObservable
  cases expr with
  | Lit value =>
      simp [Expr.lower1Unchecked?, Expr.lowerUnchecked?] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      have hDirectLower :
          Expr.toLocals? 1 (.Lit value) =
            some (.lit value : Locals.Expr 1) := by
        simp [Expr.toLocals?, Expr.cast]
      exact False.elim
        ((FunctionsObserverExpression.directNoObservableFailureAt
            contract transcript codeRel (some sourceProgram.contract)
            exprFuel).evalValues
          hDirectLower
          (StateRelation.Replay.rel_of_scopedExact hRel)
          (Yul.Source.Effectful.eval_observable_error
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hRun)
          hObservable)
  | Var name =>
      simp [Expr.lower1Unchecked?, Expr.lowerUnchecked?] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      have hDirectLower :
          Expr.toLocals? 1 (.Var name) =
            some (.var (identName name) : Locals.Expr 1) := by
        simp [Expr.toLocals?, Expr.cast]
      exact False.elim
        ((FunctionsObserverExpression.directNoObservableFailureAt
            contract transcript codeRel (some sourceProgram.contract)
            exprFuel).evalValues
          hDirectLower
          (StateRelation.Replay.rel_of_scopedExact hRel)
          (Yul.Source.Effectful.eval_observable_error
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hRun)
          hObservable)
  | Call callee args =>
      cases callee with
      | inl prim =>
          exact
            ofPrimitive hRegularExpr hTerminalExpr
              hFuel hExprOk hLower hRel hDomain hScope hRun hObservable
      | inr functionName =>
          exact
            ofFunctionCall hDecomposition hProgramOk hRegularExpr
              hTerminalExpr hTerminalBody
              hFuel hExprOk hLower hRel hDomain hScope hRun hObservable

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

theorem primitive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {prim : EvmYul.Operation .Yul} {args : List AstExpr}
      {lower : List Functions.Stmt}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      sourceFuel < bound + 1 →
        Prim.terminal? prim = none →
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout false false false
            (.ExprStmtCall (.Call (.inl prim) args)) =
          true →
        Stmt.toFunctionsListUncheckedFuel? compilerFuel before
            (.ExprStmtCall (.Call (.inl prim) args)) =
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
            (.ExprStmtCall (.Call (.inl prim) args))
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            lower failure target ctx) := by
  intro sourceFuel compilerFuel before after layout prim args lower
    source failure target ctx hFuel hNonterminal hStmtOk hLower hRel
    hDomain hScope hRun hObservable
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 0
          (.Call (.inl prim) args) =
        true := by
    simpa [SolcValidation.StmtOk?] using hStmtOk
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  obtain ⟨pre, lowerExpr, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_primitive_parts
      hNonterminal hLower
  subst lower
  obtain ⟨preResult⟩ :=
    terminalPrimitiveOfLowering
      (fuel := sourceFuel)
      (Eligible := fun expr =>
        SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
          true)
      (by simpa [Expr.lower0Unchecked?] using hExprLower)
      (fun expr hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
      (fun hExprFuel hExprOk hArgLower hExprRel hExprDomain
          hExprScope hExprRun =>
        hRegularExpr (by omega) hExprOk hArgLower hExprRel
          hExprDomain hExprScope hExprRun)
      (fun hExprFuel hExprOk hArgLower hExprRel hExprDomain
          hExprScope hExprRun hExprObservable =>
        hTerminalExpr (by omega) hExprOk hArgLower hExprRel
          hExprDomain hExprScope hExprRun hExprObservable)
      hRel hDomain hScope
      (Yul.Source.Effectful.exec_expr_primitive_observable_error_evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun hObservable)
      hObservable
  exact
    ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
      preResult [Functions.Stmt.expr lowerExpr]⟩

theorem terminalPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {prim : EvmYul.Operation .Yul} {args : List AstExpr}
      {kind : Assembly.HaltKind}
      {lower : List Functions.Stmt}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      sourceFuel < bound + 1 →
        Prim.terminal? prim = some kind →
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout false false false
            (.ExprStmtCall (.Call (.inl prim) args)) =
          true →
        Stmt.toFunctionsListUncheckedFuel? compilerFuel before
            (.ExprStmtCall (.Call (.inl prim) args)) =
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
            (.ExprStmtCall (.Call (.inl prim) args))
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            lower failure target ctx) := by
  intro sourceFuel compilerFuel before after layout prim args kind lower
    source failure target ctx hFuel hTerminal hStmtOk hLower hRel
    hDomain hScope hRun hObservable
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 0
          (.Call (.inl prim) args) =
        true := by
    simpa [SolcValidation.StmtOk?] using hStmtOk
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  rcases
      FunctionsObserverTerminal.statementClassify
        hTerminal hLower
        (fun candidate hMem =>
          SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
        (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
            hArgScope hArgRun =>
          hRegularExpr (by omega) hArgOk hArgLower hArgRel
            hArgDomain hArgScope hArgRun)
        hRel hDomain hScope hRun hObservable with
    hArgsFailure | hResult
  · rcases hArgsFailure with
      ⟨argsFuel, hSourceFuel, hArgsRun⟩
    obtain ⟨preArgs, lowerArgs, seq,
        hLowerArgs, hSeq, hLowerStmts⟩ :=
      Stmt.toFunctionsListUncheckedFuel?_expr_terminal_parts
        hTerminal hLower
    subst lower
    obtain ⟨argsResult⟩ :=
      terminalArgsOfUncheckedLowering
        (Expr.List.uncheckedBoundLowering_of_lowerBound1Unchecked?
          hLowerArgs)
        (fun candidate hMem =>
          SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
        (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
            hArgScope hArgRun =>
          hRegularExpr (by omega) hArgOk hArgLower hArgRel
            hArgDomain hArgScope hArgRun)
        (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
            hArgScope hArgRun hArgObservable =>
          hTerminalExpr (by omega) hArgOk hArgLower hArgRel
            hArgDomain hArgScope hArgRun hArgObservable)
        hRel hDomain hScope hArgsRun hObservable
    exact
      ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
        argsResult [Functions.Stmt.terminalArgs kind seq]⟩
  · exact hResult

theorem letOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {name : EvmYul.Identifier} {expr : AstExpr}
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
        (∀ functionName functionArgs,
          expr ≠ .Call (.inr functionName) functionArgs) →
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout canBreak canContinue canLeave
            (.Let [name] (some expr)) =
          true →
        Stmt.toFunctionsListUncheckedFuel? compilerFuel before
            (.Let [name] (some expr)) =
          some (lower, after) →
        StateRelation.Replay.ScopedExactRel codeRel layout source target →
        StateRelation.Vars.TargetDomainWithin
          before.used target.source.vars →
        StateRelation.Vars.NamesWithin before.used ctx.scope →
        Yul.Source.Effectful.exec
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceFuel (.Let [name] (some expr))
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            lower failure target ctx) := by
  intro sourceFuel compilerFuel before after layout name expr lower
    source failure target ctx canBreak canContinue canLeave
    hFuel hNotFunctionCall hStmtOk hLower hRel hDomain hScope
    hRun hObservable
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_one_parts
      hNotFunctionCall hLower
  subst lower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
        true := by
    simp [SolcValidation.StmtOk?] at hStmtOk
    exact hStmtOk.2
  obtain
      ⟨exprFuel, hSourceFuel, hExprValuesRun⟩ :=
    Yul.Source.Effectful.exec_let_some_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      (by
        rcases hRel.2 with
          ⟨sourceShared, sourceVars, hSource, _hShared,
            _hVars, hSourceDomain⟩
        change
          EvmYul.Yul.checkDeclaration source.source [name] = .ok ()
        rw [hSource]
        apply StateRelation.Vars.checkDeclaration_ok hSourceDomain
        · simp
        · intro candidate hMem
          simp only [List.mem_singleton] at hMem
          subst candidate
          simp [SolcValidation.StmtOk?, SolcValidation.bindableList?,
            SolcValidation.nonemptyNames?, SolcValidation.bindingNames?,
            SolcValidation.namesNodup?, SolcValidation.namesFresh?]
            at hStmtOk
          exact
            (hStmtOk.1.2.2.2 (identName name)
              (by simp [identNames, identName])).2)
      hRun hObservable
  have hExprRun :
      Yul.Source.Effectful.eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          exprFuel expr (some sourceProgram.contract) source =
        .error failure := by
    simp [Yul.Source.Effectful.eval, hExprValuesRun]
  obtain ⟨preResult⟩ :=
    hTerminalExpr (by omega) hExprOk hExprLower hRel hDomain hScope
      hExprRun hObservable
  exact
    ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
      preResult [Functions.Stmt.let_ (identName name) lowerValue]⟩

theorem assignOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {name : EvmYul.Identifier} {expr : AstExpr}
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
        (∀ functionName functionArgs,
          expr ≠ .Call (.inr functionName) functionArgs) →
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout canBreak canContinue canLeave (.Assign [name] expr) =
          true →
        Stmt.toFunctionsListUncheckedFuel? compilerFuel before
            (.Assign [name] expr) =
          some (lower, after) →
        StateRelation.Replay.ScopedExactRel codeRel layout source target →
        StateRelation.Vars.TargetDomainWithin
          before.used target.source.vars →
        StateRelation.Vars.NamesWithin before.used ctx.scope →
        Yul.Source.Effectful.exec
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            sourceFuel (.Assign [name] expr)
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            lower failure target ctx) := by
  intro sourceFuel compilerFuel before after layout name expr lower
    source failure target ctx canBreak canContinue canLeave
    hFuel hNotFunctionCall hStmtOk hLower hRel hDomain hScope
    hRun hObservable
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_one_parts
      hNotFunctionCall hLower
  subst lower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
        true := by
    simp [SolcValidation.StmtOk?] at hStmtOk
    exact hStmtOk.2
  obtain
      ⟨exprFuel, hSourceFuel, hExprValuesRun⟩ :=
    Yul.Source.Effectful.exec_assign_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      (by
        rcases hRel.2 with
          ⟨sourceShared, sourceVars, hSource, _hShared,
            _hVars, hSourceDomain⟩
        change
          EvmYul.Yul.checkAssignment source.source [name] = .ok ()
        rw [hSource]
        apply StateRelation.Vars.checkAssignment_ok hSourceDomain
        · simp
        · intro candidate hMem
          simp only [List.mem_singleton] at hMem
          subst candidate
          simp [SolcValidation.StmtOk?, SolcValidation.assignableList?,
            SolcValidation.nonemptyNames?, SolcValidation.namesNodup?,
            SolcValidation.namesIn?] at hStmtOk
          exact
            hStmtOk.1.2.2 (identName name)
              (by simp [identNames, identName]))
      hRun hObservable
  have hExprRun :
      Yul.Source.Effectful.eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          exprFuel expr (some sourceProgram.contract) source =
        .error failure := by
    simp [Yul.Source.Effectful.eval, hExprValuesRun]
  obtain ⟨preResult⟩ :=
    hTerminalExpr (by omega) hExprOk hExprLower hRel hDomain hScope
      hExprRun hObservable
  exact
    ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
      preResult [Functions.Stmt.assign (identName name) lowerValue]⟩

theorem letCall
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
      {names : List EvmYul.Identifier}
      {functionName : Name} {args : List AstExpr}
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
            layout canBreak canContinue canLeave
            (.Let names (some (.Call (.inr functionName) args))) =
          true →
        StateRelation.Vars.NamesWithin before.used (identNames names) →
        Stmt.toFunctionsListUncheckedFuel? compilerFuel before
            (.Let names (some (.Call (.inr functionName) args))) =
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
            (.Let names (some (.Call (.inr functionName) args)))
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            lower failure target ctx) := by
  intro sourceFuel compilerFuel before after layout names functionName args
    lower source failure target ctx canBreak canContinue canLeave
    hFuel hStmtOk hNamesUsed hLower hRel hDomain hScope hRun hObservable
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_call_parts hLower
  subst lower
  have hOkParts := hStmtOk
  simp [SolcValidation.StmtOk?, SolcValidation.bindableList?,
    SolcValidation.nonemptyNames?, SolcValidation.bindingNames?,
    SolcValidation.namesNodup?, SolcValidation.namesFresh?]
    at hOkParts
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          names.length (.Call (.inr functionName) args) =
        true :=
    hOkParts.2
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hCheck :
      EvmYul.Yul.checkDeclaration source.source names = .ok () := by
    rw [hSource]
    apply StateRelation.Vars.checkDeclaration_ok hSourceDomain
    · simpa [identNames_eq_self] using hOkParts.1.2.2.1
    · intro candidate hMem
      exact
        (hOkParts.1.2.2.2 candidate
          (by simpa [identNames_eq_self] using hMem)).2
  obtain ⟨hTargetsNodup, hTargetsFresh⟩ :=
    StateRelation.Vars.checkDeclaration_ok_parts
      hSourceDomain (by simpa [hSource] using hCheck)
  obtain
      ⟨evalFuel, hSourceFuel, hEvalValues⟩ :=
    Yul.Source.Effectful.exec_let_some_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hCheck hRun hObservable
  obtain
      ⟨initFuel, initVars, initCtx,
        hInsert, hInitRun, hInitCtx⟩ :=
    FunctionsObserverStatement.InitNames.run
      (contract := contract) (program := targetProgram.toFunctions)
      (identNames names) target ctx
  let targetDeclared :=
    target.withSource
      { shared := target.source.shared, vars := initVars }
  have hDeclaredRel :
      StateRelation.Replay.ScopedExactRel codeRel layout
        source targetDeclared := by
    simpa [targetDeclared] using
      StateRelation.Replay.scopedExact_insertMany_hidden
        hRel
        (by simpa [identNames_eq_self] using hTargetsFresh)
        hInsert
  have hDeclaredDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used targetDeclared.source.vars := by
    simpa [targetDeclared] using
      hDomain.insertMany hNamesUsed hInsert
  have hDeclaredScope :
      StateRelation.Vars.NamesWithin before.used initCtx.scope := by
    rw [hInitCtx]
    intro candidate hMem
    rcases List.mem_append.mp hMem with hDeclared | hOuter
    · exact hNamesUsed candidate (by simpa using hDeclared)
    · exact hScope candidate hOuter
  obtain ⟨callResult⟩ :=
    terminalCallOfUncheckedLowering
      (targets := identNames names)
      hDecomposition hProgramOk hExprOk hArgsLowering
      (by simpa [identNames_eq_self] using hTargetsNodup)
      hRegularExpr hTerminalExpr hTerminalBody
      (by omega) hDeclaredRel hDeclaredDomain hDeclaredScope
      hEvalValues hObservable
  let result :=
    FunctionsObserverTerminal.StatementResult.prependRegularRun
      (leftLower := Stmt.initNames (identNames names))
      (rightLower :=
        preArgs ++
          [Functions.Stmt.call
            (identNames names) functionName lowerArgs])
      (target := target) (middleTarget := targetDeclared)
      (ctx := ctx) (middleCtx := initCtx)
      (contract := contract) (codeRel := codeRel)
      (program := targetProgram.toFunctions)
      (failure := failure)
      ⟨initFuel, by simpa [targetDeclared] using hInitRun⟩
      callResult
  exact ⟨by simpa [result, List.append_assoc] using result⟩

theorem assignCall
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
      {names : List EvmYul.Identifier}
      {functionName : Name} {args : List AstExpr}
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
            layout canBreak canContinue canLeave
            (.Assign names (.Call (.inr functionName) args)) =
          true →
        Stmt.toFunctionsListUncheckedFuel? compilerFuel before
            (.Assign names (.Call (.inr functionName) args)) =
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
            (.Assign names (.Call (.inr functionName) args))
            (some sourceProgram.contract) source =
          .error failure →
        Yul.Source.Effectful.Exception.Observable failure.exception →
        Nonempty
          (FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            lower failure target ctx) := by
  intro sourceFuel compilerFuel before after layout names functionName args
    lower source failure target ctx canBreak canContinue canLeave
    hFuel hStmtOk hLower hRel hDomain hScope hRun hObservable
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_call_parts hLower
  subst lower
  have hOkParts := hStmtOk
  simp [SolcValidation.StmtOk?, SolcValidation.assignableList?,
    SolcValidation.nonemptyNames?, SolcValidation.namesNodup?,
    SolcValidation.namesIn?] at hOkParts
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          names.length (.Call (.inr functionName) args) =
        true :=
    hOkParts.2
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hCheck :
      EvmYul.Yul.checkAssignment source.source names = .ok () := by
    rw [hSource]
    apply StateRelation.Vars.checkAssignment_ok hSourceDomain
    · simpa [identNames_eq_self] using hOkParts.1.2.1
    · intro candidate hMem
      exact
        hOkParts.1.2.2 candidate
          (by simpa [identNames_eq_self] using hMem)
  obtain ⟨hTargetsNodup, _hTargetsVisible⟩ :=
    StateRelation.Vars.checkAssignment_ok_parts
      hSourceDomain (by simpa [hSource] using hCheck)
  obtain
      ⟨evalFuel, hSourceFuel, hEvalValues⟩ :=
    Yul.Source.Effectful.exec_assign_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hCheck hRun hObservable
  exact
    terminalCallOfUncheckedLowering
      (targets := identNames names)
      hDecomposition hProgramOk hExprOk hArgsLowering
      (by simpa [identNames_eq_self] using hTargetsNodup)
      hRegularExpr hTerminalExpr hTerminalBody
      (by omega) hRel hDomain hScope hEvalValues hObservable

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

theorem ofCompound
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
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hCompound :
      RecursiveTerminalCompoundForward contract transcript codeRel
        sourceProgram targetProgram profile (bound + 1)) :
    RecursiveTerminalStmtForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source failure target ctx canBreak canContinue canLeave
    hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
    hRun hObservable
  cases stmt with
  | Block body =>
      exact
        hCompound (.block body) hFuel hOk hNames hLower hRel hDomain
          hScope hLayout hControl hRun hObservable
  | Switch scrutinee cases defaultBody =>
      exact
        hCompound (.switch scrutinee cases defaultBody)
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
          hRun hObservable
  | For cond post body =>
      exact
        hCompound (.forLoop cond post body)
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
          hRun hObservable
  | If cond body =>
      exact
        hCompound (.ifThen cond body)
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
          hRun hObservable
  | Let names value? =>
      cases value? with
      | none =>
          have hOkParts := hOk
          simp [SolcValidation.StmtOk?, SolcValidation.bindableList?,
            SolcValidation.nonemptyNames?,
            SolcValidation.bindingNames?,
            SolcValidation.namesNodup?,
            SolcValidation.namesFresh?] at hOkParts
          obtain
              ⟨sourceShared, sourceVars, hSource,
                _hShared, _hScoped, hSourceDomain⟩ :=
            hRel.2
          have hCheck :
              EvmYul.Yul.checkDeclaration source.source names =
                .ok () := by
            rw [hSource]
            apply StateRelation.Vars.checkDeclaration_ok hSourceDomain
            · simpa [identNames_eq_self] using hOkParts.2.2.1
            · intro candidate hMem
              exact
                (hOkParts.2.2.2 candidate
                  (by simpa [identNames_eq_self] using hMem)).2
          exact
            (Yul.Source.Effectful.exec_let_none_observable_error_false
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hCheck hRun hObservable).elim
      | some value =>
          by_cases hFunctionCall :
              ∃ functionName functionArgs,
                value = .Call (.inr functionName) functionArgs
          · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
            have hNamesUsed :
                StateRelation.Vars.NamesWithin before.used
                  (identNames names) := by
              intro candidate hMem
              apply hNames candidate
              exact List.mem_append_left _ hMem
            exact
              letCall hDecomposition hProgramOk hRegularExpr
                hTerminalExpr hTerminalBody hFuel hOk hNamesUsed hLower
                hRel hDomain hScope hRun hObservable
          · have hNotFunctionCall :
                ∀ functionName functionArgs,
                  value ≠ .Call (.inr functionName) functionArgs := by
              intro functionName functionArgs hEq
              exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
            obtain ⟨name, hNamesEq⟩ :=
              Stmt.toFunctionsListUncheckedFuel?_let_noncall_singleton
                hNotFunctionCall hLower
            subst names
            exact
              letOne hTerminalExpr hFuel hNotFunctionCall hOk hLower
                hRel hDomain hScope hRun hObservable
  | Assign names value =>
      by_cases hFunctionCall :
          ∃ functionName functionArgs,
            value = .Call (.inr functionName) functionArgs
      · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
        exact
          assignCall hDecomposition hProgramOk hRegularExpr
            hTerminalExpr hTerminalBody hFuel hOk hLower hRel hDomain
            hScope hRun hObservable
      · have hNotFunctionCall :
            ∀ functionName functionArgs,
              value ≠ .Call (.inr functionName) functionArgs := by
          intro functionName functionArgs hEq
          exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
        obtain ⟨name, hNamesEq⟩ :=
          Stmt.toFunctionsListUncheckedFuel?_assign_noncall_singleton
            hNotFunctionCall hLower
        subst names
        exact
          assignOne hTerminalExpr hFuel hNotFunctionCall hOk hLower
            hRel hDomain hScope hRun hObservable
  | ExprStmtCall value =>
      cases value with
      | Lit literal =>
          simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
      | Var name =>
          simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hLeafOk :
                  SolcValidation.StmtOk? profile sourceProgram.contract
                      ((Contract.functionEntries
                        sourceProgram.contract).map Prod.fst)
                      layout false false false
                      (.ExprStmtCall (.Call (.inl prim) args)) =
                    true := by
                simpa [SolcValidation.StmtOk?] using hOk
              cases hTerminal : Prim.terminal? prim with
              | none =>
                  exact
                    primitive hRegularExpr hTerminalExpr
                      hFuel hTerminal hLeafOk hLower hRel hDomain hScope
                      hRun hObservable
              | some kind =>
                  exact
                    terminalPrimitive hRegularExpr hTerminalExpr
                      hFuel hTerminal hLeafOk hLower hRel hDomain hScope
                      hRun hObservable
          | inr functionName =>
              have hLeafOk :
                  SolcValidation.StmtOk? profile sourceProgram.contract
                      ((Contract.functionEntries
                        sourceProgram.contract).map Prod.fst)
                      layout false false false
                      (.ExprStmtCall
                        (.Call (.inr functionName) args)) =
                    true := by
                simpa [SolcValidation.StmtOk?] using hOk
              exact
                functionCall hDecomposition hProgramOk hRegularExpr
                  hTerminalExpr hTerminalBody hFuel hLeafOk hLower hRel
                  hDomain hScope hRun hObservable
  | Break =>
      exact
        (Yul.Source.Effectful.exec_break_observable_error_false
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable).elim
  | Continue =>
      exact
        (Yul.Source.Effectful.exec_continue_observable_error_false
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable).elim
  | Leave =>
      exact
        (Yul.Source.Effectful.exec_leave_observable_error_false
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable).elim

end RecursiveTerminalStmtForward

namespace RecursiveTerminalLoopForward

theorem ofCompiler
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hRegularList :
      FunctionsObserverForward.RecursiveOpenListForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveTerminalLoopForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel sourceControl before after afterCond afterPost
        layout cond post body preCond lowerCond lowerPost lowerBody
        source failure target ctx canBreak canContinue canLeave
        hFuel hCondOk hPostOk hBodyOk hCondNames hPostNames hBodyNames
        hLowerCond hLowerPost hLowerBody hRel hDomain hScope hLayout
        hControl hRun hObservable
      obtain ⟨loopFuel, hSourceFuel, hLoopRun⟩ :=
        Yul.Source.Effectful.exec_for_observable_error_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable
      obtain ⟨iterationFuel, hLoopFuel, hFailureCase⟩ :=
        Yul.Source.Effectful.loop_observable_error_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hLoopRun hObservable
      obtain
          ⟨sourceShared, sourceVars, hSource,
            _hShared, _hScoped, _hSourceDomain⟩ :=
        hRel.2
      have hConditionInput :
          source.withSource
              (EvmYul.Yul.State.mkOk source.source) =
            source := by
        rw [hSource]
        change source.withSource (.Ok sourceShared sourceVars) = source
        rw [← hSource]
        exact Simulation.ResourceReplay.State.withSource_self source
      have hCondFresh : Fresh.Extends before afterCond :=
        Expr.lower1Unchecked?_stateExtends hLowerCond
      have hPostFresh : Fresh.Extends afterCond afterPost :=
        Stmt.List.toBlockUncheckedFuel?_stateExtends hLowerPost
      have hBodyFresh : Fresh.Extends afterPost after :=
        Stmt.List.toBlockUncheckedFuel?_stateExtends hLowerBody
      have hFresh : Fresh.Extends before after :=
        Fresh.Extends.trans hCondFresh
          (Fresh.Extends.trans hPostFresh hBodyFresh)
      have hLayoutAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used layout :=
        hLayout.mono hCondFresh
      have hLayoutAfterPost :
          StateRelation.Vars.NamesWithin afterPost.used layout :=
        hLayout.mono (Fresh.Extends.trans hCondFresh hPostFresh)
      have hPostNamesAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used
            (Stmt.List.names post) :=
        hPostNames.mono hCondFresh
      have hBodyNamesAfterPost :
          StateRelation.Vars.NamesWithin afterPost.used
            (Stmt.List.names body) :=
        hBodyNames.mono (Fresh.Extends.trans hCondFresh hPostFresh)
      have hScopeAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used ctx.scope :=
        hScope.mono hCondFresh
      have hBodyBaseScope :
          StateRelation.Vars.NamesWithin before.used
            (ctx.withLoopControl ctx.scope ctx.scope).scope := by
        simpa [Functions.Source.Ctx.withLoopControl] using hScope
      have hBodyControl :
          FunctionsObserverForward.ControlContextRel
            (FunctionsObserverForward.ControlContextRel.forBodySourceControl
              layout sourceControl)
            layout true true canLeave
            (ctx.withLoopControl ctx.scope ctx.scope) :=
        FunctionsObserverForward.ControlContextRel.forBody hControl
      have hPostControl :
          FunctionsObserverForward.ControlContextRel
            (FunctionsObserverForward.ControlContextRel.forPostSourceControl
              sourceControl)
            layout false false canLeave ctx.withoutLoopControl :=
        FunctionsObserverForward.ControlContextRel.forPost hControl
      rcases hFailureCase with hCondFailure | hAfterCond
      · have hCondFailure' :
            Yul.Source.Effectful.eval
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                iterationFuel cond (some sourceProgram.contract) source =
              .error failure := by
          simpa [ObserverSemantics.SourceReplay.stateModel,
            hConditionInput] using hCondFailure
        obtain ⟨condResult⟩ :=
          hTerminalExpr (by omega) hCondOk hLowerCond hRel hDomain
            hBodyBaseScope hCondFailure' hObservable
        let guardedBody :=
          FunctionsObserverTerminal.StatementResult.appendUnreachable
            condResult
            (.if_
                (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                { stmts := [.brk] } ::
              lowerBody.stmts)
        exact
          FunctionsObserverTerminal.ForLoopResult.ofBody
            (ctx := ctx) (post := lowerPost)
            (body :=
              { stmts :=
                  preCond ++
                    .if_
                      (.prim .iszero
                        (Locals.ExprSeq.cons lowerCond .nil))
                      { stmts := [.brk] } ::
                    lowerBody.stmts })
            guardedBody
      · rcases hAfterCond with
          ⟨sourceAfterCond, condValue, hCondRun, hLoopCase⟩
        have hCondRun' :
            Yul.Source.Effectful.eval
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                iterationFuel cond (some sourceProgram.contract) source =
              .ok (sourceAfterCond, condValue) := by
          simpa [ObserverSemantics.SourceReplay.stateModel,
            hConditionInput] using hCondRun
        obtain ⟨values, hCondValues, hCondHead⟩ :=
          Yul.Source.Effectful.eval_ok_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hCondRun'
        obtain ⟨value, hValues, preparedNonempty⟩ :=
          hValue (exprFuel := iterationFuel)
            (before := before) (after := afterCond)
            (layout := layout) (expr := cond)
            (pre := preCond) (lower := lowerCond)
            (source := source) (source' := sourceAfterCond)
            (target := target)
            (ctx := ctx.withLoopControl ctx.scope ctx.scope)
            (values := values)
            (by omega) hCondOk hLowerCond hRel hDomain
            hBodyBaseScope hCondValues
        obtain ⟨prepared⟩ := preparedNonempty
        have hCondValue : condValue = value := by
          rw [hValues] at hCondHead
          simpa using hCondHead
        subst value
        have hPreparedLayoutScope :
            FunctionsObserverOutcome.LayoutWithinScope
              layout prepared.prepared.finalCtx := by
          obtain ⟨preFuel, hPreRun⟩ := prepared.prepared.run
          have hExtends :=
            Functions.Source.Effectful.Block.runOpen_scopeExtends
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hPreRun
          exact fun name hMem =>
            hExtends name (hBodyControl.scope name hMem)
        have hPreparedControl :
            FunctionsObserverForward.ControlContextRel
              (FunctionsObserverForward.ControlContextRel.forBodySourceControl
                layout sourceControl)
              layout true true canLeave prepared.prepared.finalCtx :=
          FunctionsObserverForward.ControlContextRel.transport hBodyControl
            (fun _name hMem => hMem)
            prepared.prepared.control hPreparedLayoutScope
        cases hLoopCase with
        | body hNonzero hBodyFailure =>
            obtain ⟨listCompilerFuel, lowerBodyStmts, _hBlockFuel,
                hLowerBodyList, hLowerBodyEq⟩ :=
              Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
            subst lowerBody
            rcases
                Yul.Source.Effectful.exec_block_error_parts
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  hBodyFailure with hOuter | hBodyParts
            · rcases hOuter with ⟨rfl, hFailure⟩
              rw [← hFailure] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable]
                at hObservable
            · rcases hBodyParts with
                ⟨bodyFuel, hBodyFuel, hBodyListRun⟩
              obtain ⟨bodyResult⟩ :=
                hTerminalList
                  (sourceFuel := bodyFuel)
                  (compilerFuel := listCompilerFuel)
                  (sourceControl :=
                    FunctionsObserverForward.ControlContextRel.forBodySourceControl
                      layout sourceControl)
                  (before := afterPost) (after := after)
                  (layout := layout) (stmts := body)
                  (lower := lowerBodyStmts)
                  (source := sourceAfterCond) (failure := failure)
                  (target := prepared.prepared.evalTarget)
                  (ctx := prepared.prepared.finalCtx)
                  (canBreak := true) (canContinue := true)
                  (canLeave := canLeave)
                  (by omega) hBodyOk hBodyNamesAfterPost
                  hLowerBodyList prepared.relation
                  (prepared.prepared.domain.mono hPostFresh)
                  (prepared.prepared.scope.mono hPostFresh)
                  hLayoutAfterPost hPreparedControl
                  hBodyListRun hObservable
              obtain ⟨guardFuel, hGuardRun⟩ :=
                Functions.Source.Effectful.Block.runOpen_forGuard_body_exists
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions prepared.prepared.run
                  prepared.prepared.eval
                  (Functions.ObserverSafety.SafeSemantics.eval_iszero
                    prepared.prepared.evalTarget condValue)
                  hNonzero bodyResult.run
              let guardedBody :
                  FunctionsObserverTerminal.StatementResult
                    contract codeRel targetProgram.toFunctions
                    (preCond ++
                      .if_
                          (.prim .iszero
                            (Locals.ExprSeq.cons lowerCond .nil))
                          { stmts := [.brk] } ::
                        lowerBodyStmts)
                    failure target
                    (ctx.withLoopControl ctx.scope ctx.scope) :=
                { kind := bodyResult.kind
                  finalTarget := bodyResult.finalTarget
                  finalCtx := bodyResult.finalCtx
                  run := ⟨guardFuel, hGuardRun⟩
                  relation := bodyResult.relation }
              exact
                FunctionsObserverTerminal.ForLoopResult.ofBody
                  (ctx := ctx) (post := lowerPost)
                  (body :=
                    { stmts :=
                        preCond ++
                          .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBodyStmts })
                  guardedBody
        | post hNonzero hBody hBodyContinues hPostFailure =>
            rename_i sourceAfterBody
            obtain ⟨closedBody⟩ :=
              FunctionsObserverForward.RecursiveOpenCompoundForward.closeGuardedBody
                (sourceControl :=
                  FunctionsObserverForward.ControlContextRel.forBodySourceControl
                    layout sourceControl)
                hRegularList prepared (by omega) hBodyOk
                hBodyNamesAfterPost hLowerBody hPostFresh hFresh
                hLayout hLayoutAfterPost hBodyControl hNonzero hBody
            obtain ⟨bodyResult⟩ :=
              FunctionsObserverForward.ClosedListResult.continuingBody
                closedBody hBodyContinues rfl
            obtain ⟨listCompilerFuel, lowerPostStmts, _hBlockFuel,
                hLowerPostList, hLowerPostEq⟩ :=
              Stmt.List.toBlockUncheckedFuel?_parts hLowerPost
            subst lowerPost
            rcases
                Yul.Source.Effectful.exec_block_error_parts
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  hPostFailure with hOuter | hPostParts
            · rcases hOuter with ⟨rfl, hFailure⟩
              rw [← hFailure] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable]
                at hObservable
            · rcases hPostParts with
                ⟨postFuel, hPostFuel, hPostListRun⟩
              obtain ⟨postResult⟩ :=
                hTerminalList
                  (sourceFuel := postFuel)
                  (compilerFuel := listCompilerFuel)
                  (sourceControl :=
                    FunctionsObserverForward.ControlContextRel.forPostSourceControl
                      sourceControl)
                  (before := afterCond) (after := afterPost)
                  (layout := layout) (stmts := post)
                  (lower := lowerPostStmts)
                  (source :=
                    sourceAfterBody.withSource
                      sourceAfterBody.source.reviveJump)
                  (failure := failure)
                  (target := bodyResult.outcome.state)
                  (ctx := ctx.withoutLoopControl)
                  (canBreak := false) (canContinue := false)
                  (canLeave := canLeave)
                  (by omega) hPostOk hPostNamesAfterCond
                  hLowerPostList bodyResult.relation
                  (bodyResult.targetDomain
                    (by
                      simpa [Functions.Source.Ctx.withLoopControl] using
                        hScopeAfterCond))
                  (by
                    simpa [Functions.Source.Ctx.withoutLoopControl] using
                      hScopeAfterCond)
                  hLayoutAfterCond hPostControl
                  hPostListRun hObservable
              obtain ⟨bodyTargetFuel, hBodyTarget⟩ := bodyResult.run
              obtain ⟨postTargetFuel, hPostOpen⟩ := postResult.run
              have hPostScoped :
                  Functions.Source.Effectful.Block.runScoped
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      { stmts := lowerPostStmts } postTargetFuel
                      bodyResult.outcome.state =
                    .ok
                      (Functions.Source.Effectful.Outcome.halt
                        postResult.kind postResult.finalTarget) :=
                Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions hPostOpen (by simp)
              let commonFuel := max bodyTargetFuel postTargetFuel
              have hBodyTarget' :
                  Functions.Source.Effectful.Block.runScoped
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions
                      (ctx.withLoopControl ctx.scope ctx.scope)
                      { stmts :=
                          preCond ++
                            .if_
                              (.prim .iszero
                                (Locals.ExprSeq.cons lowerCond .nil))
                              { stmts := [.brk] } ::
                            lowerBody.stmts }
                      commonFuel target =
                    .ok bodyResult.outcome :=
                Functions.Source.Effectful.Block.runScoped_mono
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (Nat.le_max_left _ _) hBodyTarget
              have hPostScoped' :
                  Functions.Source.Effectful.Block.runScoped
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      { stmts := lowerPostStmts } commonFuel
                      bodyResult.outcome.state =
                    .ok
                      (Functions.Source.Effectful.Outcome.halt
                        postResult.kind postResult.finalTarget) :=
                Functions.Source.Effectful.Block.runScoped_mono
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (Nat.le_max_right _ _) hPostScoped
              have hLoopTarget :
                  Functions.Source.Effectful.Stmt.runForLoop
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      (.lit (EvmYul.UInt256.ofNat 1))
                      ctx.withoutLoopControl
                      { stmts := lowerPostStmts }
                      (ctx.withLoopControl ctx.scope ctx.scope)
                      { stmts :=
                          preCond ++
                            .if_
                              (.prim .iszero
                                (Locals.ExprSeq.cons lowerCond .nil))
                              { stmts := [.brk] } ::
                            lowerBody.stmts }
                      (commonFuel + 1) target =
                    .ok
                      (Functions.Source.Effectful.Outcome.halt
                        postResult.kind postResult.finalTarget) := by
                rcases bodyResult.mode with hRegular | hContinue
                · have hBodyEq :
                      bodyResult.outcome =
                        Functions.Source.Effectful.Outcome.regular
                          bodyResult.outcome.state :=
                    Functions.Source.Effectful.Outcome.eq_regular_of_mode
                      hRegular
                  rw [hBodyEq] at hBodyTarget'
                  exact
                    Functions.Source.Effectful.Stmt.runForLoop_regular_post_halt_of_runs
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions
                      (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                        target)
                      hBodyTarget' hPostScoped'
                · have hBodyEq :
                      bodyResult.outcome =
                        Functions.Source.Effectful.Outcome.cont
                          bodyResult.outcome.state :=
                    Functions.Source.Effectful.Outcome.eq_cont_of_mode
                      hContinue
                  rw [hBodyEq] at hBodyTarget'
                  exact
                    Functions.Source.Effectful.Stmt.runForLoop_cont_post_halt_of_runs
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions
                      (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                        target)
                      hBodyTarget' hPostScoped'
              exact
                ⟨
                  { kind := postResult.kind
                    finalTarget := postResult.finalTarget
                    run := ⟨commonFuel + 1, hLoopTarget⟩
                    relation := postResult.relation }⟩
        | recurse hNonzero hBody hBodyContinues hPost hPostRecurs
            hRecursive =>
            rename_i sourceAfterBody sourceAfterPost
            obtain ⟨closedBody⟩ :=
              FunctionsObserverForward.RecursiveOpenCompoundForward.closeGuardedBody
                (sourceControl :=
                  FunctionsObserverForward.ControlContextRel.forBodySourceControl
                    layout sourceControl)
                hRegularList prepared (by omega) hBodyOk
                hBodyNamesAfterPost hLowerBody hPostFresh hFresh
                hLayout hLayoutAfterPost hBodyControl hNonzero hBody
            obtain ⟨bodyResult⟩ :=
              FunctionsObserverForward.ClosedListResult.continuingBody
                closedBody hBodyContinues rfl
            obtain ⟨closedPost⟩ :=
              FunctionsObserverForward.RecursiveOpenCompoundForward.closeLoopPost
                (sourceControl :=
                  FunctionsObserverForward.ControlContextRel.forPostSourceControl
                    sourceControl)
                hRegularList bodyResult (by omega) hPostOk
                hPostNamesAfterCond hLowerPost hBodyFresh
                (by
                  simpa [Functions.Source.Ctx.withLoopControl] using
                    hScopeAfterCond)
                (by
                  simpa [Functions.Source.Ctx.withoutLoopControl] using
                    hScopeAfterCond)
                hLayoutAfterCond hPostControl hPost
            cases hSourcePost : sourceAfterPost.source with
            | OutOfFuel =>
                change
                  Yul.Source.Effectful.LoopPostRecurs
                    sourceAfterPost.source at hPostRecurs
                rw [hSourcePost] at hPostRecurs
                simp [Yul.Source.Effectful.LoopPostRecurs] at hPostRecurs
            | Checkpoint jump =>
                cases jump with
                | Leave shared store =>
                    change
                      Yul.Source.Effectful.LoopPostRecurs
                        sourceAfterPost.source at hPostRecurs
                    rw [hSourcePost] at hPostRecurs
                    simp [Yul.Source.Effectful.LoopPostRecurs] at hPostRecurs
                | Break shared store =>
                    have hMode :
                        closedPost.outcome.mode = .brk := by
                      have hModeRel := closedPost.relation.mode
                      rw [hSourcePost] at hModeRel
                      exact
                        FunctionsObserverOutcome.ModeRel.source_break_target_brk
                          hModeRel
                    have hExit := closedPost.exitScope
                    simp [FunctionsObserverOutcome.ExitScopeRel,
                      FunctionsObserverForward.ControlContextRel.forPostSourceControl,
                      hMode] at hExit
                | Continue shared store =>
                    have hMode :
                        closedPost.outcome.mode = .cont := by
                      have hModeRel := closedPost.relation.mode
                      rw [hSourcePost] at hModeRel
                      exact
                        FunctionsObserverOutcome.ModeRel.source_continue_target_cont
                          hModeRel
                    have hExit := closedPost.exitScope
                    simp [FunctionsObserverOutcome.ExitScopeRel,
                      FunctionsObserverForward.ControlContextRel.forPostSourceControl,
                      hMode] at hExit
            | Ok postShared postStore =>
                rcases lowerPost with ⟨lowerPostStmts⟩
                have hPostMode :
                    closedPost.outcome.mode = .regular := by
                  have hModeRel := closedPost.relation.mode
                  rw [hSourcePost] at hModeRel
                  exact
                    FunctionsObserverOutcome.ModeRel.source_ok_target_regular
                      hModeRel
                have hPostRel :
                    StateRelation.Replay.ScopedExactRel codeRel layout
                      sourceAfterPost closedPost.outcome.state := by
                  have hExact := closedPost.relation.exact hPostMode
                  have hLayoutEq :=
                    closedPost.regularLayout hPostMode
                  have hRevived :
                      sourceAfterPost.withSource
                          sourceAfterPost.source.reviveJump =
                        sourceAfterPost := by
                    rw [hSourcePost]
                    change
                      sourceAfterPost.withSource
                          (.Ok postShared postStore) =
                        sourceAfterPost
                    rw [← hSourcePost]
                    exact
                      Simulation.ResourceReplay.State.withSource_self
                        sourceAfterPost
                  rw [hRevived] at hExact
                  simpa [hLayoutEq] using hExact
                have hPostDomain :
                    StateRelation.Vars.TargetDomainWithin before.used
                      closedPost.outcome.state.source.vars := by
                  have hRestricted := closedPost.targetRestriction
                  simp [FunctionsObserverOutcome.ScopedTargetRestriction,
                    hPostMode] at hRestricted
                  exact
                    hRestricted.domain
                      (by
                        simpa [Functions.Source.Ctx.withoutLoopControl] using
                          hScope)
                have hRecursiveInput :
                    sourceAfterPost.withSource
                        (sourceAfterPost.source.overwrite? source.source) =
                      sourceAfterPost := by
                  rw [hSourcePost, hSource]
                  change
                    sourceAfterPost.withSource
                        (.Ok postShared postStore) =
                      sourceAfterPost
                  rw [← hSourcePost]
                  exact
                    Simulation.ResourceReplay.State.withSource_self
                      sourceAfterPost
                have hRecursive' :
                    Yul.Source.Effectful.exec
                        (ObserverSemantics.SourceReplay.stateModel transcript)
                        (ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        iterationFuel (.For cond post body)
                        (some sourceProgram.contract) sourceAfterPost =
                      .error failure := by
                  simpa [ObserverSemantics.SourceReplay.stateModel,
                    hRecursiveInput] using hRecursive
                obtain ⟨recursive⟩ :=
                  ih iterationFuel (by omega)
                    (compilerFuel := compilerFuel)
                    (sourceControl := sourceControl)
                    (before := before) (after := after)
                    (afterCond := afterCond) (afterPost := afterPost)
                    (layout := layout) (cond := cond)
                    (post := post) (body := body)
                    (preCond := preCond) (lowerCond := lowerCond)
                    (lowerPost := { stmts := lowerPostStmts })
                    (lowerBody := lowerBody)
                    (source := sourceAfterPost) (failure := failure)
                    (target := closedPost.outcome.state) (ctx := ctx)
                    (canBreak := canBreak)
                    (canContinue := canContinue) (canLeave := canLeave)
                    (by omega) hCondOk hPostOk hBodyOk hCondNames
                    hPostNames hBodyNames hLowerCond hLowerPost hLowerBody
                    hPostRel hPostDomain hScope hLayout hControl
                    hRecursive' hObservable
                obtain ⟨bodyTargetFuel, hBodyTarget⟩ := bodyResult.run
                obtain ⟨postTargetFuel, hPostTarget⟩ := closedPost.run
                obtain ⟨recursiveFuel, hRecursiveTarget⟩ := recursive.run
                have hPostEq :
                    closedPost.outcome =
                  Functions.Source.Effectful.Outcome.regular
                        closedPost.outcome.state :=
                  Functions.Source.Effectful.Outcome.eq_regular_of_mode
                    hPostMode
                rw [hPostEq] at hPostTarget
                let commonFuel :=
                  max bodyTargetFuel (max postTargetFuel recursiveFuel)
                have hBodyTarget' :
                    Functions.Source.Effectful.Block.runScoped
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (ctx.withLoopControl ctx.scope ctx.scope)
                        { stmts :=
                            preCond ++
                              .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                        commonFuel target =
                      .ok bodyResult.outcome :=
                  Functions.Source.Effectful.Block.runScoped_mono
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions
                    (Nat.le_max_left _ _) hBodyTarget
                have hPostTarget' :
                    Functions.Source.Effectful.Block.runScoped
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions ctx.withoutLoopControl
                        { stmts := lowerPostStmts } commonFuel
                        bodyResult.outcome.state =
                      .ok
                        (Functions.Source.Effectful.Outcome.regular
                          closedPost.outcome.state) :=
                  by
                    have hPostMono :=
                      Functions.Source.Effectful.Block.runScoped_mono
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (fuel := postTargetFuel) (fuel' := commonFuel)
                        (ctx := ctx.withoutLoopControl)
                        (block := { stmts := lowerPostStmts })
                        (state := bodyResult.outcome.state)
                        (outcome :=
                          Functions.Source.Effectful.Outcome.regular
                            closedPost.outcome.state)
                        (Nat.le_trans (Nat.le_max_left _ _)
                          (Nat.le_max_right _ _))
                        hPostTarget
                    exact hPostMono
                have hRecursiveEta :
                    Functions.Source.Effectful.Stmt.runForLoop
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions ctx.withoutLoopControl
                        (.lit (EvmYul.UInt256.ofNat 1))
                        ctx.withoutLoopControl
                        { stmts := lowerPostStmts }
                        (ctx.withLoopControl ctx.scope ctx.scope)
                        { stmts :=
                            preCond ++
                              .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                        recursiveFuel closedPost.outcome.state =
                      .ok
                        (Functions.Source.Effectful.Outcome.halt
                          recursive.kind recursive.finalTarget) := by
                  exact hRecursiveTarget
                have hRecursiveTarget' :
                    Functions.Source.Effectful.Stmt.runForLoop
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions ctx.withoutLoopControl
                        (.lit (EvmYul.UInt256.ofNat 1))
                        ctx.withoutLoopControl
                        { stmts := lowerPostStmts }
                        (ctx.withLoopControl ctx.scope ctx.scope)
                        { stmts :=
                            preCond ++
                              .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                        commonFuel closedPost.outcome.state =
                      .ok
                        (Functions.Source.Effectful.Outcome.halt
                          recursive.kind recursive.finalTarget) :=
                  Functions.Source.Effectful.Stmt.runForLoop_mono
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions
                    (fuel := recursiveFuel) (fuel' := commonFuel)
                    (Nat.le_trans (Nat.le_max_right _ _)
                      (Nat.le_max_right _ _))
                    hRecursiveEta
                have hLoopTarget :
                    Functions.Source.Effectful.Stmt.runForLoop
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions ctx.withoutLoopControl
                        (.lit (EvmYul.UInt256.ofNat 1))
                        ctx.withoutLoopControl
                        { stmts := lowerPostStmts }
                        (ctx.withLoopControl ctx.scope ctx.scope)
                        { stmts :=
                            preCond ++
                              .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                        (commonFuel + 1) target =
                      .ok
                        (Functions.Source.Effectful.Outcome.halt
                          recursive.kind recursive.finalTarget) := by
                  rcases bodyResult.mode with hRegular | hContinue
                  · have hBodyEq :
                        bodyResult.outcome =
                          Functions.Source.Effectful.Outcome.regular
                            bodyResult.outcome.state :=
                      Functions.Source.Effectful.Outcome.eq_regular_of_mode
                        hRegular
                    rw [hBodyEq] at hBodyTarget'
                    exact
                      Functions.Source.Effectful.Stmt.runForLoop_regular_post_recurse_of_runs
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                          target)
                        hBodyTarget' hPostTarget' hRecursiveTarget'
                  · have hBodyEq :
                        bodyResult.outcome =
                          Functions.Source.Effectful.Outcome.cont
                            bodyResult.outcome.state :=
                      Functions.Source.Effectful.Outcome.eq_cont_of_mode
                        hContinue
                    rw [hBodyEq] at hBodyTarget'
                    exact
                      Functions.Source.Effectful.Stmt.runForLoop_cont_post_recurse_of_runs
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                          target)
                        hBodyTarget' hPostTarget' hRecursiveTarget'
                exact
                  ⟨
                    { kind := recursive.kind
                      finalTarget := recursive.finalTarget
                      run :=
                        ⟨commonFuel + 1, hLoopTarget⟩
                      relation := recursive.relation }⟩

end RecursiveTerminalLoopForward

namespace RecursiveTerminalCompoundForward

theorem ifThen
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound sourceFuel compilerFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {cond : AstExpr}
    {body : List AstStmt}
    {lower : List Functions.Stmt}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave (.If cond body) =
        true)
    (hNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.names (.If cond body)))
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.If cond body) =
        some (lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverForward.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.If cond body)
          (some sourceProgram.contract) source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel targetProgram.toFunctions lower
        failure target ctx) := by
  obtain
      ⟨compilerPrevious, preCond, lowerCond, middle, lowerBody,
        _hCompilerFuel, hLowerCond, hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_if_parts hLower
  subst lower
  obtain ⟨sourcePrevious, hSourceFuel, hFailureCase⟩ :=
    Yul.Source.Effectful.exec_if_observable_error_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun hObservable
  have hOkParts :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 cond =
          true ∧
        SolcValidation.StmtsOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout canBreak canContinue canLeave body =
          true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hCondFresh : Fresh.Extends before middle :=
    Expr.lower1Unchecked?_stateExtends hLowerCond
  have hBodyNamesBefore :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hBodyNamesMiddle :
      StateRelation.Vars.NamesWithin middle.used
        (Stmt.List.names body) :=
    hBodyNamesBefore.mono hCondFresh
  have hLayoutMiddle :
      StateRelation.Vars.NamesWithin middle.used layout :=
    hLayout.mono hCondFresh
  rcases hFailureCase with hCondFailure | hBodyFailure
  · obtain ⟨condResult⟩ :=
      hTerminalExpr (by omega) hOkParts.1 hLowerCond hRel hDomain
        hScope hCondFailure hObservable
    exact
      ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
        condResult [.if_ lowerCond lowerBody]⟩
  · rcases hBodyFailure with
      ⟨sourceAfterCond, condValue,
        hCondRun, hNonzero, hBodyRun⟩
    obtain ⟨prepared⟩ :=
      hRegularExpr (exprFuel := sourcePrevious)
        (before := before) (after := middle)
        (layout := layout) (expr := cond)
        (pre := preCond) (lower := lowerCond)
        (source := source) (source' := sourceAfterCond)
        (target := target) (ctx := ctx) (value := condValue)
        (by omega) hOkParts.1 hLowerCond hRel hDomain hScope hCondRun
    obtain ⟨preFuel, hPreRun⟩ := prepared.prepared.run
    have hPreparedLayoutScope :
        FunctionsObserverOutcome.LayoutWithinScope
          layout prepared.prepared.finalCtx := by
      have hExtends :=
        Functions.Source.Effectful.Block.runOpen_scopeExtends
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hPreRun
      exact fun name hMem =>
        hExtends name (hControl.scope name hMem)
    have hPreparedControl :
        FunctionsObserverForward.ControlContextRel sourceControl layout
          canBreak canContinue canLeave
          prepared.prepared.finalCtx :=
      FunctionsObserverForward.ControlContextRel.transport hControl
        (fun _name hMem => hMem)
        prepared.prepared.control hPreparedLayoutScope
    have hCondTrue :
        Functions.Source.Effectful.Expr.evalCondition
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            lowerCond prepared.prepared.preTarget =
          .ok (prepared.prepared.evalTarget, true) :=
      Functions.Source.Effectful.Expr.evalCondition_true_of_eval_singleton
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        prepared.prepared.eval hNonzero
    have hBlockOk :
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout canBreak canContinue canLeave (.Block body) =
          true := by
      simpa [SolcValidation.StmtOk?] using hOkParts.2
    have hBlockNames :
        StateRelation.Vars.NamesWithin middle.used
          (Stmt.names (.Block body)) := by
      simpa [Stmt.names] using hBodyNamesMiddle
    have hBlockLower :
        Stmt.toFunctionsListUncheckedFuel? (compilerPrevious + 1)
            middle (.Block body) =
          some ([.block lowerBody], after) :=
      Stmt.toFunctionsListUncheckedFuel?_block_of_toBlock hLowerBody
    obtain ⟨bodyResult⟩ :=
      RecursiveTerminalStmtForward.block hTerminalList
        (sourceFuel := sourcePrevious)
        (compilerFuel := compilerPrevious + 1)
        (sourceControl := sourceControl)
        (before := middle) (after := after)
        (layout := layout) (body := body)
        (lower := [.block lowerBody])
        (source := sourceAfterCond) (failure := failure)
        (target := prepared.prepared.evalTarget)
        (ctx := prepared.prepared.finalCtx)
        (canBreak := canBreak) (canContinue := canContinue)
        (canLeave := canLeave)
        (by omega) hBlockOk hBlockNames hBlockLower
        prepared.relation prepared.prepared.domain
        prepared.prepared.scope hLayoutMiddle hPreparedControl
        hBodyRun hObservable
    obtain ⟨bodyFuel, hBodyScoped, hBodyCtx⟩ :=
      Functions.Source.Effectful.Block.runScoped_of_runOpen_singleton_block
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions bodyResult.run
    have hIfStmt :
        Functions.Source.Effectful.Stmt.run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions prepared.prepared.finalCtx
            (bodyFuel + 1) (.if_ lowerCond lowerBody)
            prepared.prepared.preTarget =
          .ok
            (Functions.Source.Effectful.Outcome.halt
              bodyResult.kind bodyResult.finalTarget,
              prepared.prepared.finalCtx) :=
      Functions.Source.Effectful.Stmt.run_if_true_of_eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hCondTrue hBodyScoped
    have hIfRun :=
      Functions.Source.Effectful.Block.runOpen_singleton_of_run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hIfStmt
    let ifResult :
        FunctionsObserverTerminal.StatementResult
          contract codeRel targetProgram.toFunctions
          [.if_ lowerCond lowerBody] failure
          prepared.prepared.preTarget prepared.prepared.finalCtx :=
      { kind := bodyResult.kind
        finalTarget := bodyResult.finalTarget
        finalCtx := prepared.prepared.finalCtx
        run := hIfRun
        relation := bodyResult.relation }
    exact
      ⟨FunctionsObserverTerminal.StatementResult.prependRegularRun
        prepared.prepared.run ifResult⟩

theorem switch
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound sourceFuel compilerFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {scrutinee : AstExpr}
    {cases : List (Word × List AstStmt)}
    {defaultBody : List AstStmt}
    {lower : List Functions.Stmt}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave
          (.Switch scrutinee cases defaultBody) =
        true)
    (hNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.names (.Switch scrutinee cases defaultBody)))
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Switch scrutinee cases defaultBody) =
        some (lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverForward.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Switch scrutinee cases defaultBody)
          (some sourceProgram.contract) source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel targetProgram.toFunctions lower
        failure target ctx) := by
  obtain
      ⟨compilerPrevious, preScrutinee, lowerScrutinee,
        afterScrutinee, lowerCases, afterCases, lowerDefault,
        _hCompilerFuel, hLowerScrutinee, hLowerCases,
        hLowerDefault, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_switch_parts hLower
  subst lower
  obtain ⟨sourcePrevious, hSourceFuel, hFailureCase⟩ :=
    Yul.Source.Effectful.exec_switch_observable_error_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun hObservable
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  rcases hFailureCase with hScrutineeFailure | hSelectedFailure
  · obtain ⟨scrutineeResult⟩ :=
      hTerminalExpr (by omega) hOkParts.1 hLowerScrutinee hRel
        hDomain hScope hScrutineeFailure hObservable
    exact
      ⟨FunctionsObserverTerminal.StatementResult.appendUnreachable
        scrutineeResult
        [.switch lowerScrutinee lowerCases lowerDefault]⟩
  · rcases hSelectedFailure with
      ⟨sourceAfterScrutinee, value,
        hScrutineeRun, hSelectedRun⟩
    have hScrutineeFresh : Fresh.Extends before afterScrutinee :=
      Expr.lower1Unchecked?_stateExtends hLowerScrutinee
    have hSelection :=
      Stmt.SwitchSelectionLowering.of_compilers
        (value := value) hLowerCases hLowerDefault
    obtain ⟨prepared⟩ :=
      hRegularExpr (exprFuel := sourcePrevious)
        (before := before) (after := afterScrutinee)
        (layout := layout) (expr := scrutinee)
        (pre := preScrutinee) (lower := lowerScrutinee)
        (source := source) (source' := sourceAfterScrutinee)
        (target := target) (ctx := ctx) (value := value)
        (by omega) hOkParts.1 hLowerScrutinee hRel hDomain hScope
        hScrutineeRun
    obtain ⟨preFuel, hPreRun⟩ := prepared.prepared.run
    have hEvalOne :
        Functions.Source.Effectful.Expr.evalOne
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            lowerScrutinee prepared.prepared.preTarget =
          .ok (prepared.prepared.evalTarget, value) :=
      Functions.Source.Effectful.Expr.evalOne_of_eval_singleton
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        prepared.prepared.eval
    have hPreparedLayoutScope :
        FunctionsObserverOutcome.LayoutWithinScope
          layout prepared.prepared.finalCtx := by
      have hExtends :=
        Functions.Source.Effectful.Block.runOpen_scopeExtends
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hPreRun
      exact fun name hMem =>
        hExtends name (hControl.scope name hMem)
    have hPreparedControl :
        FunctionsObserverForward.ControlContextRel sourceControl layout
          canBreak canContinue canLeave
          prepared.prepared.finalCtx :=
      FunctionsObserverForward.ControlContextRel.transport hControl
        (fun _name hMem => hMem)
        prepared.prepared.control hPreparedLayoutScope
    cases hSelection with
    | none hSourceSelection hTargetSelection hSelectionFresh =>
        rw [hSourceSelection] at hSelectedRun
        exact
          (Yul.Source.Effectful.exec_block_nil_observable_error_false
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hSelectedRun hObservable).elim
    | some hSourceSelection hTargetSelection hSelectedLower
        hBeforeSelected hAfterSelected =>
        rename_i selectedBody selectedLowerBody selectedCompilerFuel
          selectedBefore selectedAfter
        rw [hSourceSelection] at hSelectedRun
        have hSelectedOk :
            SolcValidation.StmtsOk? profile sourceProgram.contract
                ((Contract.functionEntries
                  sourceProgram.contract).map Prod.fst)
                layout canBreak canContinue canLeave selectedBody =
              true := by
          rw [← hSourceSelection]
          exact
            Stmt.stmtsOk_selectSwitchCase (value := value)
              hOkParts.2.2.1 hOkParts.2.2.2
        have hSelectedNamesBefore :
            StateRelation.Vars.NamesWithin before.used
              (Stmt.List.names selectedBody) := by
          intro name hMem
          have hCanonical :
              name ∈
                Stmt.List.names
                  (EvmYul.Yul.selectSwitchCase
                    value defaultBody cases) := by
            rw [hSourceSelection]
            exact hMem
          exact hNames name (by
            simpa [Stmt.names] using
              List.mem_append_right (Expr.names scrutinee)
                (Stmt.selectedSwitchNames name hCanonical))
        have hSelectedFresh :
            Fresh.Extends before selectedBefore :=
          Fresh.Extends.trans hScrutineeFresh hBeforeSelected
        have hSelectedNames :
            StateRelation.Vars.NamesWithin selectedBefore.used
              (Stmt.List.names selectedBody) :=
          hSelectedNamesBefore.mono hSelectedFresh
        have hSelectedLayout :
            StateRelation.Vars.NamesWithin selectedBefore.used layout :=
          hLayout.mono hSelectedFresh
        have hBlockOk :
            SolcValidation.StmtOk? profile sourceProgram.contract
                ((Contract.functionEntries
                  sourceProgram.contract).map Prod.fst)
                layout canBreak canContinue canLeave
                (.Block selectedBody) =
              true := by
          simpa [SolcValidation.StmtOk?] using hSelectedOk
        have hBlockNames :
            StateRelation.Vars.NamesWithin selectedBefore.used
              (Stmt.names (.Block selectedBody)) := by
          simpa [Stmt.names] using hSelectedNames
        have hBlockLower :=
          Stmt.toFunctionsListUncheckedFuel?_block_of_toBlock hSelectedLower
        obtain ⟨bodyResult⟩ :=
          RecursiveTerminalStmtForward.block hTerminalList
            (sourceFuel := sourcePrevious)
            (compilerFuel := selectedCompilerFuel + 1)
            (sourceControl := sourceControl)
            (before := selectedBefore) (after := selectedAfter)
            (layout := layout) (body := selectedBody)
            (lower := [.block selectedLowerBody])
            (source := sourceAfterScrutinee) (failure := failure)
            (target := prepared.prepared.evalTarget)
            (ctx := prepared.prepared.finalCtx)
            (canBreak := canBreak) (canContinue := canContinue)
            (canLeave := canLeave)
            (by omega) hBlockOk hBlockNames hBlockLower
            prepared.relation
            (prepared.prepared.domain.mono hBeforeSelected)
            (prepared.prepared.scope.mono hBeforeSelected)
            hSelectedLayout hPreparedControl hSelectedRun hObservable
        obtain ⟨bodyFuel, hBodyScoped, hBodyCtx⟩ :=
          Functions.Source.Effectful.Block.runScoped_of_runOpen_singleton_block
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions bodyResult.run
        have hSwitchStmt :
            Functions.Source.Effectful.Stmt.run
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions prepared.prepared.finalCtx
                (bodyFuel + 1)
                (.switch lowerScrutinee lowerCases lowerDefault)
                prepared.prepared.preTarget =
              .ok
                (Functions.Source.Effectful.Outcome.halt
                  bodyResult.kind bodyResult.finalTarget,
                  prepared.prepared.finalCtx) :=
          Functions.Source.Effectful.Stmt.run_switch_some_of_eval
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hEvalOne hTargetSelection hBodyScoped
        have hSwitchRun :=
          Functions.Source.Effectful.Block.runOpen_singleton_of_run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hSwitchStmt
        let switchResult :
            FunctionsObserverTerminal.StatementResult
              contract codeRel targetProgram.toFunctions
              [.switch lowerScrutinee lowerCases lowerDefault]
              failure prepared.prepared.preTarget
              prepared.prepared.finalCtx :=
          { kind := bodyResult.kind
            finalTarget := bodyResult.finalTarget
            finalCtx := prepared.prepared.finalCtx
            run := hSwitchRun
            relation := bodyResult.relation }
        exact
          ⟨FunctionsObserverTerminal.StatementResult.prependRegularRun
            prepared.prepared.run switchResult⟩

theorem forLoop
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound sourceFuel compilerFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {cond : AstExpr}
    {post body : List AstStmt}
    {lower : List Functions.Stmt}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hLoop :
      RecursiveTerminalLoopForward contract transcript codeRel
        sourceProgram targetProgram profile (bound + 1))
    (hFuel : sourceFuel < bound + 1)
    (hOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave (.For cond post body) =
        true)
    (hNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.names (.For cond post body)))
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.For cond post body) =
        some (lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverForward.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.For cond post body)
          (some sourceProgram.contract) source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel targetProgram.toFunctions lower
        failure target ctx) := by
  obtain
      ⟨compilerPrevious, preCond, lowerCond, afterCond,
        lowerPost, afterPost, lowerBody, _hCompilerFuel,
        hLowerCond, hLowerPost, hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_for_parts hLower
  subst lower
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  have hCondNames :
      StateRelation.Vars.NamesWithin before.used
        (Expr.names cond) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hPostNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names post) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  obtain ⟨loopResult⟩ :=
    hLoop
      (sourceFuel := sourceFuel) (compilerFuel := compilerPrevious)
      (sourceControl := sourceControl)
      (before := before) (after := after)
      (afterCond := afterCond) (afterPost := afterPost)
      (layout := layout) (cond := cond) (post := post) (body := body)
      (preCond := preCond) (lowerCond := lowerCond)
      (lowerPost := lowerPost) (lowerBody := lowerBody)
      (source := source) (failure := failure)
      (target := target) (ctx := ctx)
      (canBreak := canBreak) (canContinue := canContinue)
      (canLeave := canLeave)
      hFuel hOkParts.1 hOkParts.2.1 hOkParts.2.2
      hCondNames hPostNames hBodyNames hLowerCond hLowerPost hLowerBody
      hRel hDomain hScope hLayout hControl hRun hObservable
  exact
    FunctionsObserverTerminal.StatementResult.ofForLoop
      loopResult.run loopResult.relation

theorem ofComponents
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hLoop :
      RecursiveTerminalLoopForward contract transcript codeRel
        sourceProgram targetProgram profile (bound + 1)) :
    RecursiveTerminalCompoundForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source failure target ctx canBreak canContinue canLeave
    hCompound hFuel hOk hNames hLower hRel hDomain hScope hLayout
    hControl hRun hObservable
  cases hCompound with
  | block body =>
      exact
        RecursiveTerminalStmtForward.block hTerminalList
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
          hRun hObservable
  | switch scrutinee cases defaultBody =>
      exact
        switch hRegularExpr hTerminalExpr hTerminalList
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
          hRun hObservable
  | forLoop cond post body =>
      exact
        forLoop hLoop hFuel hOk hNames hLower hRel hDomain hScope
          hLayout hControl hRun hObservable
  | ifThen cond body =>
      exact
        ifThen hRegularExpr hTerminalExpr hTerminalList
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl
          hRun hObservable

end RecursiveTerminalCompoundForward

structure RecursiveTerminalFamily
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop where
  expression :
    RecursiveTerminalExpressionForward contract transcript codeRel
      sourceProgram targetProgram profile bound
  body :
    RecursiveTerminalBodyForward contract transcript codeRel
      sourceProgram targetProgram profile bound
  stmt :
    RecursiveTerminalStmtForward contract transcript codeRel
      sourceProgram targetProgram profile bound
  list :
    RecursiveTerminalListForward contract transcript codeRel
      sourceProgram targetProgram profile bound
  compound :
    RecursiveTerminalCompoundForward contract transcript codeRel
      sourceProgram targetProgram profile bound
  loop :
    RecursiveTerminalLoopForward contract transcript codeRel
      sourceProgram targetProgram profile bound

namespace RecursiveTerminalFamily

theorem ofCompiler
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true) :
    ∀ bound,
      RecursiveTerminalFamily contract transcript codeRel
        sourceProgram targetProgram profile bound := by
  intro bound
  induction bound with
  | zero =>
      refine
        { expression := ?_
          body := ?_
          stmt := ?_
          list := ?_
          compound := ?_
          loop := ?_ }
      · simp [RecursiveTerminalExpressionForward]
      · simp [RecursiveTerminalBodyForward]
      · simp [RecursiveTerminalStmtForward]
      · simp [RecursiveTerminalListForward]
      · simp [RecursiveTerminalCompoundForward]
      · simp [RecursiveTerminalLoopForward]
  | succ bound ih =>
      have regular :
          FunctionsObserverForward.RecursiveForwardFamily
            contract transcript codeRel sourceProgram targetProgram
            profile bound :=
        FunctionsObserverForward.RecursiveForwardFamily.ofCompiler
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) hDecomposition hProgramOk bound
      have hLoop :
          RecursiveTerminalLoopForward contract transcript codeRel
            sourceProgram targetProgram profile (bound + 1) :=
        RecursiveTerminalLoopForward.ofCompiler
          regular.value regular.list ih.expression ih.list
      have hCompound :
          RecursiveTerminalCompoundForward contract transcript codeRel
            sourceProgram targetProgram profile (bound + 1) :=
        RecursiveTerminalCompoundForward.ofComponents
          (FunctionsObserverCall.RecursiveScopedValueForward.expression
            regular.value)
          ih.expression ih.list hLoop
      exact
        { expression :=
            RecursiveTerminalExpressionForward.ofComponents
              hDecomposition hProgramOk
              (FunctionsObserverCall.RecursiveScopedValueForward.expression
                regular.value)
              ih.expression ih.body
          body := RecursiveTerminalBodyForward.ofList ih.list
          stmt :=
            RecursiveTerminalStmtForward.ofCompound
              hDecomposition hProgramOk
              (FunctionsObserverCall.RecursiveScopedValueForward.expression
                regular.value)
              ih.expression ih.body hCompound
          list :=
            RecursiveTerminalListForward.ofStmt
              regular.stmt ih.stmt ih.list
          compound := hCompound
          loop := hLoop }

theorem dispatcherForward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {sourceEntry :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel [] sourceEntry target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        (Fresh.initial
          (Contract.names sourceProgram.contract)).used
        target.source.vars)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block [sourceProgram.contract.dispatcher])
          (some sourceProgram.contract) sourceEntry =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    ∃ targetFuel outcome,
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetFuel targetProgram.toFunctions target =
        .ok outcome ∧
      FunctionsObserverOutcome.TerminalFailureRel codeRel failure outcome := by
  have hCompiler := hDecomposition
  obtain
      ⟨bodyStmts, afterBody, functions, afterFunctions,
        hLowerBody, _hLowerFunctions, hTargetProgram⟩ :=
    hDecomposition
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
    have hLowerList :
        Stmt.List.toFunctionsUncheckedFuel?
            (Stmt.fuel sourceProgram.contract.dispatcher + 1)
            (Fresh.initial (Contract.names sourceProgram.contract))
            [sourceProgram.contract.dispatcher] =
          some (bodyStmts, afterBody) :=
      Stmt.List.toFunctionsUncheckedFuel?_singleton_of_stmt
        (by
          cases sourceProgram.contract.dispatcher <;>
            simp [Stmt.fuel])
        hLowerBody
    have hDispatcherOk :
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            [] false false false sourceProgram.contract.dispatcher =
          true := by
      have hParts := hProgramOk
      simp [SolcValidation.ProgramOkWith?,
        SolcValidation.ContractOkWith?,
        SolcValidation.ContractOkWithEntries?] at hParts
      exact hParts.2.1
    have hListOk :
        SolcValidation.StmtsOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            [] false false false
            [sourceProgram.contract.dispatcher] =
          true := by
      simpa [SolcValidation.StmtsOk?,
        SolcValidation.StmtOutVars] using hDispatcherOk
    let initial :=
      Fresh.initial (Contract.names sourceProgram.contract)
    have hNames :
        StateRelation.Vars.NamesWithin initial.used
          (Stmt.List.names [sourceProgram.contract.dispatcher]) := by
      intro name hMem
      change name ∈ Contract.names sourceProgram.contract
      have hDispatcherName :
          name ∈ Stmt.names sourceProgram.contract.dispatcher := by
        simpa [Stmt.List.names] using hMem
      simpa [Contract.names] using
        List.mem_append_left
          (FunctionList.names
            (Contract.functionEntries sourceProgram.contract))
          hDispatcherName
    let sourceControl : FunctionsObserverOutcome.SourceControlScopes :=
      { breakScope? := none
        continueScope? := none
        leaveScope? := none }
    have hControl :
        FunctionsObserverForward.ControlContextRel sourceControl []
          false false false Functions.Source.Ctx.initial := by
      refine
        { scope := ?_
          breakScope := ?_
          continueScope := ?_
          leaveScope := ?_ }
      · simp [FunctionsObserverOutcome.LayoutWithinScope]
      · simp [sourceControl, FunctionsObserverForward.ScopeOptionWithin,
          Functions.Source.Ctx.initial]
      · simp [sourceControl, FunctionsObserverForward.ScopeOptionWithin,
          Functions.Source.Ctx.initial]
      · simp [sourceControl, FunctionsObserverForward.ScopeOptionWithin,
          Functions.Source.Ctx.initial]
    have hFamily :=
      ofCompiler
        (contract := contract) (transcript := transcript)
        (codeRel := codeRel) (profile := profile)
        hCompiler hProgramOk (listSourceFuel + 1)
    obtain ⟨result⟩ :=
      hFamily.list
        (sourceFuel := listSourceFuel)
        (compilerFuel := Stmt.fuel sourceProgram.contract.dispatcher + 1)
        (sourceControl := sourceControl)
        (before := initial) (after := afterBody)
        (layout := []) (stmts := [sourceProgram.contract.dispatcher])
        (lower := bodyStmts)
        (source := sourceEntry) (failure := failure)
        (target := target) (ctx := Functions.Source.Ctx.initial)
        (canBreak := false) (canContinue := false) (canLeave := false)
        (by omega) hListOk hNames hLowerList hRel hDomain
        (by
          intro name hMem
          simp [Functions.Source.Ctx.initial] at hMem)
        (by
          intro name hMem
          simp at hMem)
        hControl hListRun hObservable
    obtain ⟨targetFuel, hTargetOpen⟩ := result.run
    have hTargetScoped :=
      Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetOpen (by simp)
    refine
      ⟨targetFuel,
        Functions.Source.Effectful.Outcome.halt
          result.kind result.finalTarget, ?_, result.relation⟩
    have hBodyEq :
        targetProgram.toFunctions.body = { stmts := bodyStmts } :=
      congrArg (fun program => program.body) hTargetProgram
    unfold Functions.Source.Effectful.Program.runState
    rw [hBodyEq]
    exact hTargetScoped

end RecursiveTerminalFamily

end FunctionsObserverTerminalForward
end Yul
end EvmCompiler
