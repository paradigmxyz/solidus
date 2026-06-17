import EvmCompiler.Yul.FunctionsObserverForwardFuel
import EvmCompiler.Yul.FunctionsObserverTerminalForward

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTerminalFuel

/-!
Program-indexed fuel bounds for observable terminal execution at the adjacent
Yul-to-Functions boundary.

The qualitative terminal proof remains owned by
`FunctionsObserverTerminalForward`. This module adds only quantitative
interfaces over the canonical Functions execution stored in those results.
-/

abbrev Trace := Assembly.ResourceTrace

def RecursiveTerminalStmtForwardProgramBounded
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
      FunctionsObserverStaticCost.stmt stmt ≤
        FunctionsObserverStaticCost.program sourceProgram →
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
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt (some sourceProgram.contract) source =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        { result :
            FunctionsObserverTerminal.StatementResult
              contract codeRel targetProgram.toFunctions lower
              failure target ctx //
          result.requiredFuel ≤
            FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt stmt)
              sourceFuel }

def RecursiveTerminalListForwardProgramBounded
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
      FunctionsObserverStaticCost.stmtList stmts ≤
        FunctionsObserverStaticCost.program sourceProgram →
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
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.execSeq
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmts (some sourceProgram.contract) source =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        { result :
            FunctionsObserverTerminal.StatementResult
              contract codeRel targetProgram.toFunctions lower
              failure target ctx //
          result.requiredFuel ≤
            FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmtList stmts)
              sourceFuel }

def RecursiveTerminalBodyForwardProgramBounded
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
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram →
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
        { result :
            FunctionsObserverCallTerminal.BodyResult
              contract codeRel targetProgram.toFunctions fn.body failure
              (targetCaller.withSource
                { shared := targetCaller.source.shared,
                  vars :=
                    Functions.Source.Store.initReturns
                      fn.returns paramStore })
              (Functions.Source.Effectful.FunDef.bodyCtx fn) //
          result.requiredFuel ≤
            FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmtList body)
              sourceFuel }

def RecursiveTerminalExpressionForwardProgramBounded
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
      FunctionsObserverStaticCost.expr expr ≤
        FunctionsObserverStaticCost.program sourceProgram →
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
        { result :
            FunctionsObserverTerminal.StatementResult
              contract codeRel targetProgram.toFunctions pre
              failure target ctx //
          result.requiredFuel ≤
            FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.expr expr)
              exprFuel }

namespace StatementResult

def RunBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {lower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (fuelBound : Nat)
    (result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program lower failure target ctx) : Prop :=
  result.requiredFuel ≤ fuelBound

def ProgramBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {lower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (globalCost localCost sourceFuel : Nat)
    (result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program lower failure target ctx) : Prop :=
  RunBounded
    (FunctionsObserverFuel.executionBudgetFor
      globalCost localCost sourceFuel)
    result

theorem prependRegularRun_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower rightLower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target middleTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx middleCtx : Functions.Source.Ctx}
    {leftFuel : Nat}
    (left :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx leftFuel { stmts := leftLower } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular middleTarget,
            middleCtx))
    (right :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program rightLower failure
        middleTarget middleCtx) :
    RunBounded
      (leftFuel + right.requiredFuel)
      (FunctionsObserverTerminal.StatementResult.prependRegularRun
        ⟨leftFuel, left⟩ right) := by
  apply
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
  exact
    Functions.Source.Effectful.Block.runOpen_append_regular_at_add
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program leftLower rightLower ctx middleCtx target middleTarget
      (Functions.Source.Effectful.Outcome.halt
        right.kind right.finalTarget)
      right.finalCtx leftFuel right.requiredFuel left
      (FunctionsObserverTerminal.StatementResult.run_requiredFuel right)

theorem prependPrepared_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower rightLower : List Functions.Stmt}
    {middleFresh : Fresh.State}
    {sourceMiddle :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      FunctionsObserverExpression.Prepared
        contract transcript codeRel program leftLower middleFresh
        sourceMiddle target ctx)
    (right :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program rightLower failure
        left.finalTarget left.finalCtx) :
    RunBounded
      (left.requiredFuel + right.requiredFuel)
      (FunctionsObserverTerminal.StatementResult.prependPrepared
        left right) := by
  apply
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
  exact
    Functions.Source.Effectful.Block.runOpen_append_regular_at_add
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program leftLower rightLower ctx left.finalCtx target
      left.finalTarget
      (Functions.Source.Effectful.Outcome.halt
        right.kind right.finalTarget)
      right.finalCtx left.requiredFuel right.requiredFuel
      (FunctionsObserverExpression.Prepared.run_requiredFuel left)
      (FunctionsObserverTerminal.StatementResult.run_requiredFuel right)

theorem prependRegular_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle : Fresh.State}
    {entryLayout : List Name}
    {sourceMiddle :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program leftLower initial middle
        entryLayout sourceMiddle target ctx
        (sourceControl := sourceControl))
    (hRegular : left.outcome.mode = .regular)
    (right :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program rightLower failure
        left.outcome.state left.finalCtx) :
    RunBounded
      (left.requiredFuel + right.requiredFuel)
      (FunctionsObserverTerminal.StatementResult.prependRegular
        left hRegular right) := by
  have hLeftOutcome :
      left.outcome =
        Functions.Source.Effectful.Outcome.regular left.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  have hLeftRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx left.requiredFuel { stmts := leftLower } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            left.outcome.state,
            left.finalCtx) := by
    rw [← hLeftOutcome]
    exact
      FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel left
  apply
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
  exact
    Functions.Source.Effectful.Block.runOpen_append_regular_at_add
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program leftLower rightLower ctx left.finalCtx target
      left.outcome.state
      (Functions.Source.Effectful.Outcome.halt
        right.kind right.finalTarget)
      right.finalCtx left.requiredFuel right.requiredFuel
      hLeftRun
      (FunctionsObserverTerminal.StatementResult.run_requiredFuel right)

theorem appendUnreachable_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program leftLower failure target ctx)
    (rightLower : List Functions.Stmt) :
    RunBounded left.requiredFuel
      (FunctionsObserverTerminal.StatementResult.appendUnreachable
        left rightLower) := by
  apply
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
  exact
    Functions.Source.Effectful.Block.runOpen_append_nonregular_at_same
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program leftLower rightLower ctx target
      (Functions.Source.Effectful.Outcome.halt
        left.kind left.finalTarget)
      left.finalCtx left.requiredFuel
      (FunctionsObserverTerminal.StatementResult.run_requiredFuel left)
      (by simp)

theorem block_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {lower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (body :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program lower failure target ctx) :
    RunBounded (body.requiredFuel + 2)
      (FunctionsObserverTerminal.StatementResult.block body) := by
  have hBodyScoped :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx { stmts := lower } body.requiredFuel target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget) :=
    Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program
      (FunctionsObserverTerminal.StatementResult.run_requiredFuel body)
      (by simp)
  have hStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx body.requiredFuel
          (.block { stmts := lower }) target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            ctx) := by
    unfold Functions.Source.Effectful.Stmt.run
    rw [hBodyScoped]
    rfl
  apply
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
  exact
    Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hStmt

end StatementResult

namespace ForLoopResult

def RunBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {post body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (fuelBound : Nat)
    (result :
      FunctionsObserverTerminal.ForLoopResult
        contract codeRel program post body failure target ctx) : Prop :=
  result.requiredFuel ≤ fuelBound

def ProgramBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {post body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (globalCost sourceFuel : Nat)
    (result :
      FunctionsObserverTerminal.ForLoopResult
        contract codeRel program post body failure target ctx) : Prop :=
  RunBounded
    (FunctionsObserverFuel.targetBudgetFor globalCost sourceFuel)
    result

theorem ofBody_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {post body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (bodyResult :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program body.stmts failure target
        (ctx.withLoopControl ctx.scope ctx.scope)) :
    Nonempty
      { result :
          FunctionsObserverTerminal.ForLoopResult
            contract codeRel program post body failure target ctx //
        RunBounded (bodyResult.requiredFuel + 1) result } := by
  rcases body with ⟨bodyStmts⟩
  have hBodyScoped :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program (ctx.withLoopControl ctx.scope ctx.scope)
          { stmts := bodyStmts } bodyResult.requiredFuel target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            bodyResult.kind bodyResult.finalTarget) := by
    simpa using
      Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program
        (FunctionsObserverTerminal.StatementResult.run_requiredFuel
          bodyResult)
        (by simp)
  have hOuterCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.lit (EvmYul.UInt256.ofNat 1)) target =
        .ok (target, true) :=
    Functions.ObserverSafety.SafeSemantics.evalCondition_one target
  let result :
      FunctionsObserverTerminal.ForLoopResult
        contract codeRel program post { stmts := bodyStmts }
        failure target ctx :=
    { kind := bodyResult.kind
      finalTarget := bodyResult.finalTarget
      run :=
        ⟨bodyResult.requiredFuel + 1,
          Functions.Source.Effectful.Stmt.runForLoop_body_halt_of_runs
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program hOuterCond hBodyScoped⟩
      relation := bodyResult.relation }
  refine ⟨⟨result, ?_⟩⟩
  apply
    FunctionsObserverTerminal.ForLoopResult.requiredFuel_le_of_run
  exact
    Functions.Source.Effectful.Stmt.runForLoop_body_halt_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hOuterCond hBodyScoped

end ForLoopResult

namespace BodyResult

def RunBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (fuelBound : Nat)
    (result :
      FunctionsObserverCallTerminal.BodyResult
        contract codeRel program body failure target ctx) : Prop :=
  result.requiredFuel ≤ fuelBound

def ProgramBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (globalCost localCost sourceFuel : Nat)
    (result :
      FunctionsObserverCallTerminal.BodyResult
        contract codeRel program body failure target ctx) : Prop :=
  RunBounded
    (FunctionsObserverFuel.executionBudgetFor
      globalCost localCost sourceFuel)
    result

theorem ofStatement_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {body : Functions.Block}
    {lower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hBody : body = { stmts := lower })
    (result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program lower failure target ctx) :
    RunBounded result.requiredFuel
      (FunctionsObserverCallTerminal.BodyResult.ofStatement
        hBody result) := by
  subst body
  apply
    FunctionsObserverCallTerminal.BodyResult.requiredFuel_le_of_run
  exact
    FunctionsObserverTerminal.StatementResult.run_requiredFuel result

end BodyResult

namespace StatementResult

theorem ofPreparedArgsCall_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout : List Name}
    {argValues : List Assembly.Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {paramStore : Locals.Source.Store}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh
        layout sourceAfterArgs target ctx argValues)
    (hTargets : targets.Nodup)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (hParams :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (body :
      FunctionsObserverCallTerminal.BodyResult
        contract codeRel program fn.body failure
        (argsPrepared.prepared.prepared.finalTarget.withSource
          { shared :=
              argsPrepared.prepared.prepared.finalTarget.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore })
        (Functions.Source.Effectful.FunDef.bodyCtx fn)) :
    Nonempty
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel program
            (preArgs ++
              [Functions.Stmt.call targets functionName lowerArgs])
            failure target ctx //
        RunBounded
          (argsPrepared.prepared.prepared.requiredFuel +
            body.requiredFuel + 4)
          result } := by
  let targetAfterArgs := argsPrepared.prepared.prepared.finalTarget
  have hArgsEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs targetAfterArgs =
        .ok (targetAfterArgs, argValues) :=
    argsPrepared.prepared.stable targetAfterArgs
      (StateRelation.Vars.TargetExtends.refl _)
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn argValues (body.requiredFuel + 1) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.CallResult.halted
            body.kind body.finalTarget) := by
    apply
      Functions.Source.Effectful.FunDef.runBody_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hParams
    simpa [targetAfterArgs] using
      FunctionsObserverCallTerminal.BodyResult.run_requiredFuel body
  have hCallStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx
          (body.requiredFuel + 2)
          (.call targets functionName lowerArgs) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            argsPrepared.prepared.prepared.finalCtx) := by
    apply
      Functions.Source.Effectful.Stmt.call_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hTargets hArgsEval hFind
    simpa [Nat.add_assoc] using hRunBody
  have hCallBlock :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx
          (body.requiredFuel + 4)
          { stmts :=
              [Functions.Stmt.call targets functionName lowerArgs] }
          targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            argsPrepared.prepared.prepared.finalCtx) := by
    simpa [Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hCallStmt
  have hFullRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx
          (argsPrepared.prepared.prepared.requiredFuel +
            body.requiredFuel + 4)
          { stmts :=
              preArgs ++
                [Functions.Stmt.call targets functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            argsPrepared.prepared.prepared.finalCtx) := by
    simpa [Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program preArgs
        [Functions.Stmt.call targets functionName lowerArgs]
        ctx argsPrepared.prepared.prepared.finalCtx target targetAfterArgs
        (Functions.Source.Effectful.Outcome.halt
          body.kind body.finalTarget)
        argsPrepared.prepared.prepared.finalCtx
        argsPrepared.prepared.prepared.requiredFuel
        (body.requiredFuel + 4)
        (FunctionsObserverExpression.Prepared.run_requiredFuel
          argsPrepared.prepared.prepared)
        hCallBlock
  let result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program
        (preArgs ++
          [Functions.Stmt.call targets functionName lowerArgs])
        failure target ctx :=
    { kind := body.kind
      finalTarget := body.finalTarget
      finalCtx := argsPrepared.prepared.prepared.finalCtx
      run :=
        ⟨argsPrepared.prepared.prepared.requiredFuel +
          body.requiredFuel + 4, hFullRun⟩
      relation := body.relation }
  refine ⟨⟨result, ?_⟩⟩
  exact
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
      result hFullRun

theorem ofPreparedArgsExpressionCall_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName tmp : Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {argsFresh finalFresh : Fresh.State}
    {layout : List Name}
    {argValues : List Assembly.Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {paramStore : Locals.Source.Store}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs argsFresh
        layout sourceAfterArgs target ctx argValues)
    (hFresh : Fresh.fresh? argsFresh = some (tmp, finalFresh))
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (hParams :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (body :
      FunctionsObserverCallTerminal.BodyResult
        contract codeRel program fn.body failure
        ((argsPrepared.prepared.prepared.finalTarget.withSource
          (argsPrepared.prepared.prepared.finalTarget.source.insert
            tmp Functions.Source.zero)).withSource
          { shared :=
              argsPrepared.prepared.prepared.finalTarget.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore })
        (Functions.Source.Effectful.FunDef.bodyCtx fn)) :
    Nonempty
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel program
            (preArgs ++
              [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                Functions.Stmt.call [tmp] functionName lowerArgs])
            failure target ctx //
        RunBounded
          (argsPrepared.prepared.prepared.requiredFuel +
            body.requiredFuel + 7)
          result } := by
  let targetAfterArgs := argsPrepared.prepared.prepared.finalTarget
  have hZeroEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.lit Functions.Source.zero : Locals.Expr 1) targetAfterArgs =
        .ok (targetAfterArgs, [Functions.Source.zero]) := by
    rfl
  let zeroPrepared :=
    FunctionsObserverExpression.Prepared.generated
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (program := program)
      (ctx := argsPrepared.prepared.prepared.finalCtx)
      hFresh hZeroEval argsPrepared.prepared.prepared.rel
      argsPrepared.prepared.prepared.domain
      argsPrepared.prepared.prepared.scope
  have hArgsEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs zeroPrepared.finalTarget =
        .ok (zeroPrepared.finalTarget, argValues) := by
    apply argsPrepared.prepared.stable
    exact
      StateRelation.Vars.TargetExtends.trans
        (StateRelation.Vars.TargetExtends.refl _)
        zeroPrepared.varsExtends
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn argValues (body.requiredFuel + 1)
          zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.CallResult.halted
            body.kind body.finalTarget) := by
    apply
      Functions.Source.Effectful.FunDef.runBody_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hParams
    simpa [zeroPrepared, targetAfterArgs] using
      FunctionsObserverCallTerminal.BodyResult.run_requiredFuel body
  have hCallStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program zeroPrepared.finalCtx (body.requiredFuel + 2)
          (.call [tmp] functionName lowerArgs) zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            zeroPrepared.finalCtx) := by
    apply
      Functions.Source.Effectful.Stmt.call_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program (by simp) hArgsEval hFind
    simpa [Nat.add_assoc] using hRunBody
  have hCallBlock :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program zeroPrepared.finalCtx (body.requiredFuel + 4)
          { stmts :=
              [Functions.Stmt.call [tmp] functionName lowerArgs] }
          zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            zeroPrepared.finalCtx) := by
    simpa [Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hCallStmt
  have hZeroRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx 3
          { stmts :=
              [Functions.Stmt.let_ tmp (.lit Functions.Source.zero)] }
          targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            zeroPrepared.finalTarget,
            zeroPrepared.finalCtx) := by
    exact
      Functions.Source.Effectful.Block.runOpen_mono
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program
        (FunctionsObserverExpression.Prepared.requiredFuel_generated_le
          (program := program)
          hFresh hZeroEval argsPrepared.prepared.prepared.rel
          argsPrepared.prepared.prepared.domain
          argsPrepared.prepared.prepared.scope)
        (FunctionsObserverExpression.Prepared.run_requiredFuel zeroPrepared)
  have hSuffixRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx
          (body.requiredFuel + 7)
          { stmts :=
              [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                Functions.Stmt.call [tmp] functionName lowerArgs] }
          targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            zeroPrepared.finalCtx) := by
    rw [show body.requiredFuel + 7 =
      3 + (body.requiredFuel + 4) by omega]
    exact
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero)]
        [Functions.Stmt.call [tmp] functionName lowerArgs]
        argsPrepared.prepared.prepared.finalCtx zeroPrepared.finalCtx
        targetAfterArgs zeroPrepared.finalTarget
        (Functions.Source.Effectful.Outcome.halt
          body.kind body.finalTarget)
        zeroPrepared.finalCtx 3 (body.requiredFuel + 4)
        hZeroRun hCallBlock
  have hFullRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx
          (argsPrepared.prepared.prepared.requiredFuel +
            body.requiredFuel + 7)
          { stmts :=
              preArgs ++
                [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                  Functions.Stmt.call [tmp] functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            zeroPrepared.finalCtx) := by
    simpa [Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program preArgs
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
          Functions.Stmt.call [tmp] functionName lowerArgs]
        ctx argsPrepared.prepared.prepared.finalCtx target targetAfterArgs
        (Functions.Source.Effectful.Outcome.halt
          body.kind body.finalTarget)
        zeroPrepared.finalCtx
        argsPrepared.prepared.prepared.requiredFuel
        (body.requiredFuel + 7)
        (FunctionsObserverExpression.Prepared.run_requiredFuel
          argsPrepared.prepared.prepared)
        hSuffixRun
  let result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program
        (preArgs ++
          [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
            Functions.Stmt.call [tmp] functionName lowerArgs])
        failure target ctx :=
    { kind := body.kind
      finalTarget := body.finalTarget
      finalCtx := zeroPrepared.finalCtx
      run :=
        ⟨argsPrepared.prepared.prepared.requiredFuel +
          body.requiredFuel + 7, hFullRun⟩
      relation := body.relation }
  refine ⟨⟨result, ?_⟩⟩
  exact
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
      result hFullRun

theorem ofForLoop_runBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {post body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (loopResult :
      FunctionsObserverTerminal.ForLoopResult
        contract codeRel program post body failure target ctx) :
    Nonempty
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel program
            [.for_ { stmts := [] }
              (.lit (EvmYul.UInt256.ofNat 1)) post body]
            failure target ctx //
        RunBounded (max 1 loopResult.requiredFuel + 3) result } := by
  let commonFuel := max 1 loopResult.requiredFuel
  have hInit :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx.withoutLoopControl commonFuel
          { stmts := [] } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular target,
            ctx.withoutLoopControl) :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [commonFuel])
      (Functions.Source.Effectful.Block.runOpen_nil
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program ctx.withoutLoopControl 0 target)
  have hLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx.withoutLoopControl
          (.lit (EvmYul.UInt256.ofNat 1))
          ctx.withoutLoopControl post
          (ctx.withLoopControl ctx.scope ctx.scope)
          body commonFuel target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            loopResult.kind loopResult.finalTarget) :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [commonFuel])
      (FunctionsObserverTerminal.ForLoopResult.run_requiredFuel
        loopResult)
  have hStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (commonFuel + 1)
          (.for_ { stmts := [] }
            (.lit (EvmYul.UInt256.ofNat 1)) post body)
          target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            loopResult.kind loopResult.finalTarget,
            ctx) := by
    simpa [Functions.Source.Ctx.withoutLoopControl,
      Functions.Source.Ctx.withLoopControl] using
      Functions.Source.Effectful.Stmt.run_for_halt_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hInit hLoop
  have hOpen :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (commonFuel + 3)
          { stmts :=
              [.for_ { stmts := [] }
                (.lit (EvmYul.UInt256.ofNat 1)) post body] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            loopResult.kind loopResult.finalTarget,
            ctx) := by
    simpa [Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hStmt
  let result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program
        [.for_ { stmts := [] }
          (.lit (EvmYul.UInt256.ofNat 1)) post body]
        failure target ctx :=
    { kind := loopResult.kind
      finalTarget := loopResult.finalTarget
      finalCtx := ctx
      run := ⟨commonFuel + 3, hOpen⟩
      relation := loopResult.relation }
  refine ⟨⟨result, ?_⟩⟩
  apply
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
  exact hOpen

end StatementResult

theorem terminalArgsOfUncheckedLowering_programBounded
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
    {fuel globalCost : Nat}
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
    (hCost :
      ∀ expr, expr ∈ args →
        FunctionsObserverStaticCost.expr expr ≤ globalCost)
    (hRegularExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {lower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Assembly.Word},
        exprFuel < fuel →
          FunctionsObserverStaticCost.expr expr ≤ globalCost →
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
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program exprPre lower after
                  layout exprSource' exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.ProgramBounded
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel result.prepared })
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
          FunctionsObserverStaticCost.expr expr ≤ globalCost →
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
            { result :
                FunctionsObserverTerminal.StatementResult
                  contract codeRel program exprPre exprFailure
                  exprTarget exprCtx //
              StatementResult.ProgramBounded
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel result })
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
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel program pre failure target ctx //
        StatementResult.ProgramBounded
          globalCost (FunctionsObserverStaticCost.exprList args)
          fuel result } := by
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
      · obtain ⟨restBounded⟩ :=
          ih
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            (fun candidate hMem =>
              hCost candidate (List.mem_cons_of_mem expr hMem))
            hRegularExpr hTerminalExpr hRel hDomain hScope
            hRestFailure hObservable
        let restResult := restBounded.1
        let result :=
          FunctionsObserverTerminal.StatementResult.appendUnreachable
            restResult preHead
        refine ⟨⟨result, ?_⟩⟩
        have hCompose :=
          StatementResult.appendUnreachable_runBounded
            restResult preHead
        have hRestBound :
            restResult.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                globalCost
                (FunctionsObserverStaticCost.exprList rest)
                fuel := by
          simpa [restResult] using restBounded.2
        dsimp [StatementResult.ProgramBounded,
          StatementResult.RunBounded, result] at hCompose ⊢
        exact
          hCompose.trans
            (hRestBound.trans
              (FunctionsObserverFuel.executionBudgetFor_local_mono
                globalCost fuel
                (by
                  simp [FunctionsObserverStaticCost.exprList]
                  omega)))
      · rcases hHeadFailure with
          ⟨middle, restValues, headFuel,
            hFuel, hRestRun, hHeadRun⟩
        obtain ⟨exprFuel, hExprFuel, hExprRun⟩ :=
          Yul.Source.Effectful.evalArgs_singleton_observable_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hHeadRun hObservable
        obtain ⟨restBounded⟩ :=
          FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_programBounded
            (globalCost := globalCost)
            FunctionsObserverStaticCost.expr hRest
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            (fun candidate hMem =>
              hCost candidate (List.mem_cons_of_mem expr hMem))
            (fun hArgFuel hArgCost hArgOk hArgLower hArgRel hArgDomain
                hArgScope hArgRun =>
              hRegularExpr (by omega) hArgCost hArgOk hArgLower hArgRel
                hArgDomain hArgScope hArgRun)
            hRel hDomain hScope hRestRun
        obtain ⟨headBounded⟩ :=
          hTerminalExpr (by omega)
            (hCost expr (by simp))
            (hEligible expr (by simp)) hHead
            restBounded.1.relation
            restBounded.1.prepared.prepared.domain
            restBounded.1.prepared.prepared.scope
            hExprRun hObservable
        let restPrepared := restBounded.1
        let headResult := headBounded.1
        let result :=
          FunctionsObserverTerminal.StatementResult.prependPrepared
            restPrepared.prepared.prepared headResult
        refine ⟨⟨result, ?_⟩⟩
        have hCompose :=
          StatementResult.prependPrepared_runBounded
            restPrepared.prepared.prepared headResult
        have hRestBound :
            restPrepared.prepared.prepared.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                globalCost
                (FunctionsObserverStaticCost.exprList rest)
                fuel := by
          simpa [FunctionsObserverStaticCost.exprList_eq_exprListBy,
            restPrepared] using restBounded.2
        have hHeadBound :
            headResult.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel := by
          simpa [headResult] using headBounded.2
        have hHeadDynamic :=
          FunctionsObserverFuel.executionBudgetFor_mono
            globalCost (FunctionsObserverStaticCost.expr expr)
            (show exprFuel ≤ fuel by omega)
        have hAdd :=
          FunctionsObserverFuel.executionBudgetFor_add_local
            globalCost
            (FunctionsObserverStaticCost.exprList rest)
            (FunctionsObserverStaticCost.expr expr)
            fuel
        dsimp [StatementResult.ProgramBounded,
          StatementResult.RunBounded, result] at hCompose ⊢
        calc
          _ ≤ restPrepared.prepared.prepared.requiredFuel +
                headResult.requiredFuel := hCompose
          _ ≤
              FunctionsObserverFuel.executionBudgetFor
                  globalCost
                  (FunctionsObserverStaticCost.exprList rest)
                  fuel +
                FunctionsObserverFuel.executionBudgetFor
                  globalCost
                  (FunctionsObserverStaticCost.expr expr)
                  fuel :=
            Nat.add_le_add hRestBound (hHeadBound.trans hHeadDynamic)
          _ =
              FunctionsObserverFuel.executionBudgetFor
                globalCost
                (FunctionsObserverStaticCost.exprList
                  (expr :: rest))
                fuel := by
            simpa [FunctionsObserverStaticCost.exprList,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      rw [List.reverse_cons] at hRun
      rcases
          Yul.Source.Effectful.evalArgs_append_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hRun with hRestFailure | hHeadFailure
      · obtain ⟨restBounded⟩ :=
          ih
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            (fun candidate hMem =>
              hCost candidate (List.mem_cons_of_mem expr hMem))
            hRegularExpr hTerminalExpr hRel hDomain hScope
            hRestFailure hObservable
        let restResult := restBounded.1
        have hExtendedRun :
            Functions.Source.Effectful.Block.runOpen
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                program ctx restResult.requiredFuel
                { stmts :=
                    preRest ++ preHead ++
                      [Functions.Stmt.let_ tmp lowerHead] }
                target =
              .ok
                (Functions.Source.Effectful.Outcome.halt
                  restResult.kind restResult.finalTarget,
                  restResult.finalCtx) := by
          simpa only [List.append_assoc] using
            Functions.Source.Effectful.Block.runOpen_append_nonregular_at_same
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              program preRest
              (preHead ++ [Functions.Stmt.let_ tmp lowerHead])
              ctx target
              (Functions.Source.Effectful.Outcome.halt
                restResult.kind restResult.finalTarget)
              restResult.finalCtx restResult.requiredFuel
              (FunctionsObserverTerminal.StatementResult.run_requiredFuel
                restResult)
              (by simp)
        let result :
            FunctionsObserverTerminal.StatementResult
              contract codeRel program
              (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead])
              failure target ctx :=
          { kind := restResult.kind
            finalTarget := restResult.finalTarget
            finalCtx := restResult.finalCtx
            run := ⟨restResult.requiredFuel, hExtendedRun⟩
            relation := restResult.relation }
        refine ⟨⟨result, ?_⟩⟩
        have hRestBound :
            restResult.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                globalCost
                (FunctionsObserverStaticCost.exprList rest)
                fuel := by
          simpa [restResult] using restBounded.2
        have hResultRequired :
            result.requiredFuel ≤ restResult.requiredFuel := by
          exact
            FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
              result hExtendedRun
        exact
          hResultRequired.trans
            (hRestBound.trans
              (FunctionsObserverFuel.executionBudgetFor_local_mono
                globalCost fuel
                (by
                  simp [FunctionsObserverStaticCost.exprList]
                  omega)))
      · rcases hHeadFailure with
          ⟨middle, restValues, headFuel,
            hFuel, hRestRun, hHeadRun⟩
        obtain ⟨exprFuel, hExprFuel, hExprRun⟩ :=
          Yul.Source.Effectful.evalArgs_singleton_observable_error_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hHeadRun hObservable
        obtain ⟨restBounded⟩ :=
          FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_programBounded
            (globalCost := globalCost)
            FunctionsObserverStaticCost.expr hRest
            (fun candidate hMem =>
              hEligible candidate (List.mem_cons_of_mem expr hMem))
            (fun candidate hMem =>
              hCost candidate (List.mem_cons_of_mem expr hMem))
            (fun hArgFuel hArgCost hArgOk hArgLower hArgRel hArgDomain
                hArgScope hArgRun =>
              hRegularExpr (by omega) hArgCost hArgOk hArgLower hArgRel
                hArgDomain hArgScope hArgRun)
            hRel hDomain hScope hRestRun
        obtain ⟨headBounded⟩ :=
          hTerminalExpr (by omega)
            (hCost expr (by simp))
            (hEligible expr (by simp)) hHead
            restBounded.1.relation
            restBounded.1.prepared.prepared.domain
            restBounded.1.prepared.prepared.scope
            hExprRun hObservable
        let restPrepared := restBounded.1
        let headResult := headBounded.1
        let combined :=
          FunctionsObserverTerminal.StatementResult.prependPrepared
            restPrepared.prepared.prepared headResult
        have hExtendedRun :
            Functions.Source.Effectful.Block.runOpen
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                program ctx combined.requiredFuel
                { stmts :=
                    preRest ++ preHead ++
                      [Functions.Stmt.let_ tmp lowerHead] }
                target =
              .ok
                (Functions.Source.Effectful.Outcome.halt
                  combined.kind combined.finalTarget,
                  combined.finalCtx) := by
          simpa only [List.append_assoc] using
            Functions.Source.Effectful.Block.runOpen_append_nonregular_at_same
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              program (preRest ++ preHead)
              [Functions.Stmt.let_ tmp lowerHead]
              ctx target
              (Functions.Source.Effectful.Outcome.halt
                combined.kind combined.finalTarget)
              combined.finalCtx combined.requiredFuel
              (FunctionsObserverTerminal.StatementResult.run_requiredFuel
                combined)
              (by simp)
        let result :
            FunctionsObserverTerminal.StatementResult
              contract codeRel program
              (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead])
              failure target ctx :=
          { kind := combined.kind
            finalTarget := combined.finalTarget
            finalCtx := combined.finalCtx
            run := ⟨combined.requiredFuel, hExtendedRun⟩
            relation := combined.relation }
        refine ⟨⟨result, ?_⟩⟩
        have hCombined :=
          StatementResult.prependPrepared_runBounded
            restPrepared.prepared.prepared headResult
        have hRestBound :
            restPrepared.prepared.prepared.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                globalCost
                (FunctionsObserverStaticCost.exprList rest)
                fuel := by
          simpa [FunctionsObserverStaticCost.exprList_eq_exprListBy,
            restPrepared] using restBounded.2
        have hHeadBound :
            headResult.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel := by
          simpa [headResult] using headBounded.2
        have hHeadDynamic :=
          FunctionsObserverFuel.executionBudgetFor_mono
            globalCost (FunctionsObserverStaticCost.expr expr)
            (show exprFuel ≤ fuel by omega)
        have hAdd :=
          FunctionsObserverFuel.executionBudgetFor_add_local
            globalCost
            (FunctionsObserverStaticCost.exprList rest)
            (FunctionsObserverStaticCost.expr expr)
            fuel
        have hResultRequired :
            result.requiredFuel ≤
              restPrepared.prepared.prepared.requiredFuel +
                headResult.requiredFuel := by
          have hResult :
              result.requiredFuel ≤ combined.requiredFuel :=
            FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
              result hExtendedRun
          have hCombined' :
              combined.requiredFuel ≤
                restPrepared.prepared.prepared.requiredFuel +
                  headResult.requiredFuel := by
            simpa [StatementResult.RunBounded, combined] using hCombined
          exact hResult.trans hCombined'
        calc
          result.requiredFuel ≤
              restPrepared.prepared.prepared.requiredFuel +
                headResult.requiredFuel := hResultRequired
          _ ≤
              FunctionsObserverFuel.executionBudgetFor
                  globalCost
                  (FunctionsObserverStaticCost.exprList rest)
                  fuel +
                FunctionsObserverFuel.executionBudgetFor
                  globalCost
                  (FunctionsObserverStaticCost.expr expr)
                  fuel :=
            Nat.add_le_add hRestBound (hHeadBound.trans hHeadDynamic)
          _ =
              FunctionsObserverFuel.executionBudgetFor
                globalCost
                (FunctionsObserverStaticCost.exprList
                  (expr :: rest))
                fuel := by
            simpa [FunctionsObserverStaticCost.exprList,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd

theorem selectedBodyOfCallFailure_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound expected argsFuel callFuel : Nat}
    {layout : List Name}
    {functionName : Name}
    {args : List AstExpr}
    {sourceBeforeArgs sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {reversedValues : List Assembly.Word}
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
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
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
    ∃ fn paramStore bodyFuel body,
      Functions.Source.FunList.find? functionName
          targetProgram.toFunctions.functions =
        some fn ∧
      Functions.Source.Store.insertMany fn.params reversedValues.reverse
          Locals.Source.Store.empty =
        some paramStore ∧
      bodyFuel < callFuel ∧
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram ∧
      Nonempty
        { result :
            FunctionsObserverCallTerminal.BodyResult
              contract codeRel targetProgram.toFunctions fn.body failure
              (targetCaller.withSource
                { shared := targetCaller.source.shared,
                  vars :=
                    Functions.Source.Store.initReturns
                      fn.returns paramStore })
              (Functions.Source.Effectful.FunDef.bodyCtx fn) //
          BodyResult.ProgramBounded
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList body)
            bodyFuel result } := by
  obtain
      ⟨bodyFuel, _accountContract, params, returns, body,
        hBodyFuel, _hAccount, hFunction, hBodyRun⟩ :=
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
  have hBodyCost :
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram :=
    FunctionsObserverStaticCost.function_body_le_program_of_lookup hLookup
  obtain ⟨bodyBounded⟩ :=
    hTerminalBody (by omega) hBodyCost hLowerBody hParams hFnReturns
      (by simpa [hParams] using hParamStore)
      hReserved hBodyNames hBodyOk hEntry hBodyRun hObservable
  exact
    ⟨fn, paramStore, bodyFuel, body, hFind,
      by simpa [hParams] using hParamStore,
      by omega, hBodyCost, ⟨bodyBounded⟩⟩

theorem terminalCallOfUncheckedLowering_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound expected fuel : Nat}
    {before after : Fresh.State}
    {layout targets : List Name}
    {functionName : Name}
    {args : List AstExpr}
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
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hFuel : fuel < bound)
    (hExprCost :
      FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) args) ≤
        FunctionsObserverStaticCost.program sourceProgram)
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
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            (preArgs ++
              [Functions.Stmt.call targets functionName lowerArgs])
            failure target ctx //
        StatementResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args))
          fuel result } := by
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
  have hArgsCost :
      FunctionsObserverStaticCost.exprList args ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.exprList args ≤
          FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args) := by
      simp [FunctionsObserverStaticCost.expr]
    exact hLocal.trans hExprCost
  have hArgCost :
      ∀ expr, expr ∈ args →
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.program sourceProgram := by
    intro expr hMem
    exact
      (FunctionsObserverStaticCost.expr_le_exprList_of_mem hMem).trans
        hArgsCost
  rcases hFailureCase with hArgsFailure | hCallFailure
  · have hArgsTerminal :
        Nonempty
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                preArgs failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.exprList args)
              callFuel result } := by
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
            terminalArgsOfUncheckedLowering_programBounded
              (globalCost :=
                FunctionsObserverStaticCost.program sourceProgram)
              hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              hArgCost
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun =>
                hRegularExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun)
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun hArgObservable =>
                hTerminalExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun hArgObservable)
              hRel hDomain hScope hArgsFailure hObservable
    obtain ⟨argsBounded⟩ := hArgsTerminal
    let result :=
      FunctionsObserverTerminal.StatementResult.appendUnreachable
        argsBounded.1
        [Functions.Stmt.call targets functionName lowerArgs]
    refine ⟨⟨result, ?_⟩⟩
    have hAppend :=
      StatementResult.appendUnreachable_runBounded
        argsBounded.1
        [Functions.Stmt.call targets functionName lowerArgs]
    have hResultRequired :
        result.requiredFuel ≤ argsBounded.1.requiredFuel := by
      simpa [StatementResult.RunBounded, result] using hAppend
    have hDynamic :=
      FunctionsObserverFuel.executionBudgetFor_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.exprList args)
        (show callFuel ≤ fuel by omega)
    have hLocal :=
      FunctionsObserverFuel.executionBudgetFor_local_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        fuel
        (show
          FunctionsObserverStaticCost.exprList args ≤
            FunctionsObserverStaticCost.expr
              (.Call (.inr functionName) args) by
          simp [FunctionsObserverStaticCost.expr])
    exact hResultRequired.trans
      (argsBounded.2.trans (hDynamic.trans hLocal))
  · rcases hCallFailure with
      ⟨sourceAfterArgs, reversedValues, hArgsRun, hCallRun⟩
    have hPreparedArgs :
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedArgs
                contract transcript codeRel targetProgram.toFunctions
                preArgs lowerArgs after layout sourceAfterArgs
                target ctx reversedValues.reverse //
            FunctionsObserverFuel.PreparedArgs.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.exprList args)
              callFuel result.prepared } := by
      cases hArgsLowering with
      | empty =>
          cases callFuel with
          | zero =>
              simp [Yul.Source.Effectful.evalArgs,
                Yul.Source.Effectful.fail] at hArgsRun
          | succ previous =>
              simp [Yul.Source.Effectful.evalArgs] at hArgsRun
              rcases hArgsRun with ⟨rfl, rfl⟩
              let prepared :=
                FunctionsObserverExpression.PreparedArgs.empty
                  (contract := contract)
                  (program := targetProgram.toFunctions)
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope
              let result :
                  FunctionsObserverExpression.ScopedPreparedArgs
                    contract transcript codeRel targetProgram.toFunctions
                    [] [] before layout source target ctx [] :=
                { prepared := prepared
                  relation := hRel }
              refine ⟨⟨result, ?_⟩⟩
              simpa [FunctionsObserverStaticCost.exprList,
                result, prepared] using
                FunctionsObserverExpressionFuel.PreparedArgs.empty_programBounded
                  (contract := contract)
                  (program := targetProgram.toFunctions)
                  (FunctionsObserverStaticCost.program sourceProgram)
                  previous.succ
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope
      | bound hNonempty hLowering =>
          obtain ⟨bounded⟩ :=
            FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_programBounded
              (globalCost :=
                FunctionsObserverStaticCost.program sourceProgram)
              FunctionsObserverStaticCost.expr hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              hArgCost
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun =>
                hRegularExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun)
              hRel hDomain hScope hArgsRun
          exact
            ⟨⟨bounded.1, by
                simpa
                  [FunctionsObserverStaticCost.exprList_eq_exprListBy] using
                  bounded.2⟩⟩
    obtain ⟨preparedArgsBounded⟩ := hPreparedArgs
    let preparedArgs := preparedArgsBounded.1
    obtain
        ⟨fn, paramStore, bodyFuel, body,
          hFind, hParamStore, hBodyFuel, hBodyCost, bodyBounded⟩ :=
      selectedBodyOfCallFailure_programBounded
        hDecomposition hProgramOk hExprOk hTerminalBody
        (by omega) hArgsRun hCallRun
        (StateRelation.Replay.rel_of_scopedExact preparedArgs.relation)
        hObservable
    obtain ⟨bodyBounded⟩ := bodyBounded
    obtain ⟨composed⟩ :=
      StatementResult.ofPreparedArgsCall_runBounded
        preparedArgs hTargets hFind hParamStore bodyBounded.1
    refine ⟨⟨composed.1, ?_⟩⟩
    have hArgsBound :
        preparedArgs.prepared.prepared.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.exprList args)
            callFuel := by
      simpa [preparedArgs] using preparedArgsBounded.2
    have hBodyBound :
        bodyBounded.1.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList body)
            bodyFuel := by
      simpa [BodyResult.ProgramBounded, BodyResult.RunBounded] using
        bodyBounded.2
    have hChildren :=
      FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.exprList args)
        (FunctionsObserverStaticCost.stmtList body)
        hArgsCost hBodyCost
        (show callFuel < fuel by omega)
        (show bodyFuel < fuel by omega)
    have hParent :=
      FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) args))
        fuel
    dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
    dsimp [StatementResult.RunBounded] at composed
    omega

/--
Program-indexed terminal primitive preservation after regular argument
evaluation. The generated argument prelude uses the ordinary bounded expression
lowering; the terminal statement itself costs two open-block fuel units.
-/
theorem statementAfterArgs_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {argsFuel parentFuel globalCost parentLocal : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq kind.argCount}
    {source sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {reversedValues : List Assembly.Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {Eligible : AstExpr → Prop}
    (hTerminal : Prim.terminal? prim = some kind)
    (hLowerArgs :
      Expr.List.lowerBound1Unchecked? before args =
        some (preArgs, lowerArgs, after))
    (hSeq :
      Expr.List.toStackSeq? lowerArgs kind.argCount = some seq)
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hArgsCost :
      FunctionsObserverStaticCost.exprList args ≤ globalCost)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Assembly.Word},
        exprFuel < argsFuel →
          FunctionsObserverStaticCost.expr expr ≤ globalCost →
          Eligible expr →
          Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin
              exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program exprPre exprLower
                  exprAfter layout exprSource' exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.ProgramBounded
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel result.prepared })
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hArgsFuel : argsFuel < parentFuel)
    (hArgsRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          argsFuel args.reverse codeOverride source =
        .ok (sourceAfterArgs, reversedValues))
    (hPrimRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval argsFuel sourceAfterArgs prim
          reversedValues.reverse =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel program
            (preArgs ++ [Functions.Stmt.terminalArgs kind seq])
            failure target ctx //
        StatementResult.ProgramBounded
          globalCost parentLocal parentFuel result } := by
  obtain ⟨argsBounded⟩ :=
    FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_programBounded
      (globalCost := globalCost)
      FunctionsObserverStaticCost.expr
      (Expr.List.uncheckedBoundLowering_of_lowerBound1Unchecked?
        hLowerArgs)
      hEligible
      (fun expr hMem =>
        (FunctionsObserverStaticCost.expr_le_exprList_of_mem
          hMem).trans hArgsCost)
      hExpr hRel hDomain hScope hArgsRun
  let argsPrepared := argsBounded.1
  let targetAfterArgs :=
    argsPrepared.prepared.prepared.finalTarget
  have hStackArgs :=
    argsPrepared.prepared.stackStable targetAfterArgs
      (StateRelation.Vars.TargetExtends.refl _)
  have hTargetArgList :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs.reverse targetAfterArgs =
        .ok (targetAfterArgs, reversedValues) := by
    simpa [targetAfterArgs] using hStackArgs
  obtain ⟨targetFinal, hTargetTerminal, hTerminalRel⟩ :=
    FunctionsObserverTerminal.primitiveForward
      hTerminal hObservable argsPrepared.relation hPrimRun
  have hTargetTerminal' :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).terminal kind targetAfterArgs
          reversedValues =
        .ok targetFinal := by
    simpa [targetAfterArgs] using hTargetTerminal
  have hTerminalStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx 0
          (.terminalArgs kind seq) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind targetFinal,
            argsPrepared.prepared.prepared.finalCtx) :=
    FunctionsObserverExpression.terminalArgs_run_of_argList
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hSeq hTargetArgList hTargetTerminal'
  have hTerminalBlock :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx 2
          { stmts := [Functions.Stmt.terminalArgs kind seq] }
          targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind targetFinal,
            argsPrepared.prepared.prepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTerminalStmt
  have hFullRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx
          (argsPrepared.prepared.prepared.requiredFuel + 2)
          { stmts :=
              preArgs ++ [Functions.Stmt.terminalArgs kind seq] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind targetFinal,
            argsPrepared.prepared.prepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_append_regular_at_add
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program preArgs [Functions.Stmt.terminalArgs kind seq]
      ctx argsPrepared.prepared.prepared.finalCtx target targetAfterArgs
      (Functions.Source.Effectful.Outcome.halt kind targetFinal)
      argsPrepared.prepared.prepared.finalCtx
      argsPrepared.prepared.prepared.requiredFuel 2
      (FunctionsObserverExpression.Prepared.run_requiredFuel
        argsPrepared.prepared.prepared)
      hTerminalBlock
  let result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program
        (preArgs ++ [Functions.Stmt.terminalArgs kind seq])
        failure target ctx :=
    { kind := kind
      finalTarget := targetFinal
      finalCtx := argsPrepared.prepared.prepared.finalCtx
      run :=
        ⟨argsPrepared.prepared.prepared.requiredFuel + 2, hFullRun⟩
      relation := hTerminalRel }
  refine ⟨⟨result, ?_⟩⟩
  have hRequired :
      result.requiredFuel ≤
        argsPrepared.prepared.prepared.requiredFuel + 2 :=
    FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
      result hFullRun
  have hArgsBound :
      argsPrepared.prepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          globalCost (FunctionsObserverStaticCost.exprList args)
          argsFuel := by
    simpa [FunctionsObserverStaticCost.exprList_eq_exprListBy,
      argsPrepared] using argsBounded.2
  have hChild :=
    FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
      globalCost (FunctionsObserverStaticCost.exprList args)
      hArgsCost hArgsFuel
  have hParent :=
    FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
      globalCost parentLocal parentFuel
  dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
  omega

/--
Program-indexed observable-failure preservation for compiler-selected
primitive expressions. Observable failure can only arise while evaluating a
spill-bound argument: direct argument evaluation and the selected primitive
itself are proved unable to produce an observable failure.
-/
theorem terminalPrimitiveOfLowering_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel results globalCost : Nat}
    {initial final : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr results}
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
    (hExprCost :
      FunctionsObserverStaticCost.expr (.Call (.inl prim) args) ≤
        globalCost)
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hRegularExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Assembly.Word},
        exprFuel < fuel →
          FunctionsObserverStaticCost.expr expr ≤ globalCost →
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
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program exprPre exprLower
                  after layout exprSource' exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.ProgramBounded
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel result.prepared })
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
          FunctionsObserverStaticCost.expr expr ≤ globalCost →
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
            { result :
                FunctionsObserverTerminal.StatementResult
                  contract codeRel program exprPre exprFailure
                  exprTarget exprCtx //
              StatementResult.ProgramBounded
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel result })
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
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel program pre failure target ctx //
        StatementResult.ProgramBounded
          globalCost
          (FunctionsObserverStaticCost.expr (.Call (.inl prim) args))
          fuel result } := by
  obtain ⟨callFuel, hCallFuel, hFailureCase⟩ :=
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
      · obtain ⟨argsBounded⟩ :=
          terminalArgsOfUncheckedLowering_programBounded
            (globalCost := globalCost)
            hArgs hEligible
            (fun expr hMem =>
              (FunctionsObserverStaticCost.expr_le_exprList_of_mem
                hMem).trans
                (by
                  have h := hExprCost
                  simp only [FunctionsObserverStaticCost.expr] at h
                  omega))
            (fun hExprFuel hExprCost hExprEligible hExprLower hExprRel
                hExprDomain hExprScope hExprRun =>
              hRegularExpr (by omega) hExprCost hExprEligible hExprLower
                hExprRel hExprDomain hExprScope hExprRun)
            (fun hExprFuel hExprCost hExprEligible hExprLower hExprRel
                hExprDomain hExprScope hExprRun hExprObservable =>
              hTerminalExpr (by omega) hExprCost hExprEligible hExprLower
                hExprRel hExprDomain hExprScope hExprRun hExprObservable)
            hRel hDomain hScope hArgsFailure hObservable
        refine ⟨⟨argsBounded.1, ?_⟩⟩
        have hDynamic :=
          FunctionsObserverFuel.executionBudgetFor_mono
            globalCost (FunctionsObserverStaticCost.exprList args)
            (show callFuel ≤ fuel by omega)
        have hLocal :=
          FunctionsObserverFuel.executionBudgetFor_local_mono
            globalCost fuel
            (show
              FunctionsObserverStaticCost.exprList args ≤
                FunctionsObserverStaticCost.expr
                  (.Call (.inl prim) args) by
              simp only [FunctionsObserverStaticCost.expr]
              omega)
        exact argsBounded.2.trans (hDynamic.trans hLocal)
      · rcases hPrimitiveFailure with
          ⟨sourceAfterArgs, reversedValues, hArgsRun, hPrimRun⟩
        obtain ⟨argsBounded⟩ :=
          FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_programBounded
            (globalCost := globalCost)
            FunctionsObserverStaticCost.expr hArgs hEligible
            (fun expr hMem =>
              (FunctionsObserverStaticCost.expr_le_exprList_of_mem
                hMem).trans
                (by
                  have h := hExprCost
                  simp only [FunctionsObserverStaticCost.expr] at h
                  omega))
            (fun hExprFuel hExprCost hExprEligible hExprLower hExprRel
                hExprDomain hExprScope hExprRun =>
              hRegularExpr (by omega) hExprCost hExprEligible hExprLower
                hExprRel hExprDomain hExprScope hExprRun)
            hRel hDomain hScope hArgsRun
        let argsPrepared := argsBounded.1
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
          simpa [targetAfterArgs, argsPrepared] using hStackArgs
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

namespace RecursiveTerminalExpressionForwardProgramBounded

theorem ofPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularExpr :
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {exprFuel : Nat} {before after : Fresh.State}
      {layout : List Name}
      {prim : EvmYul.Operation .Yul}
      {args : List AstExpr}
      {pre : List Functions.Stmt}
      {lower : Locals.Expr 1}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      exprFuel < bound + 1 →
        FunctionsObserverStaticCost.expr (.Call (.inl prim) args) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                pre failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.expr
                (.Call (.inl prim) args))
              exprFuel result } := by
  intro exprFuel before after layout prim args pre lower source failure
    target ctx hFuel hCost hExprOk hLower hRel hDomain hScope hRun
    hObservable
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  exact
    terminalPrimitiveOfLowering_programBounded
      (fuel := exprFuel)
      (globalCost := FunctionsObserverStaticCost.program sourceProgram)
      (Eligible := fun expr =>
        SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
          true)
      (by simpa [Expr.lower1Unchecked?] using hLower)
      hCost
      (fun expr hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
      (fun hArgFuel hArgCost hArgOk hArgLower hArgRel hArgDomain
          hArgScope hArgRun =>
        hRegularExpr (by omega) hArgCost hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun)
      (fun hArgFuel hArgCost hArgOk hArgLower hArgRel hArgDomain
          hArgScope hArgRun hArgObservable =>
        hTerminalExpr (by omega) hArgCost hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun hArgObservable)
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
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {exprFuel : Nat} {before after : Fresh.State}
      {layout : List Name}
      {functionName : Name}
      {args : List AstExpr}
      {pre : List Functions.Stmt}
      {lower : Locals.Expr 1}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      exprFuel < bound + 1 →
        FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                pre failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.expr
                (.Call (.inr functionName) args))
              exprFuel result } := by
  intro exprFuel before after layout functionName args pre lower
    source failure target ctx hFuel hCallCost hExprOk hLower hRel
    hDomain hScope hRun hObservable
  have hValuesRun :=
    Yul.Source.Effectful.eval_observable_error
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨callFuel, hCallFuel, hFailureCase⟩ :=
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
  rcases hLookupExists with
    ⟨lookupParams, lookupReturns, lookupBody, hLookup⟩
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_functionCall hExprOk hLookup
  have hArgsCost :
      FunctionsObserverStaticCost.exprList args ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.exprList args ≤
          FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args) := by
      simp [FunctionsObserverStaticCost.expr]
    exact hLocal.trans hCallCost
  have hArgCost :
      ∀ expr, expr ∈ args →
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.program sourceProgram := by
    intro expr hMem
    exact
      (FunctionsObserverStaticCost.expr_le_exprList_of_mem hMem).trans
        hArgsCost
  rcases hFailureCase with hArgsFailure | hCallFailure
  · have hArgsTerminal :
        Nonempty
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                preArgs failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.exprList args)
              callFuel result } := by
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
            terminalArgsOfUncheckedLowering_programBounded
              (globalCost :=
                FunctionsObserverStaticCost.program sourceProgram)
              hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              hArgCost
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun =>
                hRegularExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun)
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun hArgObservable =>
                hTerminalExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun hArgObservable)
              hRel hDomain hScope hArgsFailure hObservable
    obtain ⟨argsBounded⟩ := hArgsTerminal
    let result :=
      FunctionsObserverTerminal.StatementResult.appendUnreachable
        argsBounded.1
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
          Functions.Stmt.call [tmp] functionName lowerArgs]
    refine ⟨⟨result, ?_⟩⟩
    have hAppend :=
      StatementResult.appendUnreachable_runBounded
        argsBounded.1
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
          Functions.Stmt.call [tmp] functionName lowerArgs]
    have hResultRequired :
        result.requiredFuel ≤ argsBounded.1.requiredFuel := by
      simpa [StatementResult.RunBounded, result] using hAppend
    have hDynamic :=
      FunctionsObserverFuel.executionBudgetFor_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.exprList args)
        (show callFuel ≤ exprFuel by omega)
    have hLocal :=
      FunctionsObserverFuel.executionBudgetFor_local_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        exprFuel
        (show
          FunctionsObserverStaticCost.exprList args ≤
            FunctionsObserverStaticCost.expr
              (.Call (.inr functionName) args) by
          simp [FunctionsObserverStaticCost.expr])
    exact hResultRequired.trans
      (argsBounded.2.trans (hDynamic.trans hLocal))
  · rcases hCallFailure with
      ⟨sourceAfterArgs, reversedValues, hArgsRun, hCallRun⟩
    have hPreparedArgs :
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedArgs
                contract transcript codeRel targetProgram.toFunctions
                preArgs lowerArgs argsFresh layout sourceAfterArgs
                target ctx reversedValues.reverse //
            FunctionsObserverFuel.PreparedArgs.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.exprList args)
              callFuel result.prepared } := by
      cases hArgsLowering with
      | empty =>
          cases callFuel with
          | zero =>
              simp [Yul.Source.Effectful.evalArgs,
                Yul.Source.Effectful.fail] at hArgsRun
          | succ previous =>
              simp [Yul.Source.Effectful.evalArgs] at hArgsRun
              rcases hArgsRun with ⟨rfl, rfl⟩
              let prepared :=
                FunctionsObserverExpression.PreparedArgs.empty
                  (contract := contract)
                  (program := targetProgram.toFunctions)
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope
              let result :
                  FunctionsObserverExpression.ScopedPreparedArgs
                    contract transcript codeRel targetProgram.toFunctions
                    [] [] before layout source target ctx [] :=
                { prepared := prepared
                  relation := hRel }
              refine ⟨⟨result, ?_⟩⟩
              simpa [FunctionsObserverStaticCost.exprList,
                result, prepared] using
                FunctionsObserverExpressionFuel.PreparedArgs.empty_programBounded
                  (contract := contract)
                  (program := targetProgram.toFunctions)
                  (FunctionsObserverStaticCost.program sourceProgram)
                  previous.succ
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope
      | bound hNonempty hLowering =>
          obtain ⟨bounded⟩ :=
            FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_programBounded
              (globalCost :=
                FunctionsObserverStaticCost.program sourceProgram)
              FunctionsObserverStaticCost.expr hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              hArgCost
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun =>
                hRegularExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun)
              hRel hDomain hScope hArgsRun
          exact
            ⟨⟨bounded.1, by
                simpa
                  [FunctionsObserverStaticCost.exprList_eq_exprListBy] using
                  bounded.2⟩⟩
    obtain ⟨preparedArgsBounded⟩ := hPreparedArgs
    let preparedArgs := preparedArgsBounded.1
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
    obtain
        ⟨fn, paramStore, bodyFuel, body,
          hFind, hParamStore, hBodyFuel, hBodyCost, bodyBounded⟩ :=
      selectedBodyOfCallFailure_programBounded
        hDecomposition hProgramOk hExprOk hTerminalBody
        (by omega) hArgsRun hCallRun hCallerRel hObservable
    obtain ⟨bodyBounded⟩ := bodyBounded
    obtain ⟨composed⟩ :=
      StatementResult.ofPreparedArgsExpressionCall_runBounded
        preparedArgs hFresh hFind hParamStore
        (by simpa [targetCaller] using bodyBounded.1)
    refine ⟨⟨composed.1, ?_⟩⟩
    have hArgsBound :
        preparedArgs.prepared.prepared.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.exprList args)
            callFuel := by
      simpa [preparedArgs] using preparedArgsBounded.2
    have hBodyBound :
        bodyBounded.1.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList body)
            bodyFuel := by
      simpa [BodyResult.ProgramBounded, BodyResult.RunBounded] using
        bodyBounded.2
    have hChildren :=
      FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.exprList args)
        (FunctionsObserverStaticCost.stmtList body)
        hArgsCost hBodyCost
        (show callFuel < exprFuel by omega)
        (show bodyFuel < exprFuel by omega)
    have hParent :=
      FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) args))
        exprFuel
    dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
    dsimp [StatementResult.RunBounded] at composed
    omega

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
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    RecursiveTerminalExpressionForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  intro exprFuel before after layout expr pre lower source failure
    target ctx hFuel hCost hExprOk hLower hRel hDomain hScope hRun
    hObservable
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
              hFuel hCost hExprOk hLower hRel hDomain hScope hRun
              hObservable
      | inr functionName =>
          exact
            ofFunctionCall hDecomposition hProgramOk hRegularExpr
              hTerminalExpr hTerminalBody
              hFuel hCost hExprOk hLower hRel hDomain hScope hRun
              hObservable

end RecursiveTerminalExpressionForwardProgramBounded

namespace RecursiveTerminalStmtForwardProgramBounded

theorem primitive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularExpr :
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {prim : EvmYul.Operation .Yul}
      {args : List AstExpr}
      {lower : List Functions.Stmt}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      sourceFuel < bound + 1 →
        FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inl prim) args)) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                lower failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt
                (.ExprStmtCall (.Call (.inl prim) args)))
              sourceFuel result } := by
  intro sourceFuel compilerFuel before after layout prim args lower
    source failure target ctx hFuel hStmtCost hNonterminal hStmtOk hLower
    hRel hDomain hScope hRun hObservable
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
  have hExprCost :
      FunctionsObserverStaticCost.expr (.Call (.inl prim) args) ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.expr (.Call (.inl prim) args) ≤
          FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inl prim) args)) := by
      simp [FunctionsObserverStaticCost.stmt]
    exact hLocal.trans hStmtCost
  obtain ⟨preBounded⟩ :=
    terminalPrimitiveOfLowering_programBounded
      (fuel := sourceFuel)
      (globalCost := FunctionsObserverStaticCost.program sourceProgram)
      (Eligible := fun expr =>
        SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
          true)
      (by simpa [Expr.lower0Unchecked?] using hExprLower)
      hExprCost
      (fun expr hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
      (fun hExprFuel hArgCost hExprOk hArgLower hExprRel hExprDomain
          hExprScope hExprRun =>
        hRegularExpr (by omega) hArgCost hExprOk hArgLower hExprRel
          hExprDomain hExprScope hExprRun)
      (fun hExprFuel hArgCost hExprOk hArgLower hExprRel hExprDomain
          hExprScope hExprRun hExprObservable =>
        hTerminalExpr (by omega) hArgCost hExprOk hArgLower hExprRel
          hExprDomain hExprScope hExprRun hExprObservable)
      hRel hDomain hScope
      (Yul.Source.Effectful.exec_expr_primitive_observable_error_evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun hObservable)
      hObservable
  let result :=
    FunctionsObserverTerminal.StatementResult.appendUnreachable
      preBounded.1 [Functions.Stmt.expr lowerExpr]
  refine ⟨⟨result, ?_⟩⟩
  have hAppend :=
    StatementResult.appendUnreachable_runBounded
      preBounded.1 [Functions.Stmt.expr lowerExpr]
  have hResultRequired :
      result.requiredFuel ≤ preBounded.1.requiredFuel := by
    simpa [StatementResult.RunBounded, result] using hAppend
  have hLocal :=
    FunctionsObserverFuel.executionBudgetFor_local_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      sourceFuel
      (show
        FunctionsObserverStaticCost.expr (.Call (.inl prim) args) ≤
          FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inl prim) args)) by
        simp [FunctionsObserverStaticCost.stmt])
  exact hResultRequired.trans (preBounded.2.trans hLocal)

theorem terminalPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularExpr :
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {prim : EvmYul.Operation .Yul}
      {args : List AstExpr}
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
        FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inl prim) args)) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                lower failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt
                (.ExprStmtCall (.Call (.inl prim) args)))
              sourceFuel result } := by
  intro sourceFuel compilerFuel before after layout prim args kind lower
    source failure target ctx hFuel hStmtCost hTerminal hStmtOk hLower
    hRel hDomain hScope hRun hObservable
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 0
          (.Call (.inl prim) args) =
        true := by
    simpa [SolcValidation.StmtOk?] using hStmtOk
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  obtain ⟨preArgs, lowerArgs, seq,
      hLowerArgs, hSeq, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_terminal_parts
      hTerminal hLower
  subst lower
  have hArgsCost :
      FunctionsObserverStaticCost.exprList args ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.exprList args ≤
          FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inl prim) args)) := by
      simp [FunctionsObserverStaticCost.stmt,
        FunctionsObserverStaticCost.expr]
      omega
    exact hLocal.trans hStmtCost
  rcases
      Yul.Source.Effectful.exec_expr_primitive_error_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun with hOuter | hPrevious
  · rcases hOuter with ⟨rfl, hFailure⟩
    rw [← hFailure] at hObservable
    simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  · rcases hPrevious with
      ⟨argsFuel, hSourceFuel, hArgsFailure | hPrimitiveFailure⟩
    · obtain ⟨argsBounded⟩ :=
        terminalArgsOfUncheckedLowering_programBounded
          (globalCost :=
            FunctionsObserverStaticCost.program sourceProgram)
          (Expr.List.uncheckedBoundLowering_of_lowerBound1Unchecked?
            hLowerArgs)
          (fun candidate hMem =>
            SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
          (fun candidate hMem =>
            (FunctionsObserverStaticCost.expr_le_exprList_of_mem
              hMem).trans hArgsCost)
          (fun hArgFuel hArgCost hArgOk hArgLower hArgRel hArgDomain
              hArgScope hArgRun =>
            hRegularExpr (by omega) hArgCost hArgOk hArgLower hArgRel
              hArgDomain hArgScope hArgRun)
          (fun hArgFuel hArgCost hArgOk hArgLower hArgRel hArgDomain
              hArgScope hArgRun hArgObservable =>
            hTerminalExpr (by omega) hArgCost hArgOk hArgLower hArgRel
              hArgDomain hArgScope hArgRun hArgObservable)
          hRel hDomain hScope hArgsFailure hObservable
      let result :=
        FunctionsObserverTerminal.StatementResult.appendUnreachable
          argsBounded.1 [Functions.Stmt.terminalArgs kind seq]
      refine ⟨⟨result, ?_⟩⟩
      have hAppend :=
        StatementResult.appendUnreachable_runBounded
          argsBounded.1 [Functions.Stmt.terminalArgs kind seq]
      have hResultRequired :
          result.requiredFuel ≤ argsBounded.1.requiredFuel := by
        simpa [StatementResult.RunBounded, result] using hAppend
      have hDynamic :=
        FunctionsObserverFuel.executionBudgetFor_mono
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.exprList args)
          (show argsFuel ≤ sourceFuel by omega)
      have hLocal :=
        FunctionsObserverFuel.executionBudgetFor_local_mono
          (FunctionsObserverStaticCost.program sourceProgram)
          sourceFuel
          (show
            FunctionsObserverStaticCost.exprList args ≤
              FunctionsObserverStaticCost.stmt
                (.ExprStmtCall (.Call (.inl prim) args)) by
            simp [FunctionsObserverStaticCost.stmt,
              FunctionsObserverStaticCost.expr]
            omega)
      exact hResultRequired.trans
        (argsBounded.2.trans (hDynamic.trans hLocal))
    · rcases hPrimitiveFailure with
        ⟨sourceAfterArgs, reversedValues, hArgsRun, hPrimRun⟩
      exact
        statementAfterArgs_programBounded
          (parentFuel := sourceFuel)
          (globalCost :=
            FunctionsObserverStaticCost.program sourceProgram)
          (parentLocal :=
            FunctionsObserverStaticCost.stmt
              (.ExprStmtCall (.Call (.inl prim) args)))
          hTerminal hLowerArgs hSeq
          (fun candidate hMem =>
            SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
          hArgsCost
          (fun hArgFuel hArgCost hArgOk hArgLower hArgRel hArgDomain
              hArgScope hArgRun =>
            hRegularExpr (by omega) hArgCost hArgOk hArgLower hArgRel
              hArgDomain hArgScope hArgRun)
          hRel hDomain hScope (by omega) hArgsRun hPrimRun hObservable

theorem letOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {name : EvmYul.Identifier}
      {expr : AstExpr}
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
        FunctionsObserverStaticCost.stmt (.Let [name] (some expr)) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                lower failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt
                (.Let [name] (some expr)))
              sourceFuel result } := by
  intro sourceFuel compilerFuel before after layout name expr lower
    source failure target ctx canBreak canContinue canLeave
    hFuel hStmtCost hNotFunctionCall hStmtOk hLower hRel hDomain hScope
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
  obtain ⟨exprFuel, hSourceFuel, hExprValuesRun⟩ :=
    Yul.Source.Effectful.exec_let_some_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      (by
        rcases hRel.2 with
          ⟨sourceShared, sourceVars, hSource, _hShared,
            _hVars, hSourceDomain⟩
        change EvmYul.Yul.checkDeclaration source.source [name] = .ok ()
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
  have hExprCost :
      FunctionsObserverStaticCost.expr expr ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.stmt (.Let [name] (some expr)) := by
      simp [FunctionsObserverStaticCost.stmt]
      omega
    exact hLocal.trans hStmtCost
  obtain ⟨preBounded⟩ :=
    hTerminalExpr (by omega) hExprCost hExprOk hExprLower hRel hDomain
      hScope hExprRun hObservable
  let result :=
    FunctionsObserverTerminal.StatementResult.appendUnreachable
      preBounded.1 [Functions.Stmt.let_ (identName name) lowerValue]
  refine ⟨⟨result, ?_⟩⟩
  have hAppend :=
    StatementResult.appendUnreachable_runBounded
      preBounded.1 [Functions.Stmt.let_ (identName name) lowerValue]
  have hResultRequired :
      result.requiredFuel ≤ preBounded.1.requiredFuel := by
    simpa [StatementResult.RunBounded, result] using hAppend
  have hDynamic :=
    FunctionsObserverFuel.executionBudgetFor_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.expr expr)
      (show exprFuel ≤ sourceFuel by omega)
  have hLocal :=
    FunctionsObserverFuel.executionBudgetFor_local_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      sourceFuel
      (show
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.stmt (.Let [name] (some expr)) by
        simp [FunctionsObserverStaticCost.stmt]
        omega)
  exact hResultRequired.trans
    (preBounded.2.trans (hDynamic.trans hLocal))

theorem assignOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {name : EvmYul.Identifier}
      {expr : AstExpr}
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
        FunctionsObserverStaticCost.stmt (.Assign [name] expr) ≤
          FunctionsObserverStaticCost.program sourceProgram →
        (∀ functionName functionArgs,
          expr ≠ .Call (.inr functionName) functionArgs) →
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout canBreak canContinue canLeave
            (.Assign [name] expr) =
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                lower failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt
                (.Assign [name] expr))
              sourceFuel result } := by
  intro sourceFuel compilerFuel before after layout name expr lower
    source failure target ctx canBreak canContinue canLeave
    hFuel hStmtCost hNotFunctionCall hStmtOk hLower hRel hDomain hScope
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
  obtain ⟨exprFuel, hSourceFuel, hExprValuesRun⟩ :=
    Yul.Source.Effectful.exec_assign_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      (by
        rcases hRel.2 with
          ⟨sourceShared, sourceVars, hSource, _hShared,
            _hVars, hSourceDomain⟩
        change EvmYul.Yul.checkAssignment source.source [name] = .ok ()
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
  have hExprCost :
      FunctionsObserverStaticCost.expr expr ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.stmt (.Assign [name] expr) := by
      simp [FunctionsObserverStaticCost.stmt]
      omega
    exact hLocal.trans hStmtCost
  obtain ⟨preBounded⟩ :=
    hTerminalExpr (by omega) hExprCost hExprOk hExprLower hRel hDomain
      hScope hExprRun hObservable
  let result :=
    FunctionsObserverTerminal.StatementResult.appendUnreachable
      preBounded.1 [Functions.Stmt.assign (identName name) lowerValue]
  refine ⟨⟨result, ?_⟩⟩
  have hAppend :=
    StatementResult.appendUnreachable_runBounded
      preBounded.1 [Functions.Stmt.assign (identName name) lowerValue]
  have hResultRequired :
      result.requiredFuel ≤ preBounded.1.requiredFuel := by
    simpa [StatementResult.RunBounded, result] using hAppend
  have hDynamic :=
    FunctionsObserverFuel.executionBudgetFor_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.expr expr)
      (show exprFuel ≤ sourceFuel by omega)
  have hLocal :=
    FunctionsObserverFuel.executionBudgetFor_local_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      sourceFuel
      (show
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.stmt (.Assign [name] expr) by
        simp [FunctionsObserverStaticCost.stmt]
        omega)
  exact hResultRequired.trans
    (preBounded.2.trans (hDynamic.trans hLocal))

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
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {names : List EvmYul.Identifier}
      {functionName : Name}
      {args : List AstExpr}
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
        FunctionsObserverStaticCost.stmt
            (.Let names (some (.Call (.inr functionName) args))) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                lower failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt
                (.Let names
                  (some (.Call (.inr functionName) args))))
              sourceFuel result } := by
  intro sourceFuel compilerFuel before after layout names functionName args
    lower source failure target ctx canBreak canContinue canLeave
    hFuel hStmtCost hStmtOk hNamesUsed hLower hRel hDomain hScope
    hRun hObservable
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_call_parts hLower
  have hLowerStmts' :
      lower =
        Stmt.initNames (identNames names) ++
          (preArgs ++
            [Functions.Stmt.call
              (identNames names) functionName lowerArgs]) := by
    simpa [List.append_assoc] using hLowerStmts
  clear hLowerStmts
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
  obtain ⟨evalFuel, hSourceFuel, hEvalValues⟩ :=
    Yul.Source.Effectful.exec_let_some_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hCheck hRun hObservable
  obtain ⟨initVars, initCtx, hInsert, hInitRun, hInitCtx⟩ :=
    FunctionsObserverStatement.InitNames.run_at_length
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
  have hExprCost :
      FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) args) ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args) ≤
          FunctionsObserverStaticCost.stmt
            (.Let names (some (.Call (.inr functionName) args))) := by
      simp [FunctionsObserverStaticCost.stmt]
      omega
    exact hLocal.trans hStmtCost
  obtain ⟨callBounded⟩ :=
    terminalCallOfUncheckedLowering_programBounded
      (targets := identNames names)
      hDecomposition hProgramOk hExprOk hArgsLowering
      (by simpa [identNames_eq_self] using hTargetsNodup)
      hRegularExpr hTerminalExpr hTerminalBody
      (by omega) hExprCost hDeclaredRel hDeclaredDomain hDeclaredScope
      hEvalValues hObservable
  let rawResult :=
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
      ⟨(identNames names).length + 1,
        by simpa [targetDeclared] using hInitRun⟩
      callBounded.1
  let result := rawResult
  refine ⟨⟨result, ?_⟩⟩
  have hRaw :=
    StatementResult.prependRegularRun_runBounded
      (contract := contract) (codeRel := codeRel)
      (program := targetProgram.toFunctions)
      (failure := failure)
      (leftLower := Stmt.initNames (identNames names))
      (rightLower :=
        preArgs ++
          [Functions.Stmt.call
            (identNames names) functionName lowerArgs])
      (target := target) (middleTarget := targetDeclared)
      (ctx := ctx) (middleCtx := initCtx)
      (leftFuel := (identNames names).length + 1)
      (by simpa [targetDeclared] using hInitRun)
      callBounded.1
  have hResultRequired :
      result.requiredFuel ≤
        (identNames names).length + 1 +
          callBounded.1.requiredFuel := by
    simpa [StatementResult.RunBounded, result, rawResult] using hRaw
  have hCallBound :
      callBounded.1.requiredFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args))
          evalFuel := by
    simpa [StatementResult.ProgramBounded,
      StatementResult.RunBounded] using callBounded.2
  have hChild :=
    FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.expr
        (.Call (.inr functionName) args))
      hExprCost (show evalFuel < sourceFuel by omega)
  have hParent :=
    FunctionsObserverFuel.targetBudgetFor_add_localCost_le_executionBudgetFor
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmt
        (.Let names (some (.Call (.inr functionName) args))))
      sourceFuel
  have hInitCost :
      (identNames names).length + 1 ≤
        FunctionsObserverStaticCost.stmt
          (.Let names (some (.Call (.inr functionName) args))) := by
    simp [identNames, FunctionsObserverStaticCost.stmt]
    omega
  dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
  omega

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
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {names : List EvmYul.Identifier}
      {functionName : Name}
      {args : List AstExpr}
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
        FunctionsObserverStaticCost.stmt
            (.Assign names (.Call (.inr functionName) args)) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                lower failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt
                (.Assign names (.Call (.inr functionName) args)))
              sourceFuel result } := by
  intro sourceFuel compilerFuel before after layout names functionName args
    lower source failure target ctx canBreak canContinue canLeave
    hFuel hStmtCost hStmtOk hLower hRel hDomain hScope hRun hObservable
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
  obtain ⟨evalFuel, hSourceFuel, hEvalValues⟩ :=
    Yul.Source.Effectful.exec_assign_observable_error_evalValues
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hCheck hRun hObservable
  have hExprCost :
      FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) args) ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args) ≤
          FunctionsObserverStaticCost.stmt
            (.Assign names (.Call (.inr functionName) args)) := by
      simp [FunctionsObserverStaticCost.stmt]
      omega
    exact hLocal.trans hStmtCost
  obtain ⟨callBounded⟩ :=
    terminalCallOfUncheckedLowering_programBounded
      (targets := identNames names)
      hDecomposition hProgramOk hExprOk hArgsLowering
      (by simpa [identNames_eq_self] using hTargetsNodup)
      hRegularExpr hTerminalExpr hTerminalBody
      (by omega) hExprCost hRel hDomain hScope hEvalValues hObservable
  refine ⟨⟨callBounded.1, ?_⟩⟩
  have hDynamic :=
    FunctionsObserverFuel.executionBudgetFor_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.expr
        (.Call (.inr functionName) args))
      (show evalFuel ≤ sourceFuel by omega)
  have hLocal :=
    FunctionsObserverFuel.executionBudgetFor_local_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      sourceFuel
      (show
        FunctionsObserverStaticCost.expr
            (.Call (.inr functionName) args) ≤
          FunctionsObserverStaticCost.stmt
            (.Assign names (.Call (.inr functionName) args)) by
        simp [FunctionsObserverStaticCost.stmt]
        omega)
  exact callBounded.2.trans (hDynamic.trans hLocal)

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
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {before after : Fresh.State}
      {layout : List Name}
      {functionName : Name}
      {args : List AstExpr}
      {lower : List Functions.Stmt}
      {source :
        ObserverSemantics.SourceReplay.State transcript}
      {failure :
        Yul.Source.Effectful.Failure
          (ObserverSemantics.SourceReplay.State transcript)}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx},
      sourceFuel < bound + 1 →
        FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inr functionName) args)) ≤
          FunctionsObserverStaticCost.program sourceProgram →
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
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                lower failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt
                (.ExprStmtCall (.Call (.inr functionName) args)))
              sourceFuel result } := by
  intro sourceFuel compilerFuel before after layout functionName args
    lower source failure target ctx hFuel hStmtCost hStmtOk hLower hRel
    hDomain hScope hRun hObservable
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
  have hArgsCost :
      FunctionsObserverStaticCost.exprList args ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.exprList args ≤
          FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inr functionName) args)) := by
      simp [FunctionsObserverStaticCost.stmt,
        FunctionsObserverStaticCost.expr]
      omega
    exact hLocal.trans hStmtCost
  have hArgCost :
      ∀ expr, expr ∈ args →
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.program sourceProgram := by
    intro expr hMem
    exact
      (FunctionsObserverStaticCost.expr_le_exprList_of_mem hMem).trans
        hArgsCost
  rcases hFailureCase with hArgsFailure | hCallFailure
  · have hArgsTerminal :
        Nonempty
          { result :
              FunctionsObserverTerminal.StatementResult
                contract codeRel targetProgram.toFunctions
                preArgs failure target ctx //
            StatementResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.exprList args)
              argsFuel result } := by
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
            terminalArgsOfUncheckedLowering_programBounded
              (globalCost :=
                FunctionsObserverStaticCost.program sourceProgram)
              hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              hArgCost
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun =>
                hRegularExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun)
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun hArgObservable =>
                hTerminalExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun hArgObservable)
              hRel hDomain hScope hArgsFailure hObservable
    obtain ⟨argsBounded⟩ := hArgsTerminal
    let result :=
      FunctionsObserverTerminal.StatementResult.appendUnreachable
        argsBounded.1
        [Functions.Stmt.call [] functionName lowerArgs]
    refine ⟨⟨result, ?_⟩⟩
    have hAppend :=
      StatementResult.appendUnreachable_runBounded
        argsBounded.1
        [Functions.Stmt.call [] functionName lowerArgs]
    have hResultRequired :
        result.requiredFuel ≤ argsBounded.1.requiredFuel := by
      simpa [StatementResult.RunBounded, result] using hAppend
    have hDynamic :=
      FunctionsObserverFuel.executionBudgetFor_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.exprList args)
        (show argsFuel ≤ sourceFuel by omega)
    have hLocal :=
      FunctionsObserverFuel.executionBudgetFor_local_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        sourceFuel
        (show
          FunctionsObserverStaticCost.exprList args ≤
            FunctionsObserverStaticCost.stmt
              (.ExprStmtCall (.Call (.inr functionName) args)) by
          simp [FunctionsObserverStaticCost.stmt,
            FunctionsObserverStaticCost.expr]
          omega)
    exact hResultRequired.trans
      (argsBounded.2.trans (hDynamic.trans hLocal))
  · rcases hCallFailure with
      ⟨callFuel, sourceAfterArgs, reversedValues,
        hArgsFuel, hArgsRun, hCallRun⟩
    have hPreparedArgs :
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedArgs
                contract transcript codeRel targetProgram.toFunctions
                preArgs lowerArgs after layout sourceAfterArgs
                target ctx reversedValues.reverse //
            FunctionsObserverFuel.PreparedArgs.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.exprList args)
              argsFuel result.prepared } := by
      cases hArgsLowering with
      | empty =>
          cases argsFuel with
          | zero =>
              simp [Yul.Source.Effectful.evalArgs,
                Yul.Source.Effectful.fail] at hArgsRun
          | succ previous =>
              simp [Yul.Source.Effectful.evalArgs] at hArgsRun
              rcases hArgsRun with ⟨rfl, rfl⟩
              let prepared :=
                FunctionsObserverExpression.PreparedArgs.empty
                  (contract := contract)
                  (program := targetProgram.toFunctions)
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope
              let result :
                  FunctionsObserverExpression.ScopedPreparedArgs
                    contract transcript codeRel targetProgram.toFunctions
                    [] [] before layout source target ctx [] :=
                { prepared := prepared
                  relation := hRel }
              refine ⟨⟨result, ?_⟩⟩
              simpa [FunctionsObserverStaticCost.exprList,
                result, prepared] using
                FunctionsObserverExpressionFuel.PreparedArgs.empty_programBounded
                  (contract := contract)
                  (program := targetProgram.toFunctions)
                  (FunctionsObserverStaticCost.program sourceProgram)
                  previous.succ
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope
      | bound hNonempty hLowering =>
          obtain ⟨bounded⟩ :=
            FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_programBounded
              (globalCost :=
                FunctionsObserverStaticCost.program sourceProgram)
              FunctionsObserverStaticCost.expr hLowering
              (fun candidate hMem =>
                SolcValidation.exprOk_of_exprsOk_of_mem
                  hArgsOk hMem)
              hArgCost
              (fun hArgFuel hArgCost hArgOk hArgLower hArgRel
                  hArgDomain hArgScope hArgRun =>
                hRegularExpr (by omega) hArgCost hArgOk hArgLower
                  hArgRel hArgDomain hArgScope hArgRun)
              hRel hDomain hScope hArgsRun
          exact
            ⟨⟨bounded.1, by
                simpa
                  [FunctionsObserverStaticCost.exprList_eq_exprListBy] using
                  bounded.2⟩⟩
    obtain ⟨preparedArgsBounded⟩ := hPreparedArgs
    let preparedArgs := preparedArgsBounded.1
    obtain
        ⟨fn, paramStore, bodyFuel, body,
          hFind, hParamStore, hBodyFuel, hBodyCost, bodyBounded⟩ :=
      selectedBodyOfCallFailure_programBounded
        hDecomposition hProgramOk hExprOk hTerminalBody
        (by omega) hArgsRun hCallRun
        (StateRelation.Replay.rel_of_scopedExact preparedArgs.relation)
        hObservable
    obtain ⟨bodyBounded⟩ := bodyBounded
    obtain ⟨composed⟩ :=
      StatementResult.ofPreparedArgsCall_runBounded
        preparedArgs List.nodup_nil hFind hParamStore bodyBounded.1
    refine ⟨⟨composed.1, ?_⟩⟩
    have hArgsBound :
        preparedArgs.prepared.prepared.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.exprList args)
            argsFuel := by
      simpa [preparedArgs] using preparedArgsBounded.2
    have hBodyBound :
        bodyBounded.1.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList body)
            bodyFuel := by
      simpa [BodyResult.ProgramBounded, BodyResult.RunBounded] using
        bodyBounded.2
    have hChildren :=
      FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.exprList args)
        (FunctionsObserverStaticCost.stmtList body)
        hArgsCost hBodyCost
        (show argsFuel < sourceFuel by omega)
        (show bodyFuel < sourceFuel by omega)
    have hParent :=
      FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.stmt
          (.ExprStmtCall (.Call (.inr functionName) args)))
        sourceFuel
    dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
    dsimp [StatementResult.RunBounded] at composed
    omega

end RecursiveTerminalStmtForwardProgramBounded

namespace RecursiveTerminalListForwardProgramBounded

theorem ofStmt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hRegularStmt :
      FunctionsObserverForwardFuel.RecursiveOpenStmtForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalStmt :
      RecursiveTerminalStmtForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    (hTerminalList :
      RecursiveTerminalListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    RecursiveTerminalListForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram
      profile (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmts
    lower source failure target ctx canBreak canContinue canLeave
    hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout hControl
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
        have hPreviousFuel : sourcePrevious < sourceFuel := by
          omega
        have hHeadCost :
            FunctionsObserverStaticCost.stmt head ≤
              FunctionsObserverStaticCost.program sourceProgram :=
          (FunctionsObserverStaticCost.stmt_head_le_stmtList
            head tail).trans hCost
        have hTailCost :
            FunctionsObserverStaticCost.stmtList tail ≤
              FunctionsObserverStaticCost.program sourceProgram :=
          (FunctionsObserverStaticCost.stmtList_tail_le_stmtList
            head tail).trans hCost
        obtain ⟨hHeadOk, hTailOk⟩ :=
          SolcValidation.stmtsOk_cons_parts hOk
        have hHeadNames :
            StateRelation.Vars.NamesWithin before.used
              (Stmt.names head) := by
          intro name hMem
          exact hNames name (List.mem_append_left _ hMem)
        rcases hFailureCase with hHeadFailure | hTailFailure
        · obtain ⟨headBounded⟩ :=
            hTerminalStmt hPreviousBound hHeadCost hHeadOk hHeadNames
              hLowerHead hRel hDomain hScope hLayout hControl
              hHeadFailure hObservable
          let headResult := headBounded.1
          let result :=
            FunctionsObserverTerminal.StatementResult.appendUnreachable
              headResult lowerTail
          refine ⟨⟨result, ?_⟩⟩
          have hCompose :=
            StatementResult.appendUnreachable_runBounded
              headResult lowerTail
          have hHeadResultBound := headBounded.2
          dsimp [StatementResult.RunBounded, result] at hCompose ⊢
          exact
            hCompose.trans
              (hHeadResultBound.trans
                ((FunctionsObserverFuel.executionBudgetFor_local_mono
                  (FunctionsObserverStaticCost.program sourceProgram)
                  sourcePrevious
                  (FunctionsObserverStaticCost.stmt_head_le_stmtList
                    head tail)).trans
                  (FunctionsObserverFuel.executionBudgetFor_mono
                    (FunctionsObserverStaticCost.program sourceProgram)
                    (FunctionsObserverStaticCost.stmtList (head :: tail))
                    (by omega))))
        · rcases hTailFailure with
            ⟨sourceAfterHead, shared, vars,
              hHeadRun, hSourceAfterHead, hTailRun⟩
          obtain ⟨headBounded⟩ :=
            hRegularStmt hPreviousBound hHeadCost hHeadOk hHeadNames
              hLowerHead hRel hDomain hScope hLayout hControl hHeadRun
          let headResult := headBounded.1
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
          obtain ⟨tailBounded⟩ :=
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
              hPreviousBound hTailCost hTailOk' hTailNames hLowerTail
              hHeadRel headResult.openResult.domain
              headResult.openResult.scope
              headResult.openResult.layoutWithin
              (headResult.regularControl hHeadRegular)
              hTailRun hObservable
          let tailResult := tailBounded.1
          let result :=
            FunctionsObserverTerminal.StatementResult.prependRegular
              headResult.openResult hHeadRegular tailResult
          refine ⟨⟨result, ?_⟩⟩
          have hCompose :=
            StatementResult.prependRegular_runBounded
              headResult.openResult hHeadRegular tailResult
          have hChildren :=
            FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmt head)
              (FunctionsObserverStaticCost.stmtList tail)
              hHeadCost hTailCost hPreviousFuel hPreviousFuel
          have hParent :=
            FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmtList (head :: tail))
              sourceFuel
          dsimp [StatementResult.RunBounded, result] at hCompose ⊢
          have hHeadBound :
              headResult.openResult.requiredFuel ≤
                FunctionsObserverFuel.executionBudgetFor
                  (FunctionsObserverStaticCost.program sourceProgram)
                  (FunctionsObserverStaticCost.stmt head)
                  sourcePrevious := by
            simpa [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded,
              headResult] using headBounded.2
          have hTailBound :
              tailResult.requiredFuel ≤
                FunctionsObserverFuel.executionBudgetFor
                  (FunctionsObserverStaticCost.program sourceProgram)
                  (FunctionsObserverStaticCost.stmtList tail)
                  sourcePrevious := by
            simpa [tailResult] using tailBounded.2
          omega

end RecursiveTerminalListForwardProgramBounded

namespace RecursiveTerminalBodyForwardProgramBounded

theorem ofList
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hList :
      RecursiveTerminalListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    RecursiveTerminalBodyForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram
      profile (bound + 1) := by
  intro sourceFuel before after params returns body fn args paramStore
    sourceCaller failure targetCaller hFuel hCost hLower hParams hReturns
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
      ⟨listSourceFuel, hSourceFuel, hListRun⟩
    have hListBound : listSourceFuel < bound := by
      omega
    have hListFuel : listSourceFuel < sourceFuel := by
      omega
    have hLayout :
        StateRelation.Vars.NamesWithin before.used layout := by
      simpa [layout] using hReserved
    let sourceControl : FunctionsObserverOutcome.SourceControlScopes :=
      { breakScope? := none
        continueScope? := none
        leaveScope? := some layout }
    have hControl :
        FunctionsObserverOutcome.ControlContextRel sourceControl layout
          false false true (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
      refine
        { scope := ?_
          breakScope := ?_
          continueScope := ?_
          leaveScope := ?_ }
      · simp [layout, Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope,
          FunctionsObserverOutcome.LayoutWithinScope]
      · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
          Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope]
      · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
          Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope]
      · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
          Functions.Source.Effectful.FunDef.bodyCtx,
          Functions.Source.Ctx.initial,
          Functions.Source.Ctx.withLeaveScope, layout]
    obtain ⟨listBounded⟩ :=
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
        hListBound hCost hBodyOk hBodyNames hLowerList hEntry
        (by
          simpa [targetEntry] using
            FunctionsObserverForward.RecursiveBodyForward.entryTargetDomain
              hParamStore hReserved)
        (FunctionsObserverForward.RecursiveBodyForward.bodyScope
          hReserved)
        hReserved hControl hListRun hObservable
    let statementResult := listBounded.1
    let result :=
      FunctionsObserverCallTerminal.BodyResult.ofStatement
        hFnBody statementResult
    refine ⟨⟨result, ?_⟩⟩
    have hCompose :=
      BodyResult.ofStatement_runBounded hFnBody statementResult
    dsimp [BodyResult.RunBounded, result] at hCompose
    have hListResultBound := listBounded.2
    exact
      hCompose.trans
        (hListResultBound.trans
          (FunctionsObserverFuel.executionBudgetFor_mono
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList body)
            (by omega)))

end RecursiveTerminalBodyForwardProgramBounded

end FunctionsObserverTerminalFuel
end Yul
end EvmCompiler
