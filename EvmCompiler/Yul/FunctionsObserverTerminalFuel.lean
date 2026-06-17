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
