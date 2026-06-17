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

end FunctionsObserverTerminalFuel
end Yul
end EvmCompiler
