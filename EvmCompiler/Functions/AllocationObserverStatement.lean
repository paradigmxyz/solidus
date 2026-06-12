import EvmCompiler.Functions.AllocationObserverPrimitive
import EvmCompiler.Functions.AllocationObserverTerminal

namespace EvmCompiler
namespace Functions
namespace AllocationObserverStatement

open AllocationObserverRelation

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

namespace ExprLeaf

/--
Successful execution of the real statement lowerer and Locals block compiler
for an expression statement exposes exactly one Structured code statement.
-/
theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ lowered code,
      AllocationLowering.lowerExpr lowerCtx lowerState expr = some lowered ∧
      Locals.Expr.compileCode localsCtx 0 lowered = some code ∧
      loweredStmts = [.expr lowered] ∧
      lowerFinal = lowerState ∧
      compiledStmts = [Expressions.Stmt.code code] ∧
      localsFinal = localsCtx := by
  cases hLowerExpr :
      AllocationLowering.lowerExpr lowerCtx lowerState expr with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
  | some lowered =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      cases hCode :
          Locals.Expr.compileCode localsCtx 0 lowered with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode] at hCompile
      | some code =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile,
            Locals.codeStmt, hCode] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact ⟨lowered, code, rfl, hCode, rfl, rfl, rfl, rfl⟩

/--
Forward preservation for a Functions expression statement through the actual
allocation expression lowerer and Locals expression compiler.

The statement introduces no new local, so the same allocation context and live
set relate the regular outcomes.
-/
theorem forward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {expr : Functions.Expr 0}
    {lowered : Locals.Expr 0} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel (.expr expr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx) ∧
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram targetFuel (.code code) target
          (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain ⟨targetFinal, hTargetRun, hResultRel⟩ :=
    AllocationObserverExpression.forwardExpr
      (AllocationObserverPrimitive.canonicalPrimitiveForward contract)
      hSafe hCtx hScoped hLower hCompile hRel
  have hSourceRun :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.expr
      (program := sourceProgram) (ctx := sourceCtx) (fuel := sourceFuel)
      hSafe).run_eq
  have hState :
      StateRel contract plan live stackOffset frameBase
        sourceFinal targetFinal := by
    simpa using hResultRel.state.base
  exact
    ⟨targetFinal, hSourceRun,
      Structured.EffectSemantics.Stmt.Eval.code hTargetRun,
      OutcomeRel.regular hState⟩

/--
Backward adequacy for a compiled expression statement.

Determinism of the canonical Structured code runner identifies the target
state constructed by the forward theorem, yielding the same source statement
run and outcome relation.
-/
theorem backward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {expr : Functions.Expr 0}
    {lowered : Locals.Expr 0} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hTarget :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram targetFuel (.code code) target
          (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel (.expr expr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular sourceFinal,
          sourceCtx) ∧
    OutcomeRel contract plan live stackOffset frameBase
      (Functions.Source.Effectful.Outcome.regular sourceFinal)
      (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  cases hTarget with
  | code hTargetRun =>
      obtain ⟨_hSourceEval, hResultRel⟩ :=
        AllocationObserverExpression.Expr.backward_of_safeEval
          (AllocationObserverPrimitive.canonicalPrimitiveForward contract)
          hCtx hSafe hScoped hLower hCompile hRel hTargetRun
      have hSourceRun :=
        (AllocationObserverSafety.Stmt.LeafMemorySafeRun.expr
          (program := sourceProgram) (ctx := sourceCtx) (fuel := sourceFuel)
          hSafe).run_eq
      have hState :
          StateRel contract plan live stackOffset frameBase
            sourceFinal targetFinal := by
        simpa using hResultRel.state.base
      exact ⟨hSourceRun, OutcomeRel.regular hState⟩

/--
Forward preservation stated over the actual expanded statement block produced
by `lowerStmt` followed by `Locals.Block.compileOpen`.
-/
theorem forward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase frameDepth frameWords : Nat}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ScratchStateRel contract plan live
        0 frameBase frameDepth frameWords source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel (.expr expr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      OutcomeRel contract plan live 0 frameBase
        (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain
      ⟨lowered, code, hLowerExpr, hCompileCode,
        rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hLower hCompile
  obtain ⟨targetFinal, hSourceRun, hTargetStmt, hOutcome⟩ :=
    forward
      (targetFuel := targetFuel + 1)
      hSafe hCtx hScoped hLowerExpr hCompileCode hRel
  refine ⟨targetFinal, hSourceRun, ?_, hOutcome⟩
  simpa [Expressions.StmtList.toStructured, Expressions.Stmt.toStructured] using
    (Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil)

/--
Backward adequacy over the real expanded statement block.
-/
theorem backward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase frameDepth frameWords : Nat}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ScratchStateRel contract plan live
        0 frameBase frameDepth frameWords source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel (.expr expr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular sourceFinal,
          sourceCtx) ∧
    OutcomeRel contract plan live 0 frameBase
      (Functions.Source.Effectful.Outcome.regular sourceFinal)
      (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain
      ⟨lowered, code, hLowerExpr, hCompileCode,
        rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hLower hCompile
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hTarget
  cases hTarget with
  | cons_regular hTargetStmt hTail =>
      cases hTail
      exact
        backward hSafe hCtx hScoped hLowerExpr hCompileCode hRel hTargetStmt

end ExprLeaf

end AllocationObserverStatement
end Functions
end EvmCompiler
