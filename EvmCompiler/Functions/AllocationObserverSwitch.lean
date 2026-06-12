import EvmCompiler.Functions.AllocationObserverStatement

namespace EvmCompiler
namespace Functions
namespace AllocationObserverStatement

open AllocationObserverRelation

namespace Sequence
namespace RegularStmtInvariantForward

/--
Forward preservation for a regular `switch` execution that selects neither a
case nor a default body.

The proof composes the real Functions allocation lowerer, Locals compiler,
canonical source and Structured semantics, and the activation expression
relation. Branch-selection preservation remains owned by the adjacent compiler
passes.
-/
theorem switch_none_of_components
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript scrutinee source sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = none)
    (hScoped : Functions.Scope.ExprScoped live scrutinee)
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      RegularStmtInvariantForward
        contract transcript lowerCtx lowerFinal localsFinal plan live
        frameBase mode mode sourceProgram sourceCtx
        (.switch scrutinee cases defaultBody)
        source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceAfterScrutinee targetFinal sourceCtx := by
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        hLowerScrutinee, hLowerCases, hLowerDefault, rfl⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        hCompileScrutinee, hCompileCases, hCompileDefault, rfl, rfl⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  have hLoweredSelect :
      Locals.Source.Switch.select
          value loweredCases loweredDefault =
        none :=
    AllocationLowering.lowerSwitch_select_none
      hLowerCases hLowerDefault hSelect
  have hTargetSelect :
      Structured.Switch.select value
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault) =
        none :=
    Locals.Switch.select_none_of_compile
      hCompileCases hCompileDefault hLoweredSelect
  obtain
      ⟨targetWithValue, targetAfterPop,
        hTargetScrutinee, hTargetPop, hTargetAfterPop,
        hPopInvariant⟩ :=
    AllocationObserverExpression.Expr.one_forward
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hInvariant hSafe hScoped hLowerScrutinee hCompileScrutinee
  subst targetAfterPop
  have hSource :=
    Functions.Source.Effectful.Stmt.run_switch_none_of_eval
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := 0)
      hSafe.evalOne_eq hSelect
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 1
        (.switch scrutineeCode
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault))
        target
        (Structured.EffectSemantics.Outcome.regular
          (AllocationObserverRelation.StateRel.popTarget
            target.source.evm.stack targetWithValue)) := by
    simpa [AllocationObserverRelation.StateRel.popTarget] using
      (Structured.EffectSemantics.Stmt.Eval.switch_none
        hTargetScrutinee hTargetPop hTargetSelect)
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts :=
            [(.switch scrutineeCode
              (Expressions.CaseList.toStructured compiledCases)
              (Expressions.Default.toStructured compiledDefault))] }
        target
        (Structured.EffectSemantics.Outcome.regular
          (AllocationObserverRelation.StateRel.popTarget
            target.source.evm.stack targetWithValue)) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCasesShape :=
    AllocationLowering.lowerCases_state_shape hLowerCases
  have hDefaultShape :=
    AllocationLowering.lowerDefault_state_shape hLowerDefault
  exact
    ⟨AllocationObserverRelation.StateRel.popTarget
        target.source.evm.stack targetWithValue,
      1, 2, hSource,
      by
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram 2
            { stmts :=
                [Structured.Stmt.switch
                  (Expressions.Expr.code
                    (results := 1) scrutineeCode).compile
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular
              (AllocationObserverRelation.StateRel.popTarget
                target.source.evm.stack targetWithValue))
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram 2
            { stmts :=
                [Structured.Stmt.switch scrutineeCode
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular
              (AllocationObserverRelation.StateRel.popTarget
                target.source.evm.stack targetWithValue))
        exact hTarget,
      hPopInvariant.transport_state
        (hDefaultShape.1.trans hCasesShape.1)
        (hDefaultShape.2.trans hCasesShape.2),
      SameFrame.refl mode⟩

end RegularStmtInvariantForward
end Sequence
end AllocationObserverStatement
end Functions
end EvmCompiler
