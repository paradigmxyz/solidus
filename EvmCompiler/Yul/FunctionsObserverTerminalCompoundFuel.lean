import EvmCompiler.Yul.FunctionsObserverTerminalFuel

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTerminalFuel
namespace RecursiveTerminalStmtForwardProgramBounded

/-!
Program-indexed terminal composition for compound Yul statements.

The shared terminal result and fuel interfaces remain in
`FunctionsObserverTerminalFuel`; this module owns the adjacent structured
control proofs built from those interfaces.
-/

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
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hStmtCost :
      FunctionsObserverStaticCost.stmt (.If cond body) ≤
        FunctionsObserverStaticCost.program sourceProgram)
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
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
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
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions lower
            failure target ctx //
        StatementResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.If cond body))
          sourceFuel result } := by
  obtain
      ⟨compilerPrevious, preCond, lowerCond, middle, lowerBody,
        _hCompilerFuel, hLowerCond, hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_if_parts hLower
  subst lower
  obtain ⟨listCompilerFuel, lowerStmts, _hBlockFuel,
      hLowerList, hLowerBodyEq⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  subst lowerBody
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
  have hCondCost :
      FunctionsObserverStaticCost.expr cond ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.expr cond ≤
          FunctionsObserverStaticCost.stmt (.If cond body) := by
      simp [FunctionsObserverStaticCost.stmt]
      omega
    exact hLocal.trans hStmtCost
  have hBodyCost :
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    have hLocal :
        FunctionsObserverStaticCost.stmtList body ≤
          FunctionsObserverStaticCost.stmt (.If cond body) := by
      simp [FunctionsObserverStaticCost.stmt]
      omega
    exact hLocal.trans hStmtCost
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
  · obtain ⟨condBounded⟩ :=
      hTerminalExpr (by omega) hCondCost hOkParts.1 hLowerCond hRel
        hDomain hScope hCondFailure hObservable
    let result :=
      FunctionsObserverTerminal.StatementResult.appendUnreachable
        condBounded.1 [.if_ lowerCond { stmts := lowerStmts }]
    refine ⟨⟨result, ?_⟩⟩
    have hAppend :=
      StatementResult.appendUnreachable_runBounded
        condBounded.1 [.if_ lowerCond { stmts := lowerStmts }]
    have hResultRequired :
        result.requiredFuel ≤ condBounded.1.requiredFuel := by
      simpa [StatementResult.RunBounded, result] using hAppend
    have hDynamic :=
      FunctionsObserverFuel.executionBudgetFor_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.expr cond)
        (show sourcePrevious ≤ sourceFuel by omega)
    have hLocal :=
      FunctionsObserverFuel.executionBudgetFor_local_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        sourceFuel
        (show
          FunctionsObserverStaticCost.expr cond ≤
            FunctionsObserverStaticCost.stmt (.If cond body) by
          simp [FunctionsObserverStaticCost.stmt]
          omega)
    exact hResultRequired.trans
      (condBounded.2.trans (hDynamic.trans hLocal))
  · rcases hBodyFailure with
      ⟨sourceAfterCond, condValue,
        hCondRun, hNonzero, hBodyRun⟩
    obtain ⟨preparedBounded⟩ :=
      hRegularExpr (exprFuel := sourcePrevious)
        (before := before) (after := middle)
        (layout := layout) (expr := cond)
        (pre := preCond) (lower := lowerCond)
        (source := source) (source' := sourceAfterCond)
        (target := target) (ctx := ctx) (value := condValue)
        (by omega) hCondCost hOkParts.1 hLowerCond hRel hDomain hScope
        hCondRun
    let prepared := preparedBounded.1
    have hPreparedLayoutScope :
        FunctionsObserverOutcome.LayoutWithinScope
          layout prepared.prepared.finalCtx := by
      have hExtends :=
        Functions.Source.Effectful.Block.runOpen_scopeExtends
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (FunctionsObserverExpression.PreparedValue.run_requiredFuel
            prepared.prepared)
      exact fun name hMem =>
        hExtends name (hControl.scope name hMem)
    have hPreparedControl :
        FunctionsObserverOutcome.ControlContextRel sourceControl layout
          canBreak canContinue canLeave
          prepared.prepared.finalCtx :=
      FunctionsObserverOutcome.ControlContextRel.transport hControl
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
    rcases
        Yul.Source.Effectful.exec_block_error_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hBodyRun with hOuter | hBodyListFailure
    · rcases hOuter with ⟨rfl, hFailure⟩
      rw [← hFailure] at hObservable
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
    · rcases hBodyListFailure with
        ⟨bodyFuel, hBodyFuel, hBodyListRun⟩
      obtain ⟨bodyBounded⟩ :=
        hTerminalList
          (sourceFuel := bodyFuel)
          (compilerFuel := listCompilerFuel)
          (sourceControl := sourceControl)
          (before := middle) (after := after)
          (layout := layout) (stmts := body)
          (lower := lowerStmts)
          (source := sourceAfterCond) (failure := failure)
          (target := prepared.prepared.evalTarget)
          (ctx := prepared.prepared.finalCtx)
          (canBreak := canBreak) (canContinue := canContinue)
          (canLeave := canLeave)
          (by omega) hBodyCost hOkParts.2 hBodyNamesMiddle hLowerList
          prepared.relation prepared.prepared.domain
          prepared.prepared.scope hLayoutMiddle hPreparedControl
          hBodyListRun hObservable
      have hBodyScoped :
          Functions.Source.Effectful.Block.runScoped
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx
              { stmts := lowerStmts } bodyBounded.1.requiredFuel
              prepared.prepared.evalTarget =
            .ok
              (Functions.Source.Effectful.Outcome.halt
                bodyBounded.1.kind bodyBounded.1.finalTarget) :=
        Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (FunctionsObserverTerminal.StatementResult.run_requiredFuel
            bodyBounded.1)
          (by simp)
      have hIfStmt :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx
              (bodyBounded.1.requiredFuel + 1)
              (.if_ lowerCond { stmts := lowerStmts })
              prepared.prepared.preTarget =
            .ok
              (Functions.Source.Effectful.Outcome.halt
                bodyBounded.1.kind bodyBounded.1.finalTarget,
                prepared.prepared.finalCtx) :=
        Functions.Source.Effectful.Stmt.run_if_true_of_eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hCondTrue hBodyScoped
      have hIfRun :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx
              (bodyBounded.1.requiredFuel + 3)
              { stmts := [.if_ lowerCond { stmts := lowerStmts }] }
              prepared.prepared.preTarget =
            .ok
              (Functions.Source.Effectful.Outcome.halt
                bodyBounded.1.kind bodyBounded.1.finalTarget,
                prepared.prepared.finalCtx) := by
        simpa [Nat.add_assoc] using
          Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hIfStmt
      let ifResult :
          FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions
            [.if_ lowerCond { stmts := lowerStmts }] failure
            prepared.prepared.preTarget prepared.prepared.finalCtx :=
        { kind := bodyBounded.1.kind
          finalTarget := bodyBounded.1.finalTarget
          finalCtx := prepared.prepared.finalCtx
          run := ⟨bodyBounded.1.requiredFuel + 3, hIfRun⟩
          relation := bodyBounded.1.relation }
      let result :=
        FunctionsObserverTerminal.StatementResult.prependRegularRun
          prepared.prepared.run ifResult
      refine ⟨⟨result, ?_⟩⟩
      have hCompose :=
        StatementResult.prependRegularRun_runBounded
          (FunctionsObserverExpression.PreparedValue.run_requiredFuel
            prepared.prepared)
          ifResult
      have hResultRequired :
          result.requiredFuel ≤
            prepared.prepared.requiredFuel + ifResult.requiredFuel := by
        simpa [StatementResult.RunBounded, result] using hCompose
      have hIfRequired :
          ifResult.requiredFuel ≤ bodyBounded.1.requiredFuel + 3 :=
        FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
          ifResult hIfRun
      have hPreparedBound :
          prepared.prepared.requiredFuel ≤
            FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.expr cond)
              sourcePrevious := by
        simpa [prepared,
          FunctionsObserverFuel.PreparedValue.ProgramBounded] using
          preparedBounded.2
      have hBodyBound :
          bodyBounded.1.requiredFuel ≤
            FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmtList body)
              bodyFuel := by
        simpa [StatementResult.ProgramBounded,
          StatementResult.RunBounded] using bodyBounded.2
      have hChildren :=
        FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.expr cond)
          (FunctionsObserverStaticCost.stmtList body)
          hCondCost hBodyCost
          (show sourcePrevious < sourceFuel by omega)
          (show bodyFuel < sourceFuel by omega)
      have hParent :=
        FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.If cond body))
          sourceFuel
      dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
      omega

end RecursiveTerminalStmtForwardProgramBounded
end FunctionsObserverTerminalFuel
end Yul
end EvmCompiler
