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
      FunctionsObserverStaticCost.stmt
          (.Switch scrutinee cases defaultBody) ≤
        FunctionsObserverStaticCost.program sourceProgram)
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
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
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
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions lower
            failure target ctx //
        StatementResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Switch scrutinee cases defaultBody))
          sourceFuel result } := by
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
  have hCostParts := hStmtCost
  simp only [FunctionsObserverStaticCost.stmt] at hCostParts
  have hScrutineeCost :
      FunctionsObserverStaticCost.expr scrutinee ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    omega
  rcases hFailureCase with hScrutineeFailure | hSelectedFailure
  · obtain ⟨scrutineeBounded⟩ :=
      hTerminalExpr (by omega) hScrutineeCost hOkParts.1
        hLowerScrutinee hRel hDomain hScope hScrutineeFailure hObservable
    let result :=
      FunctionsObserverTerminal.StatementResult.appendUnreachable
        scrutineeBounded.1
        [.switch lowerScrutinee lowerCases lowerDefault]
    refine ⟨⟨result, ?_⟩⟩
    have hAppend :=
      StatementResult.appendUnreachable_runBounded
        scrutineeBounded.1
        [.switch lowerScrutinee lowerCases lowerDefault]
    have hResultRequired :
        result.requiredFuel ≤ scrutineeBounded.1.requiredFuel := by
      simpa [StatementResult.RunBounded, result] using hAppend
    have hDynamic :=
      FunctionsObserverFuel.executionBudgetFor_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.expr scrutinee)
        (show sourcePrevious ≤ sourceFuel by omega)
    have hLocal :=
      FunctionsObserverFuel.executionBudgetFor_local_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        sourceFuel
        (show
          FunctionsObserverStaticCost.expr scrutinee ≤
            FunctionsObserverStaticCost.stmt
              (.Switch scrutinee cases defaultBody) by
          simp [FunctionsObserverStaticCost.stmt]
          omega)
    exact hResultRequired.trans
      (scrutineeBounded.2.trans (hDynamic.trans hLocal))
  · rcases hSelectedFailure with
      ⟨sourceAfterScrutinee, value,
        hScrutineeRun, hSelectedRun⟩
    have hScrutineeFresh : Fresh.Extends before afterScrutinee :=
      Expr.lower1Unchecked?_stateExtends hLowerScrutinee
    have hSelection :=
      Stmt.SwitchSelectionLowering.of_compilers
        (value := value) hLowerCases hLowerDefault
    obtain ⟨preparedBounded⟩ :=
      hRegularExpr (exprFuel := sourcePrevious)
        (before := before) (after := afterScrutinee)
        (layout := layout) (expr := scrutinee)
        (pre := preScrutinee) (lower := lowerScrutinee)
        (source := source) (source' := sourceAfterScrutinee)
        (target := target) (ctx := ctx) (value := value)
        (by omega) hScrutineeCost hOkParts.1 hLowerScrutinee hRel
        hDomain hScope hScrutineeRun
    let prepared := preparedBounded.1
    have hPreRun :=
      FunctionsObserverExpression.PreparedValue.run_requiredFuel
        prepared.prepared
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
        FunctionsObserverOutcome.ControlContextRel sourceControl layout
          canBreak canContinue canLeave
          prepared.prepared.finalCtx :=
      FunctionsObserverOutcome.ControlContextRel.transport hControl
        (fun _name hMem => hMem)
        prepared.prepared.control hPreparedLayoutScope
    cases hSelection with
    | none hSourceSelection _hTargetSelection _hSelectionFresh =>
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
          Stmt.toFunctionsListUncheckedFuel?_block_of_toBlock
            hSelectedLower
        have hSelectedListCost :=
          FunctionsObserverStaticCost.stmtList_selectSwitchCase_le_max
            value defaultBody cases
        rw [hSourceSelection] at hSelectedListCost
        have hSelectedBlockCost :
            FunctionsObserverStaticCost.stmt (.Block selectedBody) ≤
              FunctionsObserverStaticCost.program sourceProgram := by
          simp only [FunctionsObserverStaticCost.stmt]
          omega
        obtain ⟨bodyBounded⟩ :=
          block hTerminalList
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
            (by omega) hSelectedBlockCost hBlockOk hBlockNames hBlockLower
            prepared.relation
            (prepared.prepared.domain.mono hBeforeSelected)
            (prepared.prepared.scope.mono hBeforeSelected)
            hSelectedLayout hPreparedControl hSelectedRun hObservable
        obtain ⟨hBodyScoped, _hBodyCtx⟩ :=
          Functions.Source.Effectful.Block.runScoped_at_of_runOpen_singleton_block
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions
            (FunctionsObserverTerminal.StatementResult.run_requiredFuel
              bodyBounded.1)
        have hSwitchStmt :
            Functions.Source.Effectful.Stmt.run
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions prepared.prepared.finalCtx
                (bodyBounded.1.requiredFuel + 1)
                (.switch lowerScrutinee lowerCases lowerDefault)
                prepared.prepared.preTarget =
              .ok
                (Functions.Source.Effectful.Outcome.halt
                  bodyBounded.1.kind bodyBounded.1.finalTarget,
                  prepared.prepared.finalCtx) :=
          Functions.Source.Effectful.Stmt.run_switch_some_of_eval
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hEvalOne hTargetSelection hBodyScoped
        have hSwitchRun :=
          Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
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
          { kind := bodyBounded.1.kind
            finalTarget := bodyBounded.1.finalTarget
            finalCtx := prepared.prepared.finalCtx
            run := ⟨bodyBounded.1.requiredFuel + 3, hSwitchRun⟩
            relation := bodyBounded.1.relation }
        let result :=
          FunctionsObserverTerminal.StatementResult.prependRegularRun
            prepared.prepared.run switchResult
        refine ⟨⟨result, ?_⟩⟩
        have hCompose :=
          StatementResult.prependRegularRun_runBounded
            (FunctionsObserverExpression.PreparedValue.run_requiredFuel
              prepared.prepared)
            switchResult
        have hResultRequired :
            result.requiredFuel ≤
              prepared.prepared.requiredFuel +
                switchResult.requiredFuel := by
          simpa [StatementResult.RunBounded, result] using hCompose
        have hSwitchRequired :
            switchResult.requiredFuel ≤
              bodyBounded.1.requiredFuel + 3 :=
          FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
            switchResult hSwitchRun
        have hPreparedBound :
            prepared.prepared.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                (FunctionsObserverStaticCost.program sourceProgram)
                (FunctionsObserverStaticCost.expr scrutinee)
                sourcePrevious := by
          simpa [prepared,
            FunctionsObserverFuel.PreparedValue.ProgramBounded] using
            preparedBounded.2
        have hBodyBound :
            bodyBounded.1.requiredFuel ≤
              FunctionsObserverFuel.executionBudgetFor
                (FunctionsObserverStaticCost.program sourceProgram)
                (FunctionsObserverStaticCost.stmt (.Block selectedBody))
                sourcePrevious := by
          simpa [StatementResult.ProgramBounded,
            StatementResult.RunBounded] using bodyBounded.2
        have hChildren :=
          FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.expr scrutinee)
            (FunctionsObserverStaticCost.stmt (.Block selectedBody))
            hScrutineeCost hSelectedBlockCost
            (show sourcePrevious < sourceFuel by omega)
            (show sourcePrevious < sourceFuel by omega)
        have hParent :=
          FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmt
              (.Switch scrutinee cases defaultBody))
            sourceFuel
        dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
        omega

end RecursiveTerminalStmtForwardProgramBounded
end FunctionsObserverTerminalFuel
end Yul
end EvmCompiler
