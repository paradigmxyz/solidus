import EvmCompiler.Yul.CompilerExpressionDecomposition
import EvmCompiler.Yul.FunctionsObserverListBackward

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCompoundBackward

/-!
Backward adequacy for compound statements at the adjacent Yul-to-Functions
boundary.

Each theorem in this module inverts only the ordinary compiler output and
canonical Functions execution for its source construct. Recursive bodies are
handled through the shared statement-list backward interface.
-/

abbrev Trace := Assembly.ResourceTrace

private theorem blockBackwardOfBody
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat)
    (hList :
      FunctionsObserverListBackward.RecursiveOpenListBackwardBelow
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {bodyTargetFuel listCompilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {body : List AstStmt}
    {lowerBody : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx bodyFinalCtx : Functions.Source.Ctx}
    {targetOutcome bodyOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {canBreak canContinue canLeave : Bool}
    (hBodyFuel : bodyTargetFuel < bound)
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave body =
        true)
    (hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body))
    (hLowerBody :
      Stmt.List.toFunctionsUncheckedFuel? listCompilerFuel before body =
        some (lowerBody, after))
    (hOwner :
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source)
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
    (hBodyTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx bodyTargetFuel
          { stmts := lowerBody } target =
        .ok (bodyOutcome, bodyFinalCtx))
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel
          { stmts := [.block { stmts := lowerBody }] } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (FunctionsObserverStatementBackward.AlignedStmtBackward
        contract codeRel targetProgram.toFunctions
        (some sourceProgram.contract) (.Block body)
        [.block { stmts := lowerBody }] before after layout
        source target ctx targetOutcome targetFinalCtx
        (sourceControl := sourceControl)) := by
  obtain ⟨bodyBackward⟩ :=
    hList hBodyFuel hBodyOk hBodyNames hLowerBody hOwner
      hRel hDomain hScope hLayout hControl hBodyTarget
  let sourceFinal :=
    bodyBackward.sourceFinal.withSource
      (bodyBackward.sourceFinal.source.restrictStoreTo
        source.source.store)
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (bodyBackward.sourceFuel + 1) (.Block body)
          (some sourceProgram.contract) source =
        .ok sourceFinal := by
    simp only [Yul.Source.Effectful.exec]
    rw [bodyBackward.sourceRun]
    rfl
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_block
      bodyBackward.openResult
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel)
      hScope hLayout hControl (by rfl : sourceFinal =
        bodyBackward.sourceFinal.withSource
          (bodyBackward.sourceFinal.source.restrictStoreTo
            source.source.store))
  exact
    FunctionsObserverStatementBackward.AlignedStmtBackward.ofResult
      (bodyBackward.sourceFuel + 1) hSourceRun result hTarget

theorem blockBackward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat)
    (hList :
      FunctionsObserverListBackward.RecursiveOpenListBackwardBelow
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {body : List AstStmt}
    {lower : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {canBreak canContinue canLeave : Bool}
    (hTargetFuel : targetFuel < bound)
    (hOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave (.Block body) =
        true)
    (hNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.names (.Block body)))
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Block body) =
        some (lower, after))
    (hOwner :
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source)
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
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel
          { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (FunctionsObserverStatementBackward.AlignedStmtBackward
        contract codeRel targetProgram.toFunctions
        (some sourceProgram.contract) (.Block body) lower
        before after layout source target ctx targetOutcome targetFinalCtx
        (sourceControl := sourceControl)) := by
  obtain ⟨_compilerPrevious, lowerBlock, _hCompilerFuel,
      hLowerBlock, hLower⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_block_parts hLower
  subst lower
  obtain ⟨listCompilerFuel, lowerBody, _hBlockFuel,
      hLowerBody, hLowerBlock⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBlock
  subst lowerBlock
  have hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave body =
        true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) := by
    simpa [Stmt.names] using hNames
  by_cases hRegular : targetOutcome.mode = .regular
  · have hOutcomeEq :
        targetOutcome =
          Functions.Source.Effectful.Outcome.regular
            targetOutcome.state :=
      Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
    rw [hOutcomeEq] at hTarget ⊢
    obtain ⟨stmtFuel, hFuel, hTargetStmt⟩ :=
      Functions.Source.Effectful.Block.runOpen_singleton_regular_bounded_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTarget
    obtain ⟨hTargetScoped, _hStmtCtx⟩ :=
      Functions.Source.Effectful.Stmt.run_block_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetStmt
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hTargetScoped with
      hBodyRegular | hBodyNonregular
    · rcases hBodyRegular with
        ⟨bodyFinal, bodyFinalCtx, hBodyTarget, _hOuterOutcome⟩
      exact
        blockBackwardOfBody contract transcript codeRel sourceProgram
          targetProgram profile bound hList (by omega) hBodyOk hBodyNames
          hLowerBody hOwner hRel hDomain hScope hLayout hControl
          hBodyTarget hTarget
    · rcases hBodyNonregular with
        ⟨bodyOutcome, _bodyFinalCtx, _hBodyTarget,
          hBodyNonregular, hOuterOutcome⟩
      have hImpossible : bodyOutcome.mode = .regular := by
        rw [← hOuterOutcome]
        rfl
      exact False.elim (hBodyNonregular hImpossible)
  · obtain ⟨stmtFuel, _stmtCtx, hFuel, hTargetStmt, _hFinalCtx⟩ :=
      Functions.Source.Effectful.Block.runOpen_singleton_nonregular_bounded_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTarget hRegular
    obtain ⟨hTargetScoped, _hStmtCtx⟩ :=
      Functions.Source.Effectful.Stmt.run_block_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetStmt
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hTargetScoped with
      hBodyRegular | hBodyNonregular
    · rcases hBodyRegular with
        ⟨_bodyFinal, _bodyFinalCtx, _hBodyTarget, hOuterOutcome⟩
      have hImpossible : targetOutcome.mode = .regular := by
        rw [hOuterOutcome]
        rfl
      exact False.elim (hRegular hImpossible)
    · rcases hBodyNonregular with
        ⟨bodyOutcome, bodyFinalCtx, hBodyTarget,
          _hBodyNonregular, _hOuterOutcome⟩
      exact
        blockBackwardOfBody contract transcript codeRel sourceProgram
          targetProgram profile bound hList (by omega) hBodyOk hBodyNames
          hLowerBody hOwner hRel hDomain hScope hLayout hControl
          hBodyTarget hTarget

theorem ifBackwardNonterminal
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat)
    (hList :
      FunctionsObserverListBackward.RecursiveOpenListBackwardBelow
        contract transcript codeRel sourceProgram targetProgram
        profile bound)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {cond : AstExpr}
    {body : List AstStmt}
    {lower : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {canBreak canContinue canLeave : Bool}
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceProgram.contract contract transcript codeRel
        targetProgram.toFunctions (some sourceProgram.contract) layout bound)
    (hTargetFuel : targetFuel < bound)
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
    (hOwner :
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source)
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
    (hNotHalt :
      ∀ kind, targetOutcome.mode ≠ .halt kind)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel
          { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (FunctionsObserverStatementBackward.AlignedStmtBackward
        contract codeRel targetProgram.toFunctions
        (some sourceProgram.contract) (.If cond body) lower
        before after layout source target ctx targetOutcome targetFinalCtx
        (sourceControl := sourceControl)) := by
  obtain
      ⟨compilerPrevious, preCond, lowerCond, middle, lowerBody,
        _hCompilerFuel, hLowerCond, hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_if_parts hLower
  subst lower
  obtain
      ⟨listCompilerFuel, lowerBodyStmts, _hBlockFuel,
        hLowerBodyList, hLowerBodyEq⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  subst lowerBody
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
  have hBodyFresh : Fresh.Extends middle after :=
    Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerBodyList
  have hFresh : Fresh.Extends before after :=
    Fresh.Extends.trans hCondFresh hBodyFresh
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
  rcases
      Expr.lower1Unchecked?_append_run_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hLowerCond hTarget with
    hPreludeRegular | hPreludeHalt
  · rcases hPreludeRegular with
      ⟨preTarget, preCtx, suffixFuel,
        hPreRun, hSuffixRun, hSuffixFuel⟩
    obtain
        ⟨ifStmtFuel, ifStmtCtx, hSingletonFuel, hIfStmt,
          hFinalRegular, hFinalNonregular⟩ :=
      Functions.Source.Effectful.Block.runOpen_singleton_bounded_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hSuffixRun
    obtain ⟨bodyTargetFuel, hIfStmtFuel, hBranch⟩ :=
      Functions.Source.Effectful.Stmt.run_if_ok_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hIfStmt
    rcases hBranch with hFalse | hTrue
    · rcases hFalse with
        ⟨afterCond, hCond, hOutcome, hIfCtx⟩
      have hTargetRegular : targetOutcome.mode = .regular := by
        rw [hOutcome]
        rfl
      have hTargetFinalCtx : targetFinalCtx = preCtx :=
        (hFinalRegular hTargetRegular).trans hIfCtx
      subst targetFinalCtx
      obtain ⟨value, hEval, hZero⟩ :=
        Functions.Source.Effectful.Expr.evalCondition_false_ok_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hCond
      obtain ⟨conditionBackward⟩ :=
        hExpr hTargetFuel hOkParts.1 hLowerCond
          hRel hDomain hScope hPreRun hEval
      have hPreTargetEq :=
        conditionBackward.result.preTarget_eq
      have hEvalTargetEq :=
        conditionBackward.result.evalTarget_eq
      have hPreparedCtxEq :=
        conditionBackward.result.finalCtx_eq
      have hPreparedLayoutScope :
          FunctionsObserverOutcome.LayoutWithinScope layout
            conditionBackward.result.prepared.prepared.finalCtx := by
        obtain ⟨_preparedFuel, hPreparedRun⟩ :=
          conditionBackward.result.prepared.prepared.run
        have hExtends :=
          Functions.Source.Effectful.Block.runOpen_scopeExtends
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hPreparedRun
        exact fun name hMem =>
          hExtends name (hControl.scope name hMem)
      have hTargetRun :
          ∃ fuel,
            Functions.Source.Effectful.Block.runOpen
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions ctx fuel
                { stmts :=
                    preCond ++
                      [.if_ lowerCond { stmts := lowerBodyStmts }] }
                target =
              .ok
                (Functions.Source.Effectful.Outcome.regular
                  conditionBackward.result.prepared.prepared.evalTarget,
                  conditionBackward.result.prepared.prepared.finalCtx) := by
        refine ⟨targetFuel, ?_⟩
        simpa only [hOutcome, hEvalTargetEq, hPreparedCtxEq] using
          hTarget
      obtain ⟨result⟩ :=
        FunctionsObserverStatement.OpenResult.of_regular_parts
          (sourceControl := sourceControl)
          (stmt := .If cond body)
          (lower :=
            preCond ++
              [.if_ lowerCond { stmts := lowerBodyStmts }])
          (before := before) (after := after)
          (layout := layout) (finalLayout := layout)
          (sourceFinal := conditionBackward.result.sourceFinal)
          (target := target)
          (finalTarget :=
            conditionBackward.result.prepared.prepared.evalTarget)
          (ctx := ctx)
          (finalCtx :=
            conditionBackward.result.prepared.prepared.finalCtx)
          hTargetRun conditionBackward.result.prepared.relation
          (conditionBackward.result.prepared.prepared.domain.mono
            hBodyFresh)
          (conditionBackward.result.prepared.prepared.scope.mono
            hBodyFresh)
          conditionBackward.result.prepared.prepared.control
          hFresh (fun _name hMem => hMem)
          (hLayout.mono hFresh) hPreparedLayoutScope
          (by simp [SolcValidation.StmtOutVars])
      have hSourceRun :
          Yul.Source.Effectful.exec
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (conditionBackward.sourceFuel + 1)
              (.If cond body) (some sourceProgram.contract) source =
            .ok conditionBackward.result.sourceFinal :=
        Yul.Source.Effectful.exec_if_false_of_eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          conditionBackward.result.sourceRun hZero
      exact
        FunctionsObserverStatementBackward.AlignedStmtBackward.ofResult
          (conditionBackward.sourceFuel + 1) hSourceRun result hTarget
    · rcases hTrue with
        ⟨afterCond, bodyOutcome, hCond, hBodyScoped,
          hOutcome, hIfCtx⟩
      have hTargetFinalCtx : targetFinalCtx = preCtx := by
        by_cases hRegular : targetOutcome.mode = .regular
        · exact (hFinalRegular hRegular).trans hIfCtx
        · exact hFinalNonregular hRegular
      subst targetFinalCtx
      obtain ⟨value, hEval, hNonzero⟩ :=
        Functions.Source.Effectful.Expr.evalCondition_true_ok_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hCond
      obtain ⟨conditionBackward⟩ :=
        hExpr hTargetFuel hOkParts.1 hLowerCond
          hRel hDomain hScope hPreRun hEval
      have hPreTargetEq :=
        conditionBackward.result.preTarget_eq
      have hEvalTargetEq :=
        conditionBackward.result.evalTarget_eq
      have hPreparedCtxEq :=
        conditionBackward.result.finalCtx_eq
      have hBodyScopedPrepared :
          Functions.Source.Effectful.Block.runScoped
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              conditionBackward.result.prepared.prepared.finalCtx
              { stmts := lowerBodyStmts } bodyTargetFuel
              conditionBackward.result.prepared.prepared.evalTarget =
            .ok bodyOutcome := by
        simpa only [hEvalTargetEq, hPreparedCtxEq] using hBodyScoped
      have hPreparedLayoutScope :
          FunctionsObserverOutcome.LayoutWithinScope layout
            conditionBackward.result.prepared.prepared.finalCtx := by
        obtain ⟨_preparedFuel, hPreparedRun⟩ :=
          conditionBackward.result.prepared.prepared.run
        have hExtends :=
          Functions.Source.Effectful.Block.runOpen_scopeExtends
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hPreparedRun
        exact fun name hMem =>
          hExtends name (hControl.scope name hMem)
      have hPreparedControl :
          FunctionsObserverOutcome.ControlContextRel sourceControl layout
            canBreak canContinue canLeave
            conditionBackward.result.prepared.prepared.finalCtx :=
        FunctionsObserverOutcome.ControlContextRel.transport
          hControl (fun _name hMem => hMem)
          conditionBackward.result.prepared.prepared.control
          hPreparedLayoutScope
      have hOwnerAfterCond :
          Yul.Source.Effectful.OwnerAvailable
            (ObserverSemantics.SourceReplay.stateModel transcript)
            conditionBackward.result.sourceFinal :=
        Yul.Source.Effectful.eval_preserves_owner
          (ObserverSafety.SafeSemantics.stateModel_lawful transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_preservesOwner
            contract transcript)
          hOwner conditionBackward.result.sourceRun
      obtain ⟨blockTargetFuel, hBlockTarget⟩ :
          ∃ fuel,
            Functions.Source.Effectful.Block.runOpen
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions
                conditionBackward.result.prepared.prepared.finalCtx fuel
                { stmts := [.block { stmts := lowerBodyStmts }] }
                conditionBackward.result.prepared.prepared.evalTarget =
              .ok
                (bodyOutcome,
                  conditionBackward.result.prepared.prepared.finalCtx) := by
        have hBlockStmt :
            Functions.Source.Effectful.Stmt.run
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions
                conditionBackward.result.prepared.prepared.finalCtx
                bodyTargetFuel
                (.block { stmts := lowerBodyStmts })
                conditionBackward.result.prepared.prepared.evalTarget =
              .ok
                (bodyOutcome,
                  conditionBackward.result.prepared.prepared.finalCtx) := by
          unfold Functions.Source.Effectful.Stmt.run
          rw [hBodyScopedPrepared]
          rfl
        exact
          Functions.Source.Effectful.Block.runOpen_singleton_of_run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hBlockStmt
      have hClosedBody :
          Nonempty
            (FunctionsObserverStatementBackward.AlignedStmtBackward
              contract codeRel targetProgram.toFunctions
              (some sourceProgram.contract) (.Block body)
              [.block { stmts := lowerBodyStmts }]
              middle after layout
              conditionBackward.result.sourceFinal
              conditionBackward.result.prepared.prepared.evalTarget
              conditionBackward.result.prepared.prepared.finalCtx
              bodyOutcome
              conditionBackward.result.prepared.prepared.finalCtx
              (sourceControl := sourceControl)) := by
        rcases
            Functions.Source.Effectful.Block.runScoped_cases
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hBodyScopedPrepared with
          hBodyRegular | hBodyNonregular
        · rcases hBodyRegular with
            ⟨_bodyFinal, bodyFinalCtx,
              hBodyTarget, _hScopedOutcome⟩
          exact
            blockBackwardOfBody contract transcript codeRel sourceProgram
              targetProgram profile bound hList (by omega)
              hOkParts.2 hBodyNamesMiddle hLowerBodyList hOwnerAfterCond
              conditionBackward.result.prepared.relation
              conditionBackward.result.prepared.prepared.domain
              conditionBackward.result.prepared.prepared.scope
              hLayoutMiddle hPreparedControl
              hBodyTarget hBlockTarget
        · rcases hBodyNonregular with
            ⟨_openOutcome, bodyFinalCtx,
              hBodyTarget, _hBodyMode, _hScopedOutcome⟩
          exact
            blockBackwardOfBody contract transcript codeRel sourceProgram
              targetProgram profile bound hList (by omega)
              hOkParts.2 hBodyNamesMiddle hLowerBodyList hOwnerAfterCond
              conditionBackward.result.prepared.relation
              conditionBackward.result.prepared.prepared.domain
              conditionBackward.result.prepared.prepared.scope
              hLayoutMiddle hPreparedControl
              hBodyTarget hBlockTarget
      obtain ⟨closedBody⟩ := hClosedBody
      let commonFuel :=
        max conditionBackward.sourceFuel closedBody.sourceFuel
      have hCondSource :
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              commonFuel cond (some sourceProgram.contract) source =
            .ok (conditionBackward.result.sourceFinal, value) :=
        Yul.Source.Effectful.eval_mono
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
            contract transcript)
          (Nat.le_max_left _ _) conditionBackward.result.sourceRun
      have hBodySource :
          Yul.Source.Effectful.exec
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              commonFuel (.Block body) (some sourceProgram.contract)
              conditionBackward.result.sourceFinal =
            .ok closedBody.sourceFinal :=
        Yul.Source.Effectful.exec_mono
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
            contract transcript)
          (Nat.le_max_right _ _) closedBody.sourceRun
      have hSourceRun :
          Yul.Source.Effectful.exec
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (commonFuel + 1) (.If cond body)
              (some sourceProgram.contract) source =
            .ok closedBody.sourceFinal :=
        Yul.Source.Effectful.exec_if_true_of_eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hCondSource hNonzero hBodySource
      have hTargetRun :
          ∃ fuel,
            Functions.Source.Effectful.Block.runOpen
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions ctx fuel
                { stmts :=
                    preCond ++
                      [.if_ lowerCond { stmts := lowerBodyStmts }] }
                target =
              .ok
                (closedBody.result.openResult.outcome,
                  closedBody.result.openResult.finalCtx) := by
        refine ⟨targetFuel, ?_⟩
        simpa only [closedBody.outcome_eq, closedBody.finalCtx_eq,
          hOutcome, hPreparedCtxEq] using hTarget
      obtain ⟨result⟩ :=
        FunctionsObserverStatement.OpenResult.of_if_true_prepared
          hCondFresh conditionBackward.result.prepared
          closedBody.result hTargetRun
      exact
        FunctionsObserverStatementBackward.AlignedStmtBackward.ofResult
          (commonFuel + 1) hSourceRun result hTarget
  · rcases hPreludeHalt with
      ⟨kind, preludeOutcome, _preludeCtx, _hPreludeRun,
        hPreludeMode, hOutcome, _hFinalCtx⟩
    apply False.elim
    apply hNotHalt kind
    rw [hOutcome, hPreludeMode]

end FunctionsObserverCompoundBackward
end Yul
end EvmCompiler
