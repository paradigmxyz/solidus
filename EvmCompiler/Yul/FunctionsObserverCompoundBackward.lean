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

end FunctionsObserverCompoundBackward
end Yul
end EvmCompiler
