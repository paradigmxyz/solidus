import EvmCompiler.Yul.EffectSemanticsFuel
import EvmCompiler.Yul.EffectSemanticsOwnerPreservation
import EvmCompiler.Yul.FunctionsObserverStatementBackward

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverListBackward

/-!
Backward adequacy for Yul statement lists at the adjacent Yul-to-Functions
pass.

The proof consumes the ordinary list compiler, the shared statement backward
interface, and target-semantics append inversion. It does not interpret
compound statements or reimplement either compiler.
-/

abbrev Trace := Assembly.ResourceTrace

structure AlignedListBackward
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (stmts : List AstStmt)
    (lower : List Functions.Stmt)
    (initial final : Fresh.State)
    (entryLayout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetFinalCtx : Functions.Source.Ctx)
    (canBreak canContinue canLeave : Bool)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes} where
  sourceFuel : Nat
  sourceFinal : ObserverSemantics.SourceReplay.State transcript
  sourceRun :
    Yul.Source.Effectful.execSeq
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        sourceFuel stmts codeOverride source =
      .ok sourceFinal
  openResult :
    FunctionsObserverOutcome.ScopedOpenResult
      contract codeRel program lower initial final entryLayout
      sourceFinal target ctx (sourceControl := sourceControl)
  outcome_eq : openResult.outcome = targetOutcome
  finalCtx_eq : openResult.finalCtx = targetFinalCtx
  regularLayout :
    openResult.outcome.mode = .regular →
      openResult.finalLayout =
        SolcValidation.StmtsOutVars entryLayout stmts
  regularControl :
    openResult.outcome.mode = .regular →
      FunctionsObserverOutcome.ControlContextRel sourceControl
        openResult.finalLayout canBreak canContinue canLeave
        openResult.finalCtx

def RecursiveOpenListBackwardBelow
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {targetFuel compilerFuel : Nat}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {stmts : List AstStmt}
    {lower : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {canBreak canContinue canLeave : Bool},
    targetFuel < bound →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave stmts =
        true →
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names stmts) →
      Stmt.List.toFunctionsUncheckedFuel? compilerFuel before stmts =
        some (lower, after) →
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      StateRelation.Vars.NamesWithin before.used layout →
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx) →
      Nonempty
        (AlignedListBackward contract codeRel targetProgram.toFunctions
          (some sourceProgram.contract) stmts lower before after layout
          source target ctx targetOutcome targetFinalCtx
          canBreak canContinue canLeave
          (sourceControl := sourceControl))

theorem ofStmt
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat)
    (hStmt :
      FunctionsObserverStatementBackward.RecursiveOpenStmtBackwardBelow
        contract transcript codeRel sourceProgram targetProgram
        profile bound) :
    RecursiveOpenListBackwardBelow contract transcript codeRel
      sourceProgram targetProgram profile bound := by
  intro targetFuel compilerFuel sourceControl before after layout stmts
    lower source target ctx targetFinalCtx targetOutcome
    canBreak canContinue canLeave hTargetFuel hOk hNames hLower hOwner
    hRel hDomain hScope hLayout hControl hTarget
  induction stmts generalizing targetFuel compilerFuel before after layout
      lower source target ctx targetFinalCtx targetOutcome with
  | nil =>
      obtain
          ⟨_compilerPrevious, _hCompilerFuel, hLowerNil, hAfter⟩ :=
        Stmt.List.toFunctionsUncheckedFuel?_nil_parts hLower
      subst lower
      subst after
      obtain ⟨hOutcome, hFinalCtx⟩ :=
        Functions.Source.Effectful.Block.runOpen_nil_ok
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hTarget
      let openResult :=
        FunctionsObserverOutcome.ScopedOpenResult.empty
          (contract := contract) (program := targetProgram.toFunctions)
          (sourceControl := sourceControl)
          hRel hDomain hScope hLayout hControl.scope
      have hSource :
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              1 [] (some sourceProgram.contract) source =
            .ok source := by
        simp [Yul.Source.Effectful.execSeq]
      exact
        ⟨{ sourceFuel := 1
           sourceFinal := source
           sourceRun := hSource
           openResult := openResult
           outcome_eq := hOutcome.symm
           finalCtx_eq := hFinalCtx.symm
           regularLayout := by
             intro _hRegular
             rfl
           regularControl := by
             intro _hRegular
             exact hControl }⟩
  | cons head tail ih =>
      obtain
          ⟨compilerPrevious, lowerHead, middle, lowerTail,
            _hCompilerFuel, hLowerHead, hLowerTail, hLowerAppend⟩ :=
        Stmt.List.toFunctionsUncheckedFuel?_cons_parts hLower
      subst lower
      obtain ⟨hHeadOk, hTailOk⟩ :=
        SolcValidation.stmtsOk_cons_parts hOk
      have hHeadNames :
          StateRelation.Vars.NamesWithin before.used
            (Stmt.names head) := by
        intro name hMem
        exact hNames name (List.mem_append_left _ hMem)
      rcases
          Functions.Source.Effectful.Block.runOpen_append_bounded_cases
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hTarget with
        hHeadRegular | hHeadNonregular
      · rcases hHeadRegular with
          ⟨targetMiddle, middleCtx, tailFuel,
            hTargetHead, hTargetTail, hTailFuel⟩
        obtain ⟨headBackward⟩ :=
          hStmt hTargetFuel hHeadOk hHeadNames hLowerHead hOwner
            hRel hDomain hScope hLayout hControl hTargetHead
        have hHeadRegular :
            headBackward.result.openResult.outcome.mode = .regular := by
          rw [headBackward.outcome_eq]
          rfl
        obtain ⟨sourceShared, sourceVars, hSourceAfterHead⟩ :=
          FunctionsObserverOutcome.ModeRel.target_regular_source_ok
            headBackward.result.openResult.relation.mode hHeadRegular
        have hHeadExact :
            StateRelation.Replay.ScopedExactRel codeRel
              headBackward.result.openResult.finalLayout
              headBackward.sourceFinal targetMiddle := by
          have hRevived :
              headBackward.sourceFinal.withSource
                  headBackward.sourceFinal.source.reviveJump =
                headBackward.sourceFinal := by
            rw [hSourceAfterHead]
            change
              headBackward.sourceFinal.withSource
                  (.Ok sourceShared sourceVars) =
                headBackward.sourceFinal
            rw [← hSourceAfterHead]
            exact
              Simulation.ResourceReplay.State.withSource_self
                headBackward.sourceFinal
          have hExact :=
            headBackward.result.openResult.relation.exact hHeadRegular
          rw [hRevived, headBackward.outcome_eq] at hExact
          exact hExact
        have hHeadLayout :=
          headBackward.result.regularLayout hHeadRegular
        have hTailOk' :
            SolcValidation.StmtsOk? profile sourceProgram.contract
                ((Contract.functionEntries
                  sourceProgram.contract).map Prod.fst)
                headBackward.result.openResult.finalLayout
                canBreak canContinue canLeave tail =
              true := by
          rw [hHeadLayout]
          exact hTailOk
        have hTailNames :
            StateRelation.Vars.NamesWithin middle.used
              (Stmt.List.names tail) := by
          intro name hMem
          exact
            headBackward.result.openResult.freshExtends name
              (hNames name (List.mem_append_right _ hMem))
        have hTailOwner :
            Yul.Source.Effectful.OwnerAvailable
              (ObserverSemantics.SourceReplay.stateModel transcript)
              headBackward.sourceFinal :=
          Yul.Source.Effectful.exec_preserves_owner
            (ObserverSafety.SafeSemantics.stateModel_lawful transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics_preservesOwner
              contract transcript)
            hOwner headBackward.sourceRun
        obtain ⟨tailBackward⟩ :=
          ih (targetFuel := tailFuel)
            (compilerFuel := compilerPrevious)
            (before := middle) (after := after)
            (layout := headBackward.result.openResult.finalLayout)
            (lower := lowerTail)
            (source := headBackward.sourceFinal)
            (target := targetMiddle) (ctx := middleCtx)
            (targetFinalCtx := targetFinalCtx)
            (targetOutcome := targetOutcome)
            (by omega) hTailOk' hTailNames hLowerTail hTailOwner
            hHeadExact
            (by
              simpa only [headBackward.outcome_eq] using
                headBackward.result.openResult.domain)
            (by
              simpa only [headBackward.finalCtx_eq] using
                headBackward.result.openResult.scope)
            headBackward.result.openResult.layoutWithin
            (headBackward.regularControl hControl (by rfl))
            hTargetTail
        have hHeadStateEq :
            headBackward.result.openResult.outcome.state =
              targetMiddle :=
          congrArg
            (fun outcome :
              Functions.Source.Effectful.Outcome
                (Functions.ObserverSemantics.State transcript) =>
              outcome.state)
            headBackward.outcome_eq
        let commonFuel :=
          max headBackward.sourceFuel tailBackward.sourceFuel
        have hHeadSource :
            Yul.Source.Effectful.exec
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                commonFuel head (some sourceProgram.contract) source =
              .ok headBackward.sourceFinal :=
          Yul.Source.Effectful.exec_mono
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
              contract transcript)
            (Nat.le_max_left _ _) headBackward.sourceRun
        have hTailSource :
            Yul.Source.Effectful.execSeq
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                commonFuel tail (some sourceProgram.contract)
                headBackward.sourceFinal =
              .ok tailBackward.sourceFinal :=
          Yul.Source.Effectful.execSeq_mono
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
              contract transcript)
            (Nat.le_max_right _ _) tailBackward.sourceRun
        have hSourceRun :
            Yul.Source.Effectful.execSeq
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                (commonFuel + 1) (head :: tail)
                (some sourceProgram.contract) source =
              .ok tailBackward.sourceFinal :=
          Yul.Source.Effectful.execSeq_cons_of_regular
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hHeadSource hSourceAfterHead hTailSource
        let openResult :=
          FunctionsObserverOutcome.ScopedOpenResult.appendRegularAligned
            headBackward.result.openResult hHeadRegular
            hHeadStateEq headBackward.finalCtx_eq
            tailBackward.openResult
        have hOpenParts :=
          FunctionsObserverOutcome.ScopedOpenResult.appendRegularAligned_parts
            headBackward.result.openResult hHeadRegular
            hHeadStateEq headBackward.finalCtx_eq
            tailBackward.openResult
        exact
          ⟨{ sourceFuel := commonFuel + 1
             sourceFinal := tailBackward.sourceFinal
             sourceRun := hSourceRun
             openResult := openResult
             outcome_eq :=
               hOpenParts.2.1.trans tailBackward.outcome_eq
             finalCtx_eq :=
               hOpenParts.2.2.trans tailBackward.finalCtx_eq
             regularLayout := by
               intro hResultRegular
               rw [hOpenParts.2.1] at hResultRegular
               rw [hOpenParts.1]
               rw [tailBackward.regularLayout hResultRegular]
               simpa [SolcValidation.StmtsOutVars] using
                 congrArg
                   (fun headLayout =>
                     SolcValidation.StmtsOutVars headLayout tail)
                   hHeadLayout
             regularControl := by
               intro hResultRegular
               rw [hOpenParts.2.1] at hResultRegular
               rw [hOpenParts.1, hOpenParts.2.2]
               exact tailBackward.regularControl hResultRegular }⟩
      · rcases hHeadNonregular with
          ⟨leftOutcome, leftCtx, hTargetHead, hLeftNonregular,
            hTargetOutcome, hTargetFinalCtx⟩
        obtain ⟨headBackward⟩ :=
          hStmt hTargetFuel hHeadOk hHeadNames hLowerHead hOwner
            hRel hDomain hScope hLayout hControl hTargetHead
        have hHeadNonregular :
            headBackward.result.openResult.outcome.mode ≠ .regular := by
          rw [headBackward.outcome_eq]
          exact hLeftNonregular
        obtain ⟨jump, hSourceAfterHead⟩ :=
          FunctionsObserverOutcome.ModeRel.target_nonregular_source_checkpoint
            headBackward.result.openResult.relation.mode hHeadNonregular
        have hTailFresh : Fresh.Extends middle after :=
          Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerTail
        let openResult :=
          FunctionsObserverOutcome.ScopedOpenResult.appendNonregular
            (rightLower := lowerTail)
            headBackward.result.openResult hHeadNonregular hTailFresh
        have hSourceRun :
            Yul.Source.Effectful.execSeq
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                (headBackward.sourceFuel + 1) (head :: tail)
                (some sourceProgram.contract) source =
              .ok headBackward.sourceFinal :=
          Yul.Source.Effectful.execSeq_cons_of_checkpoint
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            headBackward.sourceRun hSourceAfterHead
        exact
          ⟨{ sourceFuel := headBackward.sourceFuel + 1
             sourceFinal := headBackward.sourceFinal
             sourceRun := hSourceRun
             openResult := openResult
             outcome_eq := by
               change
                 headBackward.result.openResult.outcome = targetOutcome
               rw [headBackward.outcome_eq]
               exact hTargetOutcome.symm
             finalCtx_eq := by
               change
                 headBackward.result.openResult.finalCtx = targetFinalCtx
               rw [headBackward.finalCtx_eq]
               exact hTargetFinalCtx.symm
             regularLayout := by
               intro hRegular
               exact (hHeadNonregular hRegular).elim
             regularControl := by
               intro hRegular
               exact (hHeadNonregular hRegular).elim }⟩

end FunctionsObserverListBackward
end Yul
end EvmCompiler
