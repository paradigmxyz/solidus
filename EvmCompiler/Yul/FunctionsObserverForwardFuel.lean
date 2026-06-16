import EvmCompiler.Yul.FunctionsObserverCallFuel
import EvmCompiler.Yul.FunctionsObserverForward

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverForwardFuel

abbrev Trace := Assembly.ResourceTrace

open FunctionsObserverForward

def RecursiveOpenStmtForwardBounded
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
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool},
    sourceFuel < bound →
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
        .ok sourceFinal →
      Nonempty
        { result :
            ScopedStmtResult contract codeRel targetProgram.toFunctions
              stmt lower before after layout sourceFinal target ctx
              canBreak canContinue canLeave
              (sourceControl := sourceControl) //
          FunctionsObserverFuel.ScopedOpenResult.Bounded
            sourceFuel result.openResult }

def RecursiveOpenListForwardBounded
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
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool},
    sourceFuel < bound →
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
        .ok sourceFinal →
      Nonempty
        { result :
            ScopedListResult contract codeRel targetProgram.toFunctions
              stmts lower before after layout sourceFinal target ctx
              canBreak canContinue canLeave
              (sourceControl := sourceControl) //
          FunctionsObserverFuel.ScopedOpenResult.Bounded
            sourceFuel result.openResult }

namespace RecursiveOpenListForwardBounded

theorem ofStmt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hStmt :
      RecursiveOpenStmtForwardBounded contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveOpenListForwardBounded contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel sourceControl before after layout stmts lower
        source sourceFinal target ctx canBreak canContinue canLeave
        hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
      cases stmts with
      | nil =>
          obtain ⟨_compilerPrevious, _hCompilerFuel,
              hLowerNil, hAfter⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_nil_parts hLower
          obtain ⟨_sourcePrevious, _hSourceFuel, hSourceFinal⟩ :=
            Yul.Source.Effectful.execSeq_nil_ok_parts
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hRun
          subst lower
          subst after
          subst sourceFinal
          let openResult :=
            FunctionsObserverOutcome.ScopedOpenResult.empty
              (contract := contract) (program := targetProgram.toFunctions)
              (sourceControl := sourceControl)
              hRel hDomain hScope hLayout hControl.scope
          let result :
              ScopedListResult contract codeRel targetProgram.toFunctions
                [] [] before before layout source target ctx
                canBreak canContinue canLeave
                (sourceControl := sourceControl) :=
            { openResult := openResult
              regularLayout := by
                intro _hRegular
                rfl
              regularControl := by
                intro _hRegular
                exact hControl }
          refine ⟨⟨result, ?_⟩⟩
          exact
            FunctionsObserverFuel.ScopedOpenResult.empty_bounded
              sourceFuel hRel hDomain hScope hLayout hControl.scope
      | cons head tail =>
          obtain
              ⟨compilerPrevious, lowerHead, middle, lowerTail,
                _hCompilerFuel, hLowerHead, hLowerTail, hLowerAppend⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_cons_parts hLower
          subst lower
          obtain
              ⟨sourcePrevious, sourceAfterHead,
                hSourceFuel, hHeadRun, hTailRun⟩ :=
            Yul.Source.Effectful.execSeq_cons_ok_parts
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hRun
          have hPreviousFuel : sourcePrevious < sourceFuel := by
            omega
          have hPreviousBound : sourcePrevious < bound := by
            omega
          obtain ⟨hHeadOk, hTailOk⟩ :=
            SolcValidation.stmtsOk_cons_parts hOk
          have hHeadNames :
              StateRelation.Vars.NamesWithin before.used
                (Stmt.names head) := by
            intro name hMem
            exact hNames name (List.mem_append_left _ hMem)
          obtain ⟨headBounded⟩ :=
            hStmt hPreviousBound hHeadOk hHeadNames hLowerHead
              hRel hDomain hScope hLayout hControl hHeadRun
          let headResult := headBounded.1
          by_cases hRegular :
              headResult.openResult.outcome.mode = .regular
          · obtain ⟨sourceShared, sourceVars, hSourceAfterHead⟩ :=
              FunctionsObserverOutcome.ModeRel.target_regular_source_ok
                headResult.openResult.relation.mode hRegular
            have hTailRun' :
                Yul.Source.Effectful.execSeq
                    (ObserverSemantics.SourceReplay.stateModel transcript)
                    (ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    sourcePrevious tail (some sourceProgram.contract)
                    sourceAfterHead =
                  .ok sourceFinal := by
              simpa [ObserverSemantics.SourceReplay.stateModel,
                hSourceAfterHead] using hTailRun
            have hHeadRel :
                StateRelation.Replay.ScopedExactRel codeRel
                  headResult.openResult.finalLayout sourceAfterHead
                  headResult.openResult.outcome.state := by
              have hRevived :
                  sourceAfterHead.withSource
                      sourceAfterHead.source.reviveJump =
                    sourceAfterHead := by
                rw [hSourceAfterHead]
                change
                  sourceAfterHead.withSource
                      (.Ok sourceShared sourceVars) =
                    sourceAfterHead
                rw [← hSourceAfterHead]
                exact
                  Simulation.ResourceReplay.State.withSource_self
                    sourceAfterHead
              have hExact :=
                headResult.openResult.relation.exact hRegular
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
              headResult.regularLayout hRegular
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
              ih sourcePrevious (by omega)
                (compilerFuel := compilerPrevious)
                (before := middle) (after := after)
                (layout := headResult.openResult.finalLayout)
                (stmts := tail) (lower := lowerTail)
                (source := sourceAfterHead) (sourceFinal := sourceFinal)
                (target := headResult.openResult.outcome.state)
                (ctx := headResult.openResult.finalCtx)
                (canBreak := canBreak)
                (canContinue := canContinue) (canLeave := canLeave)
                (by omega) hTailOk' hTailNames hLowerTail hHeadRel
                headResult.openResult.domain
                headResult.openResult.scope
                headResult.openResult.layoutWithin
                (headResult.regularControl hRegular)
                hTailRun'
            let tailResult := tailBounded.1
            let openResult :=
              FunctionsObserverOutcome.ScopedOpenResult.appendRegular
                headResult.openResult hRegular tailResult.openResult
            let result :
                ScopedListResult contract codeRel targetProgram.toFunctions
                  (head :: tail) (lowerHead ++ lowerTail)
                  before after layout sourceFinal target ctx
                  canBreak canContinue canLeave
                  (sourceControl := sourceControl) :=
              { openResult := openResult
                regularLayout := by
                  intro hResultRegular
                  change
                    tailResult.openResult.finalLayout =
                      SolcValidation.StmtsOutVars layout (head :: tail)
                  rw [tailResult.regularLayout hResultRegular]
                  simpa [SolcValidation.StmtsOutVars] using
                    congrArg
                      (fun headLayout =>
                        SolcValidation.StmtsOutVars headLayout tail)
                      hHeadLayout
                regularControl := by
                  intro hResultRegular
                  exact tailResult.regularControl hResultRegular }
            refine ⟨⟨result, ?_⟩⟩
            exact
              FunctionsObserverFuel.ScopedOpenResult.appendRegular_bounded
                headResult.openResult hRegular tailResult.openResult
                headBounded.2 tailBounded.2
                hPreviousFuel hPreviousFuel
          · obtain ⟨jump, hSourceAfterHead⟩ :=
              FunctionsObserverOutcome.ModeRel.target_nonregular_source_checkpoint
                headResult.openResult.relation.mode hRegular
            have hSourceFinal : sourceFinal = sourceAfterHead := by
              simpa [ObserverSemantics.SourceReplay.stateModel,
                hSourceAfterHead] using hTailRun
            subst sourceFinal
            have hTailFresh : Fresh.Extends middle after :=
              Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerTail
            let openResult :=
              FunctionsObserverOutcome.ScopedOpenResult.appendNonregular
                (rightLower := lowerTail)
                headResult.openResult hRegular hTailFresh
            let result :
                ScopedListResult contract codeRel targetProgram.toFunctions
                  (head :: tail) (lowerHead ++ lowerTail)
                  before after layout sourceAfterHead target ctx
                  canBreak canContinue canLeave
                  (sourceControl := sourceControl) :=
              { openResult := openResult
                regularLayout := by
                  intro hResultRegular
                  exact (hRegular hResultRegular).elim
                regularControl := by
                  intro hResultRegular
                  exact (hRegular hResultRegular).elim }
            refine ⟨⟨result, ?_⟩⟩
            exact
              FunctionsObserverFuel.ScopedOpenResult.appendNonregular_bounded
                (rightLower := lowerTail)
                headResult.openResult hRegular hTailFresh
                headBounded.2 hPreviousFuel

end RecursiveOpenListForwardBounded

end FunctionsObserverForwardFuel
end Yul
end EvmCompiler
