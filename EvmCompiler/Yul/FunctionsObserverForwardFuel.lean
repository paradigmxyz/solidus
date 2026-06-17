import EvmCompiler.Yul.FunctionsObserverCallFuel
import EvmCompiler.Yul.FunctionsObserverForward
import EvmCompiler.Yul.FunctionsObserverStaticCost

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
    (staticCost bound : Nat) : Prop :=
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
      FunctionsObserverStaticCost.stmt stmt ≤ staticCost →
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
            staticCost sourceFuel result.openResult }

def RecursiveOpenListForwardBounded
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (staticCost bound : Nat) : Prop :=
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
      FunctionsObserverStaticCost.stmtList stmts ≤ staticCost →
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
            staticCost sourceFuel result.openResult }

def RecursiveOpenStmtForwardProgramBounded
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
        .ok sourceFinal →
      Nonempty
        { result :
            ScopedStmtResult contract codeRel targetProgram.toFunctions
              stmt lower before after layout sourceFinal target ctx
              canBreak canContinue canLeave
              (sourceControl := sourceControl) //
          FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmt stmt)
            sourceFuel result.openResult }

def RecursiveOpenListForwardProgramBounded
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
        .ok sourceFinal →
      Nonempty
        { result :
            ScopedListResult contract codeRel targetProgram.toFunctions
              stmts lower before after layout sourceFinal target ctx
              canBreak canContinue canLeave
              (sourceControl := sourceControl) //
          FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList stmts)
            sourceFuel result.openResult }

def RecursiveOpenCompoundForwardProgramBounded
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
    FunctionsObserverStatement.CompoundStmt stmt →
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
        .ok sourceFinal →
      Nonempty
        { result :
            ScopedStmtResult contract codeRel targetProgram.toFunctions
              stmt lower before after layout sourceFinal target ctx
              canBreak canContinue canLeave
              (sourceControl := sourceControl) //
          FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmt stmt)
            sourceFuel result.openResult }

namespace ScopedLoopResult

def ProgramBounded
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {cond : Locals.Expr 1}
    {postBase : Functions.Source.Ctx}
    {post : Functions.Block}
    {bodyBase : Functions.Source.Ctx}
    {body : Functions.Block}
    {final : Fresh.State}
    {layout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {loopCtx : Functions.Source.Ctx}
    (globalCost sourceFuel : Nat)
    (result :
      ScopedLoopResult contract codeRel program sourceControl cond
        postBase post bodyBase body final layout sourceFinal target loopCtx) :
    Prop :=
  ∃ fuel,
    fuel ≤ FunctionsObserverFuel.targetBudgetFor globalCost sourceFuel ∧
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx cond postBase post bodyBase body fuel target =
        .ok result.outcome

end ScopedLoopResult

namespace ClosedListResult

def RunBounded
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (fuelBound : Nat)
    (result :
      ClosedListResult contract codeRel program sourceControl lower
        initial final entryLayout sourceFinal target ctx) : Prop :=
  ∃ fuel,
    fuel ≤ fuelBound ∧
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx { stmts := lower } fuel target =
        .ok result.outcome

/--
Lexically closing an open block needs no additional fuel. The closed artifact
may have been packaged by a different proof path; Functions determinism aligns
its outcome with the canonical scoped execution of the open block.
-/
theorem runBounded_of_open
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {stmts : List AstStmt}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceOpen sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (opened :
      ScopedListResult contract codeRel program stmts lower
        initial final entryLayout sourceOpen target ctx
        canBreak canContinue canLeave
        (sourceControl := sourceControl))
    (closed :
      ClosedListResult contract codeRel program sourceControl lower
        initial final entryLayout sourceFinal target ctx) :
    RunBounded opened.openResult.requiredFuel closed := by
  let scopedOutcome :=
    if opened.openResult.outcome.mode = .regular then
      Functions.Source.Effectful.Outcome.regular
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          ctx.scope opened.openResult.outcome.state)
    else
      opened.openResult.outcome
  have hScoped :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx { stmts := lower }
          opened.openResult.requiredFuel target =
        .ok scopedOutcome := by
    by_cases hRegular : opened.openResult.outcome.mode = .regular
    · have hOutcome :
          opened.openResult.outcome =
            Functions.Source.Effectful.Outcome.regular
              opened.openResult.outcome.state :=
        Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
      have hOpen :=
        FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
          opened.openResult
      rw [hOutcome] at hOpen
      simp only [scopedOutcome, hRegular, ↓reduceIte]
      exact
        Functions.Source.Effectful.Block.runScoped_regular_of_runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hOpen
    · simp only [scopedOutcome, hRegular, ↓reduceIte]
      exact
        Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
            opened.openResult)
          hRegular
  obtain ⟨closedFuel, hClosed⟩ := closed.run
  have hOutcome :=
    Functions.Source.Effectful.Block.runScoped_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hScoped hClosed
  refine
    ⟨opened.openResult.requiredFuel, le_rfl, ?_⟩
  simpa [hOutcome] using hScoped

end ClosedListResult

namespace ScopedStmtResult

/--
An uninitialized declaration exposes its real static expansion cost: one
Functions block level per declared name, plus the empty suffix.
-/
theorem ofLetNone_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel staticCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {names : List EvmYul.Identifier}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hStatic :
      FunctionsObserverStaticCost.stmt (.Let names none) ≤ staticCost)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Let names none) =
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
    (hNamesUsed :
      StateRelation.Vars.NamesWithin before.used
        (identNames names))
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Let names none)
          codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program (.Let names none)
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.Bounded
          staticCost sourceFuel result.openResult } := by
  obtain ⟨⟨openResult, hRequired⟩⟩ :=
    FunctionsObserverStatement.OpenResult.of_let_none
      hLower hRel hDomain hScope hLayout hControl.scope hNamesUsed hRun
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  dsimp [FunctionsObserverFuel.ScopedOpenResult.Bounded, result,
    ScopedStmtResult.ofStatement]
  have hNamesStatic : names.length + 1 ≤ staticCost := by
    simpa [FunctionsObserverStaticCost.stmt] using hStatic
  exact
    hRequired.trans
      (hNamesStatic.trans
        (FunctionsObserverFuel.staticCost_le_executionBudget
          staticCost sourceFuel))

/--
A prepared single-value declaration adds exactly two target-fuel units around
the prepared expression run.
-/
theorem ofLetOnePrepared_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lowerStmts pre : List Functions.Stmt}
    {lowerValue : Locals.Expr 1}
    {sourceAfterValue sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Assembly.Word}
    {valueFuel sourceFuel staticCost : Nat}
    {canBreak canContinue canLeave : Bool}
    (hLower :
      lowerStmts =
        pre ++ [Functions.Stmt.let_ (identName name) lowerValue])
    (hFreshExtends : Fresh.Extends before after)
    (hNameFresh : identName name ∉ layout)
    (hNameUsed : identName name ∈ before.used)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hValue :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel program pre lowerValue after layout
        sourceAfterValue target ctx value)
    (hValueBound :
      FunctionsObserverFuel.PreparedValue.Bounded
        staticCost valueFuel hValue.prepared)
    (hValueFuel : valueFuel < sourceFuel)
    (hSourceFinal :
      sourceFinal =
        sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value])) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program
            (.Let [name] (some expr)) lowerStmts before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.Bounded
          staticCost sourceFuel result.openResult } := by
  obtain ⟨openResult⟩ :=
    FunctionsObserverStatement.OpenResult.of_let_one_prepared
      (sourceControl := sourceControl) (expr := expr)
      hLower hFreshExtends hNameFresh hNameUsed hLayout hControl.scope
      hValue hSourceFinal
  obtain
      ⟨targetFinal, finalCtx, hTargetRun,
        _hDeclaredRel, _hTargetFinal, _hFinalCtx⟩ :=
    FunctionsObserverStatement.InitializedValue.run_at_requiredFuel_add_two
      hValue.prepared hValue.relation hNameFresh
  have hTargetRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (hValue.prepared.requiredFuel + 2)
          { stmts := lowerStmts } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            finalCtx) := by
    simpa [hLower] using hTargetRun
  have hRegular :
      openResult.openResult.outcome.mode = .regular := by
    obtain
        ⟨sourceShared, sourceVars, hSourceAfterValue,
          _hShared, _hScoped, _hDomain⟩ :=
      hValue.relation.2
    have hMode := openResult.openResult.relation.mode
    have hSourceFinalOk :
        ∃ finalVars,
          sourceFinal.source = .Ok sourceShared finalVars := by
      rw [hSourceFinal]
      change
        ∃ finalVars,
          sourceAfterValue.source.multifill [name] [value] =
            .Ok sourceShared finalVars
      rw [hSourceAfterValue]
      exact ⟨sourceVars.insert name value, rfl⟩
    obtain ⟨finalVars, hFinalSource⟩ := hSourceFinalOk
    rw [hFinalSource] at hMode
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hMode
  have hResultRun :=
    FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
      openResult.openResult
  have hOutcomeEq :
      openResult.openResult.outcome =
        Functions.Source.Effectful.Outcome.regular
          openResult.openResult.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  rw [hOutcomeEq] at hResultRun
  obtain ⟨hTargetFinal, hTargetCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTargetRun' hResultRun
  rw [hTargetFinal, hTargetCtx] at hTargetRun'
  rw [← hOutcomeEq] at hTargetRun'
  have hRequired :
      openResult.openResult.requiredFuel ≤
        hValue.prepared.requiredFuel + 2 :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      openResult.openResult hTargetRun'
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  have hBudget :=
    FunctionsObserverFuel.executionBudget_child_add_eight_le_of_lt
      staticCost hValueFuel
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded] at hValueBound
  dsimp [FunctionsObserverFuel.ScopedOpenResult.Bounded, result,
    ScopedStmtResult.ofStatement]
  omega

/--
A prepared visible assignment has the same two-unit wrapper bound as a
single-value declaration.
-/
theorem ofAssignOnePrepared_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lowerStmts pre : List Functions.Stmt}
    {lowerValue : Locals.Expr 1}
    {sourceAfterValue sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Assembly.Word}
    {valueFuel sourceFuel staticCost : Nat}
    {canBreak canContinue canLeave : Bool}
    (hLower :
      lowerStmts =
        pre ++ [Functions.Stmt.assign (identName name) lowerValue])
    (hFreshExtends : Fresh.Extends before after)
    (hNameDeclared : identName name ∈ layout)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hValue :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel program pre lowerValue after layout
        sourceAfterValue target ctx value)
    (hValueBound :
      FunctionsObserverFuel.PreparedValue.Bounded
        staticCost valueFuel hValue.prepared)
    (hValueFuel : valueFuel < sourceFuel)
    (hSourceFinal :
      sourceFinal =
        sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value])) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program
            (.Assign [name] expr) lowerStmts before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.Bounded
          staticCost sourceFuel result.openResult } := by
  obtain ⟨openResult⟩ :=
    FunctionsObserverStatement.OpenResult.of_assign_one_prepared
      (sourceControl := sourceControl) (expr := expr)
      hLower hFreshExtends hNameDeclared hLayout hControl.scope
      hValue hSourceFinal
  obtain
      ⟨targetFinal, hTargetRun, _hAssignedRel, _hTargetFinal⟩ :=
    FunctionsObserverStatement.AssignedValue.run_at_requiredFuel_add_two
      hValue.prepared hValue.relation hNameDeclared
  have hTargetRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (hValue.prepared.requiredFuel + 2)
          { stmts := lowerStmts } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            hValue.prepared.finalCtx) := by
    simpa [hLower] using hTargetRun
  have hRegular :
      openResult.openResult.outcome.mode = .regular := by
    obtain
        ⟨sourceShared, sourceVars, hSourceAfterValue,
          _hShared, _hScoped, _hDomain⟩ :=
      hValue.relation.2
    have hMode := openResult.openResult.relation.mode
    have hSourceFinalOk :
        ∃ finalVars,
          sourceFinal.source = .Ok sourceShared finalVars := by
      rw [hSourceFinal]
      change
        ∃ finalVars,
          sourceAfterValue.source.multifill [name] [value] =
            .Ok sourceShared finalVars
      rw [hSourceAfterValue]
      exact ⟨sourceVars.insert name value, rfl⟩
    obtain ⟨finalVars, hFinalSource⟩ := hSourceFinalOk
    rw [hFinalSource] at hMode
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hMode
  have hResultRun :=
    FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
      openResult.openResult
  have hOutcomeEq :
      openResult.openResult.outcome =
        Functions.Source.Effectful.Outcome.regular
          openResult.openResult.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  rw [hOutcomeEq] at hResultRun
  obtain ⟨hTargetFinal, hTargetCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTargetRun' hResultRun
  rw [hTargetFinal, hTargetCtx] at hTargetRun'
  rw [← hOutcomeEq] at hTargetRun'
  have hRequired :
      openResult.openResult.requiredFuel ≤
        hValue.prepared.requiredFuel + 2 :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      openResult.openResult hTargetRun'
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  have hBudget :=
    FunctionsObserverFuel.executionBudget_child_add_eight_le_of_lt
      staticCost hValueFuel
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded] at hValueBound
  dsimp [FunctionsObserverFuel.ScopedOpenResult.Bounded, result,
    ScopedStmtResult.ofStatement]
  omega

theorem ofBreak_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel staticCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hStatic :
      FunctionsObserverStaticCost.stmt .Break ≤ staticCost)
    (hEnabled : canBreak = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Break =
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
          sourceFuel .Break codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program .Break
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.Bounded
          staticCost sourceFuel result.openResult } := by
  have hWithin := hControl.breakScope
  rw [FunctionsObserverOutcome.ScopeOptionWithin, hEnabled] at hWithin
  obtain
      ⟨breakLayout, targetBreakScope,
        hSourceBreakScope, hBreakScope,
        hBreakSubset, hBreakTarget⟩ :=
    hWithin
  obtain ⟨⟨openResult, hRequired⟩⟩ :=
    FunctionsObserverStatement.OpenResult.of_break
      (sourceControl := sourceControl)
      hLower hRel hDomain hScope hLayout
      hSourceBreakScope hBreakScope hBreakSubset hBreakTarget hRun
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  have hTwo : 2 ≤ staticCost := by
    simpa [FunctionsObserverStaticCost.stmt] using hStatic
  dsimp [FunctionsObserverFuel.ScopedOpenResult.Bounded, result,
    ScopedStmtResult.ofStatement]
  exact
    hRequired.trans
      (hTwo.trans
        (FunctionsObserverFuel.staticCost_le_executionBudget
          staticCost sourceFuel))

theorem ofContinue_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel staticCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hStatic :
      FunctionsObserverStaticCost.stmt .Continue ≤ staticCost)
    (hEnabled : canContinue = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Continue =
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
          sourceFuel .Continue codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program .Continue
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.Bounded
          staticCost sourceFuel result.openResult } := by
  have hWithin := hControl.continueScope
  rw [FunctionsObserverOutcome.ScopeOptionWithin, hEnabled] at hWithin
  obtain
      ⟨continueLayout, targetContinueScope,
        hSourceContinueScope, hContinueScope,
        hContinueSubset, hContinueTarget⟩ :=
    hWithin
  obtain ⟨⟨openResult, hRequired⟩⟩ :=
    FunctionsObserverStatement.OpenResult.of_continue
      (sourceControl := sourceControl)
      hLower hRel hDomain hScope hLayout
      hSourceContinueScope hContinueScope
      hContinueSubset hContinueTarget hRun
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  have hTwo : 2 ≤ staticCost := by
    simpa [FunctionsObserverStaticCost.stmt] using hStatic
  dsimp [FunctionsObserverFuel.ScopedOpenResult.Bounded, result,
    ScopedStmtResult.ofStatement]
  exact
    hRequired.trans
      (hTwo.trans
        (FunctionsObserverFuel.staticCost_le_executionBudget
          staticCost sourceFuel))

theorem ofLeave_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel staticCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hStatic :
      FunctionsObserverStaticCost.stmt .Leave ≤ staticCost)
    (hEnabled : canLeave = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Leave =
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
          sourceFuel .Leave codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program .Leave
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.Bounded
          staticCost sourceFuel result.openResult } := by
  have hWithin := hControl.leaveScope
  rw [FunctionsObserverOutcome.ScopeOptionWithin, hEnabled] at hWithin
  obtain
      ⟨leaveLayout, targetLeaveScope,
        hSourceLeaveScope, hLeaveScope,
        hLeaveSubset, hLeaveTarget⟩ :=
    hWithin
  obtain ⟨⟨openResult, hRequired⟩⟩ :=
    FunctionsObserverStatement.OpenResult.of_leave
      (sourceControl := sourceControl)
      hLower hRel hDomain hScope hLayout
      hSourceLeaveScope hLeaveScope hLeaveSubset hLeaveTarget hRun
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  have hTwo : 2 ≤ staticCost := by
    simpa [FunctionsObserverStaticCost.stmt] using hStatic
  dsimp [FunctionsObserverFuel.ScopedOpenResult.Bounded, result,
    ScopedStmtResult.ofStatement]
  exact
    hRequired.trans
      (hTwo.trans
        (FunctionsObserverFuel.staticCost_le_executionBudget
          staticCost sourceFuel))

theorem ofLetNone_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel globalCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {names : List EvmYul.Identifier}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Let names none) =
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
    (hNamesUsed :
      StateRelation.Vars.NamesWithin before.used
        (identNames names))
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Let names none)
          codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program (.Let names none)
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost
          (FunctionsObserverStaticCost.stmt (.Let names none))
          sourceFuel result.openResult } := by
  obtain ⟨bounded⟩ :=
    ofLetNone_bounded
      (staticCost :=
        FunctionsObserverStaticCost.stmt (.Let names none))
      (by rfl) hLower hRel hDomain hScope hLayout hControl hNamesUsed hRun
  exact
    ⟨⟨bounded.1,
      FunctionsObserverFuel.ScopedOpenResult.programBounded_of_bounded
        bounded.2⟩⟩

theorem ofLetOnePrepared_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lowerStmts pre : List Functions.Stmt}
    {lowerValue : Locals.Expr 1}
    {sourceAfterValue sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Assembly.Word}
    {valueFuel sourceFuel globalCost valueLocal resultLocal : Nat}
    {canBreak canContinue canLeave : Bool}
    (hLower :
      lowerStmts =
        pre ++ [Functions.Stmt.let_ (identName name) lowerValue])
    (hFreshExtends : Fresh.Extends before after)
    (hNameFresh : identName name ∉ layout)
    (hNameUsed : identName name ∈ before.used)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hValue :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel program pre lowerValue after layout
        sourceAfterValue target ctx value)
    (hValueBound :
      FunctionsObserverFuel.PreparedValue.ProgramBounded
        globalCost valueLocal valueFuel hValue.prepared)
    (hValueCost : valueLocal ≤ globalCost)
    (hValueFuel : valueFuel < sourceFuel)
    (hSourceFinal :
      sourceFinal =
        sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value])) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program
            (.Let [name] (some expr)) lowerStmts before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost resultLocal sourceFuel result.openResult } := by
  obtain ⟨openResult⟩ :=
    FunctionsObserverStatement.OpenResult.of_let_one_prepared
      (sourceControl := sourceControl) (expr := expr)
      hLower hFreshExtends hNameFresh hNameUsed hLayout hControl.scope
      hValue hSourceFinal
  obtain
      ⟨targetFinal, finalCtx, hTargetRun,
        _hDeclaredRel, _hTargetFinal, _hFinalCtx⟩ :=
    FunctionsObserverStatement.InitializedValue.run_at_requiredFuel_add_two
      hValue.prepared hValue.relation hNameFresh
  have hTargetRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (hValue.prepared.requiredFuel + 2)
          { stmts := lowerStmts } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            finalCtx) := by
    simpa [hLower] using hTargetRun
  have hRegular :
      openResult.openResult.outcome.mode = .regular := by
    obtain
        ⟨sourceShared, sourceVars, hSourceAfterValue,
          _hShared, _hScoped, _hDomain⟩ :=
      hValue.relation.2
    have hMode := openResult.openResult.relation.mode
    have hSourceFinalOk :
        ∃ finalVars,
          sourceFinal.source = .Ok sourceShared finalVars := by
      rw [hSourceFinal]
      change
        ∃ finalVars,
          sourceAfterValue.source.multifill [name] [value] =
            .Ok sourceShared finalVars
      rw [hSourceAfterValue]
      exact ⟨sourceVars.insert name value, rfl⟩
    obtain ⟨finalVars, hFinalSource⟩ := hSourceFinalOk
    rw [hFinalSource] at hMode
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hMode
  have hResultRun :=
    FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
      openResult.openResult
  have hOutcomeEq :
      openResult.openResult.outcome =
        Functions.Source.Effectful.Outcome.regular
          openResult.openResult.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  rw [hOutcomeEq] at hResultRun
  obtain ⟨hTargetFinal, hTargetCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTargetRun' hResultRun
  rw [hTargetFinal, hTargetCtx] at hTargetRun'
  rw [← hOutcomeEq] at hTargetRun'
  have hRequired :
      openResult.openResult.requiredFuel ≤
        hValue.prepared.requiredFuel + 2 :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      openResult.openResult hTargetRun'
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  have hChild :=
    FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
      globalCost valueLocal hValueCost hValueFuel
  have hParent :=
    FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
      globalCost resultLocal sourceFuel
  dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded] at hValueBound
  dsimp [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded, result,
    ScopedStmtResult.ofStatement]
  omega

/--
Program-indexed preservation for a non-call singleton declaration.
-/
theorem ofLetOne_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 1 expr =
        true)
    (hExprCost :
      FunctionsObserverStaticCost.expr expr ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Let [name] (some expr)) =
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
    (hNameUsed : identName name ∈ before.used)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Let [name] (some expr))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.Let [name] (some expr)) lower before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Let [name] (some expr)))
          sourceFuel result.openResult } := by
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_one_parts
      hNotFunctionCall hLower
  obtain
      ⟨evalFuel, sourceAfterValue, values, hSourceFuel,
        hCheck, hEvalValues, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_let_some_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hCheckSource :
      EvmYul.Yul.checkDeclaration
          (.Ok sourceShared sourceVars) [name] =
        .ok () := by
    rw [← hSource]
    exact hCheck
  have hNameFresh : identName name ∉ layout := by
    have hParts :=
      StateRelation.Vars.checkDeclaration_ok_parts
        (layout := layout) (source := sourceVars)
        (shared := sourceShared) hSourceDomain hCheckSource
    exact hParts.2 (identName name) (by simp [identName])
  obtain ⟨value, hValues, hPreparedNonempty⟩ :=
    hValue (by omega) hExprCost hExprOk hExprLower hRel hDomain hScope
      hEvalValues
  obtain ⟨preparedBounded⟩ := hPreparedNonempty
  have hSourceFinal' :
      sourceFinal =
        sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value]) := by
    rw [hValues] at hSourceFinal
    simpa [Yul.Source.Effectful.StateModel.multifill] using hSourceFinal
  exact
    ofLetOnePrepared_programBounded
      (resultLocal :=
        FunctionsObserverStaticCost.stmt
          (.Let [name] (some expr)))
      hLowerStmts
      (Expr.lower1Unchecked?_stateExtends hExprLower)
      hNameFresh hNameUsed hLayout hControl
      preparedBounded.1 preparedBounded.2 hExprCost
      (by omega) hSourceFinal'

theorem ofAssignOnePrepared_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lowerStmts pre : List Functions.Stmt}
    {lowerValue : Locals.Expr 1}
    {sourceAfterValue sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Assembly.Word}
    {valueFuel sourceFuel globalCost valueLocal resultLocal : Nat}
    {canBreak canContinue canLeave : Bool}
    (hLower :
      lowerStmts =
        pre ++ [Functions.Stmt.assign (identName name) lowerValue])
    (hFreshExtends : Fresh.Extends before after)
    (hNameDeclared : identName name ∈ layout)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hValue :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel program pre lowerValue after layout
        sourceAfterValue target ctx value)
    (hValueBound :
      FunctionsObserverFuel.PreparedValue.ProgramBounded
        globalCost valueLocal valueFuel hValue.prepared)
    (hValueCost : valueLocal ≤ globalCost)
    (hValueFuel : valueFuel < sourceFuel)
    (hSourceFinal :
      sourceFinal =
        sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value])) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program
            (.Assign [name] expr) lowerStmts before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost resultLocal sourceFuel result.openResult } := by
  obtain ⟨openResult⟩ :=
    FunctionsObserverStatement.OpenResult.of_assign_one_prepared
      (sourceControl := sourceControl) (expr := expr)
      hLower hFreshExtends hNameDeclared hLayout hControl.scope
      hValue hSourceFinal
  obtain
      ⟨targetFinal, hTargetRun, _hAssignedRel, _hTargetFinal⟩ :=
    FunctionsObserverStatement.AssignedValue.run_at_requiredFuel_add_two
      hValue.prepared hValue.relation hNameDeclared
  have hTargetRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (hValue.prepared.requiredFuel + 2)
          { stmts := lowerStmts } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            hValue.prepared.finalCtx) := by
    simpa [hLower] using hTargetRun
  have hRegular :
      openResult.openResult.outcome.mode = .regular := by
    obtain
        ⟨sourceShared, sourceVars, hSourceAfterValue,
          _hShared, _hScoped, _hDomain⟩ :=
      hValue.relation.2
    have hMode := openResult.openResult.relation.mode
    have hSourceFinalOk :
        ∃ finalVars,
          sourceFinal.source = .Ok sourceShared finalVars := by
      rw [hSourceFinal]
      change
        ∃ finalVars,
          sourceAfterValue.source.multifill [name] [value] =
            .Ok sourceShared finalVars
      rw [hSourceAfterValue]
      exact ⟨sourceVars.insert name value, rfl⟩
    obtain ⟨finalVars, hFinalSource⟩ := hSourceFinalOk
    rw [hFinalSource] at hMode
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hMode
  have hResultRun :=
    FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
      openResult.openResult
  have hOutcomeEq :
      openResult.openResult.outcome =
        Functions.Source.Effectful.Outcome.regular
          openResult.openResult.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  rw [hOutcomeEq] at hResultRun
  obtain ⟨hTargetFinal, hTargetCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTargetRun' hResultRun
  rw [hTargetFinal, hTargetCtx] at hTargetRun'
  rw [← hOutcomeEq] at hTargetRun'
  have hRequired :
      openResult.openResult.requiredFuel ≤
        hValue.prepared.requiredFuel + 2 :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      openResult.openResult hTargetRun'
  let result :=
    ScopedStmtResult.ofStatement openResult hControl
  refine ⟨⟨result, ?_⟩⟩
  have hChild :=
    FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
      globalCost valueLocal hValueCost hValueFuel
  have hParent :=
    FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
      globalCost resultLocal sourceFuel
  dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded] at hValueBound
  dsimp [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded, result,
    ScopedStmtResult.ofStatement]
  omega

/--
Program-indexed preservation for a non-call singleton assignment.
-/
theorem ofAssignOne_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 1 expr =
        true)
    (hExprCost :
      FunctionsObserverStaticCost.expr expr ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Assign [name] expr) =
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
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Assign [name] expr)
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.Assign [name] expr) lower before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Assign [name] expr))
          sourceFuel result.openResult } := by
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_one_parts
      hNotFunctionCall hLower
  obtain
      ⟨evalFuel, sourceAfterValue, values, hSourceFuel,
        hCheck, hEvalValues, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_assign_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hCheckSource :
      EvmYul.Yul.checkAssignment
          (.Ok sourceShared sourceVars) [name] =
        .ok () := by
    rw [← hSource]
    exact hCheck
  have hNameDeclared : identName name ∈ layout := by
    have hParts :=
      StateRelation.Vars.checkAssignment_ok_parts
        (layout := layout) (source := sourceVars)
        (shared := sourceShared) hSourceDomain hCheckSource
    exact hParts.2 (identName name) (by simp [identName])
  obtain ⟨value, hValues, hPreparedNonempty⟩ :=
    hValue (by omega) hExprCost hExprOk hExprLower hRel hDomain hScope
      hEvalValues
  obtain ⟨preparedBounded⟩ := hPreparedNonempty
  have hSourceFinal' :
      sourceFinal =
        sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value]) := by
    rw [hValues] at hSourceFinal
    simpa [Yul.Source.Effectful.StateModel.multifill] using hSourceFinal
  exact
    ofAssignOnePrepared_programBounded
      (resultLocal :=
        FunctionsObserverStaticCost.stmt
          (.Assign [name] expr))
      hLowerStmts
      (Expr.lower1Unchecked?_stateExtends hExprLower)
      hNameDeclared hLayout hControl
      preparedBounded.1 preparedBounded.2 hExprCost
      (by omega) hSourceFinal'

/--
A prepared nonterminal expression statement adds exactly two target-fuel
units around the prepared expression run.
-/
theorem ofExprPrepared_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after : Fresh.State}
    {layout : List Name}
    {expr : AstExpr}
    {lowerStmts pre : List Functions.Stmt}
    {lowerExpr : Locals.Expr 0}
    {sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    {valueFuel sourceFuel globalCost valueLocal resultLocal : Nat}
    {canBreak canContinue canLeave : Bool}
    (hLower :
      lowerStmts = pre ++ [Functions.Stmt.expr lowerExpr])
    (hFreshExtends : Fresh.Extends before after)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hPrepared :
      FunctionsObserverExpression.ScopedPreparedExpression
        contract transcript codeRel program pre lowerExpr after layout
        sourceFinal target ctx values)
    (hPreparedBound :
      FunctionsObserverFuel.PreparedExpression.ProgramBounded
        globalCost valueLocal valueFuel hPrepared.prepared)
    (hValueFuel : valueFuel ≤ sourceFuel)
    (hLocalCost : valueLocal + 1 ≤ resultLocal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program
            (.ExprStmtCall expr) lowerStmts before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost resultLocal sourceFuel result.openResult } := by
  have hExprStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPrepared.prepared.finalCtx 0
          (.expr lowerExpr) hPrepared.prepared.preTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            hPrepared.prepared.evalTarget,
            hPrepared.prepared.finalCtx) := by
    simp [Functions.Source.Effectful.Stmt.run,
      hPrepared.prepared.eval]
  have hEmpty :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPrepared.prepared.finalCtx 1
          { stmts := [] } hPrepared.prepared.evalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            hPrepared.prepared.evalTarget,
            hPrepared.prepared.finalCtx) := by
    simpa using
      Functions.Source.Effectful.Block.runOpen_nil
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hPrepared.prepared.finalCtx 0
        hPrepared.prepared.evalTarget
  have hExprBlock :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPrepared.prepared.finalCtx 2
          { stmts := [Functions.Stmt.expr lowerExpr] }
          hPrepared.prepared.preTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            hPrepared.prepared.evalTarget,
            hPrepared.prepared.finalCtx) := by
    simpa using
      Functions.Source.Effectful.Block.runOpen_cons_regular_at_max
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hExprStmt hEmpty
  have hTargetRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (hPrepared.prepared.requiredFuel + 2)
          { stmts := lowerStmts } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            hPrepared.prepared.evalTarget,
            hPrepared.prepared.finalCtx) := by
    rw [hLower]
    exact
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program pre [Functions.Stmt.expr lowerExpr]
        ctx hPrepared.prepared.finalCtx target hPrepared.prepared.preTarget
        (Functions.Source.Effectful.Outcome.regular
          hPrepared.prepared.evalTarget)
        hPrepared.prepared.finalCtx hPrepared.prepared.requiredFuel 2
        (FunctionsObserverExpression.PreparedExpression.run_requiredFuel
          hPrepared.prepared)
        hExprBlock
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
        sourceFinal
        (Functions.Source.Effectful.Outcome.regular
          hPrepared.prepared.evalTarget) := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      hPrepared.relation.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource hPrepared.relation
  let openResult :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lowerStmts before after layout
        sourceFinal target ctx (sourceControl := sourceControl) :=
    { finalLayout := layout
      outcome :=
        Functions.Source.Effectful.Outcome.regular
          hPrepared.prepared.evalTarget
      finalCtx := hPrepared.prepared.finalCtx
      run := ⟨hPrepared.prepared.requiredFuel + 2, hTargetRun⟩
      relation := hOutcomeRel
      domain := hPrepared.prepared.domain
      scope := hPrepared.prepared.scope
      control := hPrepared.prepared.control
      freshExtends := hFreshExtends
      retains := fun _hRegular _candidate hMem => hMem
      layoutWithin := hLayout.mono hFreshExtends
      sourceDefined :=
        FunctionsObserverOutcome.SourceDefined.of_scopedExact
          hPrepared.relation
      abruptTargetRestriction := by
        simp [FunctionsObserverOutcome.AbruptTargetRestriction]
      layoutScope := fun _hRegular =>
        fun name hMem =>
          Functions.Source.Effectful.Block.runOpen_scopeExtends
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program hTargetRun name (hControl.scope name hMem)
      exitScope := by
        simp [FunctionsObserverOutcome.ExitScopeRel] }
  let result :
      ScopedStmtResult contract codeRel program
        (.ExprStmtCall expr) lowerStmts before after layout sourceFinal
        target ctx canBreak canContinue canLeave
        (sourceControl := sourceControl) :=
    ScopedStmtResult.ofOpen openResult
      (by
        intro _hRegular
        rfl)
      hControl
  refine ⟨⟨result, ?_⟩⟩
  have hRequired :
      openResult.requiredFuel ≤ hPrepared.prepared.requiredFuel + 2 :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      openResult hTargetRun
  have hDynamic :=
    FunctionsObserverFuel.executionBudgetFor_mono
      globalCost valueLocal hValueFuel
  have hStep :
      FunctionsObserverFuel.executionBudgetFor
            globalCost valueLocal sourceFuel + 2 ≤
        FunctionsObserverFuel.executionBudgetFor
          globalCost (valueLocal + 1) sourceFuel := by
    rw [FunctionsObserverFuel.executionBudgetFor_add_one_local]
    have hTarget :=
      FunctionsObserverFuel.targetBudgetFor_ge_sixteen
        globalCost sourceFuel
    omega
  have hLocal :=
    FunctionsObserverFuel.executionBudgetFor_local_mono
      globalCost sourceFuel hLocalCost
  dsimp [FunctionsObserverFuel.PreparedExpression.ProgramBounded]
    at hPreparedBound
  change
    openResult.requiredFuel ≤
      FunctionsObserverFuel.executionBudgetFor
        globalCost resultLocal sourceFuel
  have hPreparedPlus :
      hPrepared.prepared.requiredFuel + 2 ≤
        FunctionsObserverFuel.executionBudgetFor
            globalCost valueLocal sourceFuel + 2 :=
    Nat.add_le_add_right (hPreparedBound.trans hDynamic) 2
  exact hRequired.trans (hPreparedPlus.trans (hStep.trans hLocal))

/--
Program-indexed preservation for a nonterminal primitive expression
statement.
-/
theorem ofExprPrimitive_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hNonterminal : Prim.terminal? prim = none)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 0 (.Call (.inl prim) args) =
        true)
    (hExprCost :
      FunctionsObserverStaticCost.expr (.Call (.inl prim) args) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.ExprStmtCall (.Call (.inl prim) args)) =
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
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.ExprStmtCall (.Call (.inl prim) args))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.ExprStmtCall (.Call (.inl prim) args))
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inl prim) args)))
          sourceFuel result.openResult } := by
  obtain ⟨pre, lowerExpr, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_primitive_parts
      hNonterminal hLower
  obtain
      ⟨evalPrevious, sourceAfterPrim, values,
        hSourceFuel, hEvalValues, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_expr_primitive_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  have hArgsOk :
      SolcValidation.ExprsOk? profile
          sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  have hArgCost :
      ∀ expr, expr ∈ args →
        FunctionsObserverStaticCost.expr expr ≤
          FunctionsObserverStaticCost.program sourceProgram := by
    intro expr hMem
    have hList :=
      FunctionsObserverStaticCost.expr_le_exprList_of_mem hMem
    have hListCall :
        FunctionsObserverStaticCost.exprList args ≤
          FunctionsObserverStaticCost.expr (.Call (.inl prim) args) := by
      simp [FunctionsObserverStaticCost.expr]
    exact hList.trans (hListCall.trans hExprCost)
  obtain ⟨preparedBounded⟩ :=
    FunctionsObserverExpressionFuel.ScopedPreparedExpression.ofPrimitive_programBounded
      (fuel := sourceFuel)
      hExprLower
      (fun expr hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
      hExprCost hArgCost
      (fun hLt hArgOk hArgLower hArgRel hArgDomain hArgScope hArgRun =>
        FunctionsObserverCall.RecursiveScopedValueForward.expression
          hValueOrdinary (by omega) hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun)
      (fun hLt hCost hArgOk hArgLower hArgRel hArgDomain
          hArgScope hArgRun =>
        FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded.expression
          hValue (by omega) hCost hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun)
      hRel hDomain hScope
      (by simpa [hSourceFuel] using hEvalValues)
  have hSourceFinal' : sourceFinal = sourceAfterPrim := by
    have hMultifill :
        sourceAfterPrim.source.multifill [] values =
          sourceAfterPrim.source := by
      cases sourceAfterPrim.source <;>
        simp [EvmYul.Yul.State.multifill]
    rw [hSourceFinal]
    change
      sourceAfterPrim.withSource
          (sourceAfterPrim.source.multifill [] values) =
        sourceAfterPrim
    rw [hMultifill]
    exact
      Simulation.ResourceReplay.State.withSource_self sourceAfterPrim
  rw [hSourceFinal']
  exact
    ofExprPrepared_programBounded
      (expr := .Call (.inl prim) args)
      (valueFuel := sourceFuel) (sourceFuel := sourceFuel)
      (resultLocal :=
        FunctionsObserverStaticCost.stmt
          (.ExprStmtCall (.Call (.inl prim) args)))
      hLowerStmts
      (Expr.lowerUnchecked?_stateExtends hExprLower)
      hLayout hControl preparedBounded.1 preparedBounded.2
      (by rfl)
      (by simp [FunctionsObserverStaticCost.stmt])

/--
Lift a bounded returned call through a statement constructor whose generated
code is exactly that call block.
-/
theorem ofCallResult_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {before after : Fresh.State}
    {layout finalLayout targets : List Name}
    {functionName : Name}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {globalCost resultLocal sourceFuel : Nat}
    {canBreak canContinue canLeave : Bool}
    (hLower :
      lower =
        preArgs ++
          [Functions.Stmt.call targets functionName lowerArgs])
    (result :
      FunctionsObserverStatement.OpenResult.Result
        contract codeRel program stmt lower before after layout
        sourceFinal target ctx (sourceControl := sourceControl))
    (hRegular : result.openResult.outcome.mode = .regular)
    (returnedCall :
      FunctionsObserverCall.ScopedReturnedCall
        contract transcript codeRel program functionName targets
        preArgs lowerArgs after finalLayout sourceFinal target ctx)
    (hCallBound :
      FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
          returnedCall ≤
        FunctionsObserverFuel.executionBudgetFor
          globalCost resultLocal sourceFuel)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx) :
    Nonempty
      { statementResult :
          ScopedStmtResult contract codeRel program stmt lower before after
            layout sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost resultLocal sourceFuel
            statementResult.openResult } := by
  have hResultRun :=
    FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
      result.openResult
  have hOutcomeEq :
      result.openResult.outcome =
        Functions.Source.Effectful.Outcome.regular
          result.openResult.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  rw [hOutcomeEq] at hResultRun
  have hCallRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx
          (FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
            returnedCall)
          { stmts := lower } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            returnedCall.finalTarget,
            returnedCall.finalCtx) := by
    simpa [hLower] using
      FunctionsObserverCallFuel.ScopedReturnedCall.run_requiredFuel
        returnedCall
  obtain ⟨hFinalTarget, hFinalCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hResultRun hCallRun
  rw [← hFinalTarget, ← hFinalCtx] at hCallRun
  rw [← hOutcomeEq] at hCallRun
  have hRequired :
      result.openResult.requiredFuel ≤
        FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
          returnedCall :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      result.openResult hCallRun
  let statementResult := ScopedStmtResult.ofStatement result hControl
  refine ⟨⟨statementResult, ?_⟩⟩
  change
    result.openResult.requiredFuel ≤
      FunctionsObserverFuel.executionBudgetFor
        globalCost resultLocal sourceFuel
  exact hRequired.trans hCallBound

/--
Program-indexed quantitative preservation for a visible multi-result call
assignment.
-/
theorem ofAssignCall_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout names.length
          (.Call (.inr functionName) callArgs) =
        true)
    (hCallCost :
      FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) callArgs) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hStmtCost :
      FunctionsObserverStaticCost.stmt
          (.Assign names (.Call (.inr functionName) callArgs)) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Assign names (.Call (.inr functionName) callArgs)) =
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
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBodyOrdinary :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBody :
      FunctionsObserverCallFuel.RecursiveBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Assign names (.Call (.inr functionName) callArgs))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.Assign names (.Call (.inr functionName) callArgs))
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Assign names (.Call (.inr functionName) callArgs)))
          sourceFuel result.openResult } := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_call_parts hLower
  obtain
      ⟨evalFuel, sourceAfterCall, returnValues, hSourceFuel,
        hCheck, hEvalValues, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_assign_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hCheckSource :
      EvmYul.Yul.checkAssignment
          (.Ok sourceShared sourceVars) names =
        .ok () := by
    rw [← hSource]
    exact hCheck
  obtain ⟨hTargetsNodup, hTargetsVisible⟩ :=
    StateRelation.Vars.checkAssignment_ok_parts
      (layout := layout) (source := sourceVars)
      (shared := sourceShared) hSourceDomain hCheckSource
  obtain ⟨boundedCall⟩ :=
    FunctionsObserverCallFuel.ScopedReturnedCall.ofFunctionCall_programBounded
      (resultLocal :=
        FunctionsObserverStaticCost.stmt
          (.Assign names (.Call (.inr functionName) callArgs)))
      hDecomposition hArgsLowering hProgramOk
      (by simpa [identNames_eq_self] using hExprOk)
      hCallCost
      (by simpa [identNames_eq_self] using hTargetsNodup)
      (by simpa [identNames_eq_self] using hTargetsVisible)
      (FunctionsObserverCall.RecursiveScopedValueForward.expression
        hValueOrdinary)
      hBodyOrdinary
      (FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded.expression
        hValue)
      hBody hRel hDomain hScope (by omega) hEvalValues
      (by simpa [identNames_eq_self] using hSourceFinal)
  obtain ⟨ordinary⟩ :=
    FunctionsObserverStatement.OpenResult.of_assign_call
      (sourceControl := sourceControl)
      hDecomposition hProgramOk hExprOk hLower hRel hDomain
      hScope hLayout hControl.scope
      (hValueOrdinary.mono (by omega))
      (hBodyOrdinary.mono (by omega))
      hRun
  have hRegular : ordinary.openResult.outcome.mode = .regular := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      boundedCall.1.relation.2
    have hMode := ordinary.openResult.relation.mode
    rw [hFinalSource] at hMode
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hMode
  have hCallBoundParent :
      FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
          boundedCall.1 ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Assign names (.Call (.inr functionName) callArgs)))
          sourceFuel := by
    have hChild :=
      FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.stmt
          (.Assign names (.Call (.inr functionName) callArgs)))
        hStmtCost
        (by omega : evalFuel < sourceFuel)
    have hParent :=
      FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.stmt
          (.Assign names (.Call (.inr functionName) callArgs)))
        sourceFuel
    omega
  exact
    ofCallResult_programBounded
      (by simpa [identNames_eq_self] using hLowerStmts)
      ordinary hRegular boundedCall.1 hCallBoundParent hControl

/--
Program-indexed quantitative preservation for a zero-result internal call
statement.
-/
theorem ofExprCall_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {functionName : Name}
    {args : List AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 0 (.Call (.inr functionName) args) =
        true)
    (hCallCost :
      FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) args) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hStmtCost :
      FunctionsObserverStaticCost.stmt
          (.ExprStmtCall (.Call (.inr functionName) args)) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.ExprStmtCall (.Call (.inr functionName) args)) =
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
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBodyOrdinary :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBody :
      FunctionsObserverCallFuel.RecursiveBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.ExprStmtCall (.Call (.inr functionName) args))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.ExprStmtCall (.Call (.inr functionName) args))
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.ExprStmtCall (.Call (.inr functionName) args)))
          sourceFuel result.openResult } := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_call_parts hLower
  obtain
      ⟨argsFuel, callFuel, sourceAfterArgs, reversedValues,
        sourceAfterCall, returnValues, hSourceFuel, hArgsFuel,
        hArgsRun, hCallRun, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_expr_function_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  have hMultifill :
      sourceAfterCall.source.multifill [] returnValues =
        sourceAfterCall.source := by
    cases sourceAfterCall.source <;>
      simp [EvmYul.Yul.State.multifill]
  have hSourceFinal' : sourceFinal = sourceAfterCall := by
    rw [hSourceFinal]
    change
      sourceAfterCall.withSource
          (sourceAfterCall.source.multifill [] returnValues) =
        sourceAfterCall
    rw [hMultifill]
    exact
      Simulation.ResourceReplay.State.withSource_self sourceAfterCall
  obtain ⟨boundedCall⟩ :=
    FunctionsObserverCallFuel.ScopedReturnedCall.ofFunctionCallParts_programBounded
      (bound := bound) (argsFuel := argsFuel)
      (callFuel := callFuel) (parentFuel := sourceFuel)
      (resultLocal :=
        FunctionsObserverStaticCost.stmt
          (.ExprStmtCall (.Call (.inr functionName) args)))
      hDecomposition hArgsLowering hProgramOk hExprOk hCallCost
      List.nodup_nil (by simp)
      (FunctionsObserverCall.RecursiveScopedValueForward.expression
        hValueOrdinary)
      hBodyOrdinary
      (FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded.expression
        hValue)
      hBody hRel hDomain hScope
      (by omega) (by omega) (by omega) (by omega)
      hArgsRun hCallRun
      (by simpa [hSourceFinal'])
  obtain ⟨ordinary⟩ :=
    FunctionsObserverStatement.OpenResult.of_expr_call
      (sourceControl := sourceControl)
      hDecomposition hProgramOk hExprOk hLower hRel hDomain
      hScope hLayout hControl.scope
      (FunctionsObserverCall.RecursiveScopedValueForward.expression
        (hValueOrdinary.mono (by omega)))
      (hBodyOrdinary.mono (by omega))
      hRun
  have hRegular : ordinary.openResult.outcome.mode = .regular := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      boundedCall.1.relation.2
    have hMode := ordinary.openResult.relation.mode
    rw [hFinalSource] at hMode
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hMode
  exact
    ofCallResult_programBounded
      hLowerStmts ordinary hRegular boundedCall.1 boundedCall.2 hControl

/--
Program-indexed quantitative preservation for a fresh multi-result call
declaration, including the generated zero-initialization prefix.
-/
theorem ofLetCall_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout names.length
          (.Call (.inr functionName) callArgs) =
        true)
    (hCallCost :
      FunctionsObserverStaticCost.expr
          (.Call (.inr functionName) callArgs) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hStmtCost :
      FunctionsObserverStaticCost.stmt
          (.Let names
            (some (.Call (.inr functionName) callArgs))) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Let names (some (.Call (.inr functionName) callArgs))) =
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
    (hNamesUsed :
      StateRelation.Vars.NamesWithin before.used (identNames names))
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBodyOrdinary :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBody :
      FunctionsObserverCallFuel.RecursiveBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Let names (some (.Call (.inr functionName) callArgs)))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.Let names (some (.Call (.inr functionName) callArgs)))
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Let names
              (some (.Call (.inr functionName) callArgs)))
          )
          sourceFuel result.openResult } := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_call_parts hLower
  obtain
      ⟨evalFuel, sourceAfterCall, returnValues, hSourceFuel,
        hCheck, hEvalValues, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_let_some_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hCheckSource :
      EvmYul.Yul.checkDeclaration
          (.Ok sourceShared sourceVars) names =
        .ok () := by
    rw [← hSource]
    exact hCheck
  obtain ⟨hTargetsNodup, hTargetsFresh⟩ :=
    StateRelation.Vars.checkDeclaration_ok_parts
      (layout := layout) (source := sourceVars)
      (shared := sourceShared) hSourceDomain hCheckSource
  obtain
      ⟨initVars, initCtx, hInsert, hInitRun, hInitCtx⟩ :=
    FunctionsObserverStatement.InitNames.run_at_length
      (contract := contract) (program := targetProgram.toFunctions)
      (identNames names) target ctx
  let targetDeclared :=
    target.withSource
      { shared := target.source.shared, vars := initVars }
  have hDeclaredRel :
      StateRelation.Replay.ScopedExactRel codeRel layout
        source targetDeclared := by
    simpa [targetDeclared] using
      StateRelation.Replay.scopedExact_insertMany_hidden
        hRel
        (by simpa [identNames_eq_self] using hTargetsFresh)
        hInsert
  have hDeclaredDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used targetDeclared.source.vars := by
    simpa [targetDeclared] using
      hDomain.insertMany hNamesUsed hInsert
  have hDeclaredScope :
      StateRelation.Vars.NamesWithin before.used initCtx.scope := by
    rw [hInitCtx]
    intro candidate hMem
    rcases List.mem_append.mp hMem with hDeclared | hOuter
    · exact hNamesUsed candidate (by simpa using hDeclared)
    · exact hScope candidate hOuter
  have hTargetsContain :
      ∀ candidate, candidate ∈ identNames names →
        targetDeclared.source.vars.contains candidate = true := by
    intro candidate hMem
    simpa [targetDeclared] using
      Functions.Source.Store.insertMany_contains_of_mem
        (by simpa [identNames_eq_self] using hTargetsNodup)
        hInsert hMem
  obtain ⟨boundedCall⟩ :=
    FunctionsObserverCallFuel.ScopedReturnedCall.ofFunctionCallFresh_programBounded
      (resultLocal :=
        FunctionsObserverStaticCost.stmt
          (.Let names
            (some (.Call (.inr functionName) callArgs))))
      hDecomposition hArgsLowering hProgramOk
      (by simpa [identNames_eq_self] using hExprOk)
      hCallCost
      (by simpa [identNames_eq_self] using hTargetsNodup)
      (by simpa [identNames_eq_self] using hTargetsFresh)
      hTargetsContain
      (FunctionsObserverCall.RecursiveScopedValueForward.expression
        hValueOrdinary)
      hBodyOrdinary
      (FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded.expression
        hValue)
      hBody hDeclaredRel hDeclaredDomain hDeclaredScope
      (by omega) hEvalValues
      (by simpa [identNames_eq_self] using hSourceFinal)
  obtain ⟨ordinary⟩ :=
    FunctionsObserverStatement.OpenResult.of_let_call
      (sourceControl := sourceControl)
      hDecomposition hProgramOk hExprOk hLower hRel hDomain
      hScope hLayout hControl.scope hNamesUsed
      (hValueOrdinary.mono (by omega))
      (hBodyOrdinary.mono (by omega))
      hRun
  have hCallRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions initCtx
          (FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
            boundedCall.1)
          { stmts :=
              preArgs ++
                [Functions.Stmt.call
                  (identNames names) functionName lowerArgs] }
          targetDeclared =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            boundedCall.1.finalTarget,
            boundedCall.1.finalCtx) :=
    FunctionsObserverCallFuel.ScopedReturnedCall.run_requiredFuel
      boundedCall.1
  have hFullRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx
          ((identNames names).length + 1 +
            FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
              boundedCall.1)
          { stmts := lower } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            boundedCall.1.finalTarget,
            boundedCall.1.finalCtx) := by
    rw [hLowerStmts]
    simpa [targetDeclared, List.append_assoc] using
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions
        (Stmt.initNames (identNames names))
        (preArgs ++
          [Functions.Stmt.call
            (identNames names) functionName lowerArgs])
        ctx initCtx target targetDeclared
        (Functions.Source.Effectful.Outcome.regular
          boundedCall.1.finalTarget)
        boundedCall.1.finalCtx ((identNames names).length + 1)
        (FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
          boundedCall.1)
        (by simpa [targetDeclared] using hInitRun) hCallRun
  have hRegular : ordinary.openResult.outcome.mode = .regular := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      boundedCall.1.relation.2
    have hMode := ordinary.openResult.relation.mode
    rw [hFinalSource] at hMode
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hMode
  have hOrdinaryRun :=
    FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
      ordinary.openResult
  have hOutcomeEq :
      ordinary.openResult.outcome =
        Functions.Source.Effectful.Outcome.regular
          ordinary.openResult.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  rw [hOutcomeEq] at hOrdinaryRun
  obtain ⟨hFinalTarget, hFinalCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hOrdinaryRun hFullRun
  rw [← hFinalTarget, ← hFinalCtx] at hFullRun
  rw [← hOutcomeEq] at hFullRun
  have hRequired :
      ordinary.openResult.requiredFuel ≤
        (identNames names).length + 1 +
          FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
            boundedCall.1 :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      ordinary.openResult hFullRun
  have hCallTarget :
      FunctionsObserverCallFuel.ScopedReturnedCall.requiredFuel
          boundedCall.1 ≤
        FunctionsObserverFuel.targetBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          sourceFuel := by
    have hChild :=
      FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.stmt
          (.Let names
            (some (.Call (.inr functionName) callArgs))))
        hStmtCost (by omega : evalFuel < sourceFuel)
    omega
  have hInitCost :
      (identNames names).length + 1 ≤
        FunctionsObserverStaticCost.stmt
          (.Let names
            (some (.Call (.inr functionName) callArgs))) := by
    simp [FunctionsObserverStaticCost.stmt, identNames]
    omega
  have hTargetWithPrefix :=
    FunctionsObserverFuel.targetBudgetFor_add_localCost_le_executionBudgetFor
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmt
        (.Let names
          (some (.Call (.inr functionName) callArgs))))
      sourceFuel
  let statementResult :=
    ScopedStmtResult.ofStatement ordinary hControl
  refine ⟨⟨statementResult, ?_⟩⟩
  change
    ordinary.openResult.requiredFuel ≤
      FunctionsObserverFuel.executionBudgetFor
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.stmt
          (.Let names
            (some (.Call (.inr functionName) callArgs))))
        sourceFuel
  omega

theorem ofBreak_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel globalCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hEnabled : canBreak = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Break =
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
          sourceFuel .Break codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program .Break
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost (FunctionsObserverStaticCost.stmt .Break)
          sourceFuel result.openResult } := by
  obtain ⟨bounded⟩ :=
    ofBreak_bounded
      (staticCost := FunctionsObserverStaticCost.stmt .Break)
      (by rfl) hEnabled hLower hRel hDomain hScope hLayout hControl hRun
  exact
    ⟨⟨bounded.1,
      FunctionsObserverFuel.ScopedOpenResult.programBounded_of_bounded
        bounded.2⟩⟩

theorem ofContinue_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel globalCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hEnabled : canContinue = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Continue =
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
          sourceFuel .Continue codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program .Continue
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost (FunctionsObserverStaticCost.stmt .Continue)
          sourceFuel result.openResult } := by
  obtain ⟨bounded⟩ :=
    ofContinue_bounded
      (staticCost := FunctionsObserverStaticCost.stmt .Continue)
      (by rfl) hEnabled hLower hRel hDomain hScope hLayout hControl hRun
  exact
    ⟨⟨bounded.1,
      FunctionsObserverFuel.ScopedOpenResult.programBounded_of_bounded
        bounded.2⟩⟩

theorem ofLeave_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel sourceFuel globalCost : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hEnabled : canLeave = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Leave =
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
          sourceFuel .Leave codeOverride source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel program .Leave
            lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          globalCost (FunctionsObserverStaticCost.stmt .Leave)
          sourceFuel result.openResult } := by
  obtain ⟨bounded⟩ :=
    ofLeave_bounded
      (staticCost := FunctionsObserverStaticCost.stmt .Leave)
      (by rfl) hEnabled hLower hRel hDomain hScope hLayout hControl hRun
  exact
    ⟨⟨bounded.1,
      FunctionsObserverFuel.ScopedOpenResult.programBounded_of_bounded
        bounded.2⟩⟩

end ScopedStmtResult

namespace RecursiveOpenCompoundForwardProgramBounded

theorem closeGuardedBody
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound sourceFuel compilerFuel : Nat}
    {initial condFresh bodyInitial final : Fresh.State}
    {layout : List Name}
    {body : List AstStmt}
    {preCond : List Functions.Stmt}
    {lowerCond : Locals.Expr 1}
    {lowerBody : Functions.Block}
    {sourceAfterCond sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {bodyBase : Functions.Source.Ctx}
    {canLeave : Bool}
    {value : Assembly.Word}
    (hList :
      RecursiveOpenListForwardProgramBounded contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (prepared :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel targetProgram.toFunctions
        preCond lowerCond condFresh layout sourceAfterCond
        target bodyBase value)
    (hCondCost : Nat)
    (hPrepared' :
      prepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          hCondCost sourceFuel)
    (hFuel : sourceFuel < bound)
    (hBodyCost :
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout true true canLeave body =
        true)
    (hBodyNames :
      StateRelation.Vars.NamesWithin bodyInitial.used
        (Stmt.List.names body))
    (hLowerBody :
      Stmt.List.toBlockUncheckedFuel? compilerFuel bodyInitial body =
        some (lowerBody, final))
    (hBodyInitial : Fresh.Extends condFresh bodyInitial)
    (hFresh : Fresh.Extends initial final)
    (hLayout :
      StateRelation.Vars.NamesWithin initial.used layout)
    (hLayoutBodyInitial :
      StateRelation.Vars.NamesWithin bodyInitial.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        true true canLeave bodyBase)
    (hNonzero : value ≠ EvmYul.UInt256.ofNat 0)
    (hBodyRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block body) (some sourceProgram.contract)
          sourceAfterCond =
        .ok sourceAfterBody) :
    Nonempty
      { result :
          ClosedListResult contract codeRel targetProgram.toFunctions
            sourceControl
            (preCond ++
              .if_
                  (.prim .iszero
                    (Locals.ExprSeq.cons lowerCond .nil))
                  { stmts := [.brk] } ::
                lowerBody.stmts)
            initial final layout sourceAfterBody target bodyBase //
        ClosedListResult.RunBounded
          (FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              hCondCost sourceFuel +
            FunctionsObserverFuel.executionBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmtList body) sourceFuel +
            3)
          result } := by
  obtain ⟨listCompilerFuel, lowerBodyStmts, _hBlockFuel,
      hLowerBodyList, hLowerBodyEq⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  subst lowerBody
  obtain ⟨listSourceFuel, sourceOpen, _hSourceFuel,
      hBodyListRun, hSourceAfterBody⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hBodyRun
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
        true true canLeave prepared.prepared.finalCtx :=
    FunctionsObserverOutcome.ControlContextRel.transport hControl
      (fun _name hMem => hMem)
      prepared.prepared.control hPreparedLayoutScope
  obtain ⟨bodyBounded⟩ :=
    hList (sourceFuel := listSourceFuel)
      (compilerFuel := listCompilerFuel)
      (before := bodyInitial) (after := final)
      (layout := layout) (stmts := body)
      (lower := lowerBodyStmts)
      (source := sourceAfterCond) (sourceFinal := sourceOpen)
      (target := prepared.prepared.evalTarget)
      (ctx := prepared.prepared.finalCtx)
      (canBreak := true) (canContinue := true)
      (canLeave := canLeave)
      (by omega) hBodyCost hBodyOk hBodyNames hLowerBodyList
      prepared.relation
      (prepared.prepared.domain.mono hBodyInitial)
      (prepared.prepared.scope.mono hBodyInitial)
      hLayoutBodyInitial
      hPreparedControl hBodyListRun
  let bodyResult := bodyBounded.1
  obtain ⟨combined⟩ :=
    ScopedListResult.prependForGuard prepared bodyResult hNonzero hFresh
  have hGuardRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions bodyBase
          (prepared.prepared.requiredFuel +
            bodyResult.openResult.requiredFuel + 3)
          { stmts :=
              preCond ++
                .if_
                    (.prim .iszero
                      (Locals.ExprSeq.cons lowerCond .nil))
                    { stmts := [.brk] } ::
                  lowerBodyStmts }
          target =
        .ok
          (bodyResult.openResult.outcome,
            bodyResult.openResult.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_forGuard_body_at_add_three
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions
      (FunctionsObserverExpression.PreparedValue.run_requiredFuel
        prepared.prepared)
      prepared.prepared.eval
      (Functions.ObserverSafety.SafeSemantics.eval_iszero
        prepared.prepared.evalTarget value)
      hNonzero
      (FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
        bodyResult.openResult)
  obtain ⟨combinedFuel, hCombinedRun⟩ := combined.openResult.run
  have hCombinedEq :=
    Functions.Source.Effectful.Block.runOpen_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hGuardRun hCombinedRun
  have hGuardRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions bodyBase
          (prepared.prepared.requiredFuel +
            bodyResult.openResult.requiredFuel + 3)
          { stmts :=
              preCond ++
                .if_
                    (.prim .iszero
                      (Locals.ExprSeq.cons lowerCond .nil))
                    { stmts := [.brk] } ::
                  lowerBodyStmts }
          target =
        .ok
          (combined.openResult.outcome,
            combined.openResult.finalCtx) := by
    simpa [hCombinedEq] using hGuardRun
  obtain ⟨closed⟩ :=
    ScopedListResult.close combined
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact
        prepared.relation)
      hLayout hControl hSourceAfterBody
  obtain ⟨closedFuel, hClosedFuel, hClosedRun⟩ :=
    ClosedListResult.runBounded_of_open combined closed
  have hCombinedRequired :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      combined.openResult hGuardRun'
  have hBodyBound := bodyBounded.2
  dsimp [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded]
    at hBodyBound
  have hBodyMono :=
    FunctionsObserverFuel.executionBudgetFor_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmtList body)
      (by omega : listSourceFuel ≤ sourceFuel)
  have hBodyRequired :
      bodyResult.openResult.requiredFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmtList body) sourceFuel :=
    le_trans hBodyBound hBodyMono
  have hCombinedBudget :
      combined.openResult.requiredFuel ≤
        FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            hCondCost sourceFuel +
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList body) sourceFuel +
          3 :=
    le_trans hCombinedRequired (by omega)
  refine ⟨⟨closed, closedFuel, ?_, hClosedRun⟩⟩
  exact le_trans hClosedFuel hCombinedBudget

theorem closeLoopPost
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound sourceFuel compilerFuel : Nat}
    {bodyFinal postInitial postFinal final : Fresh.State}
    {layout : List Name}
    {post : List AstStmt}
    {lowerBody : List Functions.Stmt}
    {lowerPost : Functions.Block}
    {sourceAfterBody sourceAfterPost :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {bodyBase postBase : Functions.Source.Ctx}
    {canLeave : Bool}
    (hList :
      RecursiveOpenListForwardProgramBounded contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (bodyResult :
      ContinuingBodyResult contract codeRel targetProgram.toFunctions
        lowerBody bodyFinal layout sourceAfterBody target bodyBase)
    (hFuel : sourceFuel < bound)
    (hPostCost :
      FunctionsObserverStaticCost.stmtList post ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hPostOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout false false canLeave post =
        true)
    (hPostNames :
      StateRelation.Vars.NamesWithin postInitial.used
        (Stmt.List.names post))
    (hLowerPost :
      Stmt.List.toBlockUncheckedFuel? compilerFuel postInitial post =
        some (lowerPost, postFinal))
    (hFinalFresh : Fresh.Extends postFinal final)
    (hBodyScope :
      StateRelation.Vars.NamesWithin postInitial.used bodyBase.scope)
    (hPostScope :
      StateRelation.Vars.NamesWithin postInitial.used postBase.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin postInitial.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        false false canLeave postBase)
    (hPostRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block post) (some sourceProgram.contract)
          (sourceAfterBody.withSource sourceAfterBody.source.reviveJump) =
        .ok sourceAfterPost) :
    Nonempty
      { result :
          ClosedListResult contract codeRel targetProgram.toFunctions
            sourceControl lowerPost.stmts postInitial final layout
            sourceAfterPost bodyResult.outcome.state postBase //
        ClosedListResult.RunBounded
          (FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmtList post) sourceFuel)
          result } := by
  obtain ⟨listCompilerFuel, lowerPostStmts, _hBlockFuel,
      hLowerPostList, hLowerPostEq⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerPost
  subst lowerPost
  obtain ⟨listSourceFuel, sourceOpen, _hSourceFuel,
      hPostListRun, hSourceAfterPost⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hPostRun
  obtain ⟨postBounded⟩ :=
    hList (sourceFuel := listSourceFuel)
      (compilerFuel := listCompilerFuel)
      (before := postInitial) (after := postFinal)
      (layout := layout) (stmts := post)
      (lower := lowerPostStmts)
      (source :=
        sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
      (sourceFinal := sourceOpen)
      (target := bodyResult.outcome.state)
      (ctx := postBase)
      (canBreak := false) (canContinue := false)
      (canLeave := canLeave)
      (by omega) hPostCost hPostOk hPostNames hLowerPostList
      bodyResult.relation
      (bodyResult.targetDomain hBodyScope)
      hPostScope hLayout hControl hPostListRun
  let postResult := postBounded.1
  obtain ⟨closed⟩ :=
    ScopedListResult.close postResult
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact
        bodyResult.relation)
      hLayout hControl hSourceAfterPost
  obtain ⟨closedFuel, hClosedFuel, hClosedRun⟩ :=
    ClosedListResult.runBounded_of_open postResult closed
  let finalResult := closed.monoFresh hFinalFresh
  have hPostBound := postBounded.2
  dsimp [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded]
    at hPostBound
  have hPostMono :=
    FunctionsObserverFuel.executionBudgetFor_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmtList post)
      (by omega : listSourceFuel ≤ sourceFuel)
  refine ⟨⟨finalResult, closedFuel, ?_, ?_⟩⟩
  · exact le_trans hClosedFuel (le_trans hPostBound hPostMono)
  · exact hClosedRun

theorem scopedLoop
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hListOrdinary :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForwardProgramBounded contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    ∀ {sourceFuel compilerFuel : Nat}
      {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
      {before after afterCond afterPost : Fresh.State}
      {layout : List Name}
      {cond : AstExpr}
      {post body : List AstStmt}
      {preCond : List Functions.Stmt}
      {lowerCond : Locals.Expr 1}
      {lowerPost lowerBody : Functions.Block}
      {source sourceFinal :
        ObserverSemantics.SourceReplay.State transcript}
      {target : Functions.ObserverSemantics.State transcript}
      {ctx : Functions.Source.Ctx}
      {canBreak canContinue canLeave : Bool},
      sourceFuel < bound + 1 →
        FunctionsObserverStaticCost.expr cond ≤
          FunctionsObserverStaticCost.program sourceProgram →
        FunctionsObserverStaticCost.stmtList post ≤
          FunctionsObserverStaticCost.program sourceProgram →
        FunctionsObserverStaticCost.stmtList body ≤
          FunctionsObserverStaticCost.program sourceProgram →
        SolcValidation.ExprOk? profile sourceProgram.contract
            layout 1 cond =
          true →
        SolcValidation.StmtsOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout false false canLeave post =
          true →
        SolcValidation.StmtsOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            layout true true canLeave body =
          true →
        StateRelation.Vars.NamesWithin before.used
            (Expr.names cond) →
        StateRelation.Vars.NamesWithin before.used
            (Stmt.List.names post) →
        StateRelation.Vars.NamesWithin before.used
            (Stmt.List.names body) →
        Expr.lower1Unchecked? before cond =
          some (preCond, lowerCond, afterCond) →
        Stmt.List.toBlockUncheckedFuel? compilerFuel afterCond post =
          some (lowerPost, afterPost) →
        Stmt.List.toBlockUncheckedFuel? compilerFuel afterPost body =
          some (lowerBody, after) →
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
            sourceFuel (.For cond post body)
            (some sourceProgram.contract) source =
          .ok sourceFinal →
        Nonempty
          { result :
              ScopedLoopResult contract codeRel targetProgram.toFunctions
                sourceControl (.lit (EvmYul.UInt256.ofNat 1))
                ctx.withoutLoopControl lowerPost
                (ctx.withLoopControl ctx.scope ctx.scope)
                { stmts :=
                    preCond ++
                      .if_
                          (.prim .iszero
                            (Locals.ExprSeq.cons lowerCond .nil))
                          { stmts := [.brk] } ::
                        lowerBody.stmts }
                after layout sourceFinal target ctx.withoutLoopControl //
            ScopedLoopResult.ProgramBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              sourceFuel result } := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel sourceControl before after afterCond afterPost
        layout cond post body preCond lowerCond lowerPost lowerBody
        source sourceFinal target ctx canBreak canContinue canLeave
        hFuel hCondCost hPostCost hBodyCost hCondOk hPostOk hBodyOk
        hCondNames hPostNames hBodyNames hLowerCond hLowerPost hLowerBody
        hRel hDomain hScope hLayout hControl hRun
      obtain ⟨ordinaryLoop⟩ :=
        FunctionsObserverForward.RecursiveOpenCompoundForward.scopedLoop
          hValueOrdinary hListOrdinary
          (sourceFuel := sourceFuel) (compilerFuel := compilerFuel)
          (sourceControl := sourceControl)
          (before := before) (after := after)
          (afterCond := afterCond) (afterPost := afterPost)
          (layout := layout) (cond := cond) (post := post) (body := body)
          (preCond := preCond) (lowerCond := lowerCond)
          (lowerPost := lowerPost) (lowerBody := lowerBody)
          (source := source) (sourceFinal := sourceFinal)
          (target := target) (ctx := ctx)
          (canBreak := canBreak) (canContinue := canContinue)
          (canLeave := canLeave)
          hFuel hCondOk hPostOk hBodyOk hCondNames hPostNames hBodyNames
          hLowerCond hLowerPost hLowerBody hRel hDomain hScope hLayout
          hControl hRun
      obtain ⟨forFuel, hSourceFuel, hLoopRun⟩ :=
        Yul.Source.Effectful.exec_for_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      obtain ⟨iterationFuel, sourceAfterCond, condValue,
          hForFuel, hCondRun, hLoopCase⟩ :=
        Yul.Source.Effectful.loop_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hLoopRun
      obtain
          ⟨sourceShared, sourceVars, hSource,
            _hShared, _hScoped, _hSourceDomain⟩ :=
        hRel.2
      have hConditionInput :
          source.withSource
              (EvmYul.Yul.State.mkOk source.source) =
            source := by
        rw [hSource]
        change source.withSource (.Ok sourceShared sourceVars) = source
        rw [← hSource]
        exact Simulation.ResourceReplay.State.withSource_self source
      have hCondRun' :
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              iterationFuel cond (some sourceProgram.contract) source =
            .ok (sourceAfterCond, condValue) := by
        simpa [ObserverSemantics.SourceReplay.stateModel,
          hConditionInput] using hCondRun
      obtain ⟨values, hCondValues, hCondHead⟩ :=
        Yul.Source.Effectful.eval_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hCondRun'
      have hBodyBaseScope :
          StateRelation.Vars.NamesWithin before.used
            (ctx.withLoopControl ctx.scope ctx.scope).scope := by
        simpa [Functions.Source.Ctx.withLoopControl] using hScope
      obtain ⟨value, hValues, preparedNonempty⟩ :=
        hValue (exprFuel := iterationFuel)
          (before := before) (after := afterCond)
          (layout := layout) (expr := cond)
          (pre := preCond) (lower := lowerCond)
          (source := source) (source' := sourceAfterCond)
          (target := target)
          (ctx := ctx.withLoopControl ctx.scope ctx.scope)
          (values := values)
          (by omega) hCondCost hCondOk hLowerCond hRel hDomain
          hBodyBaseScope hCondValues
      obtain ⟨preparedBounded⟩ := preparedNonempty
      rcases preparedBounded with ⟨prepared, hPreparedBound⟩
      have hCondValue : condValue = value := by
        rw [hValues] at hCondHead
        simpa using hCondHead
      subst value
      have hCondFresh : Fresh.Extends before afterCond :=
        Expr.lower1Unchecked?_stateExtends hLowerCond
      have hPostFresh : Fresh.Extends afterCond afterPost :=
        Stmt.List.toBlockUncheckedFuel?_stateExtends hLowerPost
      have hBodyFresh : Fresh.Extends afterPost after :=
        Stmt.List.toBlockUncheckedFuel?_stateExtends hLowerBody
      have hFresh : Fresh.Extends before after :=
        Fresh.Extends.trans hCondFresh
          (Fresh.Extends.trans hPostFresh hBodyFresh)
      have hLayoutAfterPost :
          StateRelation.Vars.NamesWithin afterPost.used layout :=
        hLayout.mono (Fresh.Extends.trans hCondFresh hPostFresh)
      have hBodyNamesAfterPost :
          StateRelation.Vars.NamesWithin afterPost.used
            (Stmt.List.names body) :=
        hBodyNames.mono (Fresh.Extends.trans hCondFresh hPostFresh)
      have hPostNamesAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used
            (Stmt.List.names post) :=
        hPostNames.mono hCondFresh
      have hLayoutAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used layout :=
        hLayout.mono hCondFresh
      have hScopeAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used ctx.scope :=
        hScope.mono hCondFresh
      have hBodyControl :
          FunctionsObserverOutcome.ControlContextRel
            (FunctionsObserverOutcome.ControlContextRel.forBodySourceControl
              layout sourceControl)
            layout true true canLeave
            (ctx.withLoopControl ctx.scope ctx.scope) :=
        FunctionsObserverOutcome.ControlContextRel.forBody hControl
      have hPostControl :
          FunctionsObserverOutcome.ControlContextRel
            (FunctionsObserverOutcome.ControlContextRel.forPostSourceControl
              sourceControl)
            layout false false canLeave ctx.withoutLoopControl :=
        FunctionsObserverOutcome.ControlContextRel.forPost hControl
      have hCommonChild :=
        FunctionsObserverFuel.eight_executionBudgetsFor_add_eight_le_target_of_lt
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.program sourceProgram)
          (le_refl _) (by omega : iterationFuel < sourceFuel)
      have hCondToCommon :=
        FunctionsObserverFuel.executionBudgetFor_local_mono
          (FunctionsObserverStaticCost.program sourceProgram)
          iterationFuel hCondCost
      have hPostToCommon :=
        FunctionsObserverFuel.executionBudgetFor_local_mono
          (FunctionsObserverStaticCost.program sourceProgram)
          iterationFuel hPostCost
      have hBodyToCommon :=
        FunctionsObserverFuel.executionBudgetFor_local_mono
          (FunctionsObserverStaticCost.program sourceProgram)
          iterationFuel hBodyCost
      have hTargetBudget :=
        FunctionsObserverFuel.targetBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram) sourceFuel
      cases hLoopCase with
      | false hZero hFinal =>
          have hPreparedBreak :
              prepared.prepared.finalCtx.breakScope? =
                some ctx.scope := by
            rw [← prepared.prepared.control.breakScope]
            simp [Functions.Source.Ctx.withLoopControl]
          have hBodyRun :
              Functions.Source.Effectful.Block.runScoped
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (ctx.withLoopControl ctx.scope ctx.scope)
                  { stmts :=
                      preCond ++
                        .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBody.stmts }
                  (prepared.prepared.requiredFuel + 5) target =
                .ok
                  (Functions.Source.Effectful.Outcome.brk
                    (prepared.prepared.evalTarget.withSource
                      (prepared.prepared.evalTarget.source.restrictTo
                        ctx.scope))) := by
            simpa using
              Functions.Source.Effectful.Block.runScoped_forGuard_break_at_add_five
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (FunctionsObserverExpression.PreparedValue.run_requiredFuel
                    prepared.prepared)
                  prepared.prepared.eval
                  (Functions.ObserverSafety.SafeSemantics.eval_iszero
                    prepared.prepared.evalTarget condValue)
                  hZero hPreparedBreak
          have hLoop :
              Functions.Source.Effectful.Stmt.runForLoop
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions ctx.withoutLoopControl
                  (.lit (EvmYul.UInt256.ofNat 1))
                  ctx.withoutLoopControl lowerPost
                  (ctx.withLoopControl ctx.scope ctx.scope)
                  { stmts :=
                      preCond ++
                        .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBody.stmts }
                  (prepared.prepared.requiredFuel + 6) target =
                .ok
                  (Functions.Source.Effectful.Outcome.regular
                    (prepared.prepared.evalTarget.withSource
                      (prepared.prepared.evalTarget.source.restrictTo
                        ctx.scope))) :=
            Functions.Source.Effectful.Stmt.runForLoop_body_brk_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (Functions.ObserverSafety.SafeSemantics.evalCondition_one target)
              hBodyRun
          obtain ⟨ordinaryFuel, hOrdinary⟩ := ordinaryLoop.run
          have hOutcome :=
            Functions.Source.Effectful.Stmt.runForLoop_success_unique
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hLoop hOrdinary
          have hLoop' :
              Functions.Source.Effectful.Stmt.runForLoop
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions ctx.withoutLoopControl
                  (.lit (EvmYul.UInt256.ofNat 1))
                  ctx.withoutLoopControl lowerPost
                  (ctx.withLoopControl ctx.scope ctx.scope)
                  { stmts :=
                      preCond ++
                        .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBody.stmts }
                  (prepared.prepared.requiredFuel + 6) target =
                .ok ordinaryLoop.outcome := by
            simpa [hOutcome] using hLoop
          dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded]
            at hPreparedBound
          refine
            ⟨⟨ordinaryLoop, prepared.prepared.requiredFuel + 6, ?_,
              hLoop'⟩⟩
          omega
      | bodyOutOfFuel hNonzero hBody hBodySource hFinal =>
          rename_i afterBody
          obtain ⟨closedBodyBounded⟩ :=
            closeGuardedBody hList prepared
              (FunctionsObserverStaticCost.expr cond) hPreparedBound
              (by omega) hBodyCost hBodyOk hBodyNamesAfterPost
              hLowerBody hPostFresh hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          let closedBody := closedBodyBounded.1
          change afterBody.source = .OutOfFuel at hBodySource
          have hImpossible := closedBody.relation.mode
          rw [hBodySource] at hImpossible
          simp [FunctionsObserverOutcome.ModeRel] at hImpossible
      | bodyBreak hNonzero hBody hBodySource hFinal =>
          rename_i afterBody shared store
          obtain ⟨closedBodyBounded⟩ :=
            closeGuardedBody hList prepared
              (FunctionsObserverStaticCost.expr cond) hPreparedBound
              (by omega) hBodyCost hBodyOk hBodyNamesAfterPost
              hLowerBody hPostFresh hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          let closedBody := closedBodyBounded.1
          obtain ⟨bodyFuel, hBodyFuel, hClosedBody⟩ :=
            closedBodyBounded.2
          change
            afterBody.source = .Checkpoint (.Break shared store)
            at hBodySource
          have hMode :
              closedBody.outcome.mode = .brk := by
            have hModeRel := closedBody.relation.mode
            rw [hBodySource] at hModeRel
            exact
              FunctionsObserverOutcome.ModeRel.source_break_target_brk
                hModeRel
          have hOutcomeEq :
              closedBody.outcome =
                Functions.Source.Effectful.Outcome.brk
                  closedBody.outcome.state :=
            Functions.Source.Effectful.Outcome.eq_brk_of_mode hMode
          rw [hOutcomeEq] at hClosedBody
          have hLoop :=
            Functions.Source.Effectful.Stmt.runForLoop_body_brk_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (loopCtx := ctx.withoutLoopControl)
              (postBase := ctx.withoutLoopControl)
              (post := lowerPost)
              (Functions.ObserverSafety.SafeSemantics.evalCondition_one target)
              hClosedBody
          obtain ⟨ordinaryFuel, hOrdinary⟩ := ordinaryLoop.run
          have hOutcome :=
            Functions.Source.Effectful.Stmt.runForLoop_success_unique
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hLoop hOrdinary
          refine ⟨⟨ordinaryLoop, bodyFuel + 1, ?_, ?_⟩⟩
          · omega
          · simpa [hOutcome] using hLoop
      | bodyLeave hNonzero hBody hBodySource hFinal =>
          rename_i afterBody shared store
          obtain ⟨closedBodyBounded⟩ :=
            closeGuardedBody hList prepared
              (FunctionsObserverStaticCost.expr cond) hPreparedBound
              (by omega) hBodyCost hBodyOk hBodyNamesAfterPost
              hLowerBody hPostFresh hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          let closedBody := closedBodyBounded.1
          obtain ⟨bodyFuel, hBodyFuel, hClosedBody⟩ :=
            closedBodyBounded.2
          change
            afterBody.source = .Checkpoint (.Leave shared store)
            at hBodySource
          have hMode :
              closedBody.outcome.mode = .leave := by
            have hModeRel := closedBody.relation.mode
            rw [hBodySource] at hModeRel
            exact
              FunctionsObserverOutcome.ModeRel.source_leave_target_leave
                hModeRel
          have hOutcomeEq :
              closedBody.outcome =
                Functions.Source.Effectful.Outcome.leave
                  closedBody.outcome.state :=
            Functions.Source.Effectful.Outcome.eq_leave_of_mode hMode
          rw [hOutcomeEq] at hClosedBody
          have hLoop :=
            Functions.Source.Effectful.Stmt.runForLoop_body_leave_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (loopCtx := ctx.withoutLoopControl)
              (postBase := ctx.withoutLoopControl)
              (post := lowerPost)
              (Functions.ObserverSafety.SafeSemantics.evalCondition_one target)
              hClosedBody
          obtain ⟨ordinaryFuel, hOrdinary⟩ := ordinaryLoop.run
          have hOutcome :=
            Functions.Source.Effectful.Stmt.runForLoop_success_unique
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hLoop hOrdinary
          refine ⟨⟨ordinaryLoop, bodyFuel + 1, ?_, ?_⟩⟩
          · omega
          · simpa [hOutcome] using hLoop
      | postOutOfFuel hNonzero hBody hBodyContinues hPost
          hPostSource hFinal =>
          rename_i afterBody afterPostSource
          obtain ⟨closedBodyBounded⟩ :=
            closeGuardedBody hList prepared
              (FunctionsObserverStaticCost.expr cond) hPreparedBound
              (by omega) hBodyCost hBodyOk hBodyNamesAfterPost
              hLowerBody hPostFresh hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          let closedBody := closedBodyBounded.1
          obtain ⟨bodyResult⟩ :=
            ClosedListResult.continuingBody closedBody hBodyContinues rfl
          obtain ⟨closedPostBounded⟩ :=
            closeLoopPost hList bodyResult (by omega) hPostCost hPostOk
              hPostNamesAfterCond hLowerPost hBodyFresh
              (by
                simpa [Functions.Source.Ctx.withLoopControl] using
                  hScopeAfterCond)
              (by
                simpa [Functions.Source.Ctx.withoutLoopControl] using
                  hScopeAfterCond)
              hLayoutAfterCond hPostControl hPost
          let closedPost := closedPostBounded.1
          change afterPostSource.source = .OutOfFuel at hPostSource
          have hImpossible := closedPost.relation.mode
          rw [hPostSource] at hImpossible
          simp [FunctionsObserverOutcome.ModeRel] at hImpossible
      | postLeave hNonzero hBody hBodyContinues hPost
          hPostSource hFinal =>
          rename_i afterBody afterPostSource shared store
          obtain ⟨closedBodyBounded⟩ :=
            closeGuardedBody hList prepared
              (FunctionsObserverStaticCost.expr cond) hPreparedBound
              (by omega) hBodyCost hBodyOk hBodyNamesAfterPost
              hLowerBody hPostFresh hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          let closedBody := closedBodyBounded.1
          obtain ⟨bodyFuel, hBodyFuel, hClosedBody⟩ :=
            closedBodyBounded.2
          obtain ⟨bodyResult⟩ :=
            ClosedListResult.continuingBody closedBody hBodyContinues rfl
          obtain ⟨bodyWitnessFuel, hBodyWitness⟩ := bodyResult.run
          have hBodyOutcome :=
            Functions.Source.Effectful.Block.runScoped_success_unique
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hClosedBody hBodyWitness
          have hClosedBody' :
              Functions.Source.Effectful.Block.runScoped
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (ctx.withLoopControl ctx.scope ctx.scope)
                  { stmts :=
                      preCond ++
                        .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBody.stmts }
                  bodyFuel target =
                .ok bodyResult.outcome := by
            simpa [hBodyOutcome] using hClosedBody
          obtain ⟨closedPostBounded⟩ :=
            closeLoopPost hList bodyResult (by omega) hPostCost hPostOk
              hPostNamesAfterCond hLowerPost hBodyFresh
              (by
                simpa [Functions.Source.Ctx.withLoopControl] using
                  hScopeAfterCond)
              (by
                simpa [Functions.Source.Ctx.withoutLoopControl] using
                  hScopeAfterCond)
              hLayoutAfterCond hPostControl hPost
          let closedPost := closedPostBounded.1
          obtain ⟨postFuel, hPostFuel, hClosedPost⟩ :=
            closedPostBounded.2
          change
            afterPostSource.source = .Checkpoint (.Leave shared store)
            at hPostSource
          have hPostMode :
              closedPost.outcome.mode = .leave := by
            have hModeRel := closedPost.relation.mode
            rw [hPostSource] at hModeRel
            exact
              FunctionsObserverOutcome.ModeRel.source_leave_target_leave
                hModeRel
          have hPostEq :
              closedPost.outcome =
                Functions.Source.Effectful.Outcome.leave
                  closedPost.outcome.state :=
            Functions.Source.Effectful.Outcome.eq_leave_of_mode hPostMode
          rw [hPostEq] at hClosedPost
          have hClosedPostBlock :
              Functions.Source.Effectful.Block.runScoped
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions ctx.withoutLoopControl
                  lowerPost postFuel bodyResult.outcome.state =
                .ok
                  (Functions.Source.Effectful.Outcome.leave
                    closedPost.outcome.state) := by
            cases lowerPost
            exact hClosedPost
          let loopFuel := max bodyFuel postFuel
          have hBody' :=
            Functions.Source.Effectful.Block.runScoped_mono
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (fuel' := loopFuel)
              (by simp [loopFuel])
              hClosedBody'
          have hPost' :=
            Functions.Source.Effectful.Block.runScoped_mono
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (fuel' := loopFuel)
              (by simp [loopFuel])
              hClosedPostBlock
          have hLoop :
              Functions.Source.Effectful.Stmt.runForLoop
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions ctx.withoutLoopControl
                  (.lit (EvmYul.UInt256.ofNat 1))
                  ctx.withoutLoopControl lowerPost
                  (ctx.withLoopControl ctx.scope ctx.scope)
                  { stmts :=
                      preCond ++
                        .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBody.stmts }
                  (loopFuel + 1) target =
                .ok
                  (Functions.Source.Effectful.Outcome.leave
                    closedPost.outcome.state) := by
            rcases bodyResult.mode with hRegular | hContinue
            · have hBodyEq :
                  bodyResult.outcome =
                    Functions.Source.Effectful.Outcome.regular
                      bodyResult.outcome.state :=
                Functions.Source.Effectful.Outcome.eq_regular_of_mode
                  hRegular
              rw [hBodyEq] at hBody'
              exact
                Functions.Source.Effectful.Stmt.runForLoop_regular_post_leave_of_runs
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions
                    (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                      target)
                    hBody' hPost'
            · have hBodyEq :
                  bodyResult.outcome =
                    Functions.Source.Effectful.Outcome.cont
                      bodyResult.outcome.state :=
                Functions.Source.Effectful.Outcome.eq_cont_of_mode
                  hContinue
              rw [hBodyEq] at hBody'
              exact
                Functions.Source.Effectful.Stmt.runForLoop_cont_post_leave_of_runs
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions
                    (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                      target)
                    hBody' hPost'
          obtain ⟨ordinaryFuel, hOrdinary⟩ := ordinaryLoop.run
          have hOutcome :=
            Functions.Source.Effectful.Stmt.runForLoop_success_unique
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hLoop hOrdinary
          refine ⟨⟨ordinaryLoop, loopFuel + 1, ?_, ?_⟩⟩
          · omega
          · simpa [hOutcome] using hLoop
      | recurse hNonzero hBody hBodyContinues hPost hPostRecurs
          hRecursive hFinal =>
          rename_i afterBody sourceAfterPost afterLoop
          obtain ⟨closedBodyBounded⟩ :=
            closeGuardedBody hList prepared
              (FunctionsObserverStaticCost.expr cond) hPreparedBound
              (by omega) hBodyCost hBodyOk hBodyNamesAfterPost
              hLowerBody hPostFresh hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          let closedBody := closedBodyBounded.1
          obtain ⟨bodyFuel, hBodyFuel, hClosedBody⟩ :=
            closedBodyBounded.2
          obtain ⟨bodyResult⟩ :=
            ClosedListResult.continuingBody closedBody hBodyContinues rfl
          obtain ⟨bodyWitnessFuel, hBodyWitness⟩ := bodyResult.run
          have hBodyOutcome :=
            Functions.Source.Effectful.Block.runScoped_success_unique
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hClosedBody hBodyWitness
          have hClosedBody' :
              Functions.Source.Effectful.Block.runScoped
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (ctx.withLoopControl ctx.scope ctx.scope)
                  { stmts :=
                      preCond ++
                        .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBody.stmts }
                  bodyFuel target =
                .ok bodyResult.outcome := by
            simpa [hBodyOutcome] using hClosedBody
          obtain ⟨closedPostBounded⟩ :=
            closeLoopPost hList bodyResult (by omega) hPostCost hPostOk
              hPostNamesAfterCond hLowerPost hBodyFresh
              (by
                simpa [Functions.Source.Ctx.withLoopControl] using
                  hScopeAfterCond)
              (by
                simpa [Functions.Source.Ctx.withoutLoopControl] using
                  hScopeAfterCond)
              hLayoutAfterCond hPostControl hPost
          let closedPost := closedPostBounded.1
          obtain ⟨postFuel, hPostFuel, hClosedPost⟩ :=
            closedPostBounded.2
          cases hSourcePost : sourceAfterPost.source with
          | OutOfFuel =>
              change
                Yul.Source.Effectful.LoopPostRecurs sourceAfterPost.source
                at hPostRecurs
              rw [hSourcePost] at hPostRecurs
              simp [Yul.Source.Effectful.LoopPostRecurs] at hPostRecurs
          | Checkpoint jump =>
              cases jump with
              | Leave shared store =>
                  change
                    Yul.Source.Effectful.LoopPostRecurs
                      sourceAfterPost.source at hPostRecurs
                  rw [hSourcePost] at hPostRecurs
                  simp [Yul.Source.Effectful.LoopPostRecurs]
                    at hPostRecurs
              | Break shared store =>
                  have hMode :
                      closedPost.outcome.mode = .brk := by
                    have hModeRel := closedPost.relation.mode
                    rw [hSourcePost] at hModeRel
                    exact
                      FunctionsObserverOutcome.ModeRel.source_break_target_brk
                        hModeRel
                  have hExit := closedPost.exitScope
                  simp [FunctionsObserverOutcome.ExitScopeRel,
                    FunctionsObserverOutcome.ControlContextRel.forPostSourceControl,
                    hMode] at hExit
              | Continue shared store =>
                  have hMode :
                      closedPost.outcome.mode = .cont := by
                    have hModeRel := closedPost.relation.mode
                    rw [hSourcePost] at hModeRel
                    exact
                      FunctionsObserverOutcome.ModeRel.source_continue_target_cont
                        hModeRel
                  have hExit := closedPost.exitScope
                  simp [FunctionsObserverOutcome.ExitScopeRel,
                    FunctionsObserverOutcome.ControlContextRel.forPostSourceControl,
                    hMode] at hExit
          | Ok postShared postStore =>
              have hPostMode :
                  closedPost.outcome.mode = .regular := by
                have hModeRel := closedPost.relation.mode
                rw [hSourcePost] at hModeRel
                exact
                  FunctionsObserverOutcome.ModeRel.source_ok_target_regular
                    hModeRel
              have hPostEq :
                  closedPost.outcome =
                    Functions.Source.Effectful.Outcome.regular
                      closedPost.outcome.state :=
                Functions.Source.Effectful.Outcome.eq_regular_of_mode
                  hPostMode
              rw [hPostEq] at hClosedPost
              have hClosedPostBlock :
                  Functions.Source.Effectful.Block.runScoped
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      lowerPost postFuel bodyResult.outcome.state =
                    .ok
                      (Functions.Source.Effectful.Outcome.regular
                        closedPost.outcome.state) := by
                cases lowerPost
                exact hClosedPost
              have hPostRel :
                  StateRelation.Replay.ScopedExactRel codeRel layout
                    sourceAfterPost closedPost.outcome.state := by
                have hExact := closedPost.relation.exact hPostMode
                have hLayoutEq := closedPost.regularLayout hPostMode
                have hRevived :
                    sourceAfterPost.withSource
                        sourceAfterPost.source.reviveJump =
                      sourceAfterPost := by
                  rw [hSourcePost]
                  change
                    sourceAfterPost.withSource
                        (.Ok postShared postStore) =
                      sourceAfterPost
                  rw [← hSourcePost]
                  exact
                    Simulation.ResourceReplay.State.withSource_self
                      sourceAfterPost
                rw [hRevived] at hExact
                simpa [hLayoutEq] using hExact
              have hPostDomain :
                  StateRelation.Vars.TargetDomainWithin before.used
                    closedPost.outcome.state.source.vars := by
                have hRestricted := closedPost.targetRestriction
                simp [FunctionsObserverOutcome.ScopedTargetRestriction,
                  hPostMode] at hRestricted
                exact
                  hRestricted.domain
                    (by
                      simpa [Functions.Source.Ctx.withoutLoopControl] using
                        hScope)
              have hRecursiveInput :
                  sourceAfterPost.withSource
                      (sourceAfterPost.source.overwrite? source.source) =
                    sourceAfterPost := by
                rw [hSourcePost, hSource]
                change
                  sourceAfterPost.withSource
                      (.Ok postShared postStore) =
                    sourceAfterPost
                rw [← hSourcePost]
                exact
                  Simulation.ResourceReplay.State.withSource_self
                    sourceAfterPost
              have hRecursive' :
                  Yul.Source.Effectful.exec
                      (ObserverSemantics.SourceReplay.stateModel transcript)
                      (ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      iterationFuel (.For cond post body)
                      (some sourceProgram.contract) sourceAfterPost =
                    .ok afterLoop := by
                simpa [ObserverSemantics.SourceReplay.stateModel,
                  hRecursiveInput] using hRecursive
              obtain ⟨recursiveBounded⟩ :=
                ih iterationFuel (by omega)
                  (compilerFuel := compilerFuel)
                  (sourceControl := sourceControl)
                  (before := before) (after := after)
                  (afterCond := afterCond) (afterPost := afterPost)
                  (layout := layout) (cond := cond)
                  (post := post) (body := body)
                  (preCond := preCond) (lowerCond := lowerCond)
                  (lowerPost := lowerPost) (lowerBody := lowerBody)
                  (source := sourceAfterPost)
                  (sourceFinal := afterLoop)
                  (target := closedPost.outcome.state)
                  (ctx := ctx)
                  (canBreak := canBreak)
                  (canContinue := canContinue) (canLeave := canLeave)
                  (by omega) hCondCost hPostCost hBodyCost
                  hCondOk hPostOk hBodyOk hCondNames hPostNames hBodyNames
                  hLowerCond hLowerPost hLowerBody hPostRel hPostDomain
                  hScope hLayout hControl hRecursive'
              let recursive := recursiveBounded.1
              obtain ⟨recursiveFuel, hRecursiveFuel, hRecursiveRun⟩ :=
                recursiveBounded.2
              let loopFuel := max bodyFuel (max postFuel recursiveFuel)
              have hBody' :=
                Functions.Source.Effectful.Block.runScoped_mono
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (fuel' := loopFuel)
                  (by simp [loopFuel])
                  hClosedBody'
              have hPost' :=
                Functions.Source.Effectful.Block.runScoped_mono
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (fuel' := loopFuel)
                  (by simp [loopFuel])
                  hClosedPostBlock
              have hRecursiveRun' :=
                Functions.Source.Effectful.Stmt.runForLoop_mono
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (fuel' := loopFuel)
                  (by simp [loopFuel])
                  hRecursiveRun
              have hLoop :
                  Functions.Source.Effectful.Stmt.runForLoop
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      (.lit (EvmYul.UInt256.ofNat 1))
                      ctx.withoutLoopControl lowerPost
                      (ctx.withLoopControl ctx.scope ctx.scope)
                      { stmts :=
                          preCond ++
                            .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                      (loopFuel + 1) target =
                    .ok recursive.outcome := by
                rcases bodyResult.mode with hRegular | hContinue
                · have hBodyEq :
                      bodyResult.outcome =
                        Functions.Source.Effectful.Outcome.regular
                          bodyResult.outcome.state :=
                    Functions.Source.Effectful.Outcome.eq_regular_of_mode
                      hRegular
                  rw [hBodyEq] at hBody'
                  exact
                    Functions.Source.Effectful.Stmt.runForLoop_regular_post_recurse_of_runs
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (loopCtx := ctx.withoutLoopControl)
                        (postBase := ctx.withoutLoopControl)
                        (post := lowerPost)
                        (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                          target)
                        hBody' hPost' hRecursiveRun'
                · have hBodyEq :
                      bodyResult.outcome =
                        Functions.Source.Effectful.Outcome.cont
                          bodyResult.outcome.state :=
                    Functions.Source.Effectful.Outcome.eq_cont_of_mode
                      hContinue
                  rw [hBodyEq] at hBody'
                  exact
                    Functions.Source.Effectful.Stmt.runForLoop_cont_post_recurse_of_runs
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (loopCtx := ctx.withoutLoopControl)
                        (postBase := ctx.withoutLoopControl)
                        (post := lowerPost)
                        (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                          target)
                        hBody' hPost' hRecursiveRun'
              obtain ⟨ordinaryFuel, hOrdinary⟩ := ordinaryLoop.run
              have hOutcome :=
                Functions.Source.Effectful.Stmt.runForLoop_success_unique
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions hLoop hOrdinary
              refine ⟨⟨ordinaryLoop, loopFuel + 1, ?_, ?_⟩⟩
              · have hRecursiveToCommon :=
                  FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
                      (FunctionsObserverStaticCost.program sourceProgram)
                      (FunctionsObserverStaticCost.program sourceProgram)
                      iterationFuel
                omega
              · simpa [hOutcome] using hLoop

theorem forLoop
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
    {post body : List AstStmt}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hListOrdinary :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hCost :
      FunctionsObserverStaticCost.stmt (.For cond post body) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave (.For cond post body) =
        true)
    (hNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.names (.For cond post body)))
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.For cond post body) =
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
          sourceFuel (.For cond post body)
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.For cond post body) lower before after layout sourceFinal target
            ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.For cond post body))
          sourceFuel result.openResult } := by
  have hFresh : Fresh.Extends before after :=
    Stmt.toFunctionsListUncheckedFuel?_stateExtends hLower
  obtain
      ⟨compilerPrevious, preCond, lowerCond, afterCond,
        lowerPost, afterPost, lowerBody, _hCompilerFuel,
        hLowerCond, hLowerPost, hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_for_parts hLower
  subst lower
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  have hCondNames :
      StateRelation.Vars.NamesWithin before.used
        (Expr.names cond) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hPostNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names post) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hCostParts := hCost
  simp only [FunctionsObserverStaticCost.stmt] at hCostParts
  have hCondCost :
      FunctionsObserverStaticCost.expr cond ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    omega
  have hMaxCost :
      max (FunctionsObserverStaticCost.stmtList post)
          (FunctionsObserverStaticCost.stmtList body) ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    exact
      (Nat.le_add_left
        (max (FunctionsObserverStaticCost.stmtList post)
          (FunctionsObserverStaticCost.stmtList body))
        (FunctionsObserverStaticCost.expr cond)).trans
        ((Nat.le_add_right
          (FunctionsObserverStaticCost.expr cond +
            max (FunctionsObserverStaticCost.stmtList post)
              (FunctionsObserverStaticCost.stmtList body))
          6).trans hCostParts)
  have hPostCost :
      FunctionsObserverStaticCost.stmtList post ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    exact (Nat.le_max_left _ _).trans hMaxCost
  have hBodyCost :
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    exact (Nat.le_max_right _ _).trans hMaxCost
  obtain ⟨loopBounded⟩ :=
    scopedLoop hValueOrdinary hListOrdinary hValue hList
      (sourceFuel := sourceFuel) (compilerFuel := compilerPrevious)
      (sourceControl := sourceControl)
      (before := before) (after := after)
      (afterCond := afterCond) (afterPost := afterPost)
      (layout := layout) (cond := cond) (post := post) (body := body)
      (preCond := preCond) (lowerCond := lowerCond)
      (lowerPost := lowerPost) (lowerBody := lowerBody)
      (source := source) (sourceFinal := sourceFinal)
      (target := target) (ctx := ctx)
      (canBreak := canBreak) (canContinue := canContinue)
      (canLeave := canLeave)
      hFuel hCondCost hPostCost hBodyCost
      hOkParts.1 hOkParts.2.1 hOkParts.2.2
      hCondNames hPostNames hBodyNames hLowerCond hLowerPost hLowerBody
      hRel hDomain hScope hLayout hControl hRun
  let loop := loopBounded.1
  obtain ⟨opened⟩ :=
    ScopedLoopResult.toOpen loop hFresh (hScope.mono hFresh) hControl
  let result :=
    ScopedStmtResult.ofOpen
      (stmt := .For cond post body) opened.1
      (by
        intro hRegular
        simpa [SolcValidation.StmtOutVars] using opened.2 hRegular)
      hControl
  obtain ⟨loopFuel, hLoopFuel, hLoopRun⟩ := loopBounded.2
  have hOpenedFuel :=
    ScopedLoopResult.toOpen_requiredFuel_le_of_run
      loop hLoopRun opened.1
  have hParent :=
    FunctionsObserverFuel.targetBudgetFor_add_localCost_le_executionBudgetFor
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmt (.For cond post body))
      sourceFuel
  have hWrapper :
      4 ≤ FunctionsObserverStaticCost.stmt (.For cond post body) := by
    simp [FunctionsObserverStaticCost.stmt]
  refine ⟨⟨result, ?_⟩⟩
  change
    opened.1.requiredFuel ≤
      FunctionsObserverFuel.executionBudgetFor
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.stmt (.For cond post body))
        sourceFuel
  omega

theorem block
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
    {body : List AstStmt}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hList :
      RecursiveOpenListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hCost :
      FunctionsObserverStaticCost.stmt (.Block body) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave (.Block body) =
        true)
    (hNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.names (.Block body)))
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before (.Block body) =
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
          sourceFuel (.Block body) (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.Block body) lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.Block body))
          sourceFuel result.openResult } := by
  obtain ⟨compilerPrevious, lowerBody, _hCompilerFuel,
      hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_block_parts hLower
  subst lower
  obtain ⟨listCompilerFuel, lowerStmts, _hBlockFuel,
      hLowerList, hLowerBodyEq⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  subst lowerBody
  obtain ⟨sourcePrevious, sourceAfterBody, hSourceFuel,
      hBodyRun, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  change
    sourceFinal =
      sourceAfterBody.withSource
        (sourceAfterBody.source.restrictStoreTo source.source.store)
    at hSourceFinal
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
  have hBodyCost :
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    simp only [FunctionsObserverStaticCost.stmt] at hCost
    omega
  obtain ⟨bodyBounded⟩ :=
    hList (sourceFuel := sourcePrevious)
      (compilerFuel := listCompilerFuel)
      (before := before) (after := after)
      (layout := layout) (stmts := body) (lower := lowerStmts)
      (source := source) (sourceFinal := sourceAfterBody)
      (target := target) (ctx := ctx)
      (canBreak := canBreak) (canContinue := canContinue)
      (canLeave := canLeave)
      (by omega) hBodyCost hBodyOk hBodyNames hLowerList hRel hDomain
      hScope hLayout hControl hBodyRun
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_block
      bodyBounded.1.openResult
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel)
      hScope hLayout hControl hSourceFinal
  let statementResult := ScopedStmtResult.ofStatement result hControl
  obtain ⟨_hScoped, _hClosedCtx, hClosedFuel⟩ :=
    FunctionsObserverOutcome.ScopedOpenResult.singletonBlock_requiredFuel_parts
      bodyBounded.1.openResult result.openResult
  have hChild :=
    FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmtList body)
      hBodyCost (by omega : sourcePrevious < sourceFuel)
  have hParent :=
    FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmt (.Block body))
      sourceFuel
  have hBodyBound := bodyBounded.2
  refine ⟨⟨statementResult, ?_⟩⟩
  change
    result.openResult.requiredFuel ≤
      FunctionsObserverFuel.executionBudgetFor
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.stmt (.Block body))
        sourceFuel
  dsimp [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded]
    at hBodyBound
  omega

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
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hExprOrdinary :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hListOrdinary :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hExpr :
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hCost :
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
          sourceFuel (.If cond body) (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.If cond body) lower before after layout sourceFinal target ctx
            canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.If cond body))
          sourceFuel result.openResult } := by
  obtain ⟨ordinary⟩ :=
    FunctionsObserverForward.RecursiveOpenCompoundForward.ifThen
      hExprOrdinary hListOrdinary hFuel hOk hNames hLower hRel hDomain
      hScope hLayout hControl hRun
  obtain
      ⟨compilerPrevious, preCond, lowerCond, middle, lowerBody,
        _hCompilerFuel, hLowerCond, hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_if_parts hLower
  subst lower
  obtain
      ⟨sourcePrevious, sourceAfterCond, condValue,
        hSourceFuel, hCondRun, hBranch⟩ :=
    Yul.Source.Effectful.exec_if_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
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
    Stmt.List.toBlockUncheckedFuel?_stateExtends hLowerBody
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
  have hCostParts := hCost
  simp only [FunctionsObserverStaticCost.stmt] at hCostParts
  have hCondCost :
      FunctionsObserverStaticCost.expr cond ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    omega
  have hBlockCost :
      FunctionsObserverStaticCost.stmt (.Block body) ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    simp only [FunctionsObserverStaticCost.stmt]
    omega
  obtain ⟨preparedBounded⟩ :=
    hExpr (exprFuel := sourcePrevious)
      (before := before) (after := middle)
      (layout := layout) (expr := cond)
      (pre := preCond) (lower := lowerCond)
      (source := source) (source' := sourceAfterCond)
      (target := target) (ctx := ctx) (value := condValue)
      (by omega) hCondCost hOkParts.1 hLowerCond hRel hDomain hScope
      hCondRun
  rcases preparedBounded with ⟨prepared, hPreparedBound⟩
  have hPreRun :=
    FunctionsObserverExpression.PreparedValue.run_requiredFuel
      prepared.prepared
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
  cases hBranch with
  | inr hFalse =>
      obtain ⟨hZero, hSourceFinal⟩ := hFalse
      subst sourceFinal
      have hCondFalse :
          Functions.Source.Effectful.Expr.evalCondition
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              lowerCond prepared.prepared.preTarget =
            .ok (prepared.prepared.evalTarget, false) :=
        Functions.Source.Effectful.Expr.evalCondition_false_of_eval_singleton
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          prepared.prepared.eval hZero
      have hIfStmt :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx 1
              (.if_ lowerCond lowerBody) prepared.prepared.preTarget =
            .ok
              (Functions.Source.Effectful.Outcome.regular
                prepared.prepared.evalTarget,
                prepared.prepared.finalCtx) :=
        Functions.Source.Effectful.Stmt.run_if_false_of_eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hCondFalse
      have hIfRun :=
        Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hIfStmt
      have hTargetRun :=
        Functions.Source.Effectful.Block.runOpen_append_regular_at_add
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions preCond [.if_ lowerCond lowerBody]
          ctx prepared.prepared.finalCtx target
          prepared.prepared.preTarget
          (Functions.Source.Effectful.Outcome.regular
            prepared.prepared.evalTarget)
          prepared.prepared.finalCtx
          prepared.prepared.requiredFuel (1 + 2)
          hPreRun hIfRun
      have hRequired :=
        FunctionsObserverFuel.ScopedOpenResult.requiredFuel_le_of_successful_run
          ordinary.openResult hTargetRun
      have hChild :=
        FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.expr cond)
          hCondCost (by omega : sourcePrevious < sourceFuel)
      have hParent :=
        FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.If cond body))
          sourceFuel
      refine ⟨⟨ordinary, ?_⟩⟩
      change
        ordinary.openResult.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmt (.If cond body))
            sourceFuel
      dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded]
        at hPreparedBound
      omega
  | inl hTrue =>
      obtain ⟨hNonzero, hBodyRun⟩ := hTrue
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
      have hBlockOk :
          SolcValidation.StmtOk? profile sourceProgram.contract
              ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
              layout canBreak canContinue canLeave (.Block body) =
            true := by
        simpa [SolcValidation.StmtOk?] using hOkParts.2
      have hBlockNames :
          StateRelation.Vars.NamesWithin middle.used
            (Stmt.names (.Block body)) := by
        simpa [Stmt.names] using hBodyNamesMiddle
      have hBlockLower :
          Stmt.toFunctionsListUncheckedFuel? (compilerPrevious + 1)
              middle (.Block body) =
            some ([.block lowerBody], after) :=
        Stmt.toFunctionsListUncheckedFuel?_block_of_toBlock hLowerBody
      obtain ⟨closedBounded⟩ :=
        block hList (sourceFuel := sourcePrevious)
          (compilerFuel := compilerPrevious + 1)
          (before := middle) (after := after)
          (layout := layout) (body := body)
          (lower := [.block lowerBody])
          (source := sourceAfterCond) (sourceFinal := sourceFinal)
          (target := prepared.prepared.evalTarget)
          (ctx := prepared.prepared.finalCtx)
          (canBreak := canBreak) (canContinue := canContinue)
          (canLeave := canLeave)
          (by omega) hBlockCost hBlockOk hBlockNames hBlockLower
          prepared.relation prepared.prepared.domain
          prepared.prepared.scope hLayoutMiddle hPreparedControl hBodyRun
      rcases closedBounded with ⟨closedBody, hClosedBound⟩
      obtain ⟨hBodyScoped, _hBodyCtx⟩ :=
        Functions.Source.Effectful.Block.runScoped_at_of_runOpen_singleton_block
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
            closedBody.openResult)
      have hIfStmt :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx
              (closedBody.openResult.requiredFuel + 1)
              (.if_ lowerCond lowerBody) prepared.prepared.preTarget =
            .ok
              (closedBody.openResult.outcome,
                prepared.prepared.finalCtx) :=
        Functions.Source.Effectful.Stmt.run_if_true_of_eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hCondTrue hBodyScoped
      have hIfRun :=
        Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hIfStmt
      have hTargetRun :=
        Functions.Source.Effectful.Block.runOpen_append_regular_at_add
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions preCond [.if_ lowerCond lowerBody]
          ctx prepared.prepared.finalCtx target
          prepared.prepared.preTarget closedBody.openResult.outcome
          prepared.prepared.finalCtx
          prepared.prepared.requiredFuel
          (closedBody.openResult.requiredFuel + 1 + 2)
          hPreRun hIfRun
      have hRequired :=
        FunctionsObserverFuel.ScopedOpenResult.requiredFuel_le_of_successful_run
          ordinary.openResult hTargetRun
      have hChildren :=
        FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.expr cond)
          (FunctionsObserverStaticCost.stmt (.Block body))
          hCondCost hBlockCost
          (by omega : sourcePrevious < sourceFuel)
          (by omega : sourcePrevious < sourceFuel)
      have hParent :=
        FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.If cond body))
          sourceFuel
      refine ⟨⟨ordinary, ?_⟩⟩
      change
        ordinary.openResult.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmt (.If cond body))
            sourceFuel
      dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded]
        at hPreparedBound
      dsimp [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded]
        at hClosedBound
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
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hExprOrdinary :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hListOrdinary :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hExpr :
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
    (hCost :
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
        .ok sourceFinal) :
    Nonempty
      { result :
          ScopedStmtResult contract codeRel targetProgram.toFunctions
            (.Switch scrutinee cases defaultBody) lower before after layout
            sourceFinal target ctx canBreak canContinue canLeave
            (sourceControl := sourceControl) //
        FunctionsObserverFuel.ScopedOpenResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Switch scrutinee cases defaultBody))
          sourceFuel result.openResult } := by
  obtain ⟨ordinary⟩ :=
    FunctionsObserverForward.RecursiveOpenCompoundForward.switch
      hExprOrdinary hListOrdinary hFuel hOk hNames hLower hRel hDomain
      hScope hLayout hControl hRun
  obtain
      ⟨compilerPrevious, preScrutinee, lowerScrutinee,
        afterScrutinee, lowerCases, afterCases, lowerDefault,
        _hCompilerFuel, hLowerScrutinee, hLowerCases,
        hLowerDefault, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_switch_parts hLower
  subst lower
  obtain
      ⟨sourcePrevious, sourceAfterScrutinee, value,
        hSourceFuel, hScrutineeRun, hSelectedRun⟩ :=
    Yul.Source.Effectful.exec_switch_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  have hScrutineeFresh : Fresh.Extends before afterScrutinee :=
    Expr.lower1Unchecked?_stateExtends hLowerScrutinee
  have hSelection :=
    Stmt.SwitchSelectionLowering.of_compilers
      (value := value) hLowerCases hLowerDefault
  have hSelectionFresh : Fresh.Extends afterScrutinee after :=
    hSelection.freshExtends
  have hCostParts := hCost
  simp only [FunctionsObserverStaticCost.stmt] at hCostParts
  have hScrutineeCost :
      FunctionsObserverStaticCost.expr scrutinee ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    omega
  obtain ⟨preparedBounded⟩ :=
    hExpr (exprFuel := sourcePrevious)
      (before := before) (after := afterScrutinee)
      (layout := layout) (expr := scrutinee)
      (pre := preScrutinee) (lower := lowerScrutinee)
      (source := source) (source' := sourceAfterScrutinee)
      (target := target) (ctx := ctx) (value := value)
      (by omega) hScrutineeCost hOkParts.1 hLowerScrutinee hRel hDomain
      hScope hScrutineeRun
  rcases preparedBounded with ⟨prepared, hPreparedBound⟩
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
  | none hSourceSelection hTargetSelection _hSelectionFresh =>
      have hSwitchStmt :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx 1
              (.switch lowerScrutinee lowerCases lowerDefault)
              prepared.prepared.preTarget =
            .ok
              (Functions.Source.Effectful.Outcome.regular
                prepared.prepared.evalTarget,
                prepared.prepared.finalCtx) :=
        Functions.Source.Effectful.Stmt.run_switch_none_of_eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hEvalOne hTargetSelection
      have hSwitchRun :=
        Functions.Source.Effectful.Block.runOpen_singleton_of_run_at_add_two
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hSwitchStmt
      have hTargetRun :=
        Functions.Source.Effectful.Block.runOpen_append_regular_at_add
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions preScrutinee
          [.switch lowerScrutinee lowerCases lowerDefault]
          ctx prepared.prepared.finalCtx target
          prepared.prepared.preTarget
          (Functions.Source.Effectful.Outcome.regular
            prepared.prepared.evalTarget)
          prepared.prepared.finalCtx
          prepared.prepared.requiredFuel (1 + 2)
          hPreRun hSwitchRun
      have hRequired :=
        FunctionsObserverFuel.ScopedOpenResult.requiredFuel_le_of_successful_run
          ordinary.openResult hTargetRun
      have hChild :=
        FunctionsObserverFuel.executionBudgetFor_add_eight_le_target_of_lt
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.expr scrutinee)
          hScrutineeCost (by omega : sourcePrevious < sourceFuel)
      have hParent :=
        FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Switch scrutinee cases defaultBody))
          sourceFuel
      refine ⟨⟨ordinary, ?_⟩⟩
      change
        ordinary.openResult.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmt
              (.Switch scrutinee cases defaultBody))
            sourceFuel
      dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded]
        at hPreparedBound
      omega
  | some hSourceSelection hTargetSelection hSelectedLower
      hBeforeSelected hAfterSelected =>
      rename_i selectedBody selectedLowerBody selectedCompilerFuel
        selectedBefore selectedAfter
      rw [hSourceSelection] at hSelectedRun
      have hSelectedOk :
          SolcValidation.StmtsOk? profile sourceProgram.contract
              ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
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
                (EvmYul.Yul.selectSwitchCase value defaultBody cases) := by
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
              ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
              layout canBreak canContinue canLeave
                (.Block selectedBody) =
            true := by
        simpa [SolcValidation.StmtOk?] using hSelectedOk
      have hBlockNames :
          StateRelation.Vars.NamesWithin selectedBefore.used
            (Stmt.names (.Block selectedBody)) := by
        simpa [Stmt.names] using hSelectedNames
      have hBlockLower :=
        Stmt.toFunctionsListUncheckedFuel?_block_of_toBlock hSelectedLower
      have hSelectedListCost :=
        FunctionsObserverStaticCost.stmtList_selectSwitchCase_le_max
          value defaultBody cases
      rw [hSourceSelection] at hSelectedListCost
      have hSelectedBlockCost :
          FunctionsObserverStaticCost.stmt (.Block selectedBody) ≤
            FunctionsObserverStaticCost.program sourceProgram := by
        simp only [FunctionsObserverStaticCost.stmt]
        omega
      obtain ⟨closedBounded⟩ :=
        block hList (sourceFuel := sourcePrevious)
          (compilerFuel := selectedCompilerFuel + 1)
          (before := selectedBefore) (after := selectedAfter)
          (layout := layout)
          (body := selectedBody)
          (lower := [.block selectedLowerBody])
          (source := sourceAfterScrutinee) (sourceFinal := sourceFinal)
          (target := prepared.prepared.evalTarget)
          (ctx := prepared.prepared.finalCtx)
          (canBreak := canBreak) (canContinue := canContinue)
          (canLeave := canLeave)
          (by omega) hSelectedBlockCost hBlockOk hBlockNames hBlockLower
          prepared.relation
          (prepared.prepared.domain.mono hBeforeSelected)
          (prepared.prepared.scope.mono hBeforeSelected)
          hSelectedLayout hPreparedControl hSelectedRun
      rcases closedBounded with ⟨closedBody, hClosedBound⟩
      obtain ⟨hBodyScoped, _hBodyCtx⟩ :=
        Functions.Source.Effectful.Block.runScoped_at_of_runOpen_singleton_block
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
            closedBody.openResult)
      have hSwitchStmt :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx
              (closedBody.openResult.requiredFuel + 1)
              (.switch lowerScrutinee lowerCases lowerDefault)
              prepared.prepared.preTarget =
            .ok
              (closedBody.openResult.outcome,
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
      have hTargetRun :=
        Functions.Source.Effectful.Block.runOpen_append_regular_at_add
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions preScrutinee
          [.switch lowerScrutinee lowerCases lowerDefault]
          ctx prepared.prepared.finalCtx target
          prepared.prepared.preTarget closedBody.openResult.outcome
          prepared.prepared.finalCtx
          prepared.prepared.requiredFuel
          (closedBody.openResult.requiredFuel + 1 + 2)
          hPreRun hSwitchRun
      have hRequired :=
        FunctionsObserverFuel.ScopedOpenResult.requiredFuel_le_of_successful_run
          ordinary.openResult hTargetRun
      have hChildren :=
        FunctionsObserverFuel.two_executionBudgetsFor_add_eight_le_target_of_lt
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.expr scrutinee)
          (FunctionsObserverStaticCost.stmt (.Block selectedBody))
          hScrutineeCost hSelectedBlockCost
          (by omega : sourcePrevious < sourceFuel)
          (by omega : sourcePrevious < sourceFuel)
      have hParent :=
        FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt
            (.Switch scrutinee cases defaultBody))
          sourceFuel
      refine ⟨⟨ordinary, ?_⟩⟩
      change
        ordinary.openResult.requiredFuel ≤
          FunctionsObserverFuel.executionBudgetFor
            (FunctionsObserverStaticCost.program sourceProgram)
            (FunctionsObserverStaticCost.stmt
              (.Switch scrutinee cases defaultBody))
            sourceFuel
      dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded]
        at hPreparedBound
      dsimp [FunctionsObserverFuel.ScopedOpenResult.ProgramBounded]
        at hClosedBound
      omega

theorem ofComponents
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hListOrdinary :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForwardProgramBounded contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveOpenCompoundForwardProgramBounded contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source sourceFinal target ctx canBreak canContinue canLeave
    hCompound hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout
    hControl hRun
  cases hCompound with
  | block body =>
      exact
        block hList hFuel hCost hOk hNames hLower hRel hDomain hScope
          hLayout hControl hRun
  | switch scrutinee cases defaultBody =>
      exact
        switch hValueOrdinary.expression hListOrdinary hValue.expression
          hList hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun
  | forLoop cond post body =>
      exact
        forLoop hValueOrdinary hListOrdinary hValue hList hFuel hCost hOk
          hNames hLower hRel hDomain hScope hLayout hControl hRun
  | ifThen cond body =>
      exact
        ifThen hValueOrdinary.expression hListOrdinary hValue.expression
          hList hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun

end RecursiveOpenCompoundForwardProgramBounded

namespace RecursiveOpenStmtForwardProgramBounded

theorem ofCompound
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hValueOrdinary :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBodyOrdinary :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBody :
      FunctionsObserverCallFuel.RecursiveBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hCompound :
      RecursiveOpenCompoundForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile
        (bound + 1)) :
    RecursiveOpenStmtForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source sourceFinal target ctx canBreak canContinue canLeave
    hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
  cases stmt with
  | Block body =>
      exact
        hCompound (.block body) hFuel hCost hOk hNames hLower hRel
          hDomain hScope hLayout hControl hRun
  | Switch scrutinee cases defaultBody =>
      exact
        hCompound (.switch scrutinee cases defaultBody)
          hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun
  | For cond post body =>
      exact
        hCompound (.forLoop cond post body)
          hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun
  | If cond body =>
      exact
        hCompound (.ifThen cond body)
          hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun
  | Let names value? =>
      cases value? with
      | none =>
          have hNamesUsed :
              StateRelation.Vars.NamesWithin before.used
                (identNames names) := by
            simpa [Stmt.names] using hNames
          exact
            ScopedStmtResult.ofLetNone_programBounded
              hLower hRel hDomain hScope hLayout hControl
              hNamesUsed hRun
      | some value =>
          by_cases hFunctionCall :
              ∃ functionName functionArgs,
                value = .Call (.inr functionName) functionArgs
          · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
            have hExprOk :
                SolcValidation.ExprOk? profile sourceProgram.contract
                    layout names.length
                    (.Call (.inr functionName) functionArgs) =
                  true := by
              simp [SolcValidation.StmtOk?] at hOk
              exact hOk.2
            have hNamesUsed :
                StateRelation.Vars.NamesWithin before.used
                  (identNames names) := by
              intro candidate hMem
              apply hNames candidate
              exact List.mem_append_left _ hMem
            have hExprCost :
                FunctionsObserverStaticCost.expr
                    (.Call (.inr functionName) functionArgs) ≤
                  FunctionsObserverStaticCost.program sourceProgram := by
              have hStmt :
                  names.length +
                        FunctionsObserverStaticCost.expr
                          (.Call (.inr functionName) functionArgs) + 4 ≤
                    FunctionsObserverStaticCost.program sourceProgram := by
                simpa [FunctionsObserverStaticCost.stmt] using hCost
              omega
            exact
              ScopedStmtResult.ofLetCall_programBounded
                hDecomposition hProgramOk hExprOk hExprCost hCost
                hLower hRel hDomain hScope hLayout hNamesUsed hControl
                hValueOrdinary hBodyOrdinary hValue hBody hFuel hRun
          · have hNotFunctionCall :
                ∀ functionName functionArgs,
                  value ≠ .Call (.inr functionName) functionArgs := by
              intro functionName functionArgs hEq
              exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
            obtain ⟨name, hNamesEq⟩ :=
              Stmt.toFunctionsListUncheckedFuel?_let_noncall_singleton
                hNotFunctionCall hLower
            subst names
            have hExprOk :
                SolcValidation.ExprOk? profile sourceProgram.contract
                    layout 1 value =
                  true := by
              simp [SolcValidation.StmtOk?] at hOk
              exact hOk.2
            have hNameUsed : identName name ∈ before.used := by
              apply hNames
              simp [Stmt.names, identNames, identName]
            have hExprCost :
                FunctionsObserverStaticCost.expr value ≤
                  FunctionsObserverStaticCost.program sourceProgram := by
              have hStmt :
                  1 + FunctionsObserverStaticCost.expr value + 4 ≤
                    FunctionsObserverStaticCost.program sourceProgram := by
                simpa [FunctionsObserverStaticCost.stmt] using hCost
              omega
            exact
              ScopedStmtResult.ofLetOne_programBounded
                hNotFunctionCall hExprOk hExprCost hLower hRel hDomain
                hScope hLayout hNameUsed hControl hValue hFuel hRun
  | Assign names value =>
      by_cases hFunctionCall :
          ∃ functionName functionArgs,
            value = .Call (.inr functionName) functionArgs
      · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
        have hExprOk :
            SolcValidation.ExprOk? profile sourceProgram.contract
                layout names.length
                (.Call (.inr functionName) functionArgs) =
              true := by
          simp [SolcValidation.StmtOk?] at hOk
          exact hOk.2
        have hExprCost :
            FunctionsObserverStaticCost.expr
                (.Call (.inr functionName) functionArgs) ≤
              FunctionsObserverStaticCost.program sourceProgram := by
          have hStmt :
              names.length +
                    FunctionsObserverStaticCost.expr
                      (.Call (.inr functionName) functionArgs) + 4 ≤
                FunctionsObserverStaticCost.program sourceProgram := by
            simpa [FunctionsObserverStaticCost.stmt] using hCost
          omega
        exact
          ScopedStmtResult.ofAssignCall_programBounded
            hDecomposition hProgramOk hExprOk hExprCost hCost
            hLower hRel hDomain hScope hLayout hControl
            hValueOrdinary hBodyOrdinary hValue hBody hFuel hRun
      · have hNotFunctionCall :
            ∀ functionName functionArgs,
              value ≠ .Call (.inr functionName) functionArgs := by
          intro functionName functionArgs hEq
          exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
        obtain ⟨name, hNamesEq⟩ :=
          Stmt.toFunctionsListUncheckedFuel?_assign_noncall_singleton
            hNotFunctionCall hLower
        subst names
        have hExprOk :
            SolcValidation.ExprOk? profile sourceProgram.contract
                layout 1 value =
              true := by
          simp [SolcValidation.StmtOk?] at hOk
          exact hOk.2
        have hExprCost :
            FunctionsObserverStaticCost.expr value ≤
              FunctionsObserverStaticCost.program sourceProgram := by
          have hStmt :
              1 + FunctionsObserverStaticCost.expr value + 4 ≤
                FunctionsObserverStaticCost.program sourceProgram := by
            simpa [FunctionsObserverStaticCost.stmt] using hCost
          omega
        exact
          ScopedStmtResult.ofAssignOne_programBounded
            hNotFunctionCall hExprOk hExprCost hLower hRel hDomain
            hScope hLayout hControl hValue hFuel hRun
  | ExprStmtCall value =>
      cases value with
      | Lit literal =>
          simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
      | Var name =>
          simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hExprOk :
                  SolcValidation.ExprOk? profile sourceProgram.contract
                      layout 0 (.Call (.inl prim) args) =
                    true := by
                simpa [SolcValidation.StmtOk?] using hOk
              obtain
                  ⟨evalPrevious, sourceAfterPrim, values,
                    _hSourceFuel, hEvalValues, _hSourceFinal⟩ :=
                Yul.Source.Effectful.exec_expr_primitive_ok_parts
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  hRun
              obtain
                  ⟨callFuel, sourceAfterArgs, reversedValues,
                    _hEvalFuel, _hArgsRun, hEval⟩ :=
                Yul.Source.Effectful.evalValues_primitive_ok_parts
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  hEvalValues
              have hNonterminal :
                  Prim.terminal? prim = none :=
                ObserverSafety.SafeSemantics.terminal_none_of_eval_ok hEval
              have hExprCost :
                  FunctionsObserverStaticCost.expr
                      (.Call (.inl prim) args) ≤
                    FunctionsObserverStaticCost.program sourceProgram := by
                have hStmt :
                    FunctionsObserverStaticCost.expr
                          (.Call (.inl prim) args) + 2 ≤
                      FunctionsObserverStaticCost.program sourceProgram := by
                  simpa [FunctionsObserverStaticCost.stmt] using hCost
                omega
              exact
                ScopedStmtResult.ofExprPrimitive_programBounded
                  hNonterminal hExprOk hExprCost hLower hRel hDomain
                  hScope hLayout hControl hValueOrdinary hValue
                  hFuel hRun
          | inr functionName =>
              have hExprOk :
                  SolcValidation.ExprOk? profile sourceProgram.contract
                      layout 0 (.Call (.inr functionName) args) =
                    true := by
                simpa [SolcValidation.StmtOk?] using hOk
              have hExprCost :
                  FunctionsObserverStaticCost.expr
                      (.Call (.inr functionName) args) ≤
                    FunctionsObserverStaticCost.program sourceProgram := by
                have hStmt :
                    FunctionsObserverStaticCost.expr
                          (.Call (.inr functionName) args) + 2 ≤
                      FunctionsObserverStaticCost.program sourceProgram := by
                  simpa [FunctionsObserverStaticCost.stmt] using hCost
                omega
              exact
                ScopedStmtResult.ofExprCall_programBounded
                  hDecomposition hProgramOk hExprOk hExprCost hCost
                  hLower hRel hDomain hScope hLayout hControl
                  hValueOrdinary hBodyOrdinary hValue hBody hFuel hRun
  | Break =>
      have hEnabled : canBreak = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      exact
        ScopedStmtResult.ofBreak_programBounded
          hEnabled hLower hRel hDomain hScope hLayout hControl hRun
  | Continue =>
      have hEnabled : canContinue = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      exact
        ScopedStmtResult.ofContinue_programBounded
          hEnabled hLower hRel hDomain hScope hLayout hControl hRun
  | Leave =>
      have hEnabled : canLeave = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      exact
        ScopedStmtResult.ofLeave_programBounded
          hEnabled hLower hRel hDomain hScope hLayout hControl hRun

end RecursiveOpenStmtForwardProgramBounded

namespace RecursiveBodyForwardBounded

theorem ofList
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hList :
      ∀ staticCost,
        RecursiveOpenListForwardBounded contract transcript codeRel
          sourceProgram targetProgram profile staticCost bound) :
    FunctionsObserverCallFuel.RecursiveBodyForwardBounded
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  have hOrdinaryList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound := by
    intro sourceFuel compilerFuel sourceControl before after layout stmts
      lower source sourceFinal target ctx canBreak canContinue canLeave
      hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
    obtain ⟨bounded⟩ :=
      hList (FunctionsObserverStaticCost.stmtList stmts)
        hFuel (by rfl) hOk hNames hLower hRel hDomain hScope hLayout
        hControl hRun
    exact ⟨bounded.1⟩
  have hOrdinaryBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        (bound + 1) :=
    FunctionsObserverForward.RecursiveBodyForward.ofList hOrdinaryList
  intro sourceFuel before after params returns body fn args paramStore
    sourceCaller sourceAfterBody targetCaller hFuel hLower hParams
    hReturns hParamStore hReserved hBodyNames hBodyOk hEntry hRun
  obtain ⟨ordinaryFuel, ordinaryNonempty⟩ :=
    hOrdinaryBody hFuel hLower hParams hReturns hParamStore
      hReserved hBodyNames hBodyOk hEntry hRun
  obtain ⟨ordinaryBody⟩ := ordinaryNonempty
  let layout := fn.returns ++ fn.params
  let sourceEntry :=
    sourceCaller.withSource
      (EvmYul.Yul.State.mkOk
        (sourceCaller.source.initcall params returns args))
  let targetEntry :=
    targetCaller.withSource
      { shared := targetCaller.source.shared
        vars :=
          Functions.Source.Store.initReturns fn.returns paramStore }
  obtain
      ⟨entryShared, entryVars, hEntrySource,
        _hEntryShared, _hEntryVars, hEntryDomain⟩ :=
    hEntry.2
  change StateRelation.Vars.DomainExact layout entryVars at hEntryDomain
  change StateRelation.Vars.NamesWithin before.used layout at hReserved
  obtain ⟨listCompilerFuel, lower, _hCompilerFuel,
      hLowerList, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  obtain ⟨listSourceFuel, sourceOpen, hSourceFuel,
      hListRun, _hSourceAfterBody⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  let sourceControl : FunctionsObserverOutcome.SourceControlScopes :=
    { breakScope? := none
      continueScope? := none
      leaveScope? := some layout }
  have hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        false false true
        (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    refine
      { scope := ?_
        breakScope := ?_
        continueScope := ?_
        leaveScope := ?_ }
    · simp [layout, Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope,
        FunctionsObserverOutcome.LayoutWithinScope]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope,
        layout]
  obtain ⟨boundedList⟩ :=
    hList (FunctionsObserverStaticCost.stmtList body)
      (sourceFuel := listSourceFuel)
      (compilerFuel := listCompilerFuel)
      (sourceControl := sourceControl)
      (before := before) (after := after)
      (layout := layout) (stmts := body) (lower := lower)
      (source := sourceEntry) (sourceFinal := sourceOpen)
      (target := targetEntry)
      (ctx := Functions.Source.Effectful.FunDef.bodyCtx fn)
      (canBreak := false) (canContinue := false) (canLeave := true)
      (by omega) (by rfl) hBodyOk hBodyNames hLowerList hEntry
      (by
        simpa [targetEntry] using
          FunctionsObserverForward.RecursiveBodyForward.entryTargetDomain
            hParamStore hReserved)
      (FunctionsObserverForward.RecursiveBodyForward.bodyScope hReserved)
      hReserved hControl hListRun
  let result := boundedList.1
  have hBoundedRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          result.openResult.requiredFuel fn.body
          (targetCaller.withSource
            { shared := targetCaller.source.shared
              vars :=
                Functions.Source.Store.initReturns
                  fn.returns paramStore }) =
        .ok
          (result.openResult.outcome,
            result.openResult.finalCtx) := by
    rw [hFnBody]
    simpa [result, targetEntry] using
      FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
        result.openResult
  have hParamStoreEq : ordinaryBody.paramStore = paramStore := by
    have hOrdinaryParams := ordinaryBody.params
    rw [hParamStore] at hOrdinaryParams
    exact (Option.some.inj hOrdinaryParams).symm
  have hOrdinaryRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          ordinaryFuel fn.body
          (targetCaller.withSource
            { shared := targetCaller.source.shared
              vars :=
                Functions.Source.Store.initReturns
                  fn.returns paramStore }) =
        .ok
          (ordinaryBody.bodyOutcome,
            ordinaryBody.finalCtx) := by
    simpa [hParamStoreEq] using ordinaryBody.run
  have hPairEq :=
    Functions.Source.Effectful.Block.runOpen_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hBoundedRun hOrdinaryRun
  have hOutcomeEq :
      result.openResult.outcome = ordinaryBody.bodyOutcome :=
    congrArg Prod.fst hPairEq
  let bodyResult :
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel targetProgram.toFunctions
        fn args result.openResult.requiredFuel sourceAfterBody targetCaller :=
    { paramStore := paramStore
      bodyOutcome := result.openResult.outcome
      finalCtx := result.openResult.finalCtx
      params := hParamStore
      run := hBoundedRun
      mode := by
        simpa [hOutcomeEq] using ordinaryBody.mode
      relation := by
        simpa [hOutcomeEq] using ordinaryBody.relation }
  refine
    ⟨result.openResult.requiredFuel, ⟨⟨bodyResult, ?_⟩⟩⟩
  have hFuelMono :
      FunctionsObserverFuel.executionBudget
          (FunctionsObserverStaticCost.stmtList body) listSourceFuel ≤
        FunctionsObserverFuel.executionBudget
          (FunctionsObserverStaticCost.stmtList body) sourceFuel :=
    FunctionsObserverFuel.executionBudget_mono
      (FunctionsObserverStaticCost.stmtList body) (by omega)
  exact boundedList.2.trans hFuelMono

end RecursiveBodyForwardBounded

namespace RecursiveBodyForwardProgramBounded

theorem ofList
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hList :
      RecursiveOpenListForwardProgramBounded contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    FunctionsObserverCallFuel.RecursiveBodyForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  have hOrdinaryBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        (bound + 1) :=
    (FunctionsObserverForward.RecursiveForwardFamily.ofCompiler
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel)
      hDecomposition hProgramOk (bound + 1)).body
  intro sourceFuel before after params returns body fn args paramStore
    sourceCaller sourceAfterBody targetCaller hFuel hBodyCost hLower hParams
    hReturns hParamStore hReserved hBodyNames hBodyOk hEntry hRun
  obtain ⟨ordinaryFuel, ordinaryNonempty⟩ :=
    hOrdinaryBody hFuel hLower hParams hReturns hParamStore
      hReserved hBodyNames hBodyOk hEntry hRun
  obtain ⟨ordinaryBody⟩ := ordinaryNonempty
  let layout := fn.returns ++ fn.params
  let sourceEntry :=
    sourceCaller.withSource
      (EvmYul.Yul.State.mkOk
        (sourceCaller.source.initcall params returns args))
  let targetEntry :=
    targetCaller.withSource
      { shared := targetCaller.source.shared
        vars :=
          Functions.Source.Store.initReturns fn.returns paramStore }
  obtain
      ⟨entryShared, entryVars, hEntrySource,
        _hEntryShared, _hEntryVars, hEntryDomain⟩ :=
    hEntry.2
  change StateRelation.Vars.DomainExact layout entryVars at hEntryDomain
  change StateRelation.Vars.NamesWithin before.used layout at hReserved
  obtain ⟨listCompilerFuel, lower, _hCompilerFuel,
      hLowerList, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  obtain ⟨listSourceFuel, sourceOpen, hSourceFuel,
      hListRun, _hSourceAfterBody⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  let sourceControl : FunctionsObserverOutcome.SourceControlScopes :=
    { breakScope? := none
      continueScope? := none
      leaveScope? := some layout }
  have hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        false false true
        (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    refine
      { scope := ?_
        breakScope := ?_
        continueScope := ?_
        leaveScope := ?_ }
    · simp [layout, Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope,
        FunctionsObserverOutcome.LayoutWithinScope]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope,
        layout]
  obtain ⟨boundedList⟩ :=
    hList
      (sourceFuel := listSourceFuel)
      (compilerFuel := listCompilerFuel)
      (sourceControl := sourceControl)
      (before := before) (after := after)
      (layout := layout) (stmts := body) (lower := lower)
      (source := sourceEntry) (sourceFinal := sourceOpen)
      (target := targetEntry)
      (ctx := Functions.Source.Effectful.FunDef.bodyCtx fn)
      (canBreak := false) (canContinue := false) (canLeave := true)
      (by omega) hBodyCost hBodyOk hBodyNames hLowerList hEntry
      (by
        simpa [targetEntry] using
          FunctionsObserverForward.RecursiveBodyForward.entryTargetDomain
            hParamStore hReserved)
      (FunctionsObserverForward.RecursiveBodyForward.bodyScope hReserved)
      hReserved hControl hListRun
  let result := boundedList.1
  have hBoundedRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          result.openResult.requiredFuel fn.body
          (targetCaller.withSource
            { shared := targetCaller.source.shared
              vars :=
                Functions.Source.Store.initReturns
                  fn.returns paramStore }) =
        .ok
          (result.openResult.outcome,
            result.openResult.finalCtx) := by
    rw [hFnBody]
    simpa [result, targetEntry] using
      FunctionsObserverOutcome.ScopedOpenResult.run_requiredFuel
        result.openResult
  have hParamStoreEq : ordinaryBody.paramStore = paramStore := by
    have hOrdinaryParams := ordinaryBody.params
    rw [hParamStore] at hOrdinaryParams
    exact (Option.some.inj hOrdinaryParams).symm
  have hOrdinaryRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          ordinaryFuel fn.body
          (targetCaller.withSource
            { shared := targetCaller.source.shared
              vars :=
                Functions.Source.Store.initReturns
                  fn.returns paramStore }) =
        .ok
          (ordinaryBody.bodyOutcome,
            ordinaryBody.finalCtx) := by
    simpa [hParamStoreEq] using ordinaryBody.run
  have hPairEq :=
    Functions.Source.Effectful.Block.runOpen_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hBoundedRun hOrdinaryRun
  have hOutcomeEq :
      result.openResult.outcome = ordinaryBody.bodyOutcome :=
    congrArg Prod.fst hPairEq
  let bodyResult :
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel targetProgram.toFunctions
        fn args result.openResult.requiredFuel sourceAfterBody targetCaller :=
    { paramStore := paramStore
      bodyOutcome := result.openResult.outcome
      finalCtx := result.openResult.finalCtx
      params := hParamStore
      run := hBoundedRun
      mode := by
        simpa [hOutcomeEq] using ordinaryBody.mode
      relation := by
        simpa [hOutcomeEq] using ordinaryBody.relation }
  refine
    ⟨result.openResult.requiredFuel, ⟨⟨bodyResult, ?_⟩⟩⟩
  have hFuelMono :
      FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmtList body)
          listSourceFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmtList body)
          sourceFuel :=
    FunctionsObserverFuel.executionBudgetFor_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmtList body) (by omega)
  exact boundedList.2.trans hFuelMono

end RecursiveBodyForwardProgramBounded

namespace RecursiveOpenListForwardBounded

theorem ofStmt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {staticCost : Nat}
    {bound : Nat}
    (hStmt :
      RecursiveOpenStmtForwardBounded contract transcript codeRel
        sourceProgram targetProgram profile staticCost bound) :
    RecursiveOpenListForwardBounded contract transcript codeRel
      sourceProgram targetProgram profile staticCost (bound + 1) := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel sourceControl before after layout stmts lower
        source sourceFinal target ctx canBreak canContinue canLeave
        hFuel hStatic hOk hNames hLower hRel hDomain hScope hLayout
        hControl hRun
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
              staticCost sourceFuel hRel hDomain hScope hLayout
              hControl.scope
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
          have hHeadStatic :
              FunctionsObserverStaticCost.stmt head ≤ staticCost :=
            (FunctionsObserverStaticCost.stmt_head_le_stmtList head tail).trans
              hStatic
          have hTailStatic :
              FunctionsObserverStaticCost.stmtList tail ≤ staticCost :=
            (FunctionsObserverStaticCost.stmtList_tail_le_stmtList
              head tail).trans hStatic
          obtain ⟨hHeadOk, hTailOk⟩ :=
            SolcValidation.stmtsOk_cons_parts hOk
          have hHeadNames :
              StateRelation.Vars.NamesWithin before.used
                (Stmt.names head) := by
            intro name hMem
            exact hNames name (List.mem_append_left _ hMem)
          obtain ⟨headBounded⟩ :=
            hStmt hPreviousBound hHeadStatic hHeadOk hHeadNames hLowerHead
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
                (by omega) hTailStatic hTailOk' hTailNames hLowerTail hHeadRel
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

namespace RecursiveOpenListForwardProgramBounded

theorem ofStmt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hStmt :
      RecursiveOpenStmtForwardProgramBounded contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveOpenListForwardProgramBounded contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel sourceControl before after layout stmts lower
        source sourceFinal target ctx canBreak canContinue canLeave
        hFuel hCost hOk hNames hLower hRel hDomain hScope hLayout
        hControl hRun
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
            FunctionsObserverFuel.ScopedOpenResult.empty_programBounded
              (FunctionsObserverStaticCost.program sourceProgram)
              (FunctionsObserverStaticCost.stmtList [])
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
          obtain ⟨headBounded⟩ :=
            hStmt hPreviousBound hHeadCost hHeadOk hHeadNames hLowerHead
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
                (by omega) hTailCost hTailOk' hTailNames hLowerTail hHeadRel
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
              FunctionsObserverFuel.ScopedOpenResult.appendRegular_programBounded
                headResult.openResult hRegular tailResult.openResult
                headBounded.2 tailBounded.2
                hHeadCost hTailCost hPreviousFuel hPreviousFuel
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
              FunctionsObserverFuel.ScopedOpenResult.appendNonregular_programBounded
                (rightLower := lowerTail)
                headResult.openResult hRegular hTailFresh
                headBounded.2 hHeadCost hPreviousFuel

end RecursiveOpenListForwardProgramBounded

structure RecursiveForwardProgramBoundedFamily
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop where
  body :
    FunctionsObserverCallFuel.RecursiveBodyForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile bound
  value :
    FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile bound
  stmt :
    RecursiveOpenStmtForwardProgramBounded contract transcript codeRel
      sourceProgram targetProgram profile bound
  list :
    RecursiveOpenListForwardProgramBounded contract transcript codeRel
      sourceProgram targetProgram profile bound
  compound :
    RecursiveOpenCompoundForwardProgramBounded contract transcript codeRel
      sourceProgram targetProgram profile bound

namespace RecursiveForwardProgramBoundedFamily

theorem ofCompiler
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true) :
    ∀ bound,
      RecursiveForwardProgramBoundedFamily contract transcript codeRel
        sourceProgram targetProgram profile bound := by
  intro bound
  induction bound with
  | zero =>
      refine
        { body := ?_
          value := ?_
          stmt := ?_
          list := ?_
          compound := ?_ }
      · simp [FunctionsObserverCallFuel.RecursiveBodyForwardProgramBounded]
      · simp [
          FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded]
      · simp [RecursiveOpenStmtForwardProgramBounded]
      · simp [RecursiveOpenListForwardProgramBounded]
      · simp [RecursiveOpenCompoundForwardProgramBounded]
  | succ bound ih =>
      have hOrdinary :
          RecursiveForwardFamily contract transcript codeRel
            sourceProgram targetProgram profile bound :=
        RecursiveForwardFamily.ofCompiler
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) (profile := profile)
          hDecomposition hProgramOk bound
      have hCompound :
          RecursiveOpenCompoundForwardProgramBounded contract transcript
            codeRel sourceProgram targetProgram profile (bound + 1) :=
        RecursiveOpenCompoundForwardProgramBounded.ofComponents
          hOrdinary.value hOrdinary.list ih.value ih.list
      exact
        { body :=
            RecursiveBodyForwardProgramBounded.ofList
              hDecomposition hProgramOk ih.list
          value :=
            FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded.ofBody
              hDecomposition hProgramOk ih.body
          stmt :=
            RecursiveOpenStmtForwardProgramBounded.ofCompound
              hDecomposition hProgramOk hOrdinary.value hOrdinary.body
              ih.value ih.body hCompound
          list := RecursiveOpenListForwardProgramBounded.ofStmt ih.stmt
          compound := hCompound }

theorem dispatcherForward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {sourceEntry sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel [] sourceEntry target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        (Fresh.initial
          (Contract.names sourceProgram.contract)).used
        target.source.vars)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block [sourceProgram.contract.dispatcher])
          (some sourceProgram.contract) sourceEntry =
        .ok sourceFinal) :
    ∃ targetFuel outcome,
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetFuel targetProgram.toFunctions target =
        .ok outcome ∧
      outcome.mode = .regular ∧
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel
        [] sourceFinal outcome ∧
      targetFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.program sourceProgram)
          sourceFuel := by
  have hCompiler := hDecomposition
  obtain
      ⟨bodyStmts, afterBody, functions, afterFunctions,
        hLowerBody, _hLowerFunctions, hTargetProgram⟩ :=
    hDecomposition
  obtain ⟨listSourceFuel, sourceOpen, hSourceFuel,
      hListRun, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  have hLowerList :
      Stmt.List.toFunctionsUncheckedFuel?
          (Stmt.fuel sourceProgram.contract.dispatcher + 1)
          (Fresh.initial (Contract.names sourceProgram.contract))
          [sourceProgram.contract.dispatcher] =
        some (bodyStmts, afterBody) :=
    Stmt.List.toFunctionsUncheckedFuel?_singleton_of_stmt
      (by
        cases sourceProgram.contract.dispatcher <;>
          simp [Stmt.fuel])
      hLowerBody
  have hDispatcherOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          [] false false false sourceProgram.contract.dispatcher =
        true := by
    have hParts := hProgramOk
    simp [SolcValidation.ProgramOkWith?,
      SolcValidation.ContractOkWith?,
      SolcValidation.ContractOkWithEntries?] at hParts
    exact hParts.2.1
  have hListOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          [] false false false
          [sourceProgram.contract.dispatcher] =
        true := by
    simpa [SolcValidation.StmtsOk?,
      SolcValidation.StmtOutVars] using hDispatcherOk
  let initial :=
    Fresh.initial (Contract.names sourceProgram.contract)
  have hNames :
      StateRelation.Vars.NamesWithin initial.used
        (Stmt.List.names [sourceProgram.contract.dispatcher]) := by
    intro name hMem
    change name ∈ Contract.names sourceProgram.contract
    have hDispatcherName :
        name ∈ Stmt.names sourceProgram.contract.dispatcher := by
      simpa [Stmt.List.names] using hMem
    simpa [Contract.names] using
      List.mem_append_left
        (FunctionList.names
          (Contract.functionEntries sourceProgram.contract))
        hDispatcherName
  let sourceControl : FunctionsObserverOutcome.SourceControlScopes :=
    { breakScope? := none
      continueScope? := none
      leaveScope? := none }
  have hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl []
        false false false Functions.Source.Ctx.initial := by
    refine
      { scope := ?_
        breakScope := ?_
        continueScope := ?_
        leaveScope := ?_ }
    · simp [FunctionsObserverOutcome.LayoutWithinScope]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Ctx.initial]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Ctx.initial]
    · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
        Functions.Source.Ctx.initial]
  have hFamily :=
    ofCompiler
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (profile := profile)
      hCompiler hProgramOk (listSourceFuel + 1)
  obtain ⟨bounded⟩ :=
    hFamily.list
      (sourceFuel := listSourceFuel)
      (compilerFuel := Stmt.fuel sourceProgram.contract.dispatcher + 1)
      (sourceControl := sourceControl)
      (before := initial) (after := afterBody)
      (layout := []) (stmts := [sourceProgram.contract.dispatcher])
      (lower := bodyStmts)
      (source := sourceEntry) (sourceFinal := sourceOpen)
      (target := target) (ctx := Functions.Source.Ctx.initial)
      (canBreak := false) (canContinue := false) (canLeave := false)
      (by omega)
      (FunctionsObserverStaticCost.dispatcherList_le_program sourceProgram)
      hListOk hNames hLowerList hRel hDomain
      (by
        intro name hMem
        simp [Functions.Source.Ctx.initial] at hMem)
      (by
        intro name hMem
        simp at hMem)
      hControl hListRun
  obtain ⟨closed⟩ :=
    ScopedListResult.close bounded.1
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel)
      (by
        intro name hMem
        simp at hMem)
      hControl hSourceFinal
  obtain ⟨targetFuel, hTargetFuel, hTargetRun⟩ :=
    ClosedListResult.runBounded_of_open bounded.1 closed
  have hOutcomeRegular : closed.outcome.mode = .regular := by
    cases hMode : closed.outcome.mode with
    | regular => rfl
    | brk =>
        have hExit := closed.exitScope
        simp [FunctionsObserverOutcome.ExitScopeRel, hMode,
          sourceControl] at hExit
    | cont =>
        have hExit := closed.exitScope
        simp [FunctionsObserverOutcome.ExitScopeRel, hMode,
          sourceControl] at hExit
    | leave =>
        have hExit := closed.exitScope
        simp [FunctionsObserverOutcome.ExitScopeRel, hMode,
          sourceControl] at hExit
    | halt kind =>
        have hExit := closed.exitScope
        simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit
  have hFinalLayout : closed.finalLayout = [] :=
    closed.regularLayout hOutcomeRegular
  have hBodyEq :
      targetProgram.toFunctions.body = { stmts := bodyStmts } :=
    congrArg (fun program => program.body) hTargetProgram
  have hTargetProgramRun :
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetFuel targetProgram.toFunctions target =
        .ok closed.outcome := by
    unfold Functions.Source.Effectful.Program.runState
    rw [hBodyEq]
    exact hTargetRun
  refine
    ⟨targetFuel, closed.outcome, hTargetProgramRun, hOutcomeRegular,
      by simpa [hFinalLayout] using closed.relation, ?_⟩
  have hLocal :
      FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmtList
            [sourceProgram.contract.dispatcher])
          listSourceFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.program sourceProgram)
          listSourceFuel :=
    FunctionsObserverFuel.executionBudgetFor_local_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      listSourceFuel
      (FunctionsObserverStaticCost.dispatcherList_le_program sourceProgram)
  have hDynamic :
      FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.program sourceProgram)
          listSourceFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.program sourceProgram)
          sourceFuel :=
    FunctionsObserverFuel.executionBudgetFor_mono
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.program sourceProgram)
      (by omega)
  exact hTargetFuel.trans (bounded.2.trans (hLocal.trans hDynamic))

end RecursiveForwardProgramBoundedFamily

end FunctionsObserverForwardFuel
end Yul
end EvmCompiler
