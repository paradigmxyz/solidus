import EvmCompiler.Yul.FunctionsObserverStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverForward

/-!
Fuel-bounded composition for the adjacent Yul-to-Functions observer proof.

This module assembles the expression, call, and statement-owned constructors.
It does not define a compiler or interpreter. Recursive premises are strictly
smaller source-fuel interfaces and remain private to this pass boundary.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open FunctionsObserverOutcome

structure ScopedStmtResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (stmt : AstStmt)
    (lower : List Functions.Stmt)
    (initial final : Fresh.State)
    (entryLayout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (canBreak canContinue canLeave : Bool)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes} where
  openResult :
    FunctionsObserverOutcome.ScopedOpenResult
      contract codeRel program lower initial final entryLayout
      sourceFinal target ctx (sourceControl := sourceControl)
  regularLayout :
    openResult.outcome.mode = .regular →
      openResult.finalLayout =
        SolcValidation.StmtOutVars entryLayout stmt
  regularControl :
    openResult.outcome.mode = .regular →
      ControlContextRel sourceControl openResult.finalLayout
        canBreak canContinue canLeave openResult.finalCtx

namespace ScopedStmtResult

def ofStatement
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (result :
      FunctionsObserverStatement.OpenResult.Result
        contract codeRel program stmt lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl))
    (hControl :
      ControlContextRel sourceControl entryLayout
        canBreak canContinue canLeave ctx) :
    ScopedStmtResult contract codeRel program stmt lower
      initial final entryLayout sourceFinal target ctx
      canBreak canContinue canLeave
      (sourceControl := sourceControl) :=
  { openResult := result.openResult
    regularLayout := result.regularLayout
    regularControl := fun hRegular =>
      ControlContextRel.transport hControl
        (result.openResult.retains hRegular)
        result.openResult.control
        (result.openResult.layoutScope hRegular) }

def ofOpen
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (result :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl))
    (hLayout :
      result.outcome.mode = .regular →
        result.finalLayout =
          SolcValidation.StmtOutVars entryLayout stmt)
    (hControl :
      ControlContextRel sourceControl entryLayout
        canBreak canContinue canLeave ctx) :
    ScopedStmtResult contract codeRel program stmt lower
      initial final entryLayout sourceFinal target ctx
      canBreak canContinue canLeave
      (sourceControl := sourceControl) :=
  { openResult := result
    regularLayout := hLayout
    regularControl := fun hRegular =>
      ControlContextRel.transport hControl
        (result.retains hRegular) result.control
        (result.layoutScope hRegular) }

end ScopedStmtResult

structure ScopedListResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (stmts : List AstStmt)
    (lower : List Functions.Stmt)
    (initial final : Fresh.State)
    (entryLayout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (canBreak canContinue canLeave : Bool)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes} where
  openResult :
    FunctionsObserverOutcome.ScopedOpenResult
      contract codeRel program lower initial final entryLayout
      sourceFinal target ctx (sourceControl := sourceControl)
  regularLayout :
    openResult.outcome.mode = .regular →
      openResult.finalLayout =
        SolcValidation.StmtsOutVars entryLayout stmts
  regularControl :
    openResult.outcome.mode = .regular →
      ControlContextRel sourceControl openResult.finalLayout
        canBreak canContinue canLeave openResult.finalCtx

structure ClosedListResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (sourceControl : FunctionsObserverOutcome.SourceControlScopes)
    (lower : List Functions.Stmt)
    (initial final : Fresh.State)
    (entryLayout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) where
  finalLayout : List Name
  outcome :
    Functions.Source.Effectful.Outcome
      (Functions.ObserverSemantics.State transcript)
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx { stmts := lower } fuel target =
        .ok outcome
  relation :
    FunctionsObserverOutcome.ScopedOutcomeRel codeRel
      finalLayout sourceFinal outcome
  domain :
    StateRelation.Vars.TargetDomainWithin
      final.used outcome.state.source.vars
  freshExtends : Fresh.Extends initial final
  regularLayout :
    outcome.mode = .regular → finalLayout = entryLayout
  layoutWithin :
    StateRelation.Vars.NamesWithin final.used finalLayout
  sourceDefined :
    FunctionsObserverOutcome.SourceDefined finalLayout sourceFinal
  sourceWithin :
    FunctionsObserverOutcome.SourceWithin entryLayout sourceFinal
  targetRestriction :
    FunctionsObserverOutcome.ScopedTargetRestriction ctx outcome
  exitScope :
    FunctionsObserverOutcome.ExitScopeRel
      sourceControl ctx outcome.mode finalLayout

structure ScopedLoopResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (sourceControl : FunctionsObserverOutcome.SourceControlScopes)
    (cond : Locals.Expr 1)
    (postBase : Functions.Source.Ctx)
    (post : Functions.Block)
    (bodyBase : Functions.Source.Ctx)
    (body : Functions.Block)
    (final : Fresh.State)
    (layout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (loopCtx : Functions.Source.Ctx) where
  finalLayout : List Name
  outcome :
    Functions.Source.Effectful.Outcome
      (Functions.ObserverSemantics.State transcript)
  run :
    ∃ fuel,
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx cond postBase post bodyBase body fuel target =
        .ok outcome
  relation :
    FunctionsObserverOutcome.ScopedOutcomeRel codeRel
      finalLayout sourceFinal outcome
  domain :
    StateRelation.Vars.TargetDomainWithin
      final.used outcome.state.source.vars
  regularLayout :
    outcome.mode = .regular → finalLayout = layout
  layoutWithin :
    StateRelation.Vars.NamesWithin final.used finalLayout
  sourceDefined :
    FunctionsObserverOutcome.SourceDefined finalLayout sourceFinal
  sourceWithin :
    FunctionsObserverOutcome.SourceWithin layout sourceFinal
  abruptTargetRestriction :
    FunctionsObserverOutcome.AbruptTargetRestriction loopCtx outcome
  exitScope :
    FunctionsObserverOutcome.ExitScopeRel
      sourceControl loopCtx outcome.mode finalLayout

structure ContinuingBodyResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (lower : List Functions.Stmt)
    (final : Fresh.State)
    (layout : List Name)
    (sourceAfterBody : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (bodyBase : Functions.Source.Ctx) where
  outcome :
    Functions.Source.Effectful.Outcome
      (Functions.ObserverSemantics.State transcript)
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program bodyBase { stmts := lower } fuel target =
        .ok outcome
  relation :
    StateRelation.Replay.ScopedExactRel codeRel layout
      (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
      outcome.state
  mode : outcome.mode = .regular ∨ outcome.mode = .cont
  domain :
    StateRelation.Vars.TargetDomainWithin
      final.used outcome.state.source.vars
  targetRestricted :
    FunctionsObserverOutcome.TargetRestrictedTo
      bodyBase.scope outcome.state

namespace ScopedListResult

def close
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {stmts : List AstStmt}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceEntry sourceOpen sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (result :
      ScopedListResult contract codeRel program stmts lower
        initial final entryLayout sourceOpen target ctx
        canBreak canContinue canLeave
        (sourceControl := sourceControl))
    (hEntryDomain :
      StateRelation.Vars.DomainExact entryLayout
        sourceEntry.source.store)
    (hLayout :
      StateRelation.Vars.NamesWithin initial.used entryLayout)
    (hControl :
      ControlContextRel sourceControl entryLayout
        canBreak canContinue canLeave ctx)
    (hSourceFinal :
      sourceFinal =
        sourceOpen.withSource
          (sourceOpen.source.restrictStoreTo sourceEntry.source.store)) :
    Nonempty
      (ClosedListResult contract codeRel program sourceControl lower
        initial final entryLayout sourceFinal target ctx) := by
  by_cases hRegular :
      result.openResult.outcome.mode = .regular
  · obtain ⟨bodyShared, bodyVars, hBodySource⟩ :=
      FunctionsObserverOutcome.ModeRel.target_regular_source_ok
        result.openResult.relation.mode hRegular
    have hOutcomeEq :
        result.openResult.outcome =
          Functions.Source.Effectful.Outcome.regular
            result.openResult.outcome.state :=
      Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
    obtain ⟨bodyFuel, hBodyOpen⟩ := result.openResult.run
    rw [hOutcomeEq] at hBodyOpen
    let targetFinal :=
      result.openResult.outcome.state.withSource
        (result.openResult.outcome.state.source.restrictTo ctx.scope)
    have hBodyScoped :
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx { stmts := lower } bodyFuel target =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetFinal) := by
      simpa [targetFinal] using
        Functions.Source.Effectful.Block.runScoped_regular_of_runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hBodyOpen
    have hRevived :
        sourceOpen.withSource sourceOpen.source.reviveJump =
          sourceOpen := by
      rw [hBodySource]
      change sourceOpen.withSource (.Ok bodyShared bodyVars) = sourceOpen
      rw [← hBodySource]
      exact Simulation.ResourceReplay.State.withSource_self sourceOpen
    have hBodyExact :=
      result.openResult.relation.exact hRegular
    rw [hRevived] at hBodyExact
    have hClosedRel :
        StateRelation.Replay.ScopedExactRel codeRel entryLayout
          (sourceOpen.withSource
            (.Ok bodyShared
              (EvmYul.Yul.State.restrictVarStore
                bodyVars sourceEntry.source.store)))
          targetFinal := by
      simpa [targetFinal] using
        StateRelation.Replay.scopedExact_restrict_scopes
          hBodySource hBodyExact hEntryDomain
          (result.openResult.retains hRegular)
          hControl.scope
    have hSourceFinal' :
        sourceFinal =
          sourceOpen.withSource
            (.Ok bodyShared
              (EvmYul.Yul.State.restrictVarStore
                bodyVars sourceEntry.source.store)) := by
      rw [hSourceFinal, hBodySource]
      rfl
    have hOutcomeRel :
        FunctionsObserverOutcome.ScopedOutcomeRel codeRel entryLayout
          sourceFinal
          (Functions.Source.Effectful.Outcome.regular targetFinal) := by
      rw [hSourceFinal']
      exact
        FunctionsObserverOutcome.ScopedOutcomeRel.regular
          rfl hClosedRel
    exact
      ⟨
        { finalLayout := entryLayout
          outcome :=
            Functions.Source.Effectful.Outcome.regular targetFinal
          run := ⟨bodyFuel, hBodyScoped⟩
          relation := hOutcomeRel
          domain := by
            simpa [targetFinal, Locals.Source.State.restrictTo] using
              result.openResult.domain.restrictTo
          freshExtends := result.openResult.freshExtends
          regularLayout := fun _hResultRegular => rfl
          layoutWithin := hLayout.mono result.openResult.freshExtends
          sourceDefined := by
            rw [hSourceFinal']
            exact
              FunctionsObserverOutcome.SourceDefined.of_scopedExact
                hClosedRel
          sourceWithin := by
            rw [hSourceFinal']
            exact
              FunctionsObserverOutcome.SourceWithin.of_scopedExact
                hClosedRel
          targetRestriction := by
            simp only [FunctionsObserverOutcome.ScopedTargetRestriction,
              Functions.Source.Effectful.Outcome.regular_mode]
            exact ⟨result.openResult.outcome.state, rfl⟩
          exitScope := by
            simp [FunctionsObserverOutcome.ExitScopeRel] }⟩
  · obtain ⟨bodyFuel, hBodyOpen⟩ := result.openResult.run
    have hBodyScoped :
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx { stmts := lower } bodyFuel target =
          .ok result.openResult.outcome :=
      Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hBodyOpen hRegular
    have hExitSubset :
        ∀ name, name ∈ result.openResult.finalLayout →
          name ∈ entryLayout :=
      hControl.exitSubset result.openResult.exitScope hRegular
    have hOutcomeRel :
        FunctionsObserverOutcome.ScopedOutcomeRel codeRel
          result.openResult.finalLayout sourceFinal
          result.openResult.outcome := by
      rw [hSourceFinal]
      exact
        FunctionsObserverOutcome.ScopedOutcomeRel.restrictNonregularSource
          result.openResult.relation hRegular hEntryDomain hExitSubset
    exact
      ⟨
        { finalLayout := result.openResult.finalLayout
          outcome := result.openResult.outcome
          run := ⟨bodyFuel, hBodyScoped⟩
          relation := hOutcomeRel
          domain := result.openResult.domain
          freshExtends := result.openResult.freshExtends
          regularLayout := fun hResultRegular =>
            False.elim (hRegular hResultRegular)
          layoutWithin := result.openResult.layoutWithin
          sourceDefined := by
            rw [hSourceFinal]
            exact
              FunctionsObserverOutcome.SourceDefined.restrictStoreTo
                result.openResult.sourceDefined hEntryDomain hExitSubset
          sourceWithin := by
            rw [hSourceFinal]
            exact
              FunctionsObserverOutcome.SourceWithin.restrictStoreTo
                (source := sourceOpen) hEntryDomain
          targetRestriction := by
            cases hMode : result.openResult.outcome.mode with
            | regular =>
                exact (hRegular hMode).elim
            | brk | cont | leave | halt =>
                simpa [FunctionsObserverOutcome.ScopedTargetRestriction,
                  hMode] using
                  result.openResult.abruptTargetRestriction
          exitScope := result.openResult.exitScope }⟩

def prependForGuard
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {body : List AstStmt}
    {pre : List Functions.Stmt}
    {cond : Locals.Expr 1}
    {lowerBody : List Functions.Stmt}
    {initial condFresh bodyInitial final : Fresh.State}
    {layout : List Name}
    {sourceAfterCond sourceOpen :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canLeave : Bool}
    {value : Word}
    (prepared :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel program pre cond condFresh layout
        sourceAfterCond target ctx value)
    (bodyResult :
      ScopedListResult contract codeRel program body lowerBody
        bodyInitial final layout sourceOpen prepared.prepared.evalTarget
        prepared.prepared.finalCtx true true canLeave
        (sourceControl := sourceControl))
    (hNonzero : value ≠ EvmYul.UInt256.ofNat 0)
    (hFresh : Fresh.Extends initial final) :
    Nonempty
      (ScopedListResult contract codeRel program body
        (pre ++
          .if_
              (.prim .iszero (Locals.ExprSeq.cons cond .nil))
              { stmts := [.brk] } ::
            lowerBody)
        initial final layout sourceOpen target ctx true true canLeave
        (sourceControl := sourceControl)) := by
  obtain ⟨runFuel, hRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_forGuard_body_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program prepared.prepared.run prepared.prepared.eval
      (Functions.ObserverSafety.SafeSemantics.eval_iszero
        prepared.prepared.evalTarget value)
      hNonzero bodyResult.openResult.run
  let openResult :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program
        (pre ++
          .if_
              (.prim .iszero (Locals.ExprSeq.cons cond .nil))
              { stmts := [.brk] } ::
            lowerBody)
        initial final layout sourceOpen target ctx
        (sourceControl := sourceControl) :=
    { finalLayout := bodyResult.openResult.finalLayout
      outcome := bodyResult.openResult.outcome
      finalCtx := bodyResult.openResult.finalCtx
      run := ⟨runFuel, hRun⟩
      relation := bodyResult.openResult.relation
      domain := bodyResult.openResult.domain
      scope := bodyResult.openResult.scope
      control :=
        Functions.Source.Ctx.SameControl.trans
          prepared.prepared.control bodyResult.openResult.control
      freshExtends := hFresh
      retains := bodyResult.openResult.retains
      layoutWithin := bodyResult.openResult.layoutWithin
      sourceDefined := bodyResult.openResult.sourceDefined
      abruptTargetRestriction :=
        FunctionsObserverOutcome.AbruptTargetRestriction.transport
          prepared.prepared.control
          bodyResult.openResult.abruptTargetRestriction
      layoutScope := bodyResult.openResult.layoutScope
      exitScope :=
        FunctionsObserverOutcome.ExitScopeRel.transportTarget
          prepared.prepared.control bodyResult.openResult.exitScope }
  exact
    ⟨{ openResult := openResult
       regularLayout := bodyResult.regularLayout
       regularControl := bodyResult.regularControl }⟩

def closeForGuardBody
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {body : List AstStmt}
    {pre : List Functions.Stmt}
    {cond : Locals.Expr 1}
    {lowerBody : List Functions.Stmt}
    {initial condFresh bodyInitial final : Fresh.State}
    {layout : List Name}
    {sourceEntry sourceAfterCond sourceOpen sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canLeave : Bool}
    {value : Word}
    (prepared :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel program pre cond condFresh layout
        sourceAfterCond target ctx value)
    (bodyResult :
      ScopedListResult contract codeRel program body lowerBody
        bodyInitial final layout sourceOpen prepared.prepared.evalTarget
        prepared.prepared.finalCtx true true canLeave
        (sourceControl := sourceControl))
    (hNonzero : value ≠ EvmYul.UInt256.ofNat 0)
    (hFresh : Fresh.Extends initial final)
    (hEntryDomain :
      StateRelation.Vars.DomainExact layout
        sourceEntry.source.store)
    (hLayout :
      StateRelation.Vars.NamesWithin initial.used layout)
    (hControl :
      ControlContextRel sourceControl layout true true canLeave ctx)
    (hSourceFinal :
      sourceFinal =
        sourceOpen.withSource
          (sourceOpen.source.restrictStoreTo sourceEntry.source.store)) :
    Nonempty
      (ClosedListResult contract codeRel program sourceControl
        (pre ++
          .if_
              (.prim .iszero (Locals.ExprSeq.cons cond .nil))
              { stmts := [.brk] } ::
            lowerBody)
        initial final layout sourceFinal target ctx) := by
  obtain ⟨combined⟩ :=
    prependForGuard prepared bodyResult hNonzero hFresh
  exact close combined hEntryDomain hLayout hControl hSourceFinal

end ScopedListResult

namespace ClosedListResult

def monoFresh
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {lower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (closed :
      ClosedListResult contract codeRel program sourceControl lower
        initial middle entryLayout sourceFinal target ctx)
    (hExtends : Fresh.Extends middle final) :
    ClosedListResult contract codeRel program sourceControl lower
      initial final entryLayout sourceFinal target ctx :=
  { finalLayout := closed.finalLayout
    outcome := closed.outcome
    run := closed.run
    relation := closed.relation
    domain := closed.domain.mono hExtends
    freshExtends := Fresh.Extends.trans closed.freshExtends hExtends
    regularLayout := closed.regularLayout
    layoutWithin := closed.layoutWithin.mono hExtends
    sourceDefined := closed.sourceDefined
    sourceWithin := closed.sourceWithin
    targetRestriction := closed.targetRestriction
    exitScope := closed.exitScope }

theorem sourceDomainAtEntry
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
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (closed :
      ClosedListResult contract codeRel program sourceControl lower
        initial final entryLayout sourceFinal target ctx)
    (hFinalLayout : closed.finalLayout = entryLayout)
    (hSource : sourceFinal.source.reviveJump = .Ok shared store) :
    StateRelation.Vars.DomainExact entryLayout store := by
  apply
    FunctionsObserverOutcome.sourceDomainExact_of_source
      (source := sourceFinal)
  · simpa [hFinalLayout] using closed.sourceDefined
  · exact closed.sourceWithin
  · exact hSource

def continuingBody
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {layout : List Name}
    {sourceAfterBody : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {bodyBase : Functions.Source.Ctx}
    (closedBody :
      ClosedListResult contract codeRel program
        (ControlContextRel.forBodySourceControl layout sourceControl)
        lower initial final layout sourceAfterBody target bodyBase)
    (hContinues :
      Yul.Source.Effectful.LoopBodyContinues sourceAfterBody.source)
    (hContinueScope :
      bodyBase.continueScope? = some bodyBase.scope) :
    Nonempty
      (ContinuingBodyResult contract codeRel program lower final layout
        sourceAfterBody target bodyBase) := by
  cases hSource : sourceAfterBody.source with
  | OutOfFuel =>
      simp [Yul.Source.Effectful.LoopBodyContinues, hSource] at hContinues
  | Ok shared store =>
      have hMode :
          closedBody.outcome.mode = .regular := by
        have hModeRel := closedBody.relation.mode
        rw [hSource] at hModeRel
        exact
          FunctionsObserverOutcome.ModeRel.source_ok_target_regular
            hModeRel
      exact
        ⟨
          { outcome := closedBody.outcome
            run := closedBody.run
            relation := by
              have hExact := closedBody.relation.exact hMode
              have hLayout := closedBody.regularLayout hMode
              simpa [hLayout] using hExact
            mode := .inl hMode
            domain := closedBody.domain
            targetRestricted := by
              simpa [FunctionsObserverOutcome.ScopedTargetRestriction,
                hMode] using closedBody.targetRestriction }⟩
  | Checkpoint jump =>
      cases jump with
      | Break shared store =>
          simp [Yul.Source.Effectful.LoopBodyContinues, hSource] at hContinues
      | Leave shared store =>
          simp [Yul.Source.Effectful.LoopBodyContinues, hSource] at hContinues
      | Continue shared store =>
          have hMode :
              closedBody.outcome.mode = .cont := by
            have hModeRel := closedBody.relation.mode
            rw [hSource] at hModeRel
            exact
              FunctionsObserverOutcome.ModeRel.source_continue_target_cont
                hModeRel
          have hExit := closedBody.exitScope
          simp [FunctionsObserverOutcome.ExitScopeRel,
            ControlContextRel.forBodySourceControl, hMode] at hExit
          have hState := closedBody.relation.state
          rw [← hExit.1] at hState
          have hDomain' :
              StateRelation.Vars.DomainExact layout store := by
            apply
              sourceDomainAtEntry closedBody hExit.1.symm
            rw [hSource]
            rfl
          exact
            ⟨
              { outcome := closedBody.outcome
                run := closedBody.run
                relation :=
                  StateRelation.Replay.scopedExact_of_scopedRel hState
                    (by
                      intro sourceShared sourceVars hSource'
                      rw [hSource] at hSource'
                      cases hSource'
                      exact hDomain')
                mode := .inr hMode
                domain := closedBody.domain
                targetRestricted := by
                  have hRestricted := closedBody.targetRestriction
                  simp [FunctionsObserverOutcome.ScopedTargetRestriction,
                    FunctionsObserverOutcome.AbruptTargetRestriction,
                    hMode] at hRestricted
                  obtain ⟨scope, hScope, hState⟩ := hRestricted
                  rw [hContinueScope] at hScope
                  cases hScope
                  exact hState }⟩

end ClosedListResult

namespace ContinuingBodyResult

theorem targetDomain
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {lower : List Functions.Stmt}
    {final : Fresh.State}
    {layout used : List Name}
    {sourceAfterBody : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {bodyBase : Functions.Source.Ctx}
    (bodyResult :
      ContinuingBodyResult contract codeRel program lower final layout
        sourceAfterBody target bodyBase)
    (hScope :
      StateRelation.Vars.NamesWithin used bodyBase.scope) :
    StateRelation.Vars.TargetDomainWithin used
      bodyResult.outcome.state.source.vars :=
  bodyResult.targetRestricted.domain hScope

end ContinuingBodyResult

namespace ScopedLoopResult

def ofFalse
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {pre : List Functions.Stmt}
    {cond : Locals.Expr 1}
    {lowerBody : List Functions.Stmt}
    {condFresh final : Fresh.State}
    {layout : List Name}
    {sourceAfterCond sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {loopCtx postBase bodyBase : Functions.Source.Ctx}
    {post : Functions.Block}
    {value : Word}
    (prepared :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel program pre cond condFresh layout
        sourceAfterCond target bodyBase value)
    (hZero : value = EvmYul.UInt256.ofNat 0)
    (hFresh : Fresh.Extends condFresh final)
    (hLayout :
      StateRelation.Vars.NamesWithin final.used layout)
    (hLayoutScope :
      FunctionsObserverOutcome.LayoutWithinScope layout loopCtx)
    (hBreakScope : bodyBase.breakScope? = some loopCtx.scope)
    (hSourceFinal : sourceFinal = sourceAfterCond) :
    Nonempty
      (ScopedLoopResult contract codeRel program sourceControl
        (.lit (EvmYul.UInt256.ofNat 1)) postBase post bodyBase
        { stmts :=
            pre ++
              .if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] } ::
              lowerBody }
        final layout sourceFinal target loopCtx) := by
  have hPreparedBreak :
      prepared.prepared.finalCtx.breakScope? = some loopCtx.scope := by
    rw [← prepared.prepared.control.breakScope]
    exact hBreakScope
  obtain ⟨bodyFuel, hBody⟩ :=
    Functions.Source.Effectful.Block.runScoped_forGuard_break_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program prepared.prepared.run prepared.prepared.eval
      (Functions.ObserverSafety.SafeSemantics.eval_iszero
        prepared.prepared.evalTarget value)
      hZero hPreparedBreak
  have hOuterCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.lit (EvmYul.UInt256.ofNat 1)) target =
        .ok (target, true) :=
    Functions.ObserverSafety.SafeSemantics.evalCondition_one target
  let targetFinal :=
    prepared.prepared.evalTarget.withSource
      (prepared.prepared.evalTarget.source.restrictTo loopCtx.scope)
  have hBody' :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program bodyBase
          { stmts :=
              pre ++
                .if_
                  (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                  { stmts := [.brk] } ::
                lowerBody }
          bodyFuel target =
        .ok (Functions.Source.Effectful.Outcome.brk targetFinal) := by
    simpa [targetFinal] using hBody
  have hLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx (.lit (EvmYul.UInt256.ofNat 1))
          postBase post bodyBase
          { stmts :=
              pre ++
                .if_
                  (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                  { stmts := [.brk] } ::
                lowerBody }
          (bodyFuel + 1) target =
        .ok (Functions.Source.Effectful.Outcome.regular targetFinal) :=
    Functions.Source.Effectful.Stmt.runForLoop_body_brk_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hOuterCond hBody'
  obtain
      ⟨sourceShared, sourceVars, hSourceAfterCond,
        _hShared, _hScoped, _hDomain⟩ :=
    prepared.relation.2
  have hFinalRel :
      StateRelation.Replay.ScopedExactRel codeRel layout
        sourceAfterCond targetFinal := by
    simpa [targetFinal] using
      StateRelation.Replay.scopedExact_restrict_target_scope
        prepared.relation hLayoutScope
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
        sourceFinal
        (Functions.Source.Effectful.Outcome.regular targetFinal) := by
    rw [hSourceFinal]
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hSourceAfterCond hFinalRel
  exact
    ⟨
      { finalLayout := layout
        outcome := Functions.Source.Effectful.Outcome.regular targetFinal
        run := ⟨bodyFuel + 1, hLoop⟩
        relation := hOutcomeRel
        domain := by
          simpa [targetFinal, Locals.Source.State.restrictTo] using
            (prepared.prepared.domain.mono hFresh).restrictTo
        regularLayout := fun _hRegular => rfl
        layoutWithin := hLayout
        sourceDefined := by
          rw [hSourceFinal]
          exact
            FunctionsObserverOutcome.SourceDefined.of_scopedExact
              hFinalRel
        sourceWithin := by
          rw [hSourceFinal]
          exact
            FunctionsObserverOutcome.SourceWithin.of_scopedExact
              hFinalRel
        abruptTargetRestriction := by
          simp [FunctionsObserverOutcome.AbruptTargetRestriction]
        exitScope := by
          simp [FunctionsObserverOutcome.ExitScopeRel] }⟩

def ofBodyBreak
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {cond : Locals.Expr 1}
    {postBase : Functions.Source.Ctx}
    {post : Functions.Block}
    {bodyBase loopCtx : Functions.Source.Ctx}
    {lowerBody : List Functions.Stmt}
    {initial final : Fresh.State}
    {layout : List Name}
    {sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (closedBody :
      ClosedListResult contract codeRel program
        (ControlContextRel.forBodySourceControl layout sourceControl)
        lowerBody initial final layout sourceAfterBody target bodyBase)
    (hSourceBody :
      sourceAfterBody.source = .Checkpoint (.Break shared store))
    (hSourceFinal :
      sourceFinal =
        sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
    (hCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          cond target =
        .ok (target, true)) :
    Nonempty
      (ScopedLoopResult contract codeRel program sourceControl cond
        postBase post bodyBase { stmts := lowerBody }
        final layout sourceFinal target loopCtx) := by
  have hMode :
      closedBody.outcome.mode = .brk := by
    have hModeRel := closedBody.relation.mode
    rw [hSourceBody] at hModeRel
    exact
      FunctionsObserverOutcome.ModeRel.source_break_target_brk
        hModeRel
  have hOutcomeEq :
      closedBody.outcome =
        Functions.Source.Effectful.Outcome.brk closedBody.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_brk_of_mode hMode
  obtain ⟨bodyFuel, hBody⟩ := closedBody.run
  rw [hOutcomeEq] at hBody
  have hLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx cond postBase post bodyBase
          { stmts := lowerBody }
          (bodyFuel + 1) target =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            closedBody.outcome.state) :=
    Functions.Source.Effectful.Stmt.runForLoop_body_brk_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hCond hBody
  have hExact :
      StateRelation.Replay.ScopedExactRel codeRel layout sourceFinal
        closedBody.outcome.state := by
    rw [hSourceFinal]
    have hExit := closedBody.exitScope
    simp [FunctionsObserverOutcome.ExitScopeRel,
      ControlContextRel.forBodySourceControl, hMode] at hExit
    have hState := closedBody.relation.state
    rw [← hExit.1] at hState
    apply
      StateRelation.Replay.scopedExact_of_scopedRel
        hState
    intro sourceShared sourceVars hSource
    rw [hSourceBody] at hSource
    cases hSource
    apply
      ClosedListResult.sourceDomainAtEntry closedBody hExit.1.symm
    rw [hSourceBody]
    rfl
  have hSourceFinalOk :
      sourceFinal.source = .Ok shared store := by
    rw [hSourceFinal, hSourceBody]
    rfl
  have hRelation :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout sourceFinal
        (Functions.Source.Effectful.Outcome.regular
          closedBody.outcome.state) :=
    FunctionsObserverOutcome.ScopedOutcomeRel.regular
      hSourceFinalOk hExact
  exact
    ⟨
      { finalLayout := layout
        outcome :=
          Functions.Source.Effectful.Outcome.regular
            closedBody.outcome.state
        run := ⟨bodyFuel + 1, hLoop⟩
        relation := hRelation
        domain := closedBody.domain
        regularLayout := fun _hRegular => rfl
        layoutWithin := by
          have hExit := closedBody.exitScope
          simp [FunctionsObserverOutcome.ExitScopeRel,
            ControlContextRel.forBodySourceControl, hMode] at hExit
          simpa [← hExit.1] using closedBody.layoutWithin
        sourceDefined :=
          FunctionsObserverOutcome.SourceDefined.of_scopedExact hExact
        sourceWithin :=
          FunctionsObserverOutcome.SourceWithin.of_scopedExact hExact
        abruptTargetRestriction := by
          simp [FunctionsObserverOutcome.AbruptTargetRestriction]
        exitScope := by
          simp [FunctionsObserverOutcome.ExitScopeRel] }⟩

def ofBodyLeave
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {cond : Locals.Expr 1}
    {postBase : Functions.Source.Ctx}
    {post : Functions.Block}
    {bodyBase loopCtx : Functions.Source.Ctx}
    {lowerBody : List Functions.Stmt}
    {initial final : Fresh.State}
    {layout : List Name}
    {sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (closedBody :
      ClosedListResult contract codeRel program
        (ControlContextRel.forBodySourceControl layout sourceControl)
        lowerBody initial final layout sourceAfterBody target bodyBase)
    (hSourceBody :
      sourceAfterBody.source = .Checkpoint (.Leave shared store))
    (hSourceFinal : sourceFinal = sourceAfterBody)
    (hLeaveScope : bodyBase.leaveScope? = loopCtx.leaveScope?)
    (hCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          cond target =
        .ok (target, true)) :
    Nonempty
      (ScopedLoopResult contract codeRel program sourceControl cond
        postBase post bodyBase { stmts := lowerBody }
        final layout sourceFinal target loopCtx) := by
  have hMode :
      closedBody.outcome.mode = .leave := by
    have hModeRel := closedBody.relation.mode
    rw [hSourceBody] at hModeRel
    exact
      FunctionsObserverOutcome.ModeRel.source_leave_target_leave
        hModeRel
  have hOutcomeEq :
      closedBody.outcome =
        Functions.Source.Effectful.Outcome.leave closedBody.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_leave_of_mode hMode
  obtain ⟨bodyFuel, hBody⟩ := closedBody.run
  rw [hOutcomeEq] at hBody
  have hLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx cond postBase post bodyBase
          { stmts := lowerBody }
          (bodyFuel + 1) target =
        .ok
          (Functions.Source.Effectful.Outcome.leave
            closedBody.outcome.state) :=
    Functions.Source.Effectful.Stmt.runForLoop_body_leave_of_runs
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hCond hBody
  exact
    ⟨
      { finalLayout := closedBody.finalLayout
        outcome :=
          Functions.Source.Effectful.Outcome.leave
            closedBody.outcome.state
        run := ⟨bodyFuel + 1, hLoop⟩
        relation := by
          rw [hSourceFinal, ← hOutcomeEq]
          exact closedBody.relation
        domain := closedBody.domain
        regularLayout := by
          intro hRegular
          simp at hRegular
        layoutWithin := closedBody.layoutWithin
        sourceDefined := by
          rw [hSourceFinal]
          exact closedBody.sourceDefined
        sourceWithin := by
          rw [hSourceFinal]
          exact closedBody.sourceWithin
        abruptTargetRestriction := by
          have hRestricted := closedBody.targetRestriction
          simp [FunctionsObserverOutcome.ScopedTargetRestriction,
            FunctionsObserverOutcome.AbruptTargetRestriction, hMode]
            at hRestricted ⊢
          obtain ⟨scope, hScope, hState⟩ := hRestricted
          exact
            ⟨scope, by rw [← hLeaveScope]; exact hScope, hState⟩
        exitScope := by
          have hExit := closedBody.exitScope
          simp [FunctionsObserverOutcome.ExitScopeRel,
            ControlContextRel.forBodySourceControl, hMode]
            at hExit ⊢
          rw [← hLeaveScope]
          exact hExit }⟩

def ofPostLeave
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {postBase : Functions.Source.Ctx}
    {lowerPost lowerBody : List Functions.Stmt}
    {bodyBase loopCtx : Functions.Source.Ctx}
    {bodyFinal postInitial final : Fresh.State}
    {layout : List Name}
    {sourceAfterBody sourceAfterPost sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (bodyResult :
      ContinuingBodyResult contract codeRel program lowerBody bodyFinal layout
        sourceAfterBody target bodyBase)
    (closedPost :
      ClosedListResult contract codeRel program
        (ControlContextRel.forPostSourceControl sourceControl)
        lowerPost postInitial final layout sourceAfterPost
        bodyResult.outcome.state postBase)
    (hSourcePost :
      sourceAfterPost.source = .Checkpoint (.Leave shared store))
    (hSourceFinal : sourceFinal = sourceAfterPost)
    (hLeaveScope : postBase.leaveScope? = loopCtx.leaveScope?) :
    Nonempty
      (ScopedLoopResult contract codeRel program sourceControl
        (.lit (EvmYul.UInt256.ofNat 1))
        postBase { stmts := lowerPost } bodyBase { stmts := lowerBody }
        final layout sourceFinal target loopCtx) := by
  have hPostMode :
      closedPost.outcome.mode = .leave := by
    have hModeRel := closedPost.relation.mode
    rw [hSourcePost] at hModeRel
    exact
      FunctionsObserverOutcome.ModeRel.source_leave_target_leave hModeRel
  have hPostEq :
      closedPost.outcome =
        Functions.Source.Effectful.Outcome.leave closedPost.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_leave_of_mode hPostMode
  obtain ⟨bodyFuel, hBody⟩ := bodyResult.run
  obtain ⟨postFuel, hPost⟩ := closedPost.run
  rw [hPostEq] at hPost
  let loopFuel := max bodyFuel postFuel
  have hBody' :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program bodyBase { stmts := lowerBody } loopFuel target =
        .ok bodyResult.outcome :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (Nat.le_max_left _ _) hBody
  have hPost' :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program postBase { stmts := lowerPost } loopFuel
          bodyResult.outcome.state =
        .ok
          (Functions.Source.Effectful.Outcome.leave
            closedPost.outcome.state) :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (Nat.le_max_right _ _) hPost
  have hLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx (.lit (EvmYul.UInt256.ofNat 1))
          postBase { stmts := lowerPost }
          bodyBase { stmts := lowerBody } (loopFuel + 1) target =
        .ok
          (Functions.Source.Effectful.Outcome.leave
            closedPost.outcome.state) := by
    rcases bodyResult.mode with hRegular | hContinue
    · have hBodyEq :
          bodyResult.outcome =
            Functions.Source.Effectful.Outcome.regular
              bodyResult.outcome.state :=
        Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
      rw [hBodyEq] at hBody'
      exact
        Functions.Source.Effectful.Stmt.runForLoop_regular_post_leave_of_runs
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (by
            exact
              Functions.ObserverSafety.SafeSemantics.evalCondition_one target)
          hBody' hPost'
    · have hBodyEq :
          bodyResult.outcome =
            Functions.Source.Effectful.Outcome.cont
              bodyResult.outcome.state :=
        Functions.Source.Effectful.Outcome.eq_cont_of_mode hContinue
      rw [hBodyEq] at hBody'
      exact
        Functions.Source.Effectful.Stmt.runForLoop_cont_post_leave_of_runs
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (by
            exact
              Functions.ObserverSafety.SafeSemantics.evalCondition_one target)
          hBody' hPost'
  exact
    ⟨
      { finalLayout := closedPost.finalLayout
        outcome :=
          Functions.Source.Effectful.Outcome.leave
            closedPost.outcome.state
        run := ⟨loopFuel + 1, hLoop⟩
        relation := by
          rw [hSourceFinal, ← hPostEq]
          exact closedPost.relation
        domain := closedPost.domain
        regularLayout := by
          intro hRegular
          simp at hRegular
        layoutWithin := closedPost.layoutWithin
        sourceDefined := by
          rw [hSourceFinal]
          exact closedPost.sourceDefined
        sourceWithin := by
          rw [hSourceFinal]
          exact closedPost.sourceWithin
        abruptTargetRestriction := by
          have hRestricted := closedPost.targetRestriction
          simp [FunctionsObserverOutcome.ScopedTargetRestriction,
            FunctionsObserverOutcome.AbruptTargetRestriction, hPostMode]
            at hRestricted ⊢
          obtain ⟨scope, hScope, hState⟩ := hRestricted
          exact
            ⟨scope, by rw [← hLeaveScope]; exact hScope, hState⟩
        exitScope := by
          have hExit := closedPost.exitScope
          simp [FunctionsObserverOutcome.ExitScopeRel,
            ControlContextRel.forPostSourceControl, hPostMode]
            at hExit ⊢
          rw [← hLeaveScope]
          exact hExit }⟩

def ofRecurse
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {postBase : Functions.Source.Ctx}
    {lowerPost lowerBody : List Functions.Stmt}
    {bodyBase loopCtx : Functions.Source.Ctx}
    {bodyFinal postInitial final : Fresh.State}
    {layout : List Name}
    {sourceAfterBody sourceAfterPost sourceAfterLoop sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (bodyResult :
      ContinuingBodyResult contract codeRel program lowerBody bodyFinal layout
        sourceAfterBody target bodyBase)
    (closedPost :
      ClosedListResult contract codeRel program
        (ControlContextRel.forPostSourceControl sourceControl)
        lowerPost postInitial final layout sourceAfterPost
        bodyResult.outcome.state postBase)
    (hSourcePost : sourceAfterPost.source = .Ok shared store)
    (recursive :
      ScopedLoopResult contract codeRel program sourceControl
        (.lit (EvmYul.UInt256.ofNat 1))
        postBase { stmts := lowerPost } bodyBase { stmts := lowerBody }
        final layout sourceAfterLoop closedPost.outcome.state loopCtx)
    (hSourceFinal : sourceFinal = sourceAfterLoop) :
    Nonempty
      (ScopedLoopResult contract codeRel program sourceControl
        (.lit (EvmYul.UInt256.ofNat 1))
        postBase { stmts := lowerPost } bodyBase { stmts := lowerBody }
        final layout sourceFinal target loopCtx) := by
  have hPostMode :
      closedPost.outcome.mode = .regular := by
    have hModeRel := closedPost.relation.mode
    rw [hSourcePost] at hModeRel
    exact
      FunctionsObserverOutcome.ModeRel.source_ok_target_regular hModeRel
  have hPostEq :
      closedPost.outcome =
        Functions.Source.Effectful.Outcome.regular
          closedPost.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hPostMode
  obtain ⟨bodyFuel, hBody⟩ := bodyResult.run
  obtain ⟨postFuel, hPost⟩ := closedPost.run
  obtain ⟨recursiveFuel, hRecursive⟩ := recursive.run
  rw [hPostEq] at hPost
  let loopFuel := max bodyFuel (max postFuel recursiveFuel)
  have hBody' :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program bodyBase { stmts := lowerBody } loopFuel target =
        .ok bodyResult.outcome :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [loopFuel]) hBody
  have hPost' :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program postBase { stmts := lowerPost } loopFuel
          bodyResult.outcome.state =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            closedPost.outcome.state) :=
    Functions.Source.Effectful.Block.runScoped_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [loopFuel]) hPost
  have hRecursive' :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx (.lit (EvmYul.UInt256.ofNat 1))
          postBase { stmts := lowerPost }
          bodyBase { stmts := lowerBody } loopFuel
          closedPost.outcome.state =
        .ok recursive.outcome :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [loopFuel]) hRecursive
  have hLoop :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program loopCtx (.lit (EvmYul.UInt256.ofNat 1))
          postBase { stmts := lowerPost }
          bodyBase { stmts := lowerBody } (loopFuel + 1) target =
        .ok recursive.outcome := by
    rcases bodyResult.mode with hRegular | hContinue
    · have hBodyEq :
          bodyResult.outcome =
            Functions.Source.Effectful.Outcome.regular
              bodyResult.outcome.state :=
        Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
      rw [hBodyEq] at hBody'
      exact
        Functions.Source.Effectful.Stmt.runForLoop_regular_post_recurse_of_runs
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (Functions.ObserverSafety.SafeSemantics.evalCondition_one target)
          hBody' hPost' hRecursive'
    · have hBodyEq :
          bodyResult.outcome =
            Functions.Source.Effectful.Outcome.cont
              bodyResult.outcome.state :=
        Functions.Source.Effectful.Outcome.eq_cont_of_mode hContinue
      rw [hBodyEq] at hBody'
      exact
        Functions.Source.Effectful.Stmt.runForLoop_cont_post_recurse_of_runs
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (Functions.ObserverSafety.SafeSemantics.evalCondition_one target)
          hBody' hPost' hRecursive'
  exact
    ⟨
      { finalLayout := recursive.finalLayout
        outcome := recursive.outcome
        run := ⟨loopFuel + 1, hLoop⟩
        relation := by
          rw [hSourceFinal]
          exact recursive.relation
        domain := recursive.domain
        regularLayout := recursive.regularLayout
        layoutWithin := recursive.layoutWithin
        sourceDefined := by
          rw [hSourceFinal]
          exact recursive.sourceDefined
        sourceWithin := by
          rw [hSourceFinal]
          exact recursive.sourceWithin
        abruptTargetRestriction := recursive.abruptTargetRestriction
        exitScope := recursive.exitScope }⟩

def toOpen
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {post body : Functions.Block}
    {initial final : Fresh.State}
    {layout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (loop :
      ScopedLoopResult contract codeRel program sourceControl
        (.lit (EvmYul.UInt256.ofNat 1))
        ctx.withoutLoopControl post
        (ctx.withLoopControl ctx.scope ctx.scope) body
        final layout sourceFinal target ctx.withoutLoopControl)
    (hFresh : Fresh.Extends initial final)
    (hScope : StateRelation.Vars.NamesWithin final.used ctx.scope)
    (hControl :
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx) :
    Nonempty
      ({ result :
          FunctionsObserverOutcome.ScopedOpenResult
            contract codeRel program
            [.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
              post body]
            initial final layout sourceFinal target ctx
            (sourceControl := sourceControl) //
          result.outcome.mode = .regular →
            result.finalLayout = layout }) := by
  obtain ⟨loopFuel, hLoop⟩ := loop.run
  let commonFuel := max 1 loopFuel
  have hInit :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx.withoutLoopControl commonFuel { stmts := [] } target =
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
  have hLoop' :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx.withoutLoopControl
          (.lit (EvmYul.UInt256.ofNat 1))
          ctx.withoutLoopControl post
          (ctx.withLoopControl ctx.scope ctx.scope)
          body commonFuel target =
        .ok loop.outcome :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [commonFuel]) hLoop
  rcases
      Functions.Source.Effectful.Stmt.runForLoop_regular_or_exit
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hLoop' with hRegular | hExit
  · have hLoopEq :
        loop.outcome =
          Functions.Source.Effectful.Outcome.regular loop.outcome.state :=
      Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
    have hLoopRegular := hLoop'
    rw [hLoopEq] at hLoopRegular
    let targetFinal :=
      loop.outcome.state.withSource
        (loop.outcome.state.source.restrictTo ctx.scope)
    have hStmt :
        Functions.Source.Effectful.Stmt.run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx (commonFuel + 1)
            (.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
              post body) target =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetFinal, ctx) := by
      simpa [targetFinal] using
        Functions.Source.Effectful.Stmt.run_for_regular_of_runs
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hInit hLoopRegular
    obtain ⟨runFuel, hRun⟩ :=
      Functions.Source.Effectful.Block.runOpen_singleton_of_run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hStmt
    obtain ⟨sourceShared, sourceVars, hSource⟩ :=
      FunctionsObserverOutcome.ModeRel.target_regular_source_ok
        loop.relation.mode hRegular
    have hLayoutEq := loop.regularLayout hRegular
    have hExact :
        StateRelation.Replay.ScopedExactRel codeRel loop.finalLayout
          sourceFinal targetFinal := by
      have hLoopExact := loop.relation.exact hRegular
      have hRevived :
          sourceFinal.withSource sourceFinal.source.reviveJump =
            sourceFinal := by
        rw [hSource]
        change sourceFinal.withSource (.Ok sourceShared sourceVars) =
          sourceFinal
        rw [← hSource]
        exact
          Simulation.ResourceReplay.State.withSource_self sourceFinal
      rw [hRevived] at hLoopExact
      simpa [targetFinal] using
        StateRelation.Replay.scopedExact_restrict_target_scope
          hLoopExact
          (by
            intro name hMem
            exact hControl.scope name (by simpa [hLayoutEq] using hMem))
    exact
      ⟨⟨
        { finalLayout := loop.finalLayout
          outcome :=
            Functions.Source.Effectful.Outcome.regular targetFinal
          finalCtx := ctx
          run := ⟨runFuel, hRun⟩
          relation :=
            FunctionsObserverOutcome.ScopedOutcomeRel.regular
              hSource hExact
          domain := by
            simpa [targetFinal, Locals.Source.State.restrictTo] using
              loop.domain.restrictTo
          scope := hScope
          control := Functions.Source.Ctx.SameControl.refl ctx
          freshExtends := hFresh
          retains := by
            intro _hResultRegular name hMem
            simpa [hLayoutEq] using hMem
          layoutWithin := loop.layoutWithin
          sourceDefined :=
            FunctionsObserverOutcome.SourceDefined.of_scopedExact hExact
          abruptTargetRestriction := by
            simp [FunctionsObserverOutcome.AbruptTargetRestriction]
          layoutScope := by
            intro _hResultRegular name hMem
            exact hControl.scope name (by simpa [hLayoutEq] using hMem)
          exitScope := by
            simp [FunctionsObserverOutcome.ExitScopeRel] },
        fun _hResultRegular => hLayoutEq⟩⟩
  · have hStmt :
        Functions.Source.Effectful.Stmt.run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx (commonFuel + 1)
            (.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
              post body) target =
          .ok (loop.outcome, ctx) :=
      Functions.Source.Effectful.Stmt.run_for_exit_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hExit hInit hLoop'
    obtain ⟨runFuel, hRun⟩ :=
      Functions.Source.Effectful.Block.runOpen_singleton_of_run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hStmt
    exact
      ⟨⟨
        { finalLayout := loop.finalLayout
          outcome := loop.outcome
          finalCtx := ctx
          run := ⟨runFuel, hRun⟩
          relation := loop.relation
          domain := loop.domain
          scope := hScope
          control := Functions.Source.Ctx.SameControl.refl ctx
          freshExtends := hFresh
          retains := by
            intro hResultRegular
            exact (hExit.not_regular hResultRegular).elim
          layoutWithin := loop.layoutWithin
          sourceDefined := loop.sourceDefined
          abruptTargetRestriction := by
            cases hMode : loop.outcome.mode with
            | regular =>
                exact (hExit.not_regular hMode).elim
            | brk =>
                exact
                  (hExit.ne_brk loop.outcome.state
                    (Functions.Source.Effectful.Outcome.eq_brk_of_mode
                      hMode)).elim
            | cont =>
                exact
                  (hExit.ne_cont loop.outcome.state
                    (Functions.Source.Effectful.Outcome.eq_cont_of_mode
                      hMode)).elim
            | leave =>
                simpa [FunctionsObserverOutcome.AbruptTargetRestriction,
                  hMode, Functions.Source.Ctx.withoutLoopControl] using
                  loop.abruptTargetRestriction
            | halt kind =>
                simp [FunctionsObserverOutcome.AbruptTargetRestriction,
                  hMode]
          layoutScope := by
            intro hResultRegular
            exact (hExit.not_regular hResultRegular).elim
          exitScope := by
            cases hMode : loop.outcome.mode with
            | regular =>
                exact (hExit.not_regular hMode).elim
            | brk =>
                exact
                  (hExit.ne_brk loop.outcome.state
                    (Functions.Source.Effectful.Outcome.eq_brk_of_mode
                      hMode)).elim
            | cont =>
                exact
                  (hExit.ne_cont loop.outcome.state
                    (Functions.Source.Effectful.Outcome.eq_cont_of_mode
                      hMode)).elim
            | leave =>
                simpa [FunctionsObserverOutcome.ExitScopeRel, hMode,
                  Functions.Source.Ctx.withoutLoopControl] using
                  loop.exitScope
            | halt kind =>
                simpa [FunctionsObserverOutcome.ExitScopeRel, hMode] using
                  loop.exitScope },
        fun hResultRegular => (hExit.not_regular hResultRegular).elim⟩⟩

end ScopedLoopResult

def RecursiveOpenStmtForward
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
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedStmtResult contract codeRel targetProgram.toFunctions
          stmt lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave
          (sourceControl := sourceControl))

def RecursiveOpenListForward
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
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.execSeq
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmts (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedListResult contract codeRel targetProgram.toFunctions
          stmts lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave
          (sourceControl := sourceControl))

def RecursiveScopedLoopForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
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
    sourceFuel < bound →
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
      Stmt.List.toBlockUncheckedFuel?
          compilerFuel
          afterCond post =
        some (lowerPost, afterPost) →
      Stmt.List.toBlockUncheckedFuel?
          compilerFuel
          afterPost body =
        some (lowerBody, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      StateRelation.Vars.NamesWithin before.used layout →
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.For cond post body)
          (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedLoopResult contract codeRel targetProgram.toFunctions
          sourceControl (.lit (EvmYul.UInt256.ofNat 1))
          ctx.withoutLoopControl lowerPost
          (ctx.withLoopControl ctx.scope ctx.scope)
          { stmts :=
              preCond ++
                .if_
                  (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                  { stmts := [.brk] } ::
                lowerBody.stmts }
          after layout sourceFinal target ctx.withoutLoopControl)

def RecursiveOpenCompoundForward
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
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedStmtResult contract codeRel targetProgram.toFunctions
          stmt lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave
          (sourceControl := sourceControl))

namespace RecursiveOpenStmtForward

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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hCompound :
      RecursiveOpenCompoundForward contract transcript codeRel
        sourceProgram targetProgram profile (bound + 1)) :
    RecursiveOpenStmtForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source sourceFinal target ctx canBreak canContinue canLeave
    hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
  have hValueAt :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel :=
    hValue.mono (by omega)
  have hExprAt :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel :=
    hValueAt.expression
  have hBodyAt :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel :=
    hBody.mono (by omega)
  cases stmt with
  | Block body =>
      exact
        hCompound (.block body) hFuel hOk hNames hLower hRel hDomain
          hScope hLayout hControl hRun
  | Switch scrutinee cases defaultBody =>
      exact
        hCompound (.switch scrutinee cases defaultBody)
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
  | For cond post body =>
      exact
        hCompound (.forLoop cond post body)
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
  | If cond body =>
      exact
        hCompound (.ifThen cond body)
          hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
  | Let names value? =>
      cases value? with
      | none =>
          have hNamesUsed :
              StateRelation.Vars.NamesWithin before.used
                (identNames names) := by
            simpa [Stmt.names] using hNames
          obtain ⟨⟨result, _hFuelBound⟩⟩ :=
            FunctionsObserverStatement.OpenResult.of_let_none
              (sourceControl := sourceControl)
              hLower hRel hDomain hScope hLayout hControl.scope
              hNamesUsed hRun
          exact ⟨ScopedStmtResult.ofStatement result hControl⟩
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
            obtain ⟨result⟩ :=
              FunctionsObserverStatement.OpenResult.of_let_call
                (sourceControl := sourceControl)
                hDecomposition hProgramOk hExprOk hLower hRel hDomain
                hScope hLayout hControl.scope hNamesUsed hValueAt hBodyAt hRun
            exact ⟨ScopedStmtResult.ofStatement result hControl⟩
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
            obtain ⟨result⟩ :=
              FunctionsObserverStatement.OpenResult.of_let_one
                (codeOverride := some sourceProgram.contract)
                (sourceControl := sourceControl)
                hNotFunctionCall hExprOk hLower hRel hDomain hScope
                hLayout hControl.scope hNameUsed hValueAt hRun
            exact ⟨ScopedStmtResult.ofStatement result hControl⟩
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
        obtain ⟨result⟩ :=
          FunctionsObserverStatement.OpenResult.of_assign_call
            (sourceControl := sourceControl)
            hDecomposition hProgramOk hExprOk hLower hRel hDomain
            hScope hLayout hControl.scope hValueAt hBodyAt hRun
        exact ⟨ScopedStmtResult.ofStatement result hControl⟩
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
        obtain ⟨result⟩ :=
          FunctionsObserverStatement.OpenResult.of_assign_one
            (sourceControl := sourceControl)
            hNotFunctionCall hExprOk hLower hRel hDomain hScope hLayout
            hControl.scope hValueAt hRun
        exact ⟨ScopedStmtResult.ofStatement result hControl⟩
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
              obtain ⟨result⟩ :=
                FunctionsObserverStatement.OpenResult.of_expr_primitive
                  (sourceControl := sourceControl)
                  hNonterminal hExprOk hLower hRel hDomain hScope hLayout
                  hControl.scope hExprAt hRun
              exact ⟨ScopedStmtResult.ofStatement result hControl⟩
          | inr functionName =>
              have hExprOk :
                  SolcValidation.ExprOk? profile sourceProgram.contract
                      layout 0 (.Call (.inr functionName) args) =
                    true := by
                simpa [SolcValidation.StmtOk?] using hOk
              obtain ⟨result⟩ :=
                FunctionsObserverStatement.OpenResult.of_expr_call
                  (sourceControl := sourceControl)
                  hDecomposition hProgramOk hExprOk hLower hRel hDomain
                  hScope hLayout hControl.scope hExprAt hBodyAt hRun
              exact ⟨ScopedStmtResult.ofStatement result hControl⟩
  | Break =>
      have hEnabled : canBreak = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      have hWithin := hControl.breakScope
      rw [ScopeOptionWithin, hEnabled] at hWithin
      obtain
          ⟨breakLayout, targetBreakScope,
            hSourceBreakScope, hBreakScope,
            hBreakSubset, hBreakTarget⟩ := hWithin
      obtain ⟨⟨result, _hFuelBound⟩⟩ :=
        FunctionsObserverStatement.OpenResult.of_break
          (sourceControl := sourceControl)
          hLower hRel hDomain hScope hLayout
          hSourceBreakScope hBreakScope hBreakSubset hBreakTarget hRun
      exact ⟨ScopedStmtResult.ofStatement result hControl⟩
  | Continue =>
      have hEnabled : canContinue = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      have hWithin := hControl.continueScope
      rw [ScopeOptionWithin, hEnabled] at hWithin
      obtain
          ⟨continueLayout, targetContinueScope,
            hSourceContinueScope, hContinueScope,
            hContinueSubset, hContinueTarget⟩ := hWithin
      obtain ⟨⟨result, _hFuelBound⟩⟩ :=
        FunctionsObserverStatement.OpenResult.of_continue
          (sourceControl := sourceControl)
          hLower hRel hDomain hScope hLayout
          hSourceContinueScope hContinueScope
          hContinueSubset hContinueTarget hRun
      exact ⟨ScopedStmtResult.ofStatement result hControl⟩
  | Leave =>
      have hEnabled : canLeave = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      have hWithin := hControl.leaveScope
      rw [ScopeOptionWithin, hEnabled] at hWithin
      obtain
          ⟨leaveLayout, targetLeaveScope,
            hSourceLeaveScope, hLeaveScope,
            hLeaveSubset, hLeaveTarget⟩ := hWithin
      obtain ⟨⟨result, _hFuelBound⟩⟩ :=
        FunctionsObserverStatement.OpenResult.of_leave
          (sourceControl := sourceControl)
          hLower hRel hDomain hScope hLayout
          hSourceLeaveScope hLeaveScope hLeaveSubset hLeaveTarget hRun
      exact ⟨ScopedStmtResult.ofStatement result hControl⟩

end RecursiveOpenStmtForward

namespace RecursiveOpenListForward

theorem ofStmt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hStmt :
      RecursiveOpenStmtForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveOpenListForward contract transcript codeRel
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
          let result :=
            FunctionsObserverOutcome.ScopedOpenResult.empty
              (contract := contract) (program := targetProgram.toFunctions)
              (sourceControl := sourceControl)
              hRel hDomain hScope hLayout hControl.scope
          exact
            ⟨{ openResult := result
               regularLayout := by
                 intro _hRegular
                 rfl
               regularControl := by
                 intro _hRegular
                 exact hControl }⟩
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
          have hPreviousBound : sourcePrevious < bound := by
            omega
          obtain ⟨hHeadOk, hTailOk⟩ :=
            SolcValidation.stmtsOk_cons_parts hOk
          have hHeadNames :
              StateRelation.Vars.NamesWithin before.used
                (Stmt.names head) := by
            intro name hMem
            exact hNames name (List.mem_append_left _ hMem)
          obtain ⟨headResult⟩ :=
            hStmt hPreviousBound hHeadOk hHeadNames hLowerHead
              hRel hDomain hScope hLayout hControl hHeadRun
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
            obtain ⟨tailResult⟩ :=
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
            let result :=
              FunctionsObserverOutcome.ScopedOpenResult.appendRegular
                headResult.openResult hRegular tailResult.openResult
            exact
              ⟨{ openResult := result
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
                   exact tailResult.regularControl hResultRegular }⟩
          · obtain ⟨jump, hSourceAfterHead⟩ :=
              FunctionsObserverOutcome.ModeRel.target_nonregular_source_checkpoint
                headResult.openResult.relation.mode hRegular
            have hSourceFinal : sourceFinal = sourceAfterHead := by
              simpa [ObserverSemantics.SourceReplay.stateModel,
                hSourceAfterHead] using hTailRun
            subst sourceFinal
            have hTailFresh : Fresh.Extends middle after :=
              Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerTail
            let result :=
              FunctionsObserverOutcome.ScopedOpenResult.appendNonregular
                (rightLower := lowerTail)
                headResult.openResult hRegular hTailFresh
            exact
              ⟨{ openResult := result
                 regularLayout := by
                   intro hResultRegular
                   exact (hRegular hResultRegular).elim
                 regularControl := by
                   intro hResultRegular
                   exact (hRegular hResultRegular).elim }⟩

end RecursiveOpenListForward

namespace RecursiveOpenCompoundForward

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
    {value : Word}
    (hList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (prepared :
      FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel targetProgram.toFunctions
        preCond lowerCond condFresh layout sourceAfterCond
        target bodyBase value)
    (hFuel : sourceFuel < bound)
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
      ControlContextRel sourceControl layout true true canLeave bodyBase)
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
      (ClosedListResult contract codeRel targetProgram.toFunctions
        sourceControl
        (preCond ++
          .if_
              (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
              { stmts := [.brk] } ::
            lowerBody.stmts)
        initial final layout sourceAfterBody target bodyBase) := by
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
    obtain ⟨preFuel, hPreRun⟩ := prepared.prepared.run
    have hExtends :=
      Functions.Source.Effectful.Block.runOpen_scopeExtends
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hPreRun
    exact fun name hMem =>
      hExtends name (hControl.scope name hMem)
  have hPreparedControl :
      ControlContextRel sourceControl layout true true canLeave
        prepared.prepared.finalCtx :=
    ControlContextRel.transport hControl
      (fun _name hMem => hMem)
      prepared.prepared.control hPreparedLayoutScope
  obtain ⟨bodyResult⟩ :=
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
      (by omega) hBodyOk hBodyNames hLowerBodyList
      prepared.relation
      (prepared.prepared.domain.mono hBodyInitial)
      (prepared.prepared.scope.mono hBodyInitial)
      hLayoutBodyInitial
      hPreparedControl hBodyListRun
  exact
    ScopedListResult.closeForGuardBody prepared bodyResult hNonzero
      hFresh
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact
        prepared.relation)
      hLayout hControl hSourceAfterBody

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
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (bodyResult :
      ContinuingBodyResult contract codeRel targetProgram.toFunctions
        lowerBody bodyFinal layout sourceAfterBody target bodyBase)
    (hFuel : sourceFuel < bound)
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
      ControlContextRel sourceControl layout false false canLeave postBase)
    (hPostRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block post) (some sourceProgram.contract)
          (sourceAfterBody.withSource sourceAfterBody.source.reviveJump) =
        .ok sourceAfterPost) :
    Nonempty
      (ClosedListResult contract codeRel targetProgram.toFunctions
        sourceControl lowerPost.stmts postInitial final layout
        sourceAfterPost bodyResult.outcome.state postBase) := by
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
  obtain ⟨postResult⟩ :=
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
      (by omega) hPostOk hPostNames hLowerPostList
      bodyResult.relation
      (bodyResult.targetDomain hBodyScope)
      hPostScope hLayout hControl hPostListRun
  obtain ⟨closed⟩ :=
    ScopedListResult.close postResult
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact
        bodyResult.relation)
      hLayout hControl hSourceAfterPost
  exact ⟨closed.monoFresh hFinalFresh⟩

theorem scopedLoop
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveScopedLoopForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel sourceControl before after afterCond afterPost
        layout cond post body preCond lowerCond lowerPost lowerBody
        source sourceFinal target ctx canBreak canContinue canLeave
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
          (by omega) hCondOk hLowerCond hRel hDomain
          hBodyBaseScope hCondValues
      obtain ⟨prepared⟩ := preparedNonempty
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
      have hBodyInitial : Fresh.Extends afterCond afterPost :=
        hPostFresh
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
          ControlContextRel
            (ControlContextRel.forBodySourceControl layout sourceControl)
            layout true true canLeave
            (ctx.withLoopControl ctx.scope ctx.scope) :=
        ControlContextRel.forBody hControl
      have hPostControl :
          ControlContextRel
            (ControlContextRel.forPostSourceControl sourceControl)
            layout false false canLeave ctx.withoutLoopControl :=
        ControlContextRel.forPost hControl
      cases hLoopCase with
      | false hZero hFinal =>
          have hSourceFinal : sourceFinal = sourceAfterCond := by
            rw [hFinal]
            change
              sourceAfterCond.withSource
                  (sourceAfterCond.source.overwrite? source.source) =
                sourceAfterCond
            rw [hSource]
            change
              sourceAfterCond.withSource sourceAfterCond.source =
                sourceAfterCond
            exact
              Simulation.ResourceReplay.State.withSource_self
                sourceAfterCond
          exact
            ScopedLoopResult.ofFalse prepared hZero
              (Fresh.Extends.trans hPostFresh hBodyFresh)
              (hLayout.mono hFresh)
              (by
                simpa [Functions.Source.Ctx.withoutLoopControl] using
                  hControl.scope)
              rfl hSourceFinal
      | bodyOutOfFuel hNonzero hBody hBodySource hFinal =>
          rename_i afterBody
          obtain ⟨closedBody⟩ :=
            closeGuardedBody
              (sourceControl :=
                ControlContextRel.forBodySourceControl layout sourceControl)
              hList prepared (by omega) hBodyOk hBodyNamesAfterPost
              hLowerBody hBodyInitial hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          change afterBody.source = .OutOfFuel at hBodySource
          have hImpossible := closedBody.relation.mode
          rw [hBodySource] at hImpossible
          simp [FunctionsObserverOutcome.ModeRel] at hImpossible
      | bodyBreak hNonzero hBody hBodySource hFinal =>
          rename_i afterBody shared store
          obtain ⟨closedBody⟩ :=
            closeGuardedBody
              (sourceControl :=
                ControlContextRel.forBodySourceControl layout sourceControl)
              hList prepared (by omega) hBodyOk hBodyNamesAfterPost
              hLowerBody hBodyInitial hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          have hSourceFinal :
              sourceFinal =
                afterBody.withSource
                  afterBody.source.reviveJump := by
            rw [hFinal]
            change
              afterBody.withSource
                  (afterBody.source.reviveJump.overwrite? source.source) =
                afterBody.withSource afterBody.source.reviveJump
            rw [hSource]
            rfl
          change
            afterBody.source = .Checkpoint (.Break shared store)
            at hBodySource
          exact
            ScopedLoopResult.ofBodyBreak closedBody hBodySource
              hSourceFinal
              (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                target)
      | bodyLeave hNonzero hBody hBodySource hFinal =>
          rename_i afterBody shared store
          obtain ⟨closedBody⟩ :=
            closeGuardedBody
              (sourceControl :=
                ControlContextRel.forBodySourceControl layout sourceControl)
              hList prepared (by omega) hBodyOk hBodyNamesAfterPost
              hLowerBody hBodyInitial hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          have hSourceFinal : sourceFinal = afterBody := by
            rw [hFinal]
            change
              afterBody.withSource
                  (afterBody.source.overwrite? source.source) =
                afterBody
            rw [hSource]
            exact
              Simulation.ResourceReplay.State.withSource_self
                afterBody
          change
            afterBody.source = .Checkpoint (.Leave shared store)
            at hBodySource
          exact
            ScopedLoopResult.ofBodyLeave closedBody hBodySource
              hSourceFinal rfl
              (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                target)
      | postOutOfFuel hNonzero hBody hBodyContinues hPost
          hPostSource hFinal =>
          rename_i afterBody afterPost
          obtain ⟨closedBody⟩ :=
            closeGuardedBody
              (sourceControl :=
                ControlContextRel.forBodySourceControl layout sourceControl)
              hList prepared (by omega) hBodyOk hBodyNamesAfterPost
              hLowerBody hBodyInitial hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          obtain ⟨bodyResult⟩ :=
            ClosedListResult.continuingBody closedBody hBodyContinues rfl
          obtain ⟨closedPost⟩ :=
            closeLoopPost
              (sourceControl :=
                ControlContextRel.forPostSourceControl sourceControl)
              hList bodyResult (by omega) hPostOk hPostNamesAfterCond
              hLowerPost hBodyFresh
              (by
                simpa [Functions.Source.Ctx.withLoopControl] using
                  hScopeAfterCond)
              (by
                simpa [Functions.Source.Ctx.withoutLoopControl] using
                  hScopeAfterCond)
              hLayoutAfterCond hPostControl hPost
          change afterPost.source = .OutOfFuel at hPostSource
          have hImpossible := closedPost.relation.mode
          rw [hPostSource] at hImpossible
          simp [FunctionsObserverOutcome.ModeRel] at hImpossible
      | postLeave hNonzero hBody hBodyContinues hPost
          hPostSource hFinal =>
          rename_i afterBody afterPost shared store
          obtain ⟨closedBody⟩ :=
            closeGuardedBody
              (sourceControl :=
                ControlContextRel.forBodySourceControl layout sourceControl)
              hList prepared (by omega) hBodyOk hBodyNamesAfterPost
              hLowerBody hBodyInitial hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          obtain ⟨bodyResult⟩ :=
            ClosedListResult.continuingBody closedBody hBodyContinues rfl
          obtain ⟨closedPost⟩ :=
            closeLoopPost
              (sourceControl :=
                ControlContextRel.forPostSourceControl sourceControl)
              hList bodyResult (by omega) hPostOk hPostNamesAfterCond
              hLowerPost hBodyFresh
              (by
                simpa [Functions.Source.Ctx.withLoopControl] using
                  hScopeAfterCond)
              (by
                simpa [Functions.Source.Ctx.withoutLoopControl] using
                  hScopeAfterCond)
              hLayoutAfterCond hPostControl hPost
          have hSourceFinal : sourceFinal = afterPost := by
            rw [hFinal]
            change
              afterPost.withSource
                  (afterPost.source.overwrite? source.source) =
                afterPost
            rw [hSource]
            exact
              Simulation.ResourceReplay.State.withSource_self
                afterPost
          change
            afterPost.source = .Checkpoint (.Leave shared store)
            at hPostSource
          cases lowerPost
          exact
            ScopedLoopResult.ofPostLeave bodyResult closedPost
              hPostSource hSourceFinal rfl
      | recurse hNonzero hBody hBodyContinues hPost hPostRecurs
          hRecursive hFinal =>
          rename_i afterBody sourceAfterPost afterLoop
          obtain ⟨closedBody⟩ :=
            closeGuardedBody
              (sourceControl :=
                ControlContextRel.forBodySourceControl layout sourceControl)
              hList prepared (by omega) hBodyOk hBodyNamesAfterPost
              hLowerBody hBodyInitial hFresh hLayout hLayoutAfterPost
              hBodyControl hNonzero hBody
          obtain ⟨bodyResult⟩ :=
            ClosedListResult.continuingBody closedBody hBodyContinues rfl
          obtain ⟨closedPost⟩ :=
            closeLoopPost
              (sourceControl :=
                ControlContextRel.forPostSourceControl sourceControl)
              hList bodyResult (by omega) hPostOk hPostNamesAfterCond
              hLowerPost hBodyFresh
              (by
                simpa [Functions.Source.Ctx.withLoopControl] using
                  hScopeAfterCond)
              (by
                simpa [Functions.Source.Ctx.withoutLoopControl] using
                  hScopeAfterCond)
              hLayoutAfterCond hPostControl hPost
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
                    Yul.Source.Effectful.LoopPostRecurs sourceAfterPost.source
                    at hPostRecurs
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
                    ControlContextRel.forPostSourceControl, hMode] at hExit
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
                    ControlContextRel.forPostSourceControl, hMode] at hExit
          | Ok postShared postStore =>
              have hPostMode :
                  closedPost.outcome.mode = .regular := by
                have hModeRel := closedPost.relation.mode
                rw [hSourcePost] at hModeRel
                exact
                  FunctionsObserverOutcome.ModeRel.source_ok_target_regular
                    hModeRel
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
              obtain ⟨recursive⟩ :=
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
                  (by omega) hCondOk hPostOk hBodyOk hCondNames
                  hPostNames hBodyNames hLowerCond hLowerPost hLowerBody
                  hPostRel hPostDomain hScope hLayout hControl hRecursive'
              have hSourceFinal : sourceFinal = afterLoop := by
                rw [hFinal]
                change
                  afterLoop.withSource
                      (afterLoop.source.overwrite? source.source) =
                    afterLoop
                rw [hSource]
                exact
                  Simulation.ResourceReplay.State.withSource_self
                    afterLoop
              cases lowerPost
              exact
                ScopedLoopResult.ofRecurse bodyResult closedPost
                  hSourcePost recursive hSourceFinal

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
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
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
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block body) (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      (ScopedStmtResult contract codeRel targetProgram.toFunctions
        (.Block body) lower before after layout sourceFinal target ctx
        canBreak canContinue canLeave
        (sourceControl := sourceControl)) := by
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
  obtain ⟨bodyResult⟩ :=
    hList (sourceFuel := sourcePrevious)
      (compilerFuel := listCompilerFuel)
      (before := before) (after := after)
      (layout := layout) (stmts := body) (lower := lowerStmts)
      (source := source) (sourceFinal := sourceAfterBody)
      (target := target) (ctx := ctx)
      (canBreak := canBreak) (canContinue := canContinue)
      (canLeave := canLeave)
      (by omega) hBodyOk hBodyNames hLowerList hRel hDomain
      hScope hLayout hControl hBodyRun
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_block
      bodyResult.openResult
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel)
      hScope hLayout hControl hSourceFinal
  exact ⟨ScopedStmtResult.ofStatement result hControl⟩

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
    (hExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
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
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.If cond body) (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      (ScopedStmtResult contract codeRel targetProgram.toFunctions
        (.If cond body) lower before after layout sourceFinal target ctx
        canBreak canContinue canLeave
        (sourceControl := sourceControl)) := by
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
  obtain ⟨prepared⟩ :=
    hExpr (exprFuel := sourcePrevious)
      (before := before) (after := middle)
      (layout := layout) (expr := cond)
      (pre := preCond) (lower := lowerCond)
      (source := source) (source' := sourceAfterCond)
      (target := target) (ctx := ctx) (value := condValue)
      (by omega) hOkParts.1 hLowerCond hRel hDomain hScope hCondRun
  obtain ⟨preFuel, hPreRun⟩ := prepared.prepared.run
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
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave
        prepared.prepared.finalCtx :=
    ControlContextRel.transport hControl
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
            .ok (prepared.prepared.evalTarget, false) := by
        exact
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
      have hEmpty :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx 1
              { stmts := [] } prepared.prepared.evalTarget =
            .ok
              (Functions.Source.Effectful.Outcome.regular
                prepared.prepared.evalTarget,
                prepared.prepared.finalCtx) := by
        simpa using
          Functions.Source.Effectful.Block.runOpen_nil
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions prepared.prepared.finalCtx 0
            prepared.prepared.evalTarget
      obtain ⟨ifFuel, hIfRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_cons_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hIfStmt hEmpty
      obtain ⟨targetFuel, hTargetRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions preCond [.if_ lowerCond lowerBody]
          ctx prepared.prepared.finalCtx target
          prepared.prepared.preTarget
          (Functions.Source.Effectful.Outcome.regular
            prepared.prepared.evalTarget)
          prepared.prepared.finalCtx
          ⟨preFuel, hPreRun⟩ ⟨ifFuel, hIfRun⟩
      obtain ⟨sourceShared, sourceVars, hSource, _hShared,
          _hScoped, _hSourceDomain⟩ :=
        prepared.relation.2
      have hOutcomeRel :
          FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
            sourceAfterCond
            (Functions.Source.Effectful.Outcome.regular
              prepared.prepared.evalTarget) :=
        FunctionsObserverOutcome.ScopedOutcomeRel.regular
          hSource prepared.relation
      let result :
          FunctionsObserverOutcome.ScopedOpenResult
            contract codeRel targetProgram.toFunctions
            (preCond ++ [.if_ lowerCond lowerBody])
            before after layout sourceAfterCond target ctx
            (sourceControl := sourceControl) :=
        { finalLayout := layout
          outcome :=
            Functions.Source.Effectful.Outcome.regular
              prepared.prepared.evalTarget
          finalCtx := prepared.prepared.finalCtx
          run := ⟨targetFuel, hTargetRun⟩
          relation := hOutcomeRel
          domain := prepared.prepared.domain.mono hBodyFresh
          scope := prepared.prepared.scope.mono hBodyFresh
          control := prepared.prepared.control
          freshExtends := hFresh
          retains := fun _hRegular _name hMem => hMem
          layoutWithin := hLayout.mono hFresh
          sourceDefined :=
            FunctionsObserverOutcome.SourceDefined.of_scopedExact
              prepared.relation
          abruptTargetRestriction := by
            simp [FunctionsObserverOutcome.AbruptTargetRestriction]
          layoutScope := fun _hRegular => hPreparedLayoutScope
          exitScope := by
            simp [FunctionsObserverOutcome.ExitScopeRel] }
      exact
        ⟨{ openResult := result
           regularLayout := fun _hRegular => rfl
           regularControl := fun _hRegular => hPreparedControl }⟩
  | inl hTrue =>
      obtain ⟨hNonzero, hBodyRun⟩ := hTrue
      have hCondTrue :
          Functions.Source.Effectful.Expr.evalCondition
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              lowerCond prepared.prepared.preTarget =
            .ok (prepared.prepared.evalTarget, true) := by
        exact
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
      obtain ⟨closedBody⟩ :=
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
          (by omega) hBlockOk hBlockNames hBlockLower
          prepared.relation prepared.prepared.domain
          prepared.prepared.scope hLayoutMiddle hPreparedControl hBodyRun
      obtain ⟨bodyFuel, hBodyScoped, hBodyCtx⟩ :=
        Functions.Source.Effectful.Block.runScoped_of_runOpen_singleton_block
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions closedBody.openResult.run
      have hIfStmt :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx
              (bodyFuel + 1) (.if_ lowerCond lowerBody)
              prepared.prepared.preTarget =
            .ok
              (closedBody.openResult.outcome,
                prepared.prepared.finalCtx) :=
        Functions.Source.Effectful.Stmt.run_if_true_of_eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hCondTrue hBodyScoped
      have hIfRun :
          ∃ fuel,
            Functions.Source.Effectful.Block.runOpen
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions prepared.prepared.finalCtx fuel
                { stmts := [.if_ lowerCond lowerBody] }
                prepared.prepared.preTarget =
              .ok
                (closedBody.openResult.outcome,
                  prepared.prepared.finalCtx) := by
        by_cases hRegular :
            closedBody.openResult.outcome.mode = .regular
        · have hOutcomeEq :
              closedBody.openResult.outcome =
                Functions.Source.Effectful.Outcome.regular
                  closedBody.openResult.outcome.state :=
            Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
          have hIfStmtRegular :
              Functions.Source.Effectful.Stmt.run
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions prepared.prepared.finalCtx
                  (bodyFuel + 1) (.if_ lowerCond lowerBody)
                  prepared.prepared.preTarget =
                .ok
                  (Functions.Source.Effectful.Outcome.regular
                    closedBody.openResult.outcome.state,
                    prepared.prepared.finalCtx) := by
            have hIfStmt' := hIfStmt
            rw [hOutcomeEq] at hIfStmt'
            exact hIfStmt'
          have hEmpty :
              Functions.Source.Effectful.Block.runOpen
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions prepared.prepared.finalCtx 1
                  { stmts := [] } closedBody.openResult.outcome.state =
                .ok
                  (Functions.Source.Effectful.Outcome.regular
                    closedBody.openResult.outcome.state,
                    prepared.prepared.finalCtx) := by
            simpa using
              Functions.Source.Effectful.Block.runOpen_nil
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions prepared.prepared.finalCtx 0
                closedBody.openResult.outcome.state
          obtain ⟨regularFuel, hRegularRun⟩ :=
            Functions.Source.Effectful.Block.runOpen_cons_regular_exists
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (outcome :=
                Functions.Source.Effectful.Outcome.regular
                  closedBody.openResult.outcome.state)
              hIfStmtRegular hEmpty
          rw [← hOutcomeEq] at hRegularRun
          exact ⟨regularFuel, hRegularRun⟩
        · exact
            ⟨bodyFuel + 2,
              Functions.Source.Effectful.Block.runOpen_cons_nonregular
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions hIfStmt hRegular⟩
      obtain ⟨targetFuel, hTargetRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions preCond [.if_ lowerCond lowerBody]
          ctx prepared.prepared.finalCtx target
          prepared.prepared.preTarget closedBody.openResult.outcome
          prepared.prepared.finalCtx
          ⟨preFuel, hPreRun⟩ hIfRun
      rcases lowerBody with ⟨lowerBodyStmts⟩
      let bodyResult :
          FunctionsObserverStatement.OpenResult.Result
            contract codeRel targetProgram.toFunctions (.Block body)
            [.block { stmts := lowerBodyStmts }]
            middle after layout sourceFinal
            prepared.prepared.evalTarget prepared.prepared.finalCtx
            (sourceControl := sourceControl) :=
        { openResult := closedBody.openResult
          regularLayout := closedBody.regularLayout }
      have hTargetForResult :
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
                (bodyResult.openResult.outcome,
                  bodyResult.openResult.finalCtx) := by
        refine ⟨targetFuel, ?_⟩
        change
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions ctx targetFuel
              { stmts :=
                  preCond ++
                    [.if_ lowerCond { stmts := lowerBodyStmts }] }
              target =
            .ok
              (closedBody.openResult.outcome,
                closedBody.openResult.finalCtx)
        rw [hBodyCtx]
        exact hTargetRun
      obtain ⟨result⟩ :=
        FunctionsObserverStatement.OpenResult.of_if_true_prepared
          (cond := cond) (body := body)
          (lowerBody := lowerBodyStmts)
          hCondFresh prepared bodyResult hTargetForResult
      exact
        ⟨ScopedStmtResult.ofStatement result hControl⟩

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
    (hExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
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
      ControlContextRel sourceControl layout
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
      (ScopedStmtResult contract codeRel targetProgram.toFunctions
        (.Switch scrutinee cases defaultBody) lower before after layout
        sourceFinal target ctx canBreak canContinue canLeave
        (sourceControl := sourceControl)) := by
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
  have hFresh : Fresh.Extends before after :=
    Fresh.Extends.trans hScrutineeFresh hSelectionFresh
  obtain ⟨prepared⟩ :=
    hExpr (exprFuel := sourcePrevious)
      (before := before) (after := afterScrutinee)
      (layout := layout) (expr := scrutinee)
      (pre := preScrutinee) (lower := lowerScrutinee)
      (source := source) (source' := sourceAfterScrutinee)
      (target := target) (ctx := ctx) (value := value)
      (by omega) hOkParts.1 hLowerScrutinee hRel hDomain hScope
      hScrutineeRun
  obtain ⟨preFuel, hPreRun⟩ := prepared.prepared.run
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
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave
        prepared.prepared.finalCtx :=
    ControlContextRel.transport hControl
      (fun _name hMem => hMem)
      prepared.prepared.control hPreparedLayoutScope
  cases hSelection with
  | none hSourceSelection hTargetSelection _hSelectionFresh =>
      rw [hSourceSelection] at hSelectedRun
      obtain
          ⟨_blockFuel, sourceAfterEmpty, _hBlockSourceFuel,
            hEmptySeq, hSourceFinal⟩ :=
        Yul.Source.Effectful.exec_block_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hSelectedRun
      obtain ⟨_seqFuel, _hSeqSourceFuel, hSourceAfterEmpty⟩ :=
        Yul.Source.Effectful.execSeq_nil_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hEmptySeq
      subst sourceAfterEmpty
      obtain ⟨sourceShared, sourceVars, hSource, _hShared,
          _hScoped, _hSourceDomain⟩ :=
        prepared.relation.2
      have hRestrict :
          sourceAfterScrutinee.source.restrictStoreTo
              sourceAfterScrutinee.source.store =
            sourceAfterScrutinee.source := by
        rw [hSource]
        simp only [EvmYul.Yul.State.store,
          EvmYul.Yul.State.restrictStoreTo]
        rw [StateRelation.VarStore.restrict_self]
      have hSourceFinalEq :
          sourceFinal = sourceAfterScrutinee := by
        change
          sourceFinal =
            sourceAfterScrutinee.withSource
              (sourceAfterScrutinee.source.restrictStoreTo
                sourceAfterScrutinee.source.store)
          at hSourceFinal
        rw [hSourceFinal, hRestrict]
        exact
          Simulation.ResourceReplay.State.withSource_self
            sourceAfterScrutinee
      rw [hSourceFinalEq]
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
      obtain ⟨switchFuel, hSwitchRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_singleton_of_run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hSwitchStmt
      obtain ⟨targetFuel, hTargetRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
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
          ⟨preFuel, hPreRun⟩ ⟨switchFuel, hSwitchRun⟩
      have hOutcomeRel :
          FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
            sourceAfterScrutinee
            (Functions.Source.Effectful.Outcome.regular
              prepared.prepared.evalTarget) :=
        FunctionsObserverOutcome.ScopedOutcomeRel.regular
          hSource prepared.relation
      let result :
          FunctionsObserverOutcome.ScopedOpenResult
            contract codeRel targetProgram.toFunctions
            (preScrutinee ++
              [.switch lowerScrutinee lowerCases lowerDefault])
            before after layout sourceAfterScrutinee target ctx
            (sourceControl := sourceControl) :=
        { finalLayout := layout
          outcome :=
            Functions.Source.Effectful.Outcome.regular
              prepared.prepared.evalTarget
          finalCtx := prepared.prepared.finalCtx
          run := ⟨targetFuel, hTargetRun⟩
          relation := hOutcomeRel
          domain := prepared.prepared.domain.mono hSelectionFresh
          scope := prepared.prepared.scope.mono hSelectionFresh
          control := prepared.prepared.control
          freshExtends := hFresh
          retains := fun _hRegular _name hMem => hMem
          layoutWithin := hLayout.mono hFresh
          sourceDefined :=
            FunctionsObserverOutcome.SourceDefined.of_scopedExact
              prepared.relation
          abruptTargetRestriction := by
            simp [FunctionsObserverOutcome.AbruptTargetRestriction]
          layoutScope := fun _hRegular => hPreparedLayoutScope
          exitScope := by
            simp [FunctionsObserverOutcome.ExitScopeRel] }
      exact
        ⟨{ openResult := result
           regularLayout := fun _hRegular => rfl
           regularControl := fun _hRegular => hPreparedControl }⟩
  | some hSourceSelection hTargetSelection hSelectedLower
      hBeforeSelected hAfterSelected =>
      rename_i selectedBody selectedLowerBody selectedCompilerFuel
        selectedBefore selectedAfter
      rw [hSourceSelection] at hSelectedRun
      have hSelectedOk :
          SolcValidation.StmtsOk? profile sourceProgram.contract
              ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
              layout canBreak canContinue canLeave selectedBody =
            true :=
        by
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
      obtain ⟨closedBody⟩ :=
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
          (by omega) hBlockOk hBlockNames hBlockLower
          prepared.relation
          (prepared.prepared.domain.mono hBeforeSelected)
          (prepared.prepared.scope.mono hBeforeSelected)
          hSelectedLayout hPreparedControl hSelectedRun
      obtain ⟨bodyFuel, hBodyScoped, hBodyCtx⟩ :=
        Functions.Source.Effectful.Block.runScoped_of_runOpen_singleton_block
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions closedBody.openResult.run
      have hSwitchStmt :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions prepared.prepared.finalCtx
              (bodyFuel + 1)
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
      obtain ⟨switchFuel, hSwitchRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_singleton_of_run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hSwitchStmt
      obtain ⟨targetFuel, hTargetRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions preScrutinee
          [.switch lowerScrutinee lowerCases lowerDefault]
          ctx prepared.prepared.finalCtx target
          prepared.prepared.preTarget closedBody.openResult.outcome
          prepared.prepared.finalCtx
          ⟨preFuel, hPreRun⟩ ⟨switchFuel, hSwitchRun⟩
      rcases selectedLowerBody with ⟨selectedLowerStmts⟩
      let bodyResult :
          FunctionsObserverStatement.OpenResult.Result
            contract codeRel targetProgram.toFunctions (.Block selectedBody)
            [.block { stmts := selectedLowerStmts }]
            selectedBefore selectedAfter layout sourceFinal
            prepared.prepared.evalTarget prepared.prepared.finalCtx
            (sourceControl := sourceControl) :=
        { openResult := closedBody.openResult
          regularLayout := closedBody.regularLayout }
      have hTargetForResult :
          ∃ fuel,
            Functions.Source.Effectful.Block.runOpen
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions ctx fuel
                { stmts :=
                    preScrutinee ++
                      [.switch lowerScrutinee lowerCases lowerDefault] }
                target =
              .ok
                (bodyResult.openResult.outcome,
                  bodyResult.openResult.finalCtx) := by
        refine ⟨targetFuel, ?_⟩
        change
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions ctx targetFuel
              { stmts :=
                  preScrutinee ++
                    [.switch lowerScrutinee lowerCases lowerDefault] }
              target =
            .ok
              (closedBody.openResult.outcome,
                closedBody.openResult.finalCtx)
        rw [hBodyCtx]
        exact hTargetRun
      obtain ⟨result⟩ :=
        FunctionsObserverStatement.OpenResult.of_switch_selected_prepared
          (scrutinee := scrutinee) (cases := cases)
          (defaultBody := defaultBody) (selectedBody := selectedBody)
          (lowerSelected := selectedLowerStmts)
          hScrutineeFresh hBeforeSelected hAfterSelected
          prepared bodyResult hTargetForResult
      exact
        ⟨ScopedStmtResult.ofStatement result hControl⟩

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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound)
    (hFuel : sourceFuel < bound + 1)
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
      ControlContextRel sourceControl layout
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
      (ScopedStmtResult contract codeRel targetProgram.toFunctions
        (.For cond post body) lower before after layout sourceFinal target ctx
        canBreak canContinue canLeave
        (sourceControl := sourceControl)) := by
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
  obtain ⟨loop⟩ :=
    scopedLoop hValue hList
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
      hFuel hOkParts.1 hOkParts.2.1 hOkParts.2.2
      hCondNames hPostNames hBodyNames hLowerCond hLowerPost hLowerBody
      hRel hDomain hScope hLayout hControl hRun
  obtain ⟨opened⟩ :=
    ScopedLoopResult.toOpen loop hFresh (hScope.mono hFresh) hControl
  exact
    ⟨ScopedStmtResult.ofOpen
      (stmt := .For cond post body) opened.1
      (by
        intro hRegular
        simpa [SolcValidation.StmtOutVars] using opened.2 hRegular)
      hControl⟩

theorem ofComponents
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveOpenCompoundForward contract transcript codeRel
      sourceProgram targetProgram profile (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source sourceFinal target ctx canBreak canContinue canLeave
    hCompound hFuel hOk hNames hLower hRel hDomain hScope hLayout
    hControl hRun
  cases hCompound with
  | block body =>
      exact
        block hList hFuel hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun
  | switch scrutinee cases defaultBody =>
      exact
        switch hValue.expression hList hFuel hOk hNames hLower hRel
          hDomain hScope hLayout hControl hRun
  | forLoop cond post body =>
      exact
        forLoop hValue hList hFuel hOk hNames hLower hRel hDomain
          hScope hLayout hControl hRun
  | ifThen cond body =>
      exact
        ifThen hValue.expression hList hFuel hOk hNames hLower hRel
          hDomain hScope hLayout hControl hRun

end RecursiveOpenCompoundForward

namespace RecursiveBodyForward

theorem entryTargetDomain
    {before : Fresh.State} {fn : Functions.FunDef}
    {args : List Word} {paramStore : Locals.Source.Store}
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params)) :
    StateRelation.Vars.TargetDomainWithin before.used
      (Functions.Source.Store.initReturns fn.returns paramStore) := by
  intro name value hLookup
  exact
    hReserved name
      (Functions.Source.Store.initReturns_insertMany_empty_apply_mem
        hParamStore hLookup)

theorem bodyScope
    {before : Fresh.State} {fn : Functions.FunDef}
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params)) :
    StateRelation.Vars.NamesWithin before.used
      (Functions.Source.Effectful.FunDef.bodyCtx fn).scope := by
  simpa [Functions.Source.Effectful.FunDef.bodyCtx] using hReserved

theorem ofList
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hList :
      RecursiveOpenListForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    FunctionsObserverCall.RecursiveBodyForward
      contract transcript codeRel sourceProgram targetProgram profile
        (bound + 1) := by
  intro sourceFuel before after params returns body fn args paramStore
    sourceCaller sourceAfterBody targetCaller hFuel hLower hParams
    hReturns hParamStore hReserved hBodyNames hBodyOk hEntry hRun
  let layout := fn.returns ++ fn.params
  let sourceEntry :=
    sourceCaller.withSource
      (EvmYul.Yul.State.mkOk
        (sourceCaller.source.initcall params returns args))
  let targetEntry :=
    targetCaller.withSource
      { shared := targetCaller.source.shared,
        vars :=
          Functions.Source.Store.initReturns fn.returns paramStore }
  obtain
      ⟨entryShared, entryVars, hEntrySource,
        _hEntryShared, _hEntryVars, hEntryDomain⟩ :=
    hEntry.2
  change StateRelation.Vars.DomainExact layout entryVars at hEntryDomain
  change StateRelation.Vars.NamesWithin before.used layout at hReserved
  have hEntryStore : sourceEntry.source.store = entryVars := by
    rw [hEntrySource]
    rfl
  have hEntryDomainStore :
      StateRelation.Vars.DomainExact layout sourceEntry.source.store := by
    rw [hEntryStore]
    exact hEntryDomain
  obtain ⟨listCompilerFuel, lower, _hCompilerFuel,
      hLowerList, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  obtain ⟨listSourceFuel, sourceOpen, _hSourceFuel,
      hListRun, hSourceAfterBody⟩ :=
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
      ControlContextRel sourceControl layout false false true
        (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    refine
      { scope := ?_
        breakScope := ?_
        continueScope := ?_
        leaveScope := ?_ }
    · simp [layout, Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope,
        FunctionsObserverOutcome.LayoutWithinScope]
    · simp [sourceControl, ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope]
    · simp [sourceControl, ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope]
    · simp [sourceControl, ScopeOptionWithin,
        Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial, Functions.Source.Ctx.withLeaveScope,
        layout]
  obtain ⟨result⟩ :=
    hList (sourceFuel := listSourceFuel)
      (compilerFuel := listCompilerFuel)
      (sourceControl := sourceControl)
      (before := before) (after := after)
      (layout := layout) (stmts := body) (lower := lower)
      (source := sourceEntry) (sourceFinal := sourceOpen)
      (target := targetEntry)
      (ctx := Functions.Source.Effectful.FunDef.bodyCtx fn)
      (canBreak := false) (canContinue := false) (canLeave := true)
      (by omega) hBodyOk hBodyNames hLowerList hEntry
      (by
        simpa [targetEntry] using
          entryTargetDomain hParamStore hReserved)
      (bodyScope hReserved) hReserved hControl hListRun
  obtain ⟨targetFuel, hTargetRun⟩ := result.openResult.run
  have hMode :
      result.openResult.outcome.mode = .regular ∨
        result.openResult.outcome.mode = .leave := by
    cases hOutcomeMode : result.openResult.outcome.mode with
    | regular => exact Or.inl rfl
    | brk =>
        have hExit := result.openResult.exitScope
        simp [FunctionsObserverOutcome.ExitScopeRel, hOutcomeMode,
          sourceControl] at hExit
    | cont =>
        have hExit := result.openResult.exitScope
        simp [FunctionsObserverOutcome.ExitScopeRel, hOutcomeMode,
          sourceControl] at hExit
    | leave => exact Or.inr rfl
    | halt kind =>
        have hExit := result.openResult.exitScope
        simp [FunctionsObserverOutcome.ExitScopeRel, hOutcomeMode] at hExit
  have hFinalRelation :
      StateRelation.Replay.ScopedExactRel codeRel layout
        (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
        result.openResult.outcome.state := by
    rcases hMode with hRegular | hLeave
    · obtain ⟨sourceShared, sourceVars, hSourceOpen⟩ :=
        FunctionsObserverOutcome.ModeRel.target_regular_source_ok
          result.openResult.relation.mode hRegular
      have hRestricted :
          StateRelation.Replay.ScopedExactRel codeRel layout
            (sourceOpen.withSource
              (.Ok sourceShared
                (EvmYul.Yul.State.restrictVarStore
                  sourceVars entryVars)))
            result.openResult.outcome.state := by
        have hExact := result.openResult.relation.exact hRegular
        have hRevived :
            sourceOpen.withSource sourceOpen.source.reviveJump =
              sourceOpen := by
          rw [hSourceOpen]
          change
            sourceOpen.withSource (.Ok sourceShared sourceVars) =
              sourceOpen
          rw [← hSourceOpen]
          exact Simulation.ResourceReplay.State.withSource_self sourceOpen
        have hExact' := hExact
        rw [hRevived] at hExact'
        exact
          StateRelation.Replay.scopedExact_restrict_source
            hSourceOpen
            hExact'
            hEntryDomain
            (result.openResult.retains hRegular)
      have hFinalRevivedEq :
          sourceAfterBody.withSource
              sourceAfterBody.source.reviveJump =
            sourceOpen.withSource
              (.Ok sourceShared
                (EvmYul.Yul.State.restrictVarStore
                  sourceVars entryVars)) := by
        rw [hSourceAfterBody]
        change
          (sourceOpen.withSource
              (sourceOpen.source.restrictStoreTo
                sourceEntry.source.store)).withSource
              (sourceOpen.source.restrictStoreTo
                sourceEntry.source.store).reviveJump =
            _
        rw [hEntryStore, hSourceOpen]
        rfl
      rw [hFinalRevivedEq]
      exact hRestricted
    · have hExit := result.openResult.exitScope
      have hFinalLayout : result.openResult.finalLayout = layout := by
        simp [FunctionsObserverOutcome.ExitScopeRel, hLeave,
          sourceControl] at hExit
        exact hExit.1.symm
      have hModeRel := result.openResult.relation.mode
      cases hSourceOpen : sourceOpen.source with
      | OutOfFuel =>
          rw [hSourceOpen] at hModeRel
          simp [FunctionsObserverOutcome.ModeRel, hLeave] at hModeRel
      | Ok shared vars =>
          rw [hSourceOpen] at hModeRel
          simp [FunctionsObserverOutcome.ModeRel, hLeave] at hModeRel
      | Checkpoint jump =>
          cases jump with
          | Break shared vars =>
              rw [hSourceOpen] at hModeRel
              simp [FunctionsObserverOutcome.ModeRel, hLeave] at hModeRel
          | Continue shared vars =>
              rw [hSourceOpen] at hModeRel
              simp [FunctionsObserverOutcome.ModeRel, hLeave] at hModeRel
          | Leave shared vars =>
              have hRevived :
                  (sourceOpen.withSource
                      sourceOpen.source.reviveJump).source =
                    .Ok shared vars := by
                rw [hSourceOpen]
                rfl
              have hScoped := result.openResult.relation.state
              rw [hFinalLayout] at hScoped
              have hRestricted :=
                StateRelation.Replay.scopedRel_restrict_source_outer
                  hRevived hScoped hEntryDomain
                  (fun _name hMem => hMem)
              have hDefined :
                  FunctionsObserverOutcome.SourceDefined layout
                    sourceAfterBody := by
                rw [hSourceAfterBody]
                have hOpenDefined := result.openResult.sourceDefined
                rw [hFinalLayout] at hOpenDefined
                exact
                  FunctionsObserverOutcome.SourceDefined.restrictStoreTo
                    hOpenDefined
                    hEntryDomainStore (fun _name hMem => hMem)
              have hWithin :
                  FunctionsObserverOutcome.SourceWithin layout
                    sourceAfterBody := by
                rw [hSourceAfterBody]
                exact
                  FunctionsObserverOutcome.SourceWithin.restrictStoreTo
                    (source := sourceOpen) hEntryDomainStore
              have hFinalRevivedEq :
                  sourceAfterBody.withSource
                      sourceAfterBody.source.reviveJump =
                    (sourceOpen.withSource
                        sourceOpen.source.reviveJump).withSource
                      (.Ok shared
                        (EvmYul.Yul.State.restrictVarStore
                          vars entryVars)) := by
                rw [hSourceAfterBody]
                change
                  (sourceOpen.withSource
                      (sourceOpen.source.restrictStoreTo
                        sourceEntry.source.store)).withSource
                      (sourceOpen.source.restrictStoreTo
                        sourceEntry.source.store).reviveJump =
                    _
                rw [hEntryStore, hSourceOpen]
                rfl
              rw [hFinalRevivedEq]
              apply StateRelation.Replay.scopedExact_of_scopedRel hRestricted
              intro finalShared finalVars hFinalSource
              apply
                FunctionsObserverOutcome.sourceDomainExact_of_source
                  hDefined hWithin
              exact
                (congrArg
                    (fun state =>
                      state.source)
                    hFinalRevivedEq).trans hFinalSource
  refine
    ⟨targetFuel,
      ⟨paramStore, result.openResult.outcome,
        result.openResult.finalCtx, hParamStore, ?_, hMode,
        hFinalRelation⟩⟩
  rw [hFnBody]
  simpa [targetEntry] using hTargetRun

end RecursiveBodyForward

namespace RecursiveScopedValueForward

theorem ofBody
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
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        bound) :
    FunctionsObserverCall.RecursiveScopedValueForward
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  intro exprFuel
  induction exprFuel using Nat.strong_induction_on with
  | h exprFuel ih =>
      intro before after layout expr pre lower source source'
        target ctx values hFuel hOk hLower hRel hDomain hScope hRun
      have hSmallerValue :
          FunctionsObserverCall.RecursiveScopedValueForward
            contract transcript codeRel sourceProgram targetProgram
            profile exprFuel := by
        intro smallerFuel smallerBefore smallerAfter smallerLayout
          smallerExpr smallerPre smallerLower smallerSource
          smallerSource' smallerTarget smallerCtx smallerValues
          hSmaller hSmallerOk hSmallerLower hSmallerRel
          hSmallerDomain hSmallerScope hSmallerRun
        exact
          ih smallerFuel hSmaller
            (by omega) hSmallerOk hSmallerLower hSmallerRel
            hSmallerDomain hSmallerScope hSmallerRun
      have hSmallerExpr :
          FunctionsObserverCall.RecursiveScopedExpressionForward
            contract transcript codeRel sourceProgram targetProgram
            profile exprFuel :=
        FunctionsObserverCall.RecursiveScopedValueForward.expression
          hSmallerValue
      have hSmallerBody :
          FunctionsObserverCall.RecursiveBodyForward
            contract transcript codeRel sourceProgram targetProgram profile
            exprFuel := by
        intro sourceFuel bodyBefore bodyAfter params returns body fn
          args paramStore sourceCaller sourceAfterBody targetCaller
          hSourceFuel hBodyLower hParams hReturns hParamStore
          hReserved hBodyNames hBodyOk hEntry hBodyRun
        exact
          hBody (by omega) hBodyLower hParams hReturns hParamStore
            hReserved hBodyNames hBodyOk hEntry hBodyRun
      cases expr with
      | Lit value =>
          exact
            FunctionsObserverExpression.ScopedPreparedValue.ofLiteral
              hLower hRel hDomain hScope hRun
      | Var name =>
          exact
            FunctionsObserverExpression.ScopedPreparedValue.ofVariable
              hLower hRel hDomain hScope hRun
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hArgsOk :
                  SolcValidation.ExprsOk? profile
                      sourceProgram.contract layout args =
                    true :=
                SolcValidation.exprsOk_of_exprOk_primitive hOk
              exact
                FunctionsObserverExpression.ScopedPreparedValue.ofPrimitive
                  hLower
                  (fun candidate hMem =>
                    SolcValidation.exprOk_of_exprsOk_of_mem
                      hArgsOk hMem)
                  (fun hArgFuel hArgOk hArgLower hArgRel
                      hArgDomain hArgScope hArgRun =>
                    hSmallerExpr hArgFuel hArgOk hArgLower hArgRel
                      hArgDomain hArgScope hArgRun)
                  hRel hDomain hScope hRun
          | inr functionName =>
              cases hLookup :
                  sourceProgram.contract.functions.lookup functionName with
              | none =>
                  simp [SolcValidation.ExprOk?,
                    SolcValidation.lookupFunction?, hLookup] at hOk
              | some fnDef =>
                  cases fnDef with
                  | Def params returns body =>
                      obtain ⟨returnName, hReturns⟩ :=
                        SolcValidation.returns_singleton_of_exprOk_functionCall
                          hOk hLookup
                      have hLength :=
                        Yul.Source.Effectful.evalValues_function_ok_length
                          (ObserverSemantics.SourceReplay.stateModel transcript)
                          (ObserverSafety.SafeSemantics.primitiveSemantics
                            contract transcript)
                          hLookup hRun
                      rw [hReturns] at hLength
                      cases values with
                      | nil =>
                          simp at hLength
                      | cons value rest =>
                          cases rest with
                          | nil =>
                              have hEval :
                                  Yul.Source.Effectful.eval
                                      (ObserverSemantics.SourceReplay.stateModel
                                        transcript)
                                      (ObserverSafety.SafeSemantics.primitiveSemantics
                                        contract transcript)
                                      exprFuel
                                      (.Call (.inr functionName) args)
                                      (some sourceProgram.contract) source =
                                    .ok (source', value) :=
                                Yul.Source.Effectful.eval_of_evalValues_singleton
                                  (ObserverSemantics.SourceReplay.stateModel
                                    transcript)
                                  (ObserverSafety.SafeSemantics.primitiveSemantics
                                    contract transcript)
                                  hRun
                              exact
                                ⟨value, rfl,
                                  FunctionsObserverCall.ScopedPreparedValue.ofFunctionCall
                                      hDecomposition hLower hProgramOk hOk
                                      hSmallerExpr hSmallerBody hRel
                                      hDomain hScope hEval⟩
                          | cons next tail =>
                              simp at hLength

end RecursiveScopedValueForward

structure RecursiveForwardFamily
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop where
  body :
    FunctionsObserverCall.RecursiveBodyForward
      contract transcript codeRel sourceProgram targetProgram profile bound
  value :
    FunctionsObserverCall.RecursiveScopedValueForward
      contract transcript codeRel sourceProgram targetProgram profile bound
  stmt :
    RecursiveOpenStmtForward contract transcript codeRel
      sourceProgram targetProgram profile bound
  list :
    RecursiveOpenListForward contract transcript codeRel
      sourceProgram targetProgram profile bound
  compound :
    RecursiveOpenCompoundForward contract transcript codeRel
      sourceProgram targetProgram profile bound

namespace RecursiveForwardFamily

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
      RecursiveForwardFamily contract transcript codeRel
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
      · simp [FunctionsObserverCall.RecursiveBodyForward]
      · simp [FunctionsObserverCall.RecursiveScopedValueForward]
      · simp [RecursiveOpenStmtForward]
      · simp [RecursiveOpenListForward]
      · simp [RecursiveOpenCompoundForward]
  | succ bound ih =>
      have hCompound :
          RecursiveOpenCompoundForward contract transcript codeRel
            sourceProgram targetProgram profile (bound + 1) :=
        RecursiveOpenCompoundForward.ofComponents
          (bound := bound) ih.value ih.list
      exact
        { body := RecursiveBodyForward.ofList ih.list
          value :=
            RecursiveScopedValueForward.ofBody
              hDecomposition hProgramOk ih.body
          stmt :=
            RecursiveOpenStmtForward.ofCompound
              hDecomposition hProgramOk ih.value ih.body hCompound
          list := RecursiveOpenListForward.ofStmt ih.stmt
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
        [] sourceFinal outcome := by
  have hCompiler := hDecomposition
  obtain
      ⟨bodyStmts, afterBody, functions, afterFunctions,
        hLowerBody, _hLowerFunctions, hTargetProgram⟩ :=
    hDecomposition
  obtain ⟨listSourceFuel, sourceOpen, _hSourceFuel,
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
      ControlContextRel sourceControl [] false false false
        Functions.Source.Ctx.initial := by
    refine
      { scope := ?_
        breakScope := ?_
        continueScope := ?_
        leaveScope := ?_ }
    · simp [FunctionsObserverOutcome.LayoutWithinScope]
    · simp [sourceControl, ScopeOptionWithin,
        Functions.Source.Ctx.initial]
    · simp [sourceControl, ScopeOptionWithin,
        Functions.Source.Ctx.initial]
    · simp [sourceControl, ScopeOptionWithin,
        Functions.Source.Ctx.initial]
  have hFamily :=
    ofCompiler
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (profile := profile)
      hCompiler hProgramOk (listSourceFuel + 1)
  obtain ⟨openResult⟩ :=
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
      (by omega) hListOk hNames hLowerList hRel hDomain
      (by
        intro name hMem
        simp [Functions.Source.Ctx.initial] at hMem)
      (by
        intro name hMem
        simp at hMem)
      hControl hListRun
  obtain ⟨closed⟩ :=
    ScopedListResult.close openResult
      (StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel)
      (by
        intro name hMem
        simp at hMem)
      hControl hSourceFinal
  obtain ⟨targetFuel, hTargetRun⟩ := closed.run
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
  refine
    ⟨targetFuel, closed.outcome, ?_, hOutcomeRegular,
      by simpa [hFinalLayout] using closed.relation⟩
  have hBodyEq :
      targetProgram.toFunctions.body = { stmts := bodyStmts } :=
    congrArg (fun program => program.body) hTargetProgram
  unfold Functions.Source.Effectful.Program.runState
  rw [hBodyEq]
  exact hTargetRun

end RecursiveForwardFamily

end FunctionsObserverForward
end Yul
end EvmCompiler
