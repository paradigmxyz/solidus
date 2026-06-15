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

def ScopeOptionWithin (enabled : Bool)
    (sourceScope? targetScope? : Option (List Name))
    (layout : List Name) : Prop :=
  if enabled then
    ∃ sourceScope targetScope,
      sourceScope? = some sourceScope ∧
        targetScope? = some targetScope ∧
        (∀ name, name ∈ sourceScope → name ∈ layout) ∧
        ∀ name, name ∈ sourceScope → name ∈ targetScope
  else
    sourceScope? = none ∧ targetScope? = none

namespace ScopeOptionWithin

theorem mono
    {enabled : Bool}
    {sourceScope? targetScope? : Option (List Name)}
    {before after : List Name}
    (hWithin :
      ScopeOptionWithin enabled sourceScope? targetScope? before)
    (hSubset : ∀ name, name ∈ before → name ∈ after) :
    ScopeOptionWithin enabled sourceScope? targetScope? after := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin ⊢
    obtain
      ⟨sourceScope, targetScope, hSource, hTarget,
        hNames, hTargetNames⟩ := hWithin
    exact
      ⟨sourceScope, targetScope, hSource, hTarget,
        fun name hMem => hSubset name (hNames name hMem),
        hTargetNames⟩
  · simp [ScopeOptionWithin, hEnabled] at hWithin ⊢
    exact hWithin

theorem source_subset_of_some
    {enabled : Bool}
    {sourceScope targetScope layout : List Name}
    (hWithin :
      ScopeOptionWithin enabled (some sourceScope)
        (some targetScope) layout) :
    ∀ name, name ∈ sourceScope → name ∈ layout := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin
    exact hWithin.1
  · simp [ScopeOptionWithin, hEnabled] at hWithin

theorem target_contains_of_some
    {enabled : Bool}
    {sourceScope targetScope layout : List Name}
    (hWithin :
      ScopeOptionWithin enabled (some sourceScope)
        (some targetScope) layout) :
    ∀ name, name ∈ sourceScope → name ∈ targetScope := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin
    exact hWithin.2
  · simp [ScopeOptionWithin, hEnabled] at hWithin

end ScopeOptionWithin

structure ControlContextRel
    (sourceControl : FunctionsObserverOutcome.SourceControlScopes)
    (layout : List Name)
    (canBreak canContinue canLeave : Bool)
    (ctx : Functions.Source.Ctx) : Prop where
  scope :
    FunctionsObserverOutcome.LayoutWithinScope layout ctx
  breakScope :
    ScopeOptionWithin canBreak sourceControl.breakScope?
      ctx.breakScope? layout
  continueScope :
    ScopeOptionWithin canContinue sourceControl.continueScope?
      ctx.continueScope? layout
  leaveScope :
    ScopeOptionWithin canLeave sourceControl.leaveScope?
      ctx.leaveScope? layout

namespace ControlContextRel

def forBodySourceControl
    (layout : List Name)
    (outer : FunctionsObserverOutcome.SourceControlScopes) :
    FunctionsObserverOutcome.SourceControlScopes :=
  { breakScope? := some layout
    continueScope? := some layout
    leaveScope? := outer.leaveScope? }

def forPostSourceControl
    (outer : FunctionsObserverOutcome.SourceControlScopes) :
    FunctionsObserverOutcome.SourceControlScopes :=
  { breakScope? := none
    continueScope? := none
    leaveScope? := outer.leaveScope? }

theorem forBody
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    (hRel :
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx) :
    ControlContextRel (forBodySourceControl layout sourceControl) layout
      true true canLeave
      (ctx.withLoopControl ctx.scope ctx.scope) := by
  refine
    { scope := ?_
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · simpa [Functions.Source.Ctx.withLoopControl] using hRel.scope
  · simpa [forBodySourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withLoopControl] using hRel.scope
  · simpa [forBodySourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withLoopControl] using hRel.scope
  · simpa [forBodySourceControl, Functions.Source.Ctx.withLoopControl] using
      hRel.leaveScope

theorem forPost
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    (hRel :
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx) :
    ControlContextRel (forPostSourceControl sourceControl) layout
      false false canLeave ctx.withoutLoopControl := by
  refine
    { scope := ?_
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · simpa [Functions.Source.Ctx.withoutLoopControl] using hRel.scope
  · simp [forPostSourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withoutLoopControl]
  · simp [forPostSourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withoutLoopControl]
  · simpa [forPostSourceControl, Functions.Source.Ctx.withoutLoopControl] using
      hRel.leaveScope

theorem transport
    {beforeLayout afterLayout : List Name}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {canBreak canContinue canLeave : Bool}
    {beforeCtx afterCtx : Functions.Source.Ctx}
    (hRel :
      ControlContextRel sourceControl beforeLayout
        canBreak canContinue canLeave beforeCtx)
    (hSubset :
      ∀ name, name ∈ beforeLayout → name ∈ afterLayout)
    (hControl : Functions.Source.Ctx.SameControl beforeCtx afterCtx)
    (hScope :
      FunctionsObserverOutcome.LayoutWithinScope afterLayout afterCtx) :
    ControlContextRel sourceControl afterLayout
      canBreak canContinue canLeave afterCtx := by
  refine
    { scope := hScope
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · rw [← hControl.breakScope]
    exact hRel.breakScope.mono hSubset
  · rw [← hControl.continueScope]
    exact hRel.continueScope.mono hSubset
  · rw [← hControl.leaveScope]
    exact hRel.leaveScope.mono hSubset

theorem exitSubset
    {layout exitLayout : List Name}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    {mode : Locals.Source.Mode}
    (hRel :
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hExit :
      FunctionsObserverOutcome.ExitScopeRel
        sourceControl ctx mode exitLayout)
    (hNonregular : mode ≠ .regular) :
    ∀ name, name ∈ exitLayout → name ∈ layout := by
  cases hMode : mode with
  | regular => exact False.elim (hNonregular hMode)
  | brk =>
      simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit
      have hWithin := hRel.breakScope
      rcases hExit with
        ⟨hSource, targetScope, hTarget, _hTargetContains⟩
      rw [hSource, hTarget] at hWithin
      exact ScopeOptionWithin.source_subset_of_some hWithin
  | cont =>
      simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit
      have hWithin := hRel.continueScope
      rcases hExit with
        ⟨hSource, targetScope, hTarget, _hTargetContains⟩
      rw [hSource, hTarget] at hWithin
      exact ScopeOptionWithin.source_subset_of_some hWithin
  | leave =>
      simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit
      have hWithin := hRel.leaveScope
      rcases hExit with
        ⟨hSource, targetScope, hTarget, _hTargetContains⟩
      rw [hSource, hTarget] at hWithin
      exact ScopeOptionWithin.source_subset_of_some hWithin
  | halt kind =>
      simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit

end ControlContextRel

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
  exitScope :
    FunctionsObserverOutcome.ExitScopeRel
      sourceControl ctx outcome.mode finalLayout

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
    (hEntryRel :
      StateRelation.Replay.ScopedExactRel codeRel
        entryLayout sourceEntry target)
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
  obtain
      ⟨entryShared, entryVars, hSourceEntry,
        _hShared, _hScoped, hEntryDomain⟩ :=
    hEntryRel.2
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
              (EvmYul.Yul.State.restrictVarStore bodyVars entryVars)))
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
              (EvmYul.Yul.State.restrictVarStore bodyVars entryVars)) := by
      rw [hSourceFinal, hBodySource, hSourceEntry]
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
      simpa [hSourceEntry] using
        FunctionsObserverOutcome.ScopedOutcomeRel.restrictNonregularSource
          result.openResult.relation hRegular
          hEntryDomain hExitSubset
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
    (hEntryRel :
      StateRelation.Replay.ScopedExactRel codeRel layout sourceEntry target)
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
  exact close combined hEntryRel hLayout hControl hSourceFinal

end ScopedListResult

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

inductive CompoundStmt : AstStmt → Prop where
  | block (body : List AstStmt) : CompoundStmt (.Block body)
  | switch (scrutinee : AstExpr)
      (cases : List (Word × List AstStmt)) (defaultBody : List AstStmt) :
      CompoundStmt (.Switch scrutinee cases defaultBody)
  | forLoop (cond : AstExpr) (post body : List AstStmt) :
      CompoundStmt (.For cond post body)
  | ifThen (cond : AstExpr) (body : List AstStmt) :
      CompoundStmt (.If cond body)

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
    CompoundStmt stmt →
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
        sourceProgram targetProgram profile bound) :
    RecursiveOpenStmtForward contract transcript codeRel
      sourceProgram targetProgram profile bound := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source sourceFinal target ctx canBreak canContinue canLeave
    hFuel hOk hNames hLower hRel hDomain hScope hLayout hControl hRun
  have hValueAt :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel :=
    hValue.mono (Nat.le_of_lt hFuel)
  have hExprAt :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel :=
    hValueAt.expression
  have hBodyAt :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel :=
    hBody.mono (Nat.le_of_lt hFuel)
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
          obtain ⟨result⟩ :=
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
      obtain ⟨result⟩ :=
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
      obtain ⟨result⟩ :=
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
      obtain ⟨result⟩ :=
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
      sourceProgram targetProgram profile bound := by
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
                hPreviousBound hTailOk' hTailNames hLowerTail hHeadRel
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

private theorem stmtsOk_selectSwitchCase
    {profile : SolcValidation.DialectProfile}
    {contract : AstContract}
    {functionNames vars : List Name}
    {canBreak canContinue canLeave : Bool}
    {value : Word} {defaultBody : List AstStmt}
    {cases : List (Word × List AstStmt)}
    (hCases :
      SolcValidation.CasesOk? profile contract functionNames vars
          canBreak canContinue canLeave cases =
        true)
    (hDefault :
      SolcValidation.StmtsOk? profile contract functionNames vars
          canBreak canContinue canLeave defaultBody =
        true) :
    SolcValidation.StmtsOk? profile contract functionNames vars
        canBreak canContinue canLeave
        (EvmYul.Yul.selectSwitchCase value defaultBody cases) =
      true := by
  induction cases with
  | nil =>
      simpa [EvmYul.Yul.selectSwitchCase] using hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      have hParts :
          SolcValidation.StmtsOk? profile contract functionNames vars
                canBreak canContinue canLeave body =
              true ∧
            SolcValidation.CasesOk? profile contract functionNames vars
                canBreak canContinue canLeave rest =
              true := by
        simpa [SolcValidation.CasesOk?] using hCases
      by_cases hMatch : caseValue = value
      · simpa [EvmYul.Yul.selectSwitchCase, hMatch] using hParts.1
      · simpa [EvmYul.Yul.selectSwitchCase, hMatch] using
          ih hParts.2

private theorem selectedSwitchNames
    {value : Word} {defaultBody : List AstStmt}
    {cases : List (Word × List AstStmt)} :
    ∀ name,
      name ∈
          Stmt.List.names
            (EvmYul.Yul.selectSwitchCase value defaultBody cases) →
        name ∈
          Stmt.CaseList.names cases ++ Stmt.List.names defaultBody := by
  induction cases with
  | nil =>
      intro name hMem
      simpa [EvmYul.Yul.selectSwitchCase, Stmt.CaseList.names] using hMem
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      intro name hMem
      by_cases hMatch : caseValue = value
      · have hBodyMem : name ∈ Stmt.List.names body := by
          simpa [EvmYul.Yul.selectSwitchCase, hMatch] using hMem
        exact
          by
            simpa [Stmt.CaseList.names, List.append_assoc] using
              List.mem_append_left
                (Stmt.CaseList.names rest ++ Stmt.List.names defaultBody)
                hBodyMem
      · have hTail := ih name (by
          simpa [EvmYul.Yul.selectSwitchCase, hMatch] using hMem)
        simpa [Stmt.CaseList.names, List.append_assoc] using
          List.mem_append_right (Stmt.List.names body) hTail

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
    (hFuel : sourceFuel < bound)
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
  obtain ⟨closedBody⟩ :=
    ScopedListResult.close bodyResult hRel hLayout hControl hSourceFinal
  obtain ⟨bodyFuel, hBodyScoped⟩ := closedBody.run
  have hTargetStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx bodyFuel
          (.block { stmts := lowerStmts }) target =
        .ok (closedBody.outcome, ctx) := by
    unfold Functions.Source.Effectful.Stmt.run
    rw [hBodyScoped]
    rfl
  obtain ⟨targetFuel, hTargetRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_singleton_of_run
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hTargetStmt
  let result :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel targetProgram.toFunctions
        [.block { stmts := lowerStmts }] before after layout
        sourceFinal target ctx (sourceControl := sourceControl) :=
    { finalLayout := closedBody.finalLayout
      outcome := closedBody.outcome
      finalCtx := ctx
      run := ⟨targetFuel, hTargetRun⟩
      relation := closedBody.relation
      domain := closedBody.domain
      scope := hScope.mono closedBody.freshExtends
      control := Functions.Source.Ctx.SameControl.refl ctx
      freshExtends := closedBody.freshExtends
      retains := by
        intro hRegular name hMem
        rw [closedBody.regularLayout hRegular]
        exact hMem
      layoutWithin := closedBody.layoutWithin
      layoutScope := by
        intro hRegular
        rw [closedBody.regularLayout hRegular]
        exact hControl.scope
      exitScope := closedBody.exitScope }
  exact
    ⟨{ openResult := result
       regularLayout := by
         intro hRegular
         simpa [SolcValidation.StmtOutVars] using
           closedBody.regularLayout hRegular
       regularControl := by
         intro hRegular
         change
           ControlContextRel sourceControl closedBody.finalLayout
             canBreak canContinue canLeave ctx
         rw [closedBody.regularLayout hRegular]
         exact hControl }⟩

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
    (hFuel : sourceFuel < bound)
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
      obtain ⟨bodyFuel, hBodyScoped, _hBodyCtx⟩ :=
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
      let result :
          FunctionsObserverOutcome.ScopedOpenResult
            contract codeRel targetProgram.toFunctions
            (preCond ++ [.if_ lowerCond lowerBody])
            before after layout sourceFinal target ctx
            (sourceControl := sourceControl) :=
        { finalLayout := closedBody.openResult.finalLayout
          outcome := closedBody.openResult.outcome
          finalCtx := prepared.prepared.finalCtx
          run := ⟨targetFuel, hTargetRun⟩
          relation := closedBody.openResult.relation
          domain := closedBody.openResult.domain
          scope := prepared.prepared.scope.mono hBodyFresh
          control := prepared.prepared.control
          freshExtends := hFresh
          retains := closedBody.openResult.retains
          layoutWithin := closedBody.openResult.layoutWithin
          layoutScope := by
            intro hRegular
            rw [closedBody.regularLayout hRegular]
            exact hPreparedLayoutScope
          exitScope :=
            FunctionsObserverOutcome.ExitScopeRel.transportTarget
              prepared.prepared.control closedBody.openResult.exitScope }
      exact
        ⟨{ openResult := result
           regularLayout := by
             intro hRegular
             simpa [SolcValidation.StmtOutVars] using
               closedBody.regularLayout hRegular
           regularControl := by
             intro hRegular
             rw [closedBody.regularLayout hRegular]
             exact hPreparedControl }⟩

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
    (hFuel : sourceFuel < bound)
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
            stmtsOk_selectSwitchCase (value := value)
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
              (selectedSwitchNames name hCanonical))
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
      obtain ⟨bodyFuel, hBodyScoped, _hBodyCtx⟩ :=
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
      let result :
          FunctionsObserverOutcome.ScopedOpenResult
            contract codeRel targetProgram.toFunctions
            (preScrutinee ++
              [.switch lowerScrutinee lowerCases lowerDefault])
            before after layout sourceFinal target ctx
            (sourceControl := sourceControl) :=
        { finalLayout := closedBody.openResult.finalLayout
          outcome := closedBody.openResult.outcome
          finalCtx := prepared.prepared.finalCtx
          run := ⟨targetFuel, hTargetRun⟩
          relation := closedBody.openResult.relation
          domain := closedBody.openResult.domain.mono hAfterSelected
          scope := prepared.prepared.scope.mono hSelectionFresh
          control := prepared.prepared.control
          freshExtends := hFresh
          retains := closedBody.openResult.retains
          layoutWithin :=
            closedBody.openResult.layoutWithin.mono hAfterSelected
          layoutScope := by
            intro hRegular
            rw [closedBody.regularLayout hRegular]
            exact hPreparedLayoutScope
          exitScope :=
            FunctionsObserverOutcome.ExitScopeRel.transportTarget
              prepared.prepared.control closedBody.openResult.exitScope }
      exact
        ⟨{ openResult := result
           regularLayout := by
             intro hRegular
             simpa [SolcValidation.StmtOutVars] using
               closedBody.regularLayout hRegular
           regularControl := by
             intro hRegular
             rw [closedBody.regularLayout hRegular]
             exact hPreparedControl }⟩

end RecursiveOpenCompoundForward

namespace RecursiveBodyForward

theorem ofEmpty
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (_hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names []))
    (_hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true [] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) :=
  FunctionsObserverStatement.ReturnedBody.of_empty
    hLower hParams hReturns hParamStore hEntry hRun

theorem ofLeave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Leave] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (_hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Leave]))
    (_hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true [.Leave] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Leave])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) :=
  FunctionsObserverStatement.ReturnedBody.of_leave
    hLower hParams hReturns hParamStore hEntry hRun

theorem ofLetNone
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Let names none] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (_hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Let names none]))
    (_hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true [.Let names none] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Let names none])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) :=
  FunctionsObserverStatement.ReturnedBody.of_let_none
    hLower hParams hReturns hParamStore hEntry hRun

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

theorem ofLetOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Let [name] (some expr)] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Let [name] (some expr)]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Let [name] (some expr)] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Let [name] (some expr)])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  apply
    FunctionsObserverStatement.ReturnedBody.of_let_one
      hNotFunctionCall hExprOk hLower hParams hReturns hParamStore
      hEntry
  · simpa using entryTargetDomain hParamStore hReserved
  · exact bodyScope hReserved
  · exact hValue
  · exact hRun

theorem ofAssignOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Assign [name] expr] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Assign [name] expr]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Assign [name] expr] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Assign [name] expr])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  apply
    FunctionsObserverStatement.ReturnedBody.of_assign_one
      hNotFunctionCall hExprOk hLower hParams hReturns hParamStore
      hEntry
  · simpa using entryTargetDomain hParamStore hReserved
  · exact bodyScope hReserved
  · exact hValue
  · exact hRun

theorem ofAssignCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before
          [.Assign names (.Call (.inr functionName) callArgs)] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names
          [.Assign names (.Call (.inr functionName) callArgs)]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Assign names (.Call (.inr functionName) callArgs)] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block
            [.Assign names
              (.Call (.inr functionName) callArgs)])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_assign_call_parts hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  exact
    FunctionsObserverStatement.ReturnedBody.of_assign_call
      hDecomposition hArgsLowering hFnBody hExprOk hProgramOk
      hParams hReturns hParamStore hEntry
      (by simpa using entryTargetDomain hParamStore hReserved)
      (bodyScope hReserved)
      (FunctionsObserverCall.RecursiveScopedValueForward.expression hValue)
      hBody hRun

theorem ofLetCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before
          [.Let names (some (.Call (.inr functionName) callArgs))] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names
          [.Let names (some (.Call (.inr functionName) callArgs))]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Let names (some (.Call (.inr functionName) callArgs))] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block
            [.Let names
              (some (.Call (.inr functionName) callArgs))])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_let_call_parts hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  exact
    FunctionsObserverStatement.ReturnedBody.of_let_call
      hDecomposition hArgsLowering hFnBody hExprOk hProgramOk
      hParams hReturns hParamStore hEntry
      (by simpa using entryTargetDomain hParamStore hReserved)
      (bodyScope hReserved) hBodyNames
      (FunctionsObserverCall.RecursiveScopedValueForward.expression hValue)
      hBody hRun

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
      bound := by
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

end FunctionsObserverForward
end Yul
end EvmCompiler
