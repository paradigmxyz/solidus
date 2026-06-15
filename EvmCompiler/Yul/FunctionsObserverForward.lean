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
    (scope? : Option (List Name)) (layout : List Name) : Prop :=
  if enabled then
    ∃ scope,
      scope? = some scope ∧
        ∀ name, name ∈ scope → name ∈ layout
  else
    scope? = none

namespace ScopeOptionWithin

theorem mono
    {enabled : Bool}
    {scope? : Option (List Name)}
    {before after : List Name}
    (hWithin : ScopeOptionWithin enabled scope? before)
    (hSubset : ∀ name, name ∈ before → name ∈ after) :
    ScopeOptionWithin enabled scope? after := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin ⊢
    obtain ⟨scope, hScope, hNames⟩ := hWithin
    exact ⟨scope, hScope, fun name hMem => hSubset name (hNames name hMem)⟩
  · simp [ScopeOptionWithin, hEnabled] at hWithin ⊢
    exact hWithin

theorem subset_of_some
    {enabled : Bool}
    {scope layout : List Name}
    (hWithin : ScopeOptionWithin enabled (some scope) layout) :
    ∀ name, name ∈ scope → name ∈ layout := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin
    exact hWithin
  · simp [ScopeOptionWithin, hEnabled] at hWithin

end ScopeOptionWithin

structure ControlContextRel
    (layout : List Name)
    (canBreak canContinue canLeave : Bool)
    (ctx : Functions.Source.Ctx) : Prop where
  scope :
    FunctionsObserverOutcome.LayoutWithinScope layout ctx
  breakScope :
    ScopeOptionWithin canBreak ctx.breakScope? layout
  continueScope :
    ScopeOptionWithin canContinue ctx.continueScope? layout
  leaveScope :
    ScopeOptionWithin canLeave ctx.leaveScope? layout

namespace ControlContextRel

theorem transport
    {beforeLayout afterLayout : List Name}
    {canBreak canContinue canLeave : Bool}
    {beforeCtx afterCtx : Functions.Source.Ctx}
    (hRel :
      ControlContextRel beforeLayout
        canBreak canContinue canLeave beforeCtx)
    (hSubset :
      ∀ name, name ∈ beforeLayout → name ∈ afterLayout)
    (hControl : Functions.Source.Ctx.SameControl beforeCtx afterCtx)
    (hScope :
      FunctionsObserverOutcome.LayoutWithinScope afterLayout afterCtx) :
    ControlContextRel afterLayout
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
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    {mode : Locals.Source.Mode}
    (hRel :
      ControlContextRel layout canBreak canContinue canLeave ctx)
    (hExit :
      FunctionsObserverOutcome.ExitScopeRel ctx mode exitLayout)
    (hNonregular : mode ≠ .regular) :
    ∀ name, name ∈ exitLayout → name ∈ layout := by
  cases hMode : mode with
  | regular => exact False.elim (hNonregular hMode)
  | brk =>
      simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit
      have hWithin := hRel.breakScope
      rw [hExit] at hWithin
      exact ScopeOptionWithin.subset_of_some hWithin
  | cont =>
      simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit
      have hWithin := hRel.continueScope
      rw [hExit] at hWithin
      exact ScopeOptionWithin.subset_of_some hWithin
  | leave =>
      simp [FunctionsObserverOutcome.ExitScopeRel, hMode] at hExit
      have hWithin := hRel.leaveScope
      rw [hExit] at hWithin
      exact ScopeOptionWithin.subset_of_some hWithin
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
    (canBreak canContinue canLeave : Bool) where
  openResult :
    FunctionsObserverOutcome.ScopedOpenResult
      contract codeRel program lower initial final entryLayout
      sourceFinal target ctx
  regularLayout :
    openResult.outcome.mode = .regular →
      openResult.finalLayout =
        SolcValidation.StmtOutVars entryLayout stmt
  regularControl :
    openResult.outcome.mode = .regular →
      ControlContextRel openResult.finalLayout
        canBreak canContinue canLeave openResult.finalCtx

namespace ScopedStmtResult

def ofStatement
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
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
        sourceFinal target ctx)
    (hControl :
      ControlContextRel entryLayout
        canBreak canContinue canLeave ctx) :
    ScopedStmtResult contract codeRel program stmt lower
      initial final entryLayout sourceFinal target ctx
      canBreak canContinue canLeave :=
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
        sourceFinal target ctx)
    (hLayout :
      result.outcome.mode = .regular →
        result.finalLayout =
          SolcValidation.StmtOutVars entryLayout stmt)
    (hControl :
      ControlContextRel entryLayout
        canBreak canContinue canLeave ctx) :
    ScopedStmtResult contract codeRel program stmt lower
      initial final entryLayout sourceFinal target ctx
      canBreak canContinue canLeave :=
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
    (canBreak canContinue canLeave : Bool) where
  openResult :
    FunctionsObserverOutcome.ScopedOpenResult
      contract codeRel program lower initial final entryLayout
      sourceFinal target ctx
  regularLayout :
    openResult.outcome.mode = .regular →
      openResult.finalLayout =
        SolcValidation.StmtsOutVars entryLayout stmts
  regularControl :
    openResult.outcome.mode = .regular →
      ControlContextRel openResult.finalLayout
        canBreak canContinue canLeave openResult.finalCtx

def RecursiveOpenStmtForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
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
      ControlContextRel layout canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedStmtResult contract codeRel targetProgram.toFunctions
          stmt lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave)

def RecursiveOpenListForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
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
      ControlContextRel layout canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.execSeq
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmts (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedListResult contract codeRel targetProgram.toFunctions
          stmts lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave)

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
      ControlContextRel layout canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt (some sourceProgram.contract) source =
        .ok sourceFinal →
      Nonempty
        (ScopedStmtResult contract codeRel targetProgram.toFunctions
          stmt lower before after layout sourceFinal target ctx
          canBreak canContinue canLeave)

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
  intro sourceFuel compilerFuel before after layout stmt lower
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
                  hDecomposition hProgramOk hExprOk hLower hRel hDomain
                  hScope hLayout hControl.scope hExprAt hBodyAt hRun
              exact ⟨ScopedStmtResult.ofStatement result hControl⟩
  | Break =>
      have hEnabled : canBreak = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      have hWithin := hControl.breakScope
      simp [ScopeOptionWithin, hEnabled] at hWithin
      obtain ⟨breakLayout, hBreakScope, hBreakSubset⟩ := hWithin
      obtain ⟨result⟩ :=
        FunctionsObserverStatement.OpenResult.of_break
          hLower hRel hDomain hScope hLayout hBreakScope hBreakSubset hRun
      exact ⟨ScopedStmtResult.ofStatement result hControl⟩
  | Continue =>
      have hEnabled : canContinue = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      have hWithin := hControl.continueScope
      simp [ScopeOptionWithin, hEnabled] at hWithin
      obtain ⟨continueLayout, hContinueScope, hContinueSubset⟩ := hWithin
      obtain ⟨result⟩ :=
        FunctionsObserverStatement.OpenResult.of_continue
          hLower hRel hDomain hScope hLayout
          hContinueScope hContinueSubset hRun
      exact ⟨ScopedStmtResult.ofStatement result hControl⟩
  | Leave =>
      have hEnabled : canLeave = true := by
        simpa [SolcValidation.StmtOk?] using hOk
      have hWithin := hControl.leaveScope
      simp [ScopeOptionWithin, hEnabled] at hWithin
      obtain ⟨leaveLayout, hLeaveScope, hLeaveSubset⟩ := hWithin
      obtain ⟨result⟩ :=
        FunctionsObserverStatement.OpenResult.of_leave
          hLower hRel hDomain hScope hLayout hLeaveScope hLeaveSubset hRun
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
      intro compilerFuel before after layout stmts lower
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

theorem block
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
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
      ControlContextRel layout canBreak canContinue canLeave ctx)
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
        canBreak canContinue canLeave) := by
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
  obtain
      ⟨entryShared, entryVars, hSource,
        _hShared, _hScoped, hEntryDomain⟩ :=
    hRel.2
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
  by_cases hRegular :
      bodyResult.openResult.outcome.mode = .regular
  · obtain ⟨bodyShared, bodyVars, hBodySource⟩ :=
      FunctionsObserverOutcome.ModeRel.target_regular_source_ok
        bodyResult.openResult.relation.mode hRegular
    have hOutcomeEq :
        bodyResult.openResult.outcome =
          Functions.Source.Effectful.Outcome.regular
            bodyResult.openResult.outcome.state :=
      Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
    obtain ⟨bodyFuel, hBodyOpen⟩ := bodyResult.openResult.run
    rw [hOutcomeEq] at hBodyOpen
    let targetFinal :=
      bodyResult.openResult.outcome.state.withSource
        (bodyResult.openResult.outcome.state.source.restrictTo ctx.scope)
    have hBodyScoped :
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions ctx
            { stmts := lowerStmts } bodyFuel target =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetFinal) := by
      simpa [targetFinal] using
        Functions.Source.Effectful.Block.runScoped_regular_of_runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions hBodyOpen
    have hTargetStmt :
        Functions.Source.Effectful.Stmt.run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions ctx bodyFuel
            (.block { stmts := lowerStmts }) target =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetFinal, ctx) := by
      unfold Functions.Source.Effectful.Stmt.run
      rw [hBodyScoped]
      rfl
    have hEmpty :
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions ctx 1 { stmts := [] } targetFinal =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetFinal, ctx) := by
      simpa using
        Functions.Source.Effectful.Block.runOpen_nil
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx 0 targetFinal
    obtain ⟨targetFuel, hTargetRun⟩ :=
      Functions.Source.Effectful.Block.runOpen_cons_regular_exists
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetStmt hEmpty
    have hRevived :
        sourceAfterBody.withSource
            sourceAfterBody.source.reviveJump =
          sourceAfterBody := by
      rw [hBodySource]
      change
        sourceAfterBody.withSource (.Ok bodyShared bodyVars) =
          sourceAfterBody
      rw [← hBodySource]
      exact
        Simulation.ResourceReplay.State.withSource_self sourceAfterBody
    have hBodyExact :=
      bodyResult.openResult.relation.exact hRegular
    rw [hRevived] at hBodyExact
    have hClosedRel :
        StateRelation.Replay.ScopedExactRel codeRel layout
          (sourceAfterBody.withSource
            (.Ok bodyShared
              (EvmYul.Yul.State.restrictVarStore bodyVars entryVars)))
          targetFinal := by
      simpa [targetFinal] using
        StateRelation.Replay.scopedExact_restrict_scopes
          hBodySource hBodyExact hEntryDomain
          (bodyResult.openResult.retains hRegular)
          hControl.scope
    have hSourceFinal' :
        sourceFinal =
          sourceAfterBody.withSource
            (.Ok bodyShared
              (EvmYul.Yul.State.restrictVarStore bodyVars entryVars)) := by
      rw [hSourceFinal, hBodySource, hSource]
      rfl
    have hOutcomeRel :
        FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
          sourceFinal
          (Functions.Source.Effectful.Outcome.regular targetFinal) := by
      rw [hSourceFinal']
      exact
        FunctionsObserverOutcome.ScopedOutcomeRel.regular
          rfl hClosedRel
    let result :
        FunctionsObserverOutcome.ScopedOpenResult
          contract codeRel targetProgram.toFunctions
          [.block { stmts := lowerStmts }] before after layout
          sourceFinal target ctx :=
      { finalLayout := layout
        outcome := Functions.Source.Effectful.Outcome.regular targetFinal
        finalCtx := ctx
        run := ⟨targetFuel, hTargetRun⟩
        relation := hOutcomeRel
        domain := by
          simpa [targetFinal, Locals.Source.State.restrictTo] using
            bodyResult.openResult.domain.restrictTo
        scope := hScope.mono bodyResult.openResult.freshExtends
        control := Functions.Source.Ctx.SameControl.refl ctx
        freshExtends := bodyResult.openResult.freshExtends
        retains := fun _hRegular _name hMem => hMem
        layoutWithin := hLayout.mono bodyResult.openResult.freshExtends
        layoutScope := fun _hRegular => hControl.scope
        exitScope := by
          simp [FunctionsObserverOutcome.ExitScopeRel] }
    exact
      ⟨{ openResult := result
         regularLayout := fun _hResultRegular => rfl
         regularControl := fun _hResultRegular => hControl }⟩
  · obtain ⟨bodyFuel, hBodyOpen⟩ := bodyResult.openResult.run
    have hBodyScoped :
        Functions.Source.Effectful.Block.runScoped
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions ctx
            { stmts := lowerStmts } bodyFuel target =
          .ok bodyResult.openResult.outcome :=
      Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hBodyOpen hRegular
    have hTargetStmt :
        Functions.Source.Effectful.Stmt.run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions ctx bodyFuel
            (.block { stmts := lowerStmts }) target =
          .ok (bodyResult.openResult.outcome, ctx) := by
      unfold Functions.Source.Effectful.Stmt.run
      rw [hBodyScoped]
      rfl
    have hTargetRun :
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions ctx (bodyFuel + 1)
            { stmts := [.block { stmts := lowerStmts }] } target =
          .ok (bodyResult.openResult.outcome, ctx) :=
      Functions.Source.Effectful.Block.runOpen_cons_nonregular
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetStmt hRegular
    have hExitSubset :
        ∀ name, name ∈ bodyResult.openResult.finalLayout →
          name ∈ layout :=
      hControl.exitSubset bodyResult.openResult.exitScope hRegular
    have hOutcomeRel :
        FunctionsObserverOutcome.ScopedOutcomeRel codeRel
          bodyResult.openResult.finalLayout sourceFinal
          bodyResult.openResult.outcome := by
      rw [hSourceFinal]
      simpa [hSource] using
        FunctionsObserverOutcome.ScopedOutcomeRel.restrictNonregularSource
          bodyResult.openResult.relation hRegular
          hEntryDomain hExitSubset
    let result :
        FunctionsObserverOutcome.ScopedOpenResult
          contract codeRel targetProgram.toFunctions
          [.block { stmts := lowerStmts }] before after layout
          sourceFinal target ctx :=
      { finalLayout := bodyResult.openResult.finalLayout
        outcome := bodyResult.openResult.outcome
        finalCtx := ctx
        run := ⟨bodyFuel + 1, hTargetRun⟩
        relation := hOutcomeRel
        domain := bodyResult.openResult.domain
        scope := hScope.mono bodyResult.openResult.freshExtends
        control := Functions.Source.Ctx.SameControl.refl ctx
        freshExtends := bodyResult.openResult.freshExtends
        retains := fun hResultRegular =>
          False.elim (hRegular hResultRegular)
        layoutWithin := bodyResult.openResult.layoutWithin
        layoutScope := fun hResultRegular =>
          False.elim (hRegular hResultRegular)
        exitScope := bodyResult.openResult.exitScope }
    exact
      ⟨{ openResult := result
         regularLayout := fun hResultRegular =>
           False.elim (hRegular hResultRegular)
         regularControl := fun hResultRegular =>
           False.elim (hRegular hResultRegular) }⟩

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
