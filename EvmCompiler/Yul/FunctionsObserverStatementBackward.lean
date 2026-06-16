import EvmCompiler.Functions.EffectSemanticsInversion
import EvmCompiler.Yul.FunctionsObserverExpressionBackward
import EvmCompiler.Yul.FunctionsObserverStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverStatementBackward

/-!
Backward adequacy for statement leaves at the adjacent Yul-to-Functions pass.

Each artifact contains a canonical source execution and the existing
outcome-indexed statement result, aligned to the concrete target execution.
The target run is never replayed through a second interpreter.
-/

abbrev Trace := Assembly.ResourceTrace

structure AlignedStmtBackward
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (stmt : AstStmt)
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
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes} where
  sourceFuel : Nat
  sourceFinal : ObserverSemantics.SourceReplay.State transcript
  sourceRun :
    Yul.Source.Effectful.exec
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        sourceFuel stmt codeOverride source =
      .ok sourceFinal
  result :
    FunctionsObserverStatement.OpenResult.Result
      contract codeRel program stmt lower initial final entryLayout
      sourceFinal target ctx (sourceControl := sourceControl)
  outcome_eq : result.openResult.outcome = targetOutcome
  finalCtx_eq : result.openResult.finalCtx = targetFinalCtx

def RecursiveOpenStmtBackwardBelow
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
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {canBreak canContinue canLeave : Bool},
    targetFuel < bound →
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave stmt =
        true →
      StateRelation.Vars.NamesWithin before.used (Stmt.names stmt) →
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before stmt =
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
        (AlignedStmtBackward contract codeRel targetProgram.toFunctions
          (some sourceProgram.contract) stmt lower before after layout
          source target ctx targetOutcome targetFinalCtx
          (sourceControl := sourceControl))

namespace AlignedStmtBackward

theorem regularControl
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {canBreak canContinue canLeave : Bool}
    (backward :
      AlignedStmtBackward contract codeRel program codeOverride
        stmt lower initial final entryLayout source target ctx
        targetOutcome targetFinalCtx (sourceControl := sourceControl))
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl entryLayout
        canBreak canContinue canLeave ctx)
    (hRegular : targetOutcome.mode = .regular) :
    FunctionsObserverOutcome.ControlContextRel sourceControl
      backward.result.openResult.finalLayout
      canBreak canContinue canLeave targetFinalCtx := by
  have hResultRegular :
      backward.result.openResult.outcome.mode = .regular := by
    rw [backward.outcome_eq]
    exact hRegular
  have hResultControl :=
    FunctionsObserverOutcome.ControlContextRel.transport hControl
      (backward.result.openResult.retains hResultRegular)
      backward.result.openResult.control
      (backward.result.openResult.layoutScope hResultRegular)
  simpa only [backward.finalCtx_eq] using hResultControl

theorem ofResult
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    (sourceFuel : Nat)
    (hSource :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel stmt codeOverride source =
        .ok sourceFinal)
    (result :
      FunctionsObserverStatement.OpenResult.Result
        contract codeRel program stmt lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl))
    {targetFuel : Nat}
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        stmt lower initial final entryLayout source target ctx
        targetOutcome targetFinalCtx (sourceControl := sourceControl)) := by
  obtain ⟨expectedFuel, hExpected⟩ := result.openResult.run
  have hAligned :=
    Functions.Source.Effectful.Block.runOpen_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hExpected hTarget
  exact
    ⟨⟨sourceFuel, sourceFinal, hSource, result,
      congrArg Prod.fst hAligned, congrArg Prod.snd hAligned⟩⟩

end AlignedStmtBackward

theorem letNoneBackward
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {functionNames layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {names : List EvmYul.Identifier}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hOk :
      SolcValidation.StmtOk? profile sourceContract
          functionNames layout canBreak canContinue canLeave
          (.Let names none) =
        true)
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
    (hLayoutScope :
      FunctionsObserverOutcome.LayoutWithinScope layout ctx)
    (hNamesUsed :
      StateRelation.Vars.NamesWithin before.used
        (identNames names))
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        (.Let names none) lower before after layout source target ctx
        targetOutcome targetFinalCtx (sourceControl := sourceControl)) := by
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hNoDup : (identNames names).Nodup := by
    simp [SolcValidation.StmtOk?, SolcValidation.bindableList?,
      SolcValidation.namesNodup?] at hOk
    exact hOk.2.2.1
  have hFresh :
      ∀ name, name ∈ identNames names → name ∉ layout := by
    simp [SolcValidation.StmtOk?, SolcValidation.bindableList?,
      SolcValidation.namesFresh?] at hOk
    intro name hMem hLayoutMem
    exact (hOk.2.2.2 name hMem).2 hLayoutMem
  have hCheck :
      EvmYul.Yul.checkDeclaration source.source names = .ok () := by
    rw [hSource]
    simpa [identNames_eq_self] using
      StateRelation.Vars.checkDeclaration_ok
        hSourceDomain hNoDup hFresh
  let sourceFinal :=
    source.withSource (source.source.zeroFill names)
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
        1 (.Let names none) codeOverride source =
        .ok sourceFinal := by
    simp [Yul.Source.Effectful.exec,
      ObserverSemantics.SourceReplay.stateModel, hCheck, sourceFinal]
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_let_none
      (program := program)
      (sourceControl := sourceControl)
      hLower hRel hDomain hScope hLayout hLayoutScope hNamesUsed
      hSourceRun
  exact
    AlignedStmtBackward.ofResult 1 hSourceRun result hTarget

theorem letOneBackward
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {functionNames layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lower : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hOk :
      SolcValidation.StmtOk? profile sourceContract
          functionNames layout canBreak canContinue canLeave
          (.Let [name] (some expr)) =
        true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Let [name] (some expr)) =
        some (lower, after))
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceContract contract transcript codeRel program
        codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hLayoutScope :
      FunctionsObserverOutcome.LayoutWithinScope layout ctx)
    (hNameUsed : identName name ∈ before.used)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        (.Let [name] (some expr)) lower before after layout
        source target ctx
        (Functions.Source.Effectful.Outcome.regular targetFinal)
        targetFinalCtx (sourceControl := sourceControl)) := by
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_one_parts
      hNotFunctionCall hLower
  rw [hLowerStmts] at hTarget
  obtain
      ⟨preTarget, preCtx, _rightFuel,
        hPre, hTail, _hRightFuel⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_bounded_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTarget
  obtain ⟨_stmtFuel, hLet⟩ :=
    Functions.Source.Effectful.Block.runOpen_singleton_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTail
  obtain ⟨evalTarget, value, hEval, _hFinal, _hFinalCtx⟩ :=
    Functions.Source.Effectful.Stmt.run_let_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hLet
  have hOkParts :
      SolcValidation.bindableList?
          (functionNames ++ layout) [identName name] = true ∧
        SolcValidation.ExprOk? profile sourceContract layout 1 expr =
          true := by
    simpa [SolcValidation.StmtOk?, identNames, identName] using hOk
  obtain ⟨valueBackward⟩ :=
    hExpr hTargetFuel hOkParts.2 hExprLower hRel hDomain hScope hPre hEval
  let exactValue := valueBackward.result
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hNameFresh : identName name ∉ layout := by
    have hBind := hOkParts.1
    simp [SolcValidation.bindableList?,
      SolcValidation.namesFresh?] at hBind
    exact hBind.2.2.2.2
  have hCheck :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok () := by
    rw [hSource]
    apply StateRelation.Vars.checkDeclaration_ok hSourceDomain
    · simp
    · intro candidate hMem
      simp at hMem
      simpa [hMem] using hNameFresh
  let sourceFinal :=
    exactValue.sourceFinal.withSource
      (exactValue.sourceFinal.source.multifill [name] [value])
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (valueBackward.sourceFuel + 1)
          (.Let [name] (some expr)) codeOverride source =
        .ok sourceFinal := by
    have hFilled :=
      congrArg
        (Yul.Source.Effectful.multifill
          (ObserverSemantics.SourceReplay.stateModel transcript) [name])
        exactValue.sourceValuesRun
    simpa [Yul.Source.Effectful.exec, hCheck,
      ObserverSemantics.SourceReplay.stateModel,
      Yul.Source.Effectful.multifill,
      Yul.Source.Effectful.StateModel.multifill, sourceFinal] using
      hFilled
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_let_one_prepared
      (sourceControl := sourceControl)
      hLowerStmts
      (Expr.lower1Unchecked?_stateExtends hExprLower)
      hNameFresh hNameUsed hLayout hLayoutScope exactValue.prepared rfl
  exact
    AlignedStmtBackward.ofResult
      (valueBackward.sourceFuel + 1) hSourceRun result
      (by simpa [hLowerStmts] using hTarget)

theorem assignOneBackward
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {functionNames layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lower : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hOk :
      SolcValidation.StmtOk? profile sourceContract
          functionNames layout canBreak canContinue canLeave
          (.Assign [name] expr) =
        true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Assign [name] expr) =
        some (lower, after))
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceContract contract transcript codeRel program
        codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hLayoutScope :
      FunctionsObserverOutcome.LayoutWithinScope layout ctx)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        (.Assign [name] expr) lower before after layout
        source target ctx
        (Functions.Source.Effectful.Outcome.regular targetFinal)
        targetFinalCtx (sourceControl := sourceControl)) := by
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_one_parts
      hNotFunctionCall hLower
  rw [hLowerStmts] at hTarget
  obtain
      ⟨preTarget, preCtx, _rightFuel,
        hPre, hTail, _hRightFuel⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_bounded_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTarget
  obtain ⟨_stmtFuel, hAssign⟩ :=
    Functions.Source.Effectful.Block.runOpen_singleton_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTail
  obtain
      ⟨_hTargetContains, evalTarget, value,
        hEval, _hFinal, _hFinalCtx⟩ :=
    Functions.Source.Effectful.Stmt.run_assign_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hAssign
  have hOkParts :
      SolcValidation.assignableList? layout [identName name] = true ∧
        SolcValidation.ExprOk? profile sourceContract layout 1 expr =
          true := by
    simpa [SolcValidation.StmtOk?, identNames, identName] using hOk
  obtain ⟨valueBackward⟩ :=
    hExpr hTargetFuel hOkParts.2 hExprLower hRel hDomain hScope hPre hEval
  let exactValue := valueBackward.result
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, hSourceDomain⟩ :=
    hRel.2
  have hAssignable := hOkParts.1
  simp [SolcValidation.assignableList?,
    SolcValidation.namesIn?] at hAssignable
  have hNameDeclared : identName name ∈ layout :=
    hAssignable.2.2
  have hCheck :
      EvmYul.Yul.checkAssignment source.source [name] = .ok () := by
    rw [hSource]
    apply StateRelation.Vars.checkAssignment_ok hSourceDomain
    · simp
    · intro candidate hMem
      simp at hMem
      simpa [hMem] using hNameDeclared
  let sourceFinal :=
    exactValue.sourceFinal.withSource
      (exactValue.sourceFinal.source.multifill [name] [value])
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (valueBackward.sourceFuel + 1)
          (.Assign [name] expr) codeOverride source =
        .ok sourceFinal := by
    have hFilled :=
      congrArg
        (Yul.Source.Effectful.multifill
          (ObserverSemantics.SourceReplay.stateModel transcript) [name])
        exactValue.sourceValuesRun
    simpa [Yul.Source.Effectful.exec, hCheck,
      ObserverSemantics.SourceReplay.stateModel,
      Yul.Source.Effectful.multifill,
      Yul.Source.Effectful.StateModel.multifill, sourceFinal] using
      hFilled
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_assign_one_prepared
      (sourceControl := sourceControl)
      hLowerStmts
      (Expr.lower1Unchecked?_stateExtends hExprLower)
      hNameDeclared hLayout hLayoutScope exactValue.prepared rfl
  exact
    AlignedStmtBackward.ofResult
      (valueBackward.sourceFuel + 1) hSourceRun result
      (by simpa [hLowerStmts] using hTarget)

theorem exprPrimitiveBackward
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {functionNames layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {lower : List Functions.Stmt}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hNonterminal : Prim.terminal? prim = none)
    (hOk :
      SolcValidation.StmtOk? profile sourceContract
          functionNames layout canBreak canContinue canLeave
          (.ExprStmtCall (.Call (.inl prim) args)) =
        true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.ExprStmtCall (.Call (.inl prim) args)) =
        some (lower, after))
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceContract contract transcript codeRel program
        codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hLayoutScope :
      FunctionsObserverOutcome.LayoutWithinScope layout ctx)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        (.ExprStmtCall (.Call (.inl prim) args))
        lower before after layout source target ctx
        (Functions.Source.Effectful.Outcome.regular targetFinal)
        targetFinalCtx (sourceControl := sourceControl)) := by
  obtain ⟨pre, lowerExpr, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_primitive_parts
      hNonterminal hLower
  rw [hLowerStmts] at hTarget
  obtain
      ⟨preTarget, preCtx, _rightFuel,
        hPre, hTail, _hRightFuel⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_bounded_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTarget
  obtain ⟨_stmtFuel, hExprStmt⟩ :=
    Functions.Source.Effectful.Block.runOpen_singleton_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTail
  obtain ⟨values, hEval, _hFinalCtx⟩ :=
    Functions.Source.Effectful.Stmt.run_expr_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hExprStmt
  have hExprOk :
      SolcValidation.ExprOk? profile sourceContract layout 0
          (.Call (.inl prim) args) =
        true := by
    simpa [SolcValidation.StmtOk?] using hOk
  obtain ⟨expressionBackward⟩ :=
    FunctionsObserverExpressionBackward.primitiveExpressionBackwardBelow
      profile sourceContract contract transcript codeRel program
      codeOverride bound hTargetFuel hExprOk hExprLower hExpr
      hRel hDomain hScope hPre hEval
  let exactExpr := expressionBackward.result
  have hMultifill :
      exactExpr.sourceFinal.source.multifill [] values =
        exactExpr.sourceFinal.source := by
    cases exactExpr.sourceFinal.source <;>
      simp [EvmYul.Yul.State.multifill]
  have hFilled :
      (ObserverSemantics.SourceReplay.stateModel transcript).multifill
          [] exactExpr.sourceFinal values =
        exactExpr.sourceFinal := by
    change
      exactExpr.sourceFinal.withSource
          (exactExpr.sourceFinal.source.multifill [] values) =
        exactExpr.sourceFinal
    rw [hMultifill]
    exact
      Simulation.ResourceReplay.State.withSource_self exactExpr.sourceFinal
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          expressionBackward.sourceFuel
          (.ExprStmtCall (.Call (.inl prim) args))
          codeOverride source =
        .ok exactExpr.sourceFinal := by
    rw [← hFilled]
    exact
      Yul.Source.Effectful.exec_expr_primitive_of_evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        exactExpr.sourceRun
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_expr_prepared
      (sourceControl := sourceControl)
      hLowerStmts
      (Expr.lowerUnchecked?_stateExtends hExprLower)
      hLayout hLayoutScope exactExpr.prepared
  exact
    AlignedStmtBackward.ofResult
      expressionBackward.sourceFuel hSourceRun result
      (by simpa [hLowerStmts] using hTarget)

theorem breakBackward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {layout breakLayout targetBreakScope : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
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
    (hSourceBreakScope :
      sourceControl.breakScope? = some breakLayout)
    (hBreakScope : ctx.breakScope? = some targetBreakScope)
    (hBreakSubset :
      ∀ name, name ∈ breakLayout → name ∈ layout)
    (hBreakTarget :
      ∀ name, name ∈ breakLayout → name ∈ targetBreakScope)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        .Break lower before after layout source target ctx
        targetOutcome targetFinalCtx (sourceControl := sourceControl)) := by
  let sourceFinal :=
    source.withSource (EvmYul.Yul.State.setBreak source.source)
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          1 .Break codeOverride source =
        .ok sourceFinal := by
    simp [Yul.Source.Effectful.exec,
      ObserverSemantics.SourceReplay.stateModel, sourceFinal]
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_break
      (sourceControl := sourceControl)
      hLower hRel hDomain hScope hLayout
      hSourceBreakScope hBreakScope hBreakSubset hBreakTarget hSourceRun
  exact
    AlignedStmtBackward.ofResult 1 hSourceRun result hTarget

theorem continueBackward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {layout continueLayout targetContinueScope : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
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
    (hSourceContinueScope :
      sourceControl.continueScope? = some continueLayout)
    (hContinueScope :
      ctx.continueScope? = some targetContinueScope)
    (hContinueSubset :
      ∀ name, name ∈ continueLayout → name ∈ layout)
    (hContinueTarget :
      ∀ name, name ∈ continueLayout → name ∈ targetContinueScope)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        .Continue lower before after layout source target ctx
        targetOutcome targetFinalCtx (sourceControl := sourceControl)) := by
  let sourceFinal :=
    source.withSource (EvmYul.Yul.State.setContinue source.source)
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          1 .Continue codeOverride source =
        .ok sourceFinal := by
    simp [Yul.Source.Effectful.exec,
      ObserverSemantics.SourceReplay.stateModel, sourceFinal]
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_continue
      (sourceControl := sourceControl)
      hLower hRel hDomain hScope hLayout
      hSourceContinueScope hContinueScope
      hContinueSubset hContinueTarget hSourceRun
  exact
    AlignedStmtBackward.ofResult 1 hSourceRun result hTarget

theorem leaveBackward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {compilerFuel targetFuel : Nat}
    {before after : Fresh.State}
    {layout leaveLayout targetLeaveScope : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    {targetOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
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
    (hSourceLeaveScope :
      sourceControl.leaveScope? = some leaveLayout)
    (hLeaveScope : ctx.leaveScope? = some targetLeaveScope)
    (hLeaveSubset :
      ∀ name, name ∈ leaveLayout → name ∈ layout)
    (hLeaveTarget :
      ∀ name, name ∈ leaveLayout → name ∈ targetLeaveScope)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := lower } target =
        .ok (targetOutcome, targetFinalCtx)) :
    Nonempty
      (AlignedStmtBackward contract codeRel program codeOverride
        .Leave lower before after layout source target ctx
        targetOutcome targetFinalCtx (sourceControl := sourceControl)) := by
  let sourceFinal :=
    source.withSource (EvmYul.Yul.State.setLeave source.source)
  have hSourceRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          1 .Leave codeOverride source =
        .ok sourceFinal := by
    simp [Yul.Source.Effectful.exec,
      ObserverSemantics.SourceReplay.stateModel, sourceFinal]
  obtain ⟨result⟩ :=
    FunctionsObserverStatement.OpenResult.of_leave
      (sourceControl := sourceControl)
      hLower hRel hDomain hScope hLayout
      hSourceLeaveScope hLeaveScope hLeaveSubset hLeaveTarget hSourceRun
  exact
    AlignedStmtBackward.ofResult 1 hSourceRun result hTarget

end FunctionsObserverStatementBackward
end Yul
end EvmCompiler
