import EvmCompiler.Yul.CompilerCallDecomposition
import EvmCompiler.Yul.CompilerStatementDecomposition
import EvmCompiler.Yul.FunctionsObserverCall
import EvmCompiler.Yul.FunctionsObserverOutcome

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverStatement

/-!
Statement and block preservation owned by the adjacent Yul-to-Functions pass.

The first constructor is the empty function-body base case. Subsequent
constructors compose ordinary statement lowering with the expression and call
interfaces; this module does not define a compiler or a control interpreter.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

namespace InitializedValue

theorem run
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {sourceAfterValue :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Word}
    (hValue :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program pre lower fresh
        sourceAfterValue target ctx value)
    (hScoped :
      StateRelation.Replay.ScopedExactRel codeRel layout
        sourceAfterValue hValue.evalTarget)
    (hFresh : identName name ∉ layout) :
    ∃ fuel finalTarget finalCtx,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel
          { stmts :=
              pre ++
                [Functions.Stmt.let_ (identName name) lower] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            finalCtx) ∧
      StateRelation.Replay.ScopedExactRel codeRel
        (identName name :: layout)
        (sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value]))
        finalTarget ∧
      finalTarget =
        hValue.evalTarget.withSource
          (hValue.evalTarget.source.insert (identName name) value) ∧
      finalCtx =
        { hValue.finalCtx with
          scope := identName name :: hValue.finalCtx.scope } := by
  let finalTarget :=
    hValue.evalTarget.withSource
      (hValue.evalTarget.source.insert (identName name) value)
  let finalCtx :=
    { hValue.finalCtx with
      scope := identName name :: hValue.finalCtx.scope }
  have hEvalOne :
      Functions.Source.Effectful.Expr.evalOne
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower hValue.preTarget =
        .ok (hValue.evalTarget, value) :=
    Functions.Source.Effectful.Expr.evalOne_of_eval_singleton
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hValue.eval
  have hLet :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hValue.finalCtx 1
          (.let_ (identName name) lower) hValue.preTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            finalCtx) := by
    simpa [finalTarget, finalCtx,
      Functions.ObserverSemantics.stateModel_insert] using
        Functions.Source.Effectful.Stmt.run_let_of_eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hEvalOne
  have hEmpty :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program finalCtx 1 { stmts := [] } finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_nil
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program finalCtx 0 finalTarget
  obtain ⟨rightFuel, hRight⟩ :=
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hLet hEmpty
  obtain ⟨fuel, hRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program pre [.let_ (identName name) lower] ctx
      hValue.finalCtx target hValue.preTarget
      (Functions.Source.Effectful.Outcome.regular finalTarget)
      finalCtx hValue.run ⟨rightFuel, hRight⟩
  refine ⟨fuel, finalTarget, finalCtx, hRun, ?_, rfl, rfl⟩
  simpa [finalTarget] using
    StateRelation.Replay.scopedExact_multifill_single_fresh
      hScoped name value hFresh

end InitializedValue

namespace AssignedValue

theorem run
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {sourceAfterValue :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Word}
    (hValue :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program pre lower fresh
        sourceAfterValue target ctx value)
    (hScoped :
      StateRelation.Replay.ScopedExactRel codeRel layout
        sourceAfterValue hValue.evalTarget)
    (hDeclared : identName name ∈ layout) :
    ∃ fuel finalTarget,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel
          { stmts :=
              pre ++
                [Functions.Stmt.assign (identName name) lower] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            hValue.finalCtx) ∧
      StateRelation.Replay.ScopedExactRel codeRel layout
        (sourceAfterValue.withSource
          (sourceAfterValue.source.multifill [name] [value]))
        finalTarget ∧
      finalTarget =
        hValue.evalTarget.withSource
          (hValue.evalTarget.source.insert (identName name) value) := by
  let finalTarget :=
    hValue.evalTarget.withSource
      (hValue.evalTarget.source.insert (identName name) value)
  obtain
      ⟨_sourceShared, _sourceVars, _hSource,
        _hShared, hVars, hDomain⟩ :=
    hScoped.2
  have hEvalContains :
      hValue.evalTarget.source.vars.contains (identName name) = true :=
    StateRelation.Vars.target_contains_of_scopedExact
      hVars hDomain hDeclared
  have hEvalVars :
      hValue.evalTarget.source.vars =
        hValue.preTarget.source.vars :=
    Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hValue.eval
  have hPreContains :
      hValue.preTarget.source.vars.contains (identName name) = true := by
    rw [← hEvalVars]
    exact hEvalContains
  have hEvalOne :
      Functions.Source.Effectful.Expr.evalOne
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower hValue.preTarget =
        .ok (hValue.evalTarget, value) :=
    Functions.Source.Effectful.Expr.evalOne_of_eval_singleton
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hValue.eval
  have hAssign :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hValue.finalCtx 1
          (.assign (identName name) lower) hValue.preTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            hValue.finalCtx) := by
    simpa [finalTarget,
      Functions.ObserverSemantics.stateModel_withVars] using
        Functions.Source.Effectful.Stmt.run_assign_of_eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPreContains hEvalOne
  have hEmpty :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hValue.finalCtx 1 { stmts := [] } finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            hValue.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_nil
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hValue.finalCtx 0 finalTarget
  obtain ⟨rightFuel, hRight⟩ :=
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hAssign hEmpty
  obtain ⟨fuel, hRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program pre [.assign (identName name) lower] ctx
      hValue.finalCtx target hValue.preTarget
      (Functions.Source.Effectful.Outcome.regular finalTarget)
      hValue.finalCtx hValue.run ⟨rightFuel, hRight⟩
  refine ⟨fuel, finalTarget, hRun, ?_, rfl⟩
  simpa [finalTarget] using
    StateRelation.Replay.scopedExact_multifill_single_visible
      hScoped name value hDeclared

end AssignedValue

namespace InitNames

theorem run
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {program : Functions.Program}
    (names : List Name)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) :
    ∃ fuel finalVars finalCtx,
      Functions.Source.Store.insertMany names
          (names.map fun _name => Functions.Source.zero)
          target.source.vars =
        some finalVars ∧
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel
          { stmts := Stmt.initNames names } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            (target.withSource
              { shared := target.source.shared, vars := finalVars }),
            finalCtx) ∧
      finalCtx =
        { ctx with scope := names.reverse ++ ctx.scope } := by
  induction names generalizing target ctx with
  | nil =>
      refine ⟨1, target.source.vars, ctx, rfl, ?_, ?_⟩
      · simpa [Stmt.initNames] using
          Functions.Source.Effectful.Block.runOpen_nil
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx 0 target
      · rfl
  | cons name rest ih =>
      let targetHead :=
        target.withSource (target.source.insert name Functions.Source.zero)
      let ctxHead := { ctx with scope := name :: ctx.scope }
      have hHead :
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              program ctx 0
              (.let_ name (.lit Functions.Source.zero)) target =
            .ok
              (Functions.Source.Effectful.Outcome.regular targetHead,
                ctxHead) := by
        simpa [targetHead, ctxHead,
          Functions.ObserverSemantics.stateModel_insert] using
            Functions.Source.Effectful.Stmt.run_let_lit
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              program name Functions.Source.zero
      obtain ⟨tailFuel, finalVars, finalCtx,
          hInsert, hTail, hFinalCtx⟩ :=
        ih (target := targetHead) (ctx := ctxHead)
      have hTarget :
          targetHead.withSource
              { shared := targetHead.source.shared, vars := finalVars } =
            target.withSource
              { shared := target.source.shared, vars := finalVars } := by
        cases target
        rfl
      rw [hTarget] at hTail
      obtain ⟨fuel, hRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_cons_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hHead hTail
      refine ⟨fuel, finalVars, finalCtx, ?_, ?_, ?_⟩
      · simpa [Functions.Source.Store.insertMany, targetHead,
          Locals.Source.State.insert] using hInsert
      · simpa [Stmt.initNames] using hRun
      · rw [hFinalCtx]
        simp [ctxHead, List.reverse_cons, List.append_assoc]

end InitNames

namespace OpenResult

theorem of_let_none
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {names : List EvmYul.Identifier}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
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
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨hLowerStmts, hAfter⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_none_parts hLower
  subst lower
  subst after
  obtain ⟨_previous, _hFuel, hCheck, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_let_none_ok_parts
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
  obtain ⟨hNamesNodup, hNamesFresh⟩ :=
    StateRelation.Vars.checkDeclaration_ok_parts
      (layout := layout) (source := sourceVars)
      (shared := sourceShared) hSourceDomain hCheckSource
  obtain ⟨targetFuel, finalVars, finalCtx,
      hInsert, hTargetRun, hFinalCtx⟩ :=
    InitNames.run
      (contract := contract) (program := program)
      (identNames names) target ctx
  let targetFinal :=
    target.withSource
      { shared := target.source.shared, vars := finalVars }
  have hSourceFinal' :
      sourceFinal =
        source.withSource (source.source.zeroFill names) := by
    simpa using hSourceFinal
  have hFinalRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (identNames names ++ layout) sourceFinal targetFinal := by
    rw [hSourceFinal']
    simpa [targetFinal, identNames_eq_self] using
      StateRelation.Replay.scopedExact_zeroFill_insertMany
        hRel
        (by simpa [identNames_eq_self] using hNamesNodup)
        (by simpa [identNames_eq_self] using hNamesFresh)
        hInsert
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel
        (identNames names ++ layout) sourceFinal
        (Functions.Source.Effectful.Outcome.regular targetFinal) := by
    obtain
        ⟨finalShared, finalSourceVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalDomain⟩ :=
      hFinalRel.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource hFinalRel
  have hFinalDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used targetFinal.source.vars := by
    simpa [targetFinal] using
      hDomain.insertMany hNamesUsed hInsert
  have hFinalScope :
      StateRelation.Vars.NamesWithin before.used finalCtx.scope := by
    rw [hFinalCtx]
    intro name hMem
    rcases List.mem_append.mp hMem with hDeclared | hOuter
    · exact hNamesUsed name (by simpa using hDeclared)
    · exact hScope name hOuter
  exact
    ⟨{ finalLayout := identNames names ++ layout
       outcome := Functions.Source.Effectful.Outcome.regular targetFinal
       finalCtx := finalCtx
       run := ⟨targetFuel, by simpa [targetFinal] using hTargetRun⟩
       relation := hOutcomeRel
       domain := hFinalDomain
       scope := hFinalScope
       control := by
         rw [hFinalCtx]
         exact Functions.Source.Ctx.SameControl.scopeUpdate ctx _
       freshExtends := Fresh.Extends.refl before
       retains := fun _hRegular name hMem =>
         List.mem_append_right _ hMem
       layoutWithin := by
         intro name hMem
         rcases List.mem_append.mp hMem with hDeclared | hOuter
         · exact hNamesUsed name hDeclared
         · exact hLayout name hOuter }⟩

theorem of_let_one
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 1 expr =
        true)
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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Let [name] (some expr))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel targetProgram.toFunctions lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_one_parts
      hNotFunctionCall hLower
  subst lower
  obtain
      ⟨evalFuel, sourceAfterValue, values, hFuel,
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
  obtain ⟨value, hValues, hScopedValueNonempty⟩ :=
    hValue (exprFuel := evalFuel) (by omega)
      hExprOk hExprLower hRel hDomain hScope hEvalValues
  obtain ⟨hScopedValue⟩ := hScopedValueNonempty
  let sourceDeclared :=
    sourceAfterValue.withSource
      (sourceAfterValue.source.multifill [name] [value])
  have hSourceFinal' : sourceFinal = sourceDeclared := by
    rw [hSourceFinal, hValues]
    rfl
  obtain
      ⟨targetFuel, targetFinal, finalCtx,
        hTargetRun, hDeclaredRel, hTargetFinal, hFinalCtx⟩ :=
    InitializedValue.run hScopedValue.prepared
      hScopedValue.relation hNameFresh
  have hFreshExtends : Fresh.Extends before after :=
    Expr.lower1Unchecked?_stateExtends hExprLower
  have hNameAfter : identName name ∈ after.used :=
    hFreshExtends (identName name) hNameUsed
  have hFinalDomain :
      StateRelation.Vars.TargetDomainWithin
        after.used targetFinal.source.vars := by
    rw [hTargetFinal]
    simpa using
      hScopedValue.prepared.domain.insert_visible hNameAfter
  have hFinalScope :
      StateRelation.Vars.NamesWithin after.used finalCtx.scope := by
    rw [hFinalCtx]
    intro candidate hMem
    rcases List.mem_cons.mp hMem with hHead | hTail
    · simpa [hHead] using hNameAfter
    · exact hScopedValue.prepared.scope candidate hTail
  have hFinalControl :
      Functions.Source.Ctx.SameControl ctx finalCtx := by
    apply Functions.Source.Ctx.SameControl.trans
      hScopedValue.prepared.control
    rw [hFinalCtx]
    exact
      Functions.Source.Ctx.SameControl.scopeUpdate
        hScopedValue.prepared.finalCtx _
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel
        (identName name :: layout) sourceFinal
        (Functions.Source.Effectful.Outcome.regular targetFinal) := by
    rw [hSourceFinal']
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      hDeclaredRel.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource hDeclaredRel
  exact
    ⟨{ finalLayout := identName name :: layout
       outcome := Functions.Source.Effectful.Outcome.regular targetFinal
       finalCtx := finalCtx
       run := ⟨targetFuel, hTargetRun⟩
       relation := hOutcomeRel
       domain := hFinalDomain
       scope := hFinalScope
       control := hFinalControl
       freshExtends := hFreshExtends
       retains := fun _hRegular candidate hMem =>
         List.mem_cons_of_mem (identName name) hMem
       layoutWithin := by
         intro candidate hMem
         rcases List.mem_cons.mp hMem with hHead | hTail
         · simpa [hHead] using hNameAfter
         · exact
             hFreshExtends candidate
               (hLayout candidate hTail) }⟩

theorem of_assign_one
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 1 expr =
        true)
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
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Assign [name] expr)
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel targetProgram.toFunctions lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨pre, lowerValue, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_one_parts
      hNotFunctionCall hLower
  subst lower
  obtain
      ⟨evalFuel, sourceAfterValue, values, hFuel,
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
  obtain ⟨value, hValues, hScopedValueNonempty⟩ :=
    hValue (exprFuel := evalFuel) (by omega)
      hExprOk hExprLower hRel hDomain hScope hEvalValues
  obtain ⟨hScopedValue⟩ := hScopedValueNonempty
  let sourceAssigned :=
    sourceAfterValue.withSource
      (sourceAfterValue.source.multifill [name] [value])
  have hSourceFinal' : sourceFinal = sourceAssigned := by
    rw [hSourceFinal, hValues]
    rfl
  obtain
      ⟨targetFuel, targetFinal,
        hTargetRun, hAssignedRel, hTargetFinal⟩ :=
    AssignedValue.run hScopedValue.prepared
      hScopedValue.relation hNameDeclared
  have hFreshExtends : Fresh.Extends before after :=
    Expr.lower1Unchecked?_stateExtends hExprLower
  have hNameAfter : identName name ∈ after.used :=
    hFreshExtends (identName name)
      (hLayout (identName name) hNameDeclared)
  have hFinalDomain :
      StateRelation.Vars.TargetDomainWithin
        after.used targetFinal.source.vars := by
    rw [hTargetFinal]
    simpa using
      hScopedValue.prepared.domain.insert_visible hNameAfter
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
        sourceFinal
        (Functions.Source.Effectful.Outcome.regular targetFinal) := by
    rw [hSourceFinal']
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      hAssignedRel.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource hAssignedRel
  exact
    ⟨{ finalLayout := layout
       outcome := Functions.Source.Effectful.Outcome.regular targetFinal
       finalCtx := hScopedValue.prepared.finalCtx
       run := ⟨targetFuel, hTargetRun⟩
       relation := hOutcomeRel
       domain := hFinalDomain
       scope := hScopedValue.prepared.scope
       control := hScopedValue.prepared.control
       freshExtends := hFreshExtends
       retains := fun _hRegular _candidate hMem => hMem
       layoutWithin := hLayout.mono hFreshExtends }⟩

theorem of_expr_primitive
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hNonterminal : Prim.terminal? prim = none)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 0 (.Call (.inl prim) args) =
        true)
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
    (hExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
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
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel targetProgram.toFunctions lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨pre, lowerExpr, hExprLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_primitive_parts
      hNonterminal hLower
  subst lower
  obtain
      ⟨evalPrevious, sourceAfterPrim, values,
        hSourceFuel, hEvalValues, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_expr_primitive_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  subst sourceFuel
  have hMultifill :
      sourceAfterPrim.source.multifill [] values =
        sourceAfterPrim.source := by
    cases sourceAfterPrim.source <;>
      simp [EvmYul.Yul.State.multifill]
  have hSourceFinal' : sourceFinal = sourceAfterPrim := by
    rw [hSourceFinal]
    change
      sourceAfterPrim.withSource
          (sourceAfterPrim.source.multifill [] values) =
        sourceAfterPrim
    rw [hMultifill]
    exact
      Simulation.ResourceReplay.State.withSource_self sourceAfterPrim
  clear hSourceFinal
  subst sourceFinal
  have hArgsOk :
      SolcValidation.ExprsOk? profile
          sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  obtain ⟨prepared⟩ :=
    FunctionsObserverExpression.ScopedPreparedExpression.ofPrimitive
      hExprLower
      (fun candidate hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
      (fun hArgFuel hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun =>
        hExpr hArgFuel hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun)
      hRel hDomain hScope hEvalValues
  have hExprStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions prepared.prepared.finalCtx 0
          (.expr lowerExpr) prepared.prepared.preTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            prepared.prepared.evalTarget,
            prepared.prepared.finalCtx) := by
    simp [Functions.Source.Effectful.Stmt.run,
      prepared.prepared.eval]
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
  obtain ⟨exprFuel, hExprBlock⟩ :=
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hExprStmt hEmpty
  obtain ⟨targetFuel, hTargetRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions pre [.expr lowerExpr]
      ctx prepared.prepared.finalCtx target
      prepared.prepared.preTarget
      (Functions.Source.Effectful.Outcome.regular
        prepared.prepared.evalTarget)
      prepared.prepared.finalCtx prepared.prepared.run
      ⟨exprFuel, hExprBlock⟩
  have hFreshExtends : Fresh.Extends before after :=
    Expr.lowerUnchecked?_stateExtends hExprLower
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
        sourceAfterPrim
        (Functions.Source.Effectful.Outcome.regular
          prepared.prepared.evalTarget) := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      prepared.relation.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource prepared.relation
  exact
    ⟨{ finalLayout := layout
       outcome :=
         Functions.Source.Effectful.Outcome.regular
           prepared.prepared.evalTarget
       finalCtx := prepared.prepared.finalCtx
       run := ⟨targetFuel, by simpa using hTargetRun⟩
       relation := hOutcomeRel
       domain := prepared.prepared.domain
       scope := prepared.prepared.scope
       control := prepared.prepared.control
       freshExtends := hFreshExtends
       retains := fun _hRegular _candidate hMem => hMem
       layoutWithin := hLayout.mono hFreshExtends }⟩

theorem of_expr_call
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {functionName : Name}
    {args : List AstExpr}
    {lower : List Functions.Stmt}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 0 (.Call (.inr functionName) args) =
        true)
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
    (hExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
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
          (.ExprStmtCall (.Call (.inr functionName) args))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel targetProgram.toFunctions lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_call_parts hLower
  subst lower
  obtain
      ⟨argsFuel, callFuel, sourceAfterArgs, reversedValues,
        sourceAfterCall, returnValues, hSourceFuel, hArgsFuel,
        hArgsRun, hCallRun, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_expr_function_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨returnedCall⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofFunctionCallParts
      (targets := [])
      hDecomposition hArgsLowering hProgramOk
      hExprOk
      List.nodup_nil (by simp) hExpr hBody
      hRel hDomain hScope (by omega) (by omega)
      hArgsRun hCallRun
      (by
        simpa [Yul.Source.Effectful.StateModel.multifill] using
          hSourceFinal)
  have hFreshExtends : Fresh.Extends before after :=
    hArgsLowering.stateExtends
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout
        sourceFinal
        (Functions.Source.Effectful.Outcome.regular
          returnedCall.finalTarget) := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      returnedCall.relation.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource returnedCall.relation
  exact
    ⟨{ finalLayout := layout
       outcome :=
         Functions.Source.Effectful.Outcome.regular
           returnedCall.finalTarget
       finalCtx := returnedCall.finalCtx
       run := by simpa using returnedCall.run
       relation := hOutcomeRel
       domain := returnedCall.domain
       scope := returnedCall.scope
       control := returnedCall.control
       freshExtends := hFreshExtends
       retains := fun _hRegular _candidate hMem => hMem
       layoutWithin := hLayout.mono hFreshExtends }⟩

theorem of_assign_call
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {compilerFuel sourceFuel : Nat}
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
          (.Assign names (.Call (.inr functionName) callArgs))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel targetProgram.toFunctions lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_call_parts hLower
  subst lower
  obtain
      ⟨evalFuel, sourceAfterCall, returnValues, hFuel,
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
  obtain ⟨returnedCall⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofFunctionCall
      hDecomposition hArgsLowering hProgramOk
      (by simpa [identNames_eq_self] using hExprOk)
      (by simpa [identNames_eq_self] using hTargetsNodup)
      (by simpa [identNames_eq_self] using hTargetsVisible)
      (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
          hArgScope hArgRun =>
        FunctionsObserverCall.RecursiveScopedValueForward.expression
          hValue (by omega) hArgOk hArgLower hArgRel hArgDomain
          hArgScope hArgRun)
      (fun hBodyFuel hBodyLower hParams hReturns hParamStore
          hReserved hBodyNames hBodyOk hBodyEntry hBodyRun =>
        hBody (by omega) hBodyLower hParams hReturns hParamStore
          hReserved hBodyNames hBodyOk hBodyEntry hBodyRun)
      hRel hDomain hScope hEvalValues
      (by simpa [identNames_eq_self] using hSourceFinal)
  have hFreshExtends : Fresh.Extends before after :=
    hArgsLowering.stateExtends
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel layout sourceFinal
        (Functions.Source.Effectful.Outcome.regular
          returnedCall.finalTarget) := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      returnedCall.relation.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource returnedCall.relation
  exact
    ⟨{ finalLayout := layout
       outcome :=
         Functions.Source.Effectful.Outcome.regular
           returnedCall.finalTarget
       finalCtx := returnedCall.finalCtx
       run := by
         simpa [identNames_eq_self] using returnedCall.run
       relation := hOutcomeRel
       domain := returnedCall.domain
       scope := returnedCall.scope
       control := returnedCall.control
       freshExtends := hFreshExtends
       retains := fun _hRegular _candidate hMem => hMem
       layoutWithin := hLayout.mono hFreshExtends }⟩

theorem of_let_call
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {compilerFuel sourceFuel : Nat}
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
          (.Let names (some (.Call (.inr functionName) callArgs)))
          (some sourceProgram.contract) source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel targetProgram.toFunctions lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_call_parts hLower
  subst lower
  obtain
      ⟨evalFuel, sourceAfterCall, returnValues, hFuel,
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
      ⟨initFuel, initVars, initCtx,
        hInsert, hInitRun, hInitCtx⟩ :=
    InitNames.run
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
  obtain ⟨returnedCall⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofFunctionCallFresh
      hDecomposition hArgsLowering hProgramOk
      (by simpa [identNames_eq_self] using hExprOk)
      (by simpa [identNames_eq_self] using hTargetsNodup)
      (by simpa [identNames_eq_self] using hTargetsFresh)
      hTargetsContain
      (fun hArgFuel hArgOk hArgLower hArgRel hArgDomain
          hArgScope hArgRun =>
        FunctionsObserverCall.RecursiveScopedValueForward.expression
          hValue (by omega) hArgOk hArgLower hArgRel hArgDomain
          hArgScope hArgRun)
      (fun hBodyFuel hBodyLower hParams hReturns hParamStore
          hReserved hBodyNames hBodyOk hBodyEntry hBodyRun =>
        hBody (by omega) hBodyLower hParams hReturns hParamStore
          hReserved hBodyNames hBodyOk hBodyEntry hBodyRun)
      hDeclaredRel hDeclaredDomain hDeclaredScope hEvalValues
      (by simpa [identNames_eq_self] using hSourceFinal)
  obtain ⟨callFuel, hCallRun⟩ := returnedCall.run
  obtain ⟨targetFuel, hTargetRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
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
        returnedCall.finalTarget)
      returnedCall.finalCtx
      ⟨initFuel, by simpa [targetDeclared] using hInitRun⟩
      ⟨callFuel, by simpa [identNames_eq_self] using hCallRun⟩
  have hFreshExtends : Fresh.Extends before after :=
    hArgsLowering.stateExtends
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel
        (identNames names ++ layout) sourceFinal
        (Functions.Source.Effectful.Outcome.regular
          returnedCall.finalTarget) := by
    obtain
        ⟨finalShared, finalVars, hFinalSource,
          _hFinalShared, _hFinalScoped, _hFinalSourceDomain⟩ :=
      returnedCall.relation.2
    exact
      FunctionsObserverOutcome.ScopedOutcomeRel.regular
        hFinalSource returnedCall.relation
  exact
    ⟨{ finalLayout := identNames names ++ layout
       outcome :=
         Functions.Source.Effectful.Outcome.regular
           returnedCall.finalTarget
       finalCtx := returnedCall.finalCtx
       run := ⟨targetFuel, by
         simpa [List.append_assoc] using hTargetRun⟩
       relation := hOutcomeRel
       domain := returnedCall.domain
       scope := returnedCall.scope
       control := by
         have hInitControl :
             Functions.Source.Ctx.SameControl ctx initCtx := by
           rw [hInitCtx]
           exact Functions.Source.Ctx.SameControl.scopeUpdate ctx _
         exact
           Functions.Source.Ctx.SameControl.trans
             hInitControl returnedCall.control
       freshExtends := hFreshExtends
       retains := fun _hRegular candidate hMem =>
         List.mem_append_right _ hMem
       layoutWithin := by
         intro candidate hMem
         rcases List.mem_append.mp hMem with hDeclared | hOuter
         · exact
             hFreshExtends candidate
               (hNamesUsed candidate hDeclared)
         · exact
             hFreshExtends candidate
               (hLayout candidate hOuter) }⟩

private theorem of_single_nonregular
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {before after : Fresh.State}
    {layout finalLayout : List Name}
    {lower : List Functions.Stmt}
    {stmt : Functions.Stmt}
    {sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {outcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hLower : lower = [stmt])
    (hAfter : after = before)
    (hTargetStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx 1 stmt target =
        .ok (outcome, ctx))
    (hNonregular : outcome.mode ≠ .regular)
    (hRelation :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel finalLayout
        sourceFinal outcome)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used outcome.state.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used finalLayout) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower before after layout
        sourceFinal target ctx) := by
  subst lower
  subst after
  have hTargetRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx 2 { stmts := [stmt] } target =
        .ok (outcome, ctx) := by
    exact
      Functions.Source.Effectful.Block.runOpen_cons_nonregular
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hTargetStmt hNonregular
  exact
    ⟨{ finalLayout := finalLayout
       outcome := outcome
       finalCtx := ctx
       run := ⟨2, hTargetRun⟩
       relation := hRelation
       domain := hDomain
       scope := hScope
       control := Functions.Source.Ctx.SameControl.refl ctx
       freshExtends := Fresh.Extends.refl before
       retains := fun hRegular => False.elim (hNonregular hRegular)
       layoutWithin := hLayout }⟩

theorem of_leave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout leaveLayout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
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
    (hLeaveScope : ctx.leaveScope? = some leaveLayout)
    (hLeaveSubset :
      ∀ name, name ∈ leaveLayout → name ∈ layout)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel .Leave codeOverride source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨hLowerStmts, hAfter⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_leave_parts hLower
  subst lower
  subst after
  obtain ⟨_previous, _hFuel, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_leave_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, _hSourceDomain⟩ :=
    hRel.2
  let sourceLeave :=
    source.withSource (EvmYul.Yul.State.setLeave source.source)
  have hSourceFinal' : sourceFinal = sourceLeave := by
    simpa [sourceLeave] using hSourceFinal
  have hSourceLeave :
      sourceLeave.source =
        .Checkpoint (.Leave sourceShared sourceVars) := by
    change
      EvmYul.Yul.State.setLeave source.source =
        .Checkpoint (.Leave sourceShared sourceVars)
    rw [hSource]
    rfl
  let targetLeave :=
    target.withSource (target.source.restrictTo leaveLayout)
  have hTargetStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx 1 .leave target =
        .ok
          (Functions.Source.Effectful.Outcome.leave targetLeave, ctx) := by
    simpa [targetLeave] using
      Functions.Source.Effectful.Stmt.run_leave_of_scope
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hLeaveScope
  have hWeakRel :
      StateRelation.Replay.ScopedRel codeRel leaveLayout source targetLeave := by
    simpa [targetLeave] using
      StateRelation.Replay.scopedRel_restrict_target_of_scopedExact
        hRel hLeaveSubset
  have hSourceRestored :
      sourceFinal.withSource (.Ok sourceShared sourceVars) = source := by
    rw [hSourceFinal']
    change sourceLeave.withSource (.Ok sourceShared sourceVars) = source
    change source.withSource (.Ok sourceShared sourceVars) = source
    rw [← hSource]
    exact Simulation.ResourceReplay.State.withSource_self source
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel leaveLayout
        sourceFinal
        (Functions.Source.Effectful.Outcome.leave targetLeave) := by
    apply
      FunctionsObserverOutcome.ScopedOutcomeRel.leave
        (shared := sourceShared) (vars := sourceVars)
    · rw [hSourceFinal']
      exact hSourceLeave
    · rw [hSourceRestored]
      exact hWeakRel
  have hLeaveUsed :
      StateRelation.Vars.NamesWithin before.used leaveLayout := by
    intro name hMem
    exact hLayout name (hLeaveSubset name hMem)
  exact of_single_nonregular
    rfl rfl hTargetStmt
    (Functions.Source.Effectful.Outcome.leave_not_regular targetLeave)
    hOutcomeRel
    (by
      simpa [targetLeave, Locals.Source.State.restrictTo] using
        hDomain.restrictTo)
    hScope hLeaveUsed

theorem of_break
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout breakLayout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
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
    (hBreakScope : ctx.breakScope? = some breakLayout)
    (hBreakSubset :
      ∀ name, name ∈ breakLayout → name ∈ layout)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel .Break codeOverride source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨hLowerStmts, hAfter⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_break_parts hLower
  obtain ⟨_previous, _hFuel, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_break_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, _hSourceDomain⟩ :=
    hRel.2
  let sourceBreak :=
    source.withSource (EvmYul.Yul.State.setBreak source.source)
  have hSourceFinal' : sourceFinal = sourceBreak := by
    simpa [sourceBreak] using hSourceFinal
  have hSourceBreak :
      sourceBreak.source =
        .Checkpoint (.Break sourceShared sourceVars) := by
    change
      EvmYul.Yul.State.setBreak source.source =
        .Checkpoint (.Break sourceShared sourceVars)
    rw [hSource]
    rfl
  let targetBreak :=
    target.withSource (target.source.restrictTo breakLayout)
  have hTargetStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx 1 .brk target =
        .ok
          (Functions.Source.Effectful.Outcome.brk targetBreak, ctx) := by
    simpa [targetBreak] using
      Functions.Source.Effectful.Stmt.run_brk_of_scope
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hBreakScope
  have hWeakRel :
      StateRelation.Replay.ScopedRel codeRel breakLayout source targetBreak := by
    simpa [targetBreak] using
      StateRelation.Replay.scopedRel_restrict_target_of_scopedExact
        hRel hBreakSubset
  have hSourceRestored :
      sourceFinal.withSource (.Ok sourceShared sourceVars) = source := by
    rw [hSourceFinal']
    change sourceBreak.withSource (.Ok sourceShared sourceVars) = source
    change source.withSource (.Ok sourceShared sourceVars) = source
    rw [← hSource]
    exact Simulation.ResourceReplay.State.withSource_self source
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel breakLayout
        sourceFinal
        (Functions.Source.Effectful.Outcome.brk targetBreak) := by
    apply
      FunctionsObserverOutcome.ScopedOutcomeRel.brk
        (shared := sourceShared) (vars := sourceVars)
    · rw [hSourceFinal']
      exact hSourceBreak
    · rw [hSourceRestored]
      exact hWeakRel
  have hBreakUsed :
      StateRelation.Vars.NamesWithin before.used breakLayout := by
    intro name hMem
    exact hLayout name (hBreakSubset name hMem)
  exact of_single_nonregular
    hLowerStmts hAfter hTargetStmt
    (Functions.Source.Effectful.Outcome.brk_not_regular targetBreak)
    hOutcomeRel
    (by
      simpa [targetBreak, Locals.Source.State.restrictTo] using
        hDomain.restrictTo)
    hScope hBreakUsed

theorem of_continue
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {compilerFuel sourceFuel : Nat}
    {before after : Fresh.State}
    {layout continueLayout : List Name}
    {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
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
    (hContinueScope : ctx.continueScope? = some continueLayout)
    (hContinueSubset :
      ∀ name, name ∈ continueLayout → name ∈ layout)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel .Continue codeOverride source =
        .ok sourceFinal) :
    Nonempty
      (FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower before after layout
        sourceFinal target ctx) := by
  obtain ⟨hLowerStmts, hAfter⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_continue_parts hLower
  obtain ⟨_previous, _hFuel, hSourceFinal⟩ :=
    Yul.Source.Effectful.exec_continue_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨sourceShared, sourceVars, hSource,
        _hShared, _hScoped, _hSourceDomain⟩ :=
    hRel.2
  let sourceContinue :=
    source.withSource (EvmYul.Yul.State.setContinue source.source)
  have hSourceFinal' : sourceFinal = sourceContinue := by
    simpa [sourceContinue] using hSourceFinal
  have hSourceContinue :
      sourceContinue.source =
        .Checkpoint (.Continue sourceShared sourceVars) := by
    change
      EvmYul.Yul.State.setContinue source.source =
        .Checkpoint (.Continue sourceShared sourceVars)
    rw [hSource]
    rfl
  let targetContinue :=
    target.withSource (target.source.restrictTo continueLayout)
  have hTargetStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx 1 .cont target =
        .ok
          (Functions.Source.Effectful.Outcome.cont targetContinue, ctx) := by
    simpa [targetContinue] using
      Functions.Source.Effectful.Stmt.run_cont_of_scope
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hContinueScope
  have hWeakRel :
      StateRelation.Replay.ScopedRel codeRel continueLayout
        source targetContinue := by
    simpa [targetContinue] using
      StateRelation.Replay.scopedRel_restrict_target_of_scopedExact
        hRel hContinueSubset
  have hSourceRestored :
      sourceFinal.withSource (.Ok sourceShared sourceVars) = source := by
    rw [hSourceFinal']
    change
      sourceContinue.withSource (.Ok sourceShared sourceVars) = source
    change source.withSource (.Ok sourceShared sourceVars) = source
    rw [← hSource]
    exact Simulation.ResourceReplay.State.withSource_self source
  have hOutcomeRel :
      FunctionsObserverOutcome.ScopedOutcomeRel codeRel continueLayout
        sourceFinal
        (Functions.Source.Effectful.Outcome.cont targetContinue) := by
    apply
      FunctionsObserverOutcome.ScopedOutcomeRel.cont
        (shared := sourceShared) (vars := sourceVars)
    · rw [hSourceFinal']
      exact hSourceContinue
    · rw [hSourceRestored]
      exact hWeakRel
  have hContinueUsed :
      StateRelation.Vars.NamesWithin before.used continueLayout := by
    intro name hMem
    exact hLayout name (hContinueSubset name hMem)
  exact of_single_nonregular
    hLowerStmts hAfter hTargetStmt
    (Functions.Source.Effectful.Outcome.cont_not_regular targetContinue)
    hOutcomeRel
    (by
      simpa [targetContinue, Locals.Source.State.restrictTo] using
        hDomain.restrictTo)
    hScope hContinueUsed

end OpenResult

namespace ReturnedBody

theorem of_empty
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
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
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨compilerFuel, lowerStmts, _hCompilerFuel, hLowerList, hBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  obtain ⟨_previous, _hPrevious, hLowerStmts, _hAfter⟩ :=
    Stmt.List.toFunctionsUncheckedFuel?_nil_parts hLowerList
  subst lowerStmts
  have hFnBody : fn.body = { stmts := [] } := by
    simpa using hBody
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨_seqPrevious, _hSeqFuel, hStateAfterSeq⟩ :=
    Yul.Source.Effectful.execSeq_nil_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  subst stateAfterSeq
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
        _hEntryShared, _hEntryVars, _hEntryDomain⟩ :=
    hEntry.2
  have hRestrict :
      sourceEntry.source.restrictStoreTo sourceEntry.source.store =
        sourceEntry.source := by
    rw [hEntrySource]
    simp only [EvmYul.Yul.State.store,
      EvmYul.Yul.State.restrictStoreTo]
    rw [StateRelation.VarStore.restrict_self]
  have hSourceAfterBody : sourceAfterBody = sourceEntry := by
    rw [hSourceAfter]
    change
      sourceEntry.withSource
          (sourceEntry.source.restrictStoreTo sourceEntry.source.store) =
        sourceEntry
    rw [hRestrict]
    exact Simulation.ResourceReplay.State.withSource_self sourceEntry
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.regular targetEntry
  have hTargetRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          1 fn.body targetEntry =
        .ok
          (targetOutcome,
            Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    rw [hFnBody]
    exact
      Functions.Source.Effectful.Block.runOpen_nil
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions
        (Functions.Source.Effectful.FunDef.bodyCtx fn)
        0 targetEntry
  have hFinalRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
        targetOutcome.state := by
    have hRevive :
        sourceEntry.source.reviveJump = sourceEntry.source := by
      rw [hEntrySource]
      rfl
    rw [hSourceAfterBody]
    rw [hRevive]
    simpa [targetEntry, targetOutcome]
      using hEntry
  refine
    ⟨1, ⟨paramStore, targetOutcome,
      Functions.Source.Effectful.FunDef.bodyCtx fn,
      hParamStore, ?_, ?_, hFinalRel⟩⟩
  · simpa [targetEntry] using hTargetRun
  · exact Or.inl rfl

theorem of_leave
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
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
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨hFnBody, _hAfter⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_leave_parts hLower
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
        _hEntryShared, _hEntryVars, _hEntryDomain⟩ :=
    hEntry.2
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨_seqPrevious, stateAfterLeave, _hSeqFuel,
        hLeaveRun, hSeqFinal⟩ :=
    Yul.Source.Effectful.execSeq_cons_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  obtain ⟨_leavePrevious, _hLeaveFuel, hStateAfterLeave⟩ :=
    Yul.Source.Effectful.exec_leave_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hLeaveRun
  let sourceLeave :=
    sourceEntry.withSource
      (EvmYul.Yul.State.setLeave sourceEntry.source)
  have hStateAfterLeave' : stateAfterLeave = sourceLeave := by
    simpa [sourceEntry, sourceLeave] using hStateAfterLeave
  have hSourceLeave :
      sourceLeave.source =
        .Checkpoint (.Leave entryShared entryVars) := by
    change
      EvmYul.Yul.State.setLeave sourceEntry.source =
        .Checkpoint (.Leave entryShared entryVars)
    rw [hEntrySource]
    rfl
  have hStateAfterSeq : stateAfterSeq = sourceLeave := by
    rw [hStateAfterLeave'] at hSeqFinal
    change
      (match sourceLeave.source with
      | .Ok _ _ =>
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              _ [] (some sourceProgram.contract) sourceLeave =
            .ok stateAfterSeq
      | .OutOfFuel | .Checkpoint _ =>
          stateAfterSeq = sourceLeave) at hSeqFinal
    rw [hSourceLeave] at hSeqFinal
    exact hSeqFinal
  have hRestrictedLeave :
      sourceLeave.source.restrictStoreTo sourceEntry.source.store =
        sourceLeave.source := by
    rw [hSourceLeave, hEntrySource]
    simp only [EvmYul.Yul.State.store,
      EvmYul.Yul.State.restrictStoreTo]
    rw [StateRelation.VarStore.restrict_self]
  have hSourceAfterBody : sourceAfterBody = sourceLeave := by
    rw [hSourceAfter, hStateAfterSeq]
    change
      sourceLeave.withSource
          (sourceLeave.source.restrictStoreTo sourceEntry.source.store) =
        sourceLeave
    rw [hRestrictedLeave]
    exact Simulation.ResourceReplay.State.withSource_self sourceLeave
  let targetLeave :=
    targetEntry.withSource (targetEntry.source.restrictTo
      (fn.returns ++ fn.params))
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.leave targetLeave
  have hLeaveScope :
      (Functions.Source.Effectful.FunDef.bodyCtx fn).leaveScope? =
        some (fn.returns ++ fn.params) := by
    rfl
  have hTargetStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          1 .leave targetEntry =
        .ok
          (targetOutcome,
            Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    simpa [targetLeave, targetOutcome] using
      Functions.Source.Effectful.Stmt.run_leave_of_scope
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hLeaveScope
  have hTargetRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          2 fn.body targetEntry =
        .ok
          (targetOutcome,
            Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    rw [hFnBody]
    exact
      Functions.Source.Effectful.Block.runOpen_cons_nonregular
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetStmt (by
          intro hMode
          cases hMode)
  have hRevived :
      sourceAfterBody.withSource sourceAfterBody.source.reviveJump =
        sourceEntry := by
    rw [hSourceAfterBody]
    change
      (sourceEntry.withSource
          (EvmYul.Yul.State.setLeave sourceEntry.source)).withSource
          (EvmYul.Yul.State.setLeave sourceEntry.source).reviveJump =
        sourceEntry
    rw [hEntrySource]
    change
      sourceEntry.withSource (.Ok entryShared entryVars) = sourceEntry
    rw [← hEntrySource]
    exact Simulation.ResourceReplay.State.withSource_self sourceEntry
  have hFinalRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
        targetOutcome.state := by
    rw [hRevived]
    simpa [targetEntry, targetLeave, targetOutcome] using
      StateRelation.Replay.scopedExact_restrict_target hEntry
  refine
    ⟨2, ⟨paramStore, targetOutcome,
      Functions.Source.Effectful.FunDef.bodyCtx fn,
      hParamStore, ?_, ?_, hFinalRel⟩⟩
  · simpa [targetEntry] using hTargetRun
  · exact Or.inr rfl

theorem of_let_none
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
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
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨hFnBody, _hAfter⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_let_none_parts hLower
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
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨_seqPrevious, stateAfterLet, _hSeqFuel,
        hLetRun, hSeqFinal⟩ :=
    Yul.Source.Effectful.execSeq_cons_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  obtain ⟨_letPrevious, _hLetFuel, hCheck, hStateAfterLet⟩ :=
    Yul.Source.Effectful.exec_let_none_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hLetRun
  let sourceDeclared :=
    sourceEntry.withSource (sourceEntry.source.zeroFill names)
  have hStateAfterLet' : stateAfterLet = sourceDeclared := by
    simpa [sourceEntry, sourceDeclared] using hStateAfterLet
  have hCheck' :
      EvmYul.Yul.checkDeclaration sourceEntry.source names = .ok () := by
    simpa [sourceEntry] using hCheck
  have hCheckEntry :
      EvmYul.Yul.checkDeclaration (.Ok entryShared entryVars) names =
        .ok () := by
    rw [← hEntrySource]
    exact hCheck'
  have hDeclarationParts :
      (identNames names).Nodup ∧
        ∀ name, name ∈ identNames names →
          name ∉ fn.returns ++ fn.params := by
    have hParts :=
      StateRelation.Vars.checkDeclaration_ok_parts
        (layout := fn.returns ++ fn.params)
        (source := entryVars) (shared := entryShared)
        hEntryDomain hCheckEntry
    simpa [identNames_eq_self] using hParts
  obtain ⟨targetFuel, finalVars, finalCtx,
      hInsert, hTargetRun, _hFinalCtx⟩ :=
    InitNames.run
      (contract := contract) (program := targetProgram.toFunctions)
      (identNames names) targetEntry
      (Functions.Source.Effectful.FunDef.bodyCtx fn)
  let targetFinal :=
    targetEntry.withSource
      { shared := targetEntry.source.shared, vars := finalVars }
  have hNamesEq : identNames names = names :=
    identNames_eq_self names
  have hSourceDeclaredEq :
      sourceDeclared =
        sourceEntry.withSource
          (sourceEntry.source.zeroFill (identNames names)) := by
    rw [hNamesEq]
  have hDeclaredRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (identNames names ++ (fn.returns ++ fn.params))
        sourceDeclared targetFinal := by
    rw [hSourceDeclaredEq]
    simpa [targetFinal, sourceEntry, targetEntry] using
      StateRelation.Replay.scopedExact_zeroFill_insertMany
        hEntry hDeclarationParts.1 hDeclarationParts.2 hInsert
  obtain
      ⟨declaredShared, declaredVars, hDeclaredSource,
        _hDeclaredShared, _hDeclaredVars, _hDeclaredDomain⟩ :=
    hDeclaredRel.2
  have hStateAfterSeq : stateAfterSeq = sourceDeclared := by
    rw [hStateAfterLet'] at hSeqFinal
    change
      (match sourceDeclared.source with
      | .Ok _ _ =>
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              _ [] (some sourceProgram.contract) sourceDeclared =
            .ok stateAfterSeq
      | .OutOfFuel | .Checkpoint _ =>
          stateAfterSeq = sourceDeclared) at hSeqFinal
    rw [hDeclaredSource] at hSeqFinal
    obtain ⟨_tailPrevious, _hTailFuel, hTailFinal⟩ :=
      Yul.Source.Effectful.execSeq_nil_ok_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hSeqFinal
    exact hTailFinal
  have hSourceAfterBody :
      sourceAfterBody =
        sourceDeclared.withSource
          (.Ok declaredShared
            (EvmYul.Yul.State.restrictVarStore
              declaredVars entryVars)) := by
    rw [hSourceAfter, hStateAfterSeq]
    change
      sourceDeclared.withSource
          (sourceDeclared.source.restrictStoreTo sourceEntry.source.store) =
        _
    rw [hDeclaredSource, hEntrySource]
    rfl
  have hRestrictedRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params) sourceAfterBody targetFinal := by
    rw [hSourceAfterBody]
    exact
      StateRelation.Replay.scopedExact_restrict_source
        hDeclaredSource hDeclaredRel hEntryDomain
        (by
          intro name hMem
          exact List.mem_append_right _ hMem)
  have hRevived :
      sourceAfterBody.withSource sourceAfterBody.source.reviveJump =
        sourceAfterBody := by
    rw [hSourceAfterBody]
    rfl
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.regular targetFinal
  have hBodyRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          targetFuel fn.body targetEntry =
        .ok (targetOutcome, finalCtx) := by
    rw [hFnBody]
    simpa [targetFinal, targetOutcome] using hTargetRun
  refine
    ⟨targetFuel, ⟨paramStore, targetOutcome, finalCtx,
      hParamStore, ?_, ?_, ?_⟩⟩
  · simpa [targetEntry] using hBodyRun
  · exact Or.inl rfl
  · rw [hRevived]
    exact hRestrictedRel

theorem of_let_one
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
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true)
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
    (hTargetDomain :
      StateRelation.Vars.TargetDomainWithin before.used
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore }).source.vars)
    (hTargetScope :
      StateRelation.Vars.NamesWithin before.used
        (Functions.Source.Effectful.FunDef.bodyCtx fn).scope)
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
  obtain ⟨pre, lowerValue, hExprLower, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_let_one_parts
      hNotFunctionCall hLower
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
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨_seqPrevious, stateAfterLet, _hSeqFuel,
        hLetRun, hSeqFinal⟩ :=
    Yul.Source.Effectful.execSeq_cons_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  obtain
      ⟨evalFuel, sourceAfterValue, values, hLetFuel,
        hCheck, hEvalValues, hStateAfterLet⟩ :=
    Yul.Source.Effectful.exec_let_some_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hLetRun
  have hCheckEntry :
      EvmYul.Yul.checkDeclaration
          (.Ok entryShared entryVars) [name] =
        .ok () := by
    rw [← hEntrySource]
    simpa [sourceEntry] using hCheck
  have hNameFresh : identName name ∉ fn.returns ++ fn.params := by
    have hParts :=
      StateRelation.Vars.checkDeclaration_ok_parts
        (layout := fn.returns ++ fn.params)
        (source := entryVars) (shared := entryShared)
        hEntryDomain hCheckEntry
    exact hParts.2 (identName name) (by simp [identName])
  obtain ⟨value, hValues, hScopedValueNonempty⟩ :=
    hValue (by omega) hExprOk hExprLower hEntry
      (by simpa [targetEntry] using hTargetDomain)
      hTargetScope hEvalValues
  obtain ⟨hScopedValue⟩ := hScopedValueNonempty
  let sourceDeclared :=
    sourceAfterValue.withSource
      (sourceAfterValue.source.multifill [name] [value])
  have hStateAfterLet' : stateAfterLet = sourceDeclared := by
    rw [hStateAfterLet, hValues]
    rfl
  obtain ⟨targetFuel, targetFinal, finalCtx,
      hTargetRun, hDeclaredRel, _hTargetFinal, _hFinalCtx⟩ :=
    InitializedValue.run hScopedValue.prepared
      hScopedValue.relation hNameFresh
  obtain
      ⟨declaredShared, declaredVars, hDeclaredSource,
        _hDeclaredShared, _hDeclaredVars, _hDeclaredDomain⟩ :=
    hDeclaredRel.2
  have hStateAfterSeq : stateAfterSeq = sourceDeclared := by
    rw [hStateAfterLet'] at hSeqFinal
    change
      (match sourceDeclared.source with
      | .Ok _ _ =>
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              _ [] (some sourceProgram.contract) sourceDeclared =
            .ok stateAfterSeq
      | .OutOfFuel | .Checkpoint _ =>
          stateAfterSeq = sourceDeclared) at hSeqFinal
    rw [hDeclaredSource] at hSeqFinal
    obtain ⟨_tailPrevious, _hTailFuel, hTailFinal⟩ :=
      Yul.Source.Effectful.execSeq_nil_ok_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hSeqFinal
    exact hTailFinal
  have hSourceAfterBody :
      sourceAfterBody =
        sourceDeclared.withSource
          (.Ok declaredShared
            (EvmYul.Yul.State.restrictVarStore
              declaredVars entryVars)) := by
    rw [hSourceAfter, hStateAfterSeq]
    change
      sourceDeclared.withSource
          (sourceDeclared.source.restrictStoreTo sourceEntry.source.store) =
        _
    rw [hDeclaredSource, hEntrySource]
    rfl
  have hRestrictedRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params) sourceAfterBody targetFinal := by
    rw [hSourceAfterBody]
    exact
      StateRelation.Replay.scopedExact_restrict_source
        hDeclaredSource hDeclaredRel hEntryDomain
        (by
          intro candidate hMem
          exact List.mem_cons_of_mem (identName name) hMem)
  have hRevived :
      sourceAfterBody.withSource sourceAfterBody.source.reviveJump =
        sourceAfterBody := by
    rw [hSourceAfterBody]
    rfl
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.regular targetFinal
  have hBodyRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          targetFuel fn.body targetEntry =
        .ok (targetOutcome, finalCtx) := by
    rw [hFnBody]
    simpa [targetOutcome] using hTargetRun
  refine
    ⟨targetFuel, ⟨paramStore, targetOutcome, finalCtx,
      hParamStore, ?_, ?_, ?_⟩⟩
  · simpa [targetEntry] using hBodyRun
  · exact Or.inl rfl
  · rw [hRevived]
    exact hRestrictedRel

theorem of_assign_one
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
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true)
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
    (hTargetDomain :
      StateRelation.Vars.TargetDomainWithin before.used
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore }).source.vars)
    (hTargetScope :
      StateRelation.Vars.NamesWithin before.used
        (Functions.Source.Effectful.FunDef.bodyCtx fn).scope)
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
  obtain ⟨pre, lowerValue, hExprLower, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_assign_one_parts
      hNotFunctionCall hLower
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
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨_seqPrevious, stateAfterAssign, _hSeqFuel,
        hAssignRun, hSeqFinal⟩ :=
    Yul.Source.Effectful.execSeq_cons_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  obtain
      ⟨evalFuel, sourceAfterValue, values, hAssignFuel,
        hCheck, hEvalValues, hStateAfterAssign⟩ :=
    Yul.Source.Effectful.exec_assign_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hAssignRun
  have hCheckEntry :
      EvmYul.Yul.checkAssignment
          (.Ok entryShared entryVars) [name] =
        .ok () := by
    rw [← hEntrySource]
    simpa [sourceEntry] using hCheck
  have hNameDeclared : identName name ∈ fn.returns ++ fn.params := by
    have hParts :=
      StateRelation.Vars.checkAssignment_ok_parts
        (layout := fn.returns ++ fn.params)
        (source := entryVars) (shared := entryShared)
        hEntryDomain hCheckEntry
    exact hParts.2 (identName name) (by simp [identName])
  obtain ⟨value, hValues, hScopedValueNonempty⟩ :=
    hValue (by omega) hExprOk hExprLower hEntry
      (by simpa [targetEntry] using hTargetDomain)
      hTargetScope hEvalValues
  obtain ⟨hScopedValue⟩ := hScopedValueNonempty
  let sourceAssigned :=
    sourceAfterValue.withSource
      (sourceAfterValue.source.multifill [name] [value])
  have hStateAfterAssign' : stateAfterAssign = sourceAssigned := by
    rw [hStateAfterAssign, hValues]
    rfl
  obtain ⟨targetFuel, targetFinal,
      hTargetRun, hAssignedRel, _hTargetFinal⟩ :=
    AssignedValue.run hScopedValue.prepared
      hScopedValue.relation hNameDeclared
  obtain
      ⟨assignedShared, assignedVars, hAssignedSource,
        _hAssignedShared, _hAssignedVars, _hAssignedDomain⟩ :=
    hAssignedRel.2
  have hStateAfterSeq : stateAfterSeq = sourceAssigned := by
    rw [hStateAfterAssign'] at hSeqFinal
    change
      (match sourceAssigned.source with
      | .Ok _ _ =>
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              _ [] (some sourceProgram.contract) sourceAssigned =
            .ok stateAfterSeq
      | .OutOfFuel | .Checkpoint _ =>
          stateAfterSeq = sourceAssigned) at hSeqFinal
    rw [hAssignedSource] at hSeqFinal
    obtain ⟨_tailPrevious, _hTailFuel, hTailFinal⟩ :=
      Yul.Source.Effectful.execSeq_nil_ok_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hSeqFinal
    exact hTailFinal
  have hSourceAfterBody :
      sourceAfterBody =
        sourceAssigned.withSource
          (.Ok assignedShared
            (EvmYul.Yul.State.restrictVarStore
              assignedVars entryVars)) := by
    rw [hSourceAfter, hStateAfterSeq]
    change
      sourceAssigned.withSource
          (sourceAssigned.source.restrictStoreTo sourceEntry.source.store) =
        _
    rw [hAssignedSource, hEntrySource]
    rfl
  have hRestrictedRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params) sourceAfterBody targetFinal := by
    rw [hSourceAfterBody]
    exact
      StateRelation.Replay.scopedExact_restrict_source
        hAssignedSource hAssignedRel hEntryDomain
        (by
          intro candidate hMem
          exact hMem)
  have hRevived :
      sourceAfterBody.withSource sourceAfterBody.source.reviveJump =
        sourceAfterBody := by
    rw [hSourceAfterBody]
    rfl
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.regular targetFinal
  have hBodyRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          targetFuel fn.body targetEntry =
        .ok (targetOutcome, hScopedValue.prepared.finalCtx) := by
    rw [hFnBody]
    simpa [targetOutcome] using hTargetRun
  refine
    ⟨targetFuel,
      ⟨paramStore, targetOutcome, hScopedValue.prepared.finalCtx,
        hParamStore, ?_, ?_, ?_⟩⟩
  · simpa [targetEntry] using hBodyRun
  · exact Or.inl rfl
  · rw [hRevived]
    exact hRestrictedRel

theorem of_let_call
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
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering before callArgs
        preArgs lowerArgs after)
    (hFnBody :
      fn.body =
        { stmts :=
            Stmt.initNames (identNames names) ++ preArgs ++
              [Functions.Stmt.call
                (identNames names) functionName lowerArgs] })
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
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
    (hTargetDomain :
      StateRelation.Vars.TargetDomainWithin before.used
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore }).source.vars)
    (hTargetScope :
      StateRelation.Vars.NamesWithin before.used
        (Functions.Source.Effectful.FunDef.bodyCtx fn).scope)
    (hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names
          [.Let names (some (.Call (.inr functionName) callArgs))]))
    (hExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
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
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨_seqPrevious, stateAfterLet, _hSeqFuel,
        hLetRun, hSeqFinal⟩ :=
    Yul.Source.Effectful.execSeq_cons_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  obtain
      ⟨evalFuel, sourceAfterCall, values, hLetFuel,
        hCheck, hEvalValues, hStateAfterLet⟩ :=
    Yul.Source.Effectful.exec_let_some_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hLetRun
  have hCheckEntry :
      EvmYul.Yul.checkDeclaration
          (.Ok entryShared entryVars) names =
        .ok () := by
    rw [← hEntrySource]
    simpa [sourceEntry] using hCheck
  obtain ⟨hTargetsNodup, hTargetsFresh⟩ :=
    StateRelation.Vars.checkDeclaration_ok_parts
      (layout := fn.returns ++ fn.params)
      (source := entryVars) (shared := entryShared)
      hEntryDomain hCheckEntry
  have hNamesUsed :
      StateRelation.Vars.NamesWithin before.used
        (identNames names) := by
    intro name hMem
    apply hBodyNames name
    simp [Stmt.List.names, Stmt.names, hMem]
  obtain ⟨initFuel, initVars, initCtx,
      hInsert, hInitRun, hInitCtx⟩ :=
    InitNames.run
      (contract := contract) (program := targetProgram.toFunctions)
      (identNames names) targetEntry
      (Functions.Source.Effectful.FunDef.bodyCtx fn)
  let targetDeclared :=
    targetEntry.withSource
      { shared := targetEntry.source.shared, vars := initVars }
  have hDeclaredRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params) sourceEntry targetDeclared := by
    simpa [sourceEntry, targetEntry, targetDeclared] using
      StateRelation.Replay.scopedExact_insertMany_hidden
        hEntry
        (by simpa [identNames_eq_self] using hTargetsFresh)
        hInsert
  have hDeclaredDomain :
      StateRelation.Vars.TargetDomainWithin before.used
        targetDeclared.source.vars := by
    simpa [targetEntry, targetDeclared] using
      hTargetDomain.insertMany hNamesUsed hInsert
  have hDeclaredScope :
      StateRelation.Vars.NamesWithin before.used initCtx.scope := by
    rw [hInitCtx]
    intro name hMem
    rcases List.mem_append.mp hMem with hDeclared | hOuter
    · exact hNamesUsed name (by simpa using hDeclared)
    · exact hTargetScope name hOuter
  have hTargetsContain :
      ∀ name, name ∈ identNames names →
        targetDeclared.source.vars.contains name = true := by
    intro name hMem
    simpa [targetDeclared] using
      Functions.Source.Store.insertMany_contains_of_mem
        (by simpa [identNames_eq_self] using hTargetsNodup)
        hInsert hMem
  let sourceDeclared :=
    sourceAfterCall.withSource
      (sourceAfterCall.source.multifill names values)
  have hStateAfterLet' : stateAfterLet = sourceDeclared := by
    simpa [sourceDeclared] using hStateAfterLet
  obtain ⟨returnedCall⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofFunctionCallFresh
      (sourceFinal := sourceDeclared)
      hDecomposition hArgsLowering hProgramOk
      (by simpa [identNames_eq_self] using hExprOk)
      (by simpa [identNames_eq_self] using hTargetsNodup)
      (by simpa [identNames_eq_self] using hTargetsFresh)
      hTargetsContain
      (fun hFuel hOk hLower hRel hDomain hScope hExprRun =>
        hExpr (by omega) hOk hLower hRel hDomain hScope hExprRun)
      (fun hFuel hLower hCallParams hCallReturns hCallParamStore
          hReserved hCallBodyNames hBodyOk hCallEntry hBodyRun =>
        hBody (by omega) hLower hCallParams hCallReturns
          hCallParamStore hReserved hCallBodyNames hBodyOk
          hCallEntry hBodyRun)
      hDeclaredRel hDeclaredDomain hDeclaredScope hEvalValues
      (by simp [sourceDeclared, identNames_eq_self])
  obtain
      ⟨declaredShared, declaredVars, hDeclaredSource,
        _hDeclaredShared, _hDeclaredVars, _hDeclaredSourceDomain⟩ :=
    returnedCall.relation.2
  have hStateAfterSeq : stateAfterSeq = sourceDeclared := by
    rw [hStateAfterLet'] at hSeqFinal
    change
      (match sourceDeclared.source with
      | .Ok _ _ =>
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              _ [] (some sourceProgram.contract) sourceDeclared =
            .ok stateAfterSeq
      | .OutOfFuel | .Checkpoint _ =>
          stateAfterSeq = sourceDeclared) at hSeqFinal
    rw [hDeclaredSource] at hSeqFinal
    obtain ⟨_tailPrevious, _hTailFuel, hTailFinal⟩ :=
      Yul.Source.Effectful.execSeq_nil_ok_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hSeqFinal
    exact hTailFinal
  have hSourceAfterBody :
      sourceAfterBody =
        sourceDeclared.withSource
          (.Ok declaredShared
            (EvmYul.Yul.State.restrictVarStore
              declaredVars entryVars)) := by
    rw [hSourceAfter, hStateAfterSeq]
    change
      sourceDeclared.withSource
          (sourceDeclared.source.restrictStoreTo sourceEntry.source.store) =
        _
    rw [hDeclaredSource, hEntrySource]
    rfl
  have hRestrictedRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params) sourceAfterBody
        returnedCall.finalTarget := by
    rw [hSourceAfterBody]
    exact
      StateRelation.Replay.scopedExact_restrict_source
        hDeclaredSource returnedCall.relation hEntryDomain
        (by
          intro candidate hMem
          exact List.mem_append_right _ hMem)
  have hRevived :
      sourceAfterBody.withSource sourceAfterBody.source.reviveJump =
        sourceAfterBody := by
    rw [hSourceAfterBody]
    rfl
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.regular returnedCall.finalTarget
  obtain ⟨callFuel, hCallRun⟩ := returnedCall.run
  obtain ⟨targetFuel, hTargetRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions
      (Stmt.initNames (identNames names))
      (preArgs ++
        [Functions.Stmt.call
          (identNames names) functionName lowerArgs])
      (Functions.Source.Effectful.FunDef.bodyCtx fn)
      initCtx targetEntry targetDeclared
      targetOutcome returnedCall.finalCtx
      ⟨initFuel, by simpa [targetDeclared] using hInitRun⟩
      ⟨callFuel, hCallRun⟩
  have hBodyRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          targetFuel fn.body targetEntry =
        .ok (targetOutcome, returnedCall.finalCtx) := by
    rw [hFnBody]
    simpa [targetOutcome, targetDeclared] using hTargetRun
  refine
    ⟨targetFuel,
      ⟨paramStore, targetOutcome, returnedCall.finalCtx,
        hParamStore, ?_, ?_, ?_⟩⟩
  · simpa [targetEntry] using hBodyRun
  · exact Or.inl rfl
  · rw [hRevived]
    exact hRestrictedRel

theorem of_assign_call
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
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering before callArgs
        preArgs lowerArgs after)
    (hFnBody :
      fn.body =
        { stmts :=
            preArgs ++
              [Functions.Stmt.call
                (identNames names) functionName lowerArgs] })
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
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
    (hTargetDomain :
      StateRelation.Vars.TargetDomainWithin before.used
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore }).source.vars)
    (hTargetScope :
      StateRelation.Vars.NamesWithin before.used
        (Functions.Source.Effectful.FunDef.bodyCtx fn).scope)
    (hExpr :
      FunctionsObserverCall.RecursiveScopedExpressionForward
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
  obtain
      ⟨_sourcePrevious, stateAfterSeq, _hSourceFuel,
        hSeqRun, hSourceAfter⟩ :=
    Yul.Source.Effectful.exec_block_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain
      ⟨_seqPrevious, stateAfterAssign, _hSeqFuel,
        hAssignRun, hSeqFinal⟩ :=
    Yul.Source.Effectful.execSeq_cons_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSeqRun
  obtain
      ⟨evalFuel, sourceAfterCall, values, hAssignFuel,
        hCheck, hEvalValues, hStateAfterAssign⟩ :=
    Yul.Source.Effectful.exec_assign_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hAssignRun
  have hCheckEntry :
      EvmYul.Yul.checkAssignment
          (.Ok entryShared entryVars) names =
        .ok () := by
    rw [← hEntrySource]
    simpa [sourceEntry] using hCheck
  obtain ⟨hTargetsNodup, hTargetsVisible⟩ :=
    StateRelation.Vars.checkAssignment_ok_parts
      (layout := fn.returns ++ fn.params)
      (source := entryVars) (shared := entryShared)
      hEntryDomain hCheckEntry
  let sourceAssigned :=
    sourceAfterCall.withSource
      (sourceAfterCall.source.multifill names values)
  have hStateAfterAssign' : stateAfterAssign = sourceAssigned := by
    simpa [sourceAssigned] using hStateAfterAssign
  obtain ⟨returnedCall⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofFunctionCall
      hDecomposition hArgsLowering hProgramOk
      hExprOk hTargetsNodup hTargetsVisible
      (fun hFuel hOk hLower hRel hDomain hScope hExprRun =>
        hExpr (by omega) hOk hLower hRel hDomain hScope hExprRun)
      (fun hFuel hLower hCallParams hCallReturns hCallParamStore
          hReserved hBodyNames hBodyOk hCallEntry hBodyRun =>
        hBody (by omega) hLower hCallParams hCallReturns
          hCallParamStore hReserved hBodyNames hBodyOk hCallEntry hBodyRun)
      hEntry
      (by simpa [targetEntry] using hTargetDomain)
      hTargetScope hEvalValues rfl
  obtain
      ⟨assignedShared, assignedVars, hAssignedSource,
        _hAssignedShared, _hAssignedVars, _hAssignedDomain⟩ :=
    returnedCall.relation.2
  have hStateAfterSeq : stateAfterSeq = sourceAssigned := by
    rw [hStateAfterAssign'] at hSeqFinal
    change
      (match sourceAssigned.source with
      | .Ok _ _ =>
          Yul.Source.Effectful.execSeq
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              _ [] (some sourceProgram.contract) sourceAssigned =
            .ok stateAfterSeq
      | .OutOfFuel | .Checkpoint _ =>
          stateAfterSeq = sourceAssigned) at hSeqFinal
    rw [hAssignedSource] at hSeqFinal
    obtain ⟨_tailPrevious, _hTailFuel, hTailFinal⟩ :=
      Yul.Source.Effectful.execSeq_nil_ok_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hSeqFinal
    exact hTailFinal
  have hSourceAfterBody :
      sourceAfterBody =
        sourceAssigned.withSource
          (.Ok assignedShared
            (EvmYul.Yul.State.restrictVarStore
              assignedVars entryVars)) := by
    rw [hSourceAfter, hStateAfterSeq]
    change
      sourceAssigned.withSource
          (sourceAssigned.source.restrictStoreTo sourceEntry.source.store) =
        _
    rw [hAssignedSource, hEntrySource]
    rfl
  have hRestrictedRel :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params) sourceAfterBody
        returnedCall.finalTarget := by
    rw [hSourceAfterBody]
    exact
      StateRelation.Replay.scopedExact_restrict_source
        hAssignedSource returnedCall.relation hEntryDomain
        (by
          intro candidate hMem
          exact hMem)
  have hRevived :
      sourceAfterBody.withSource sourceAfterBody.source.reviveJump =
        sourceAfterBody := by
    rw [hSourceAfterBody]
    rfl
  let targetOutcome :=
    Functions.Source.Effectful.Outcome.regular returnedCall.finalTarget
  obtain ⟨targetFuel, hTargetRun⟩ := returnedCall.run
  have hBodyRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          targetFuel fn.body targetEntry =
        .ok (targetOutcome, returnedCall.finalCtx) := by
    rw [hFnBody]
    simpa [targetOutcome, identNames_eq_self] using hTargetRun
  refine
    ⟨targetFuel,
      ⟨paramStore, targetOutcome, returnedCall.finalCtx,
        hParamStore, ?_, ?_, ?_⟩⟩
  · simpa [targetEntry] using hBodyRun
  · exact Or.inl rfl
  · rw [hRevived]
    exact hRestrictedRel

end ReturnedBody

end FunctionsObserverStatement
end Yul
end EvmCompiler
