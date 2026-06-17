import EvmCompiler.Yul.FunctionsObserverStaticCost

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverExpressionFuel

/-!
Source-owned target-fuel bounds for Yul expression preparation.

This module strengthens the ordinary adjacent Yul-to-Functions expression
constructors. It does not define a compiler or an interpreter.
-/

abbrev Trace := Assembly.ResourceTrace

namespace PreparedArgs

theorem empty_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope) :
    FunctionsObserverFuel.PreparedArgs.Bounded 0 sourceFuel
      (FunctionsObserverExpression.PreparedArgs.empty
        (contract := contract) (program := program)
        hRel hDomain hScope) := by
  have hRequired :=
    FunctionsObserverExpression.Prepared.requiredFuel_empty_le
      (contract := contract) (program := program)
      hRel hDomain hScope
  have hBudget :=
    FunctionsObserverFuel.executionBudget_ge_sixteen 0 sourceFuel
  exact hRequired.trans (by omega)

theorem direct_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {stateRest stateHead : Fresh.State}
    {expr : AstExpr}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)}
    {lowerHead : Locals.Expr 1}
    {sourceRest sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {restValues : List Assembly.Word}
    {value : Assembly.Word}
    {headStatic restStatic sourceFuel : Nat}
    (rest :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program preRest lowerRest stateRest
        sourceRest target ctx restValues)
    (hRest :
      FunctionsObserverFuel.PreparedArgs.Bounded
        restStatic sourceFuel rest)
    (hLower :
      Expr.lower1Unchecked? stateRest expr =
        some (preHead, lowerHead, stateHead))
    (hSafe : Expr.deferredBoundArgSafe? expr = true)
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerHead rest.prepared.finalTarget =
        .ok (rest.prepared.finalTarget, [value]))
    (hRel :
      StateRelation.Replay.Rel codeRel sourceFinal
        rest.prepared.finalTarget) :
    FunctionsObserverFuel.PreparedArgs.Bounded
      (headStatic + restStatic + 1)
      sourceFuel
      (FunctionsObserverExpression.PreparedArgs.direct
        rest hLower hSafe hEval hRel) := by
  obtain ⟨rfl, rfl, _hDirectLower⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hLower
  let result :=
    FunctionsObserverExpression.PreparedArgs.direct
      rest hLower hSafe hEval hRel
  have hRequired :
      result.prepared.requiredFuel ≤ rest.prepared.requiredFuel := by
    exact
      FunctionsObserverExpression.Prepared.requiredFuel_le_of_code_eq
        result.prepared rest.prepared (by simp)
  have hStatic :
      restStatic ≤
        headStatic + restStatic + 1 := by
    omega
  exact
    hRequired.trans
      (hRest.trans
        (FunctionsObserverFuel.executionBudget_static_mono
          hStatic sourceFuel))

theorem bound_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {stateRest stateHead stateFresh : Fresh.State}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)}
    {lowerHead : Locals.Expr 1}
    {tmp : Name}
    {sourceRest sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {restValues : List Assembly.Word}
    {value : Assembly.Word}
    {restStatic headStatic headFuel sourceFuel : Nat}
    (rest :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program preRest lowerRest stateRest
        sourceRest target ctx restValues)
    (hRest :
      FunctionsObserverFuel.PreparedArgs.Bounded
        restStatic sourceFuel rest)
    (head :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program preHead lowerHead stateHead
        sourceFinal rest.prepared.finalTarget rest.prepared.finalCtx value)
    (hHead :
      FunctionsObserverFuel.PreparedValue.Bounded
        headStatic headFuel head)
    (hHeadFuel : headFuel < sourceFuel)
    (hFresh : Fresh.fresh? stateHead = some (tmp, stateFresh)) :
    FunctionsObserverFuel.PreparedArgs.Bounded
      (headStatic + restStatic + 1) sourceFuel
      (FunctionsObserverExpression.PreparedArgs.bound
        rest head hFresh) := by
  let result :=
    FunctionsObserverExpression.PreparedArgs.bound rest head hFresh
  have hAppend :=
    FunctionsObserverExpression.Prepared.requiredFuel_append_le
      rest.prepared
      (FunctionsObserverExpression.PreparedValue.bind head hFresh).prepared
  have hBind :=
    FunctionsObserverExpression.PreparedValue.requiredFuel_bind_le
      head hFresh
  have hBudget :=
    FunctionsObserverFuel.executionBudget_static_children_add_eight_le_of_lt
      restStatic headStatic hHeadFuel
  dsimp [FunctionsObserverFuel.PreparedArgs.Bounded] at hRest ⊢
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded] at hHead
  change
    result.prepared.requiredFuel ≤
      FunctionsObserverFuel.executionBudget
        (headStatic + restStatic + 1) sourceFuel
  have hResult :
      result.prepared.requiredFuel ≤
        rest.prepared.requiredFuel + head.requiredFuel + 3 := by
    have hSameCode :=
      FunctionsObserverExpression.Prepared.requiredFuel_le_of_code_eq
        result.prepared
        (FunctionsObserverExpression.Prepared.append
          rest.prepared
          (FunctionsObserverExpression.PreparedValue.bind
            head hFresh).prepared)
        (by simp [List.append_assoc])
    have hComposed :=
      hAppend.trans (Nat.add_le_add_left hBind _)
    exact hSameCode.trans hComposed
  have hBudget' :
      FunctionsObserverFuel.executionBudget restStatic sourceFuel +
          FunctionsObserverFuel.executionBudget headStatic headFuel + 8 ≤
        FunctionsObserverFuel.executionBudget
          (headStatic + restStatic + 1) sourceFuel := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hBudget
  omega

theorem empty_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (globalCost sourceFuel : Nat)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope) :
    FunctionsObserverFuel.PreparedArgs.ProgramBounded globalCost 0 sourceFuel
      (FunctionsObserverExpression.PreparedArgs.empty
        (contract := contract) (program := program)
        hRel hDomain hScope) := by
  exact
    FunctionsObserverFuel.PreparedArgs.programBounded_of_bounded
      (empty_bounded sourceFuel hRel hDomain hScope)

theorem direct_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {stateRest stateHead : Fresh.State}
    {expr : AstExpr}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)}
    {lowerHead : Locals.Expr 1}
    {sourceRest sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {restValues : List Assembly.Word}
    {value : Assembly.Word}
    {globalCost headLocal restLocal sourceFuel : Nat}
    (rest :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program preRest lowerRest stateRest
        sourceRest target ctx restValues)
    (hRest :
      FunctionsObserverFuel.PreparedArgs.ProgramBounded
        globalCost restLocal sourceFuel rest)
    (hLower :
      Expr.lower1Unchecked? stateRest expr =
        some (preHead, lowerHead, stateHead))
    (hSafe : Expr.deferredBoundArgSafe? expr = true)
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerHead rest.prepared.finalTarget =
        .ok (rest.prepared.finalTarget, [value]))
    (hRel :
      StateRelation.Replay.Rel codeRel sourceFinal
        rest.prepared.finalTarget) :
    FunctionsObserverFuel.PreparedArgs.ProgramBounded
      globalCost (headLocal + restLocal + 1) sourceFuel
      (FunctionsObserverExpression.PreparedArgs.direct
        rest hLower hSafe hEval hRel) := by
  obtain ⟨rfl, rfl, _hDirectLower⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hLower
  let result :=
    FunctionsObserverExpression.PreparedArgs.direct
      rest hLower hSafe hEval hRel
  have hRequired :
      result.prepared.requiredFuel ≤ rest.prepared.requiredFuel := by
    exact
      FunctionsObserverExpression.Prepared.requiredFuel_le_of_code_eq
        result.prepared rest.prepared (by simp)
  have hLocal :
      restLocal ≤ headLocal + restLocal + 1 := by
    omega
  exact
    hRequired.trans
      (hRest.trans
        (FunctionsObserverFuel.executionBudgetFor_local_mono
          globalCost sourceFuel hLocal))

theorem bound_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {stateRest stateHead stateFresh : Fresh.State}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)}
    {lowerHead : Locals.Expr 1}
    {tmp : Name}
    {sourceRest sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {restValues : List Assembly.Word}
    {value : Assembly.Word}
    {globalCost restLocal headLocal headFuel sourceFuel : Nat}
    (rest :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program preRest lowerRest stateRest
        sourceRest target ctx restValues)
    (hRest :
      FunctionsObserverFuel.PreparedArgs.ProgramBounded
        globalCost restLocal sourceFuel rest)
    (head :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program preHead lowerHead stateHead
        sourceFinal rest.prepared.finalTarget rest.prepared.finalCtx value)
    (hHead :
      FunctionsObserverFuel.PreparedValue.ProgramBounded
        globalCost headLocal headFuel head)
    (hHeadCost : headLocal ≤ globalCost)
    (hHeadFuel : headFuel < sourceFuel)
    (hFresh : Fresh.fresh? stateHead = some (tmp, stateFresh)) :
    FunctionsObserverFuel.PreparedArgs.ProgramBounded
      globalCost (headLocal + restLocal + 1) sourceFuel
      (FunctionsObserverExpression.PreparedArgs.bound
        rest head hFresh) := by
  let result :=
    FunctionsObserverExpression.PreparedArgs.bound rest head hFresh
  have hAppend :=
    FunctionsObserverExpression.Prepared.requiredFuel_append_le
      rest.prepared
      (FunctionsObserverExpression.PreparedValue.bind head hFresh).prepared
  have hBind :=
    FunctionsObserverExpression.PreparedValue.requiredFuel_bind_le
      head hFresh
  dsimp [FunctionsObserverFuel.PreparedArgs.ProgramBounded] at hRest ⊢
  dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded] at hHead
  change
    result.prepared.requiredFuel ≤
      FunctionsObserverFuel.executionBudgetFor
        globalCost (headLocal + restLocal + 1) sourceFuel
  have hResult :
      result.prepared.requiredFuel ≤
        rest.prepared.requiredFuel + head.requiredFuel + 3 := by
    have hSameCode :=
      FunctionsObserverExpression.Prepared.requiredFuel_le_of_code_eq
        result.prepared
        (FunctionsObserverExpression.Prepared.append
          rest.prepared
          (FunctionsObserverExpression.PreparedValue.bind
            head hFresh).prepared)
        (by simp [List.append_assoc])
    have hComposed :=
      hAppend.trans (Nat.add_le_add_left hBind _)
    exact hSameCode.trans hComposed
  have hAbsorb :=
    FunctionsObserverFuel.executionBudgetFor_child_add_eight_le
      globalCost restLocal headLocal hHeadCost hHeadFuel
  have hLocal :
      restLocal + 1 ≤ headLocal + restLocal + 1 := by
    omega
  have hBudget :=
    hAbsorb.trans
      (FunctionsObserverFuel.executionBudgetFor_local_mono
        globalCost sourceFuel hLocal)
  omega

end PreparedArgs

namespace ScopedPreparedArgs

theorem ofUncheckedLowering_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {initial final : Fresh.State}
    {layout : List Name}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {reversedValues : List Assembly.Word}
    {Eligible : AstExpr → Prop}
    (cost : AstExpr → Nat)
    (hLowering :
      Expr.List.UncheckedBoundLowering
        initial args pre lowerArgs final)
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr}
        {exprPre : List Functions.Stmt}
        {lower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx}
        {value : Assembly.Word},
        exprFuel < fuel →
          Eligible expr →
          Expr.lower1Unchecked? before expr =
            some (exprPre, lower, after) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              before.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin before.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program
                  exprPre lower after layout exprSource'
                  exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.Bounded
                (cost expr)
                exprFuel result.prepared })
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin initial.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel args.reverse codeOverride source =
        .ok (source', reversedValues)) :
    Nonempty
      { result :
          FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel program pre lowerArgs final
            layout source' target ctx reversedValues.reverse //
        FunctionsObserverFuel.PreparedArgs.Bounded
          (FunctionsObserverStaticCost.exprListBy cost args)
          fuel result.prepared } := by
  induction hLowering generalizing fuel source source' target ctx reversedValues with
  | nil =>
      cases fuel with
      | zero =>
          simp [Yul.Source.Effectful.evalArgs,
            Yul.Source.Effectful.fail] at hRun
      | succ previous =>
          simp [Yul.Source.Effectful.evalArgs] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          let prepared :=
            FunctionsObserverExpression.PreparedArgs.empty
              (contract := contract) (program := program)
              (StateRelation.Replay.rel_of_scopedExact hRel)
              hDomain hScope
          let result :
              FunctionsObserverExpression.ScopedPreparedArgs
                contract transcript codeRel program [] [] initial
                layout source target ctx [] :=
            { prepared := prepared
              relation := hRel }
          refine ⟨⟨result, ?_⟩⟩
          simpa [FunctionsObserverStaticCost.exprListBy, result, prepared] using
            PreparedArgs.empty_bounded
              (contract := contract) (program := program)
              (Nat.succ previous)
              (StateRelation.Replay.rel_of_scopedExact hRel)
              hDomain hScope
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      rw [List.reverse_cons] at hRun
      obtain
          ⟨middle, restReversed, headValues, headFuel,
            hFuel, hRestRun, hHeadRun, hValues⟩ :=
        Yul.Source.Effectful.evalArgs_append_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      obtain ⟨exprFuel, value, hExprFuel, hHeadEval, hHeadValues⟩ :=
        Yul.Source.Effectful.evalArgs_singleton_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hHeadRun
      obtain ⟨restBounded⟩ :=
        ih
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hExpr hRel hDomain hScope hRestRun
      let restPrepared := restBounded.1
      have hSourceEq : source' = middle :=
        FunctionsObserverExpression.deferredSourceEval_state_eq
          hDirect.1 hHeadEval
      subst source'
      have hHeadEvalValues :=
        FunctionsObserverExpression.deferredSourceEvalValues_of_eval
          hDirect.1 hHeadEval
      obtain ⟨_hPre, _hState, hDirectLower⟩ :=
        Expr.lower1Unchecked?_deferred_parts hDirect.1 hHead
      obtain
          ⟨targetAfter, hTargetEval, hFinalRel,
            _hLength, _hFinalDomain⟩ :=
        FunctionsObserverExpression.toLocals_forward_targetDomain
          hDirectLower
          (StateRelation.Replay.rel_of_scopedExact
            restPrepared.relation)
          restPrepared.prepared.prepared.domain hHeadEvalValues
      have hTargetEq :
          targetAfter = restPrepared.prepared.prepared.finalTarget :=
        FunctionsObserverExpression.deferredEval_state_eq
          hDirect.1 hHead hTargetEval
      subst targetAfter
      let prepared :=
        FunctionsObserverExpression.PreparedArgs.direct
          restPrepared.prepared hHead hDirect.1 hTargetEval hFinalRel
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      let result :
          FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel program
            (preRest ++ preHead) (lowerHead :: lowerRest)
            stateHead layout middle target ctx
            (value :: restReversed.reverse) :=
        { prepared := prepared
          relation :=
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.prepared.rel
              (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                restPrepared.relation) }
      refine ⟨⟨result, ?_⟩⟩
      simpa [FunctionsObserverStaticCost.exprListBy, result, prepared,
        restPrepared] using
        PreparedArgs.direct_bounded
          (headStatic := cost expr)
          restPrepared.prepared restBounded.2
          hHead hDirect.1 hTargetEval hFinalRel
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      rw [List.reverse_cons] at hRun
      obtain
          ⟨middle, restReversed, headValues, headFuel,
            hFuel, hRestRun, hHeadRun, hValues⟩ :=
        Yul.Source.Effectful.evalArgs_append_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      obtain ⟨exprFuel, value, hExprFuel, hHeadEval, hHeadValues⟩ :=
        Yul.Source.Effectful.evalArgs_singleton_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hHeadRun
      obtain ⟨restBounded⟩ :=
        ih
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hExpr hRel hDomain hScope hRestRun
      let restPrepared := restBounded.1
      obtain ⟨headBounded⟩ :=
        hExpr (by omega) (hEligible expr (by simp)) hHead
          restPrepared.relation
          restPrepared.prepared.prepared.domain
          restPrepared.prepared.prepared.scope hHeadEval
      let headPrepared := headBounded.1
      let prepared :=
        FunctionsObserverExpression.PreparedArgs.bound
          restPrepared.prepared headPrepared.prepared hFresh
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      let result :
          FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel program
            (preRest ++ preHead ++
              [.let_ tmp lowerHead])
            (.var tmp :: lowerRest) stateFresh layout source'
            target ctx (value :: restReversed.reverse) :=
        { prepared := prepared
          relation :=
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.prepared.rel
              (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                headPrepared.relation) }
      refine ⟨⟨result, ?_⟩⟩
      simpa [FunctionsObserverStaticCost.exprListBy, result, prepared,
        restPrepared, headPrepared] using
        PreparedArgs.bound_bounded
          restPrepared.prepared restBounded.2
          headPrepared.prepared headBounded.2
          (by omega) hFresh

theorem ofUncheckedLowering_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {initial final : Fresh.State}
    {layout : List Name}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel globalCost : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {reversedValues : List Assembly.Word}
    {Eligible : AstExpr → Prop}
    (cost : AstExpr → Nat)
    (hLowering :
      Expr.List.UncheckedBoundLowering
        initial args pre lowerArgs final)
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hCost : ∀ expr, expr ∈ args → cost expr ≤ globalCost)
    (hExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr}
        {exprPre : List Functions.Stmt}
        {lower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx}
        {value : Assembly.Word},
        exprFuel < fuel →
          cost expr ≤ globalCost →
          Eligible expr →
          Expr.lower1Unchecked? before expr =
            some (exprPre, lower, after) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              before.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin before.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program
                  exprPre lower after layout exprSource'
                  exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.ProgramBounded
                globalCost (cost expr)
                exprFuel result.prepared })
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin initial.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel args.reverse codeOverride source =
        .ok (source', reversedValues)) :
    Nonempty
      { result :
          FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel program pre lowerArgs final
            layout source' target ctx reversedValues.reverse //
        FunctionsObserverFuel.PreparedArgs.ProgramBounded
          globalCost
          (FunctionsObserverStaticCost.exprListBy cost args)
          fuel result.prepared } := by
  induction hLowering generalizing fuel source source' target ctx reversedValues with
  | nil =>
      cases fuel with
      | zero =>
          simp [Yul.Source.Effectful.evalArgs,
            Yul.Source.Effectful.fail] at hRun
      | succ previous =>
          simp [Yul.Source.Effectful.evalArgs] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          let prepared :=
            FunctionsObserverExpression.PreparedArgs.empty
              (contract := contract) (program := program)
              (StateRelation.Replay.rel_of_scopedExact hRel)
              hDomain hScope
          let result :
              FunctionsObserverExpression.ScopedPreparedArgs
                contract transcript codeRel program [] [] initial
                layout source target ctx [] :=
            { prepared := prepared
              relation := hRel }
          refine ⟨⟨result, ?_⟩⟩
          simpa [FunctionsObserverStaticCost.exprListBy, result, prepared] using
            PreparedArgs.empty_programBounded
              (contract := contract) (program := program)
              globalCost (Nat.succ previous)
              (StateRelation.Replay.rel_of_scopedExact hRel)
              hDomain hScope
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      rw [List.reverse_cons] at hRun
      obtain
          ⟨middle, restReversed, headValues, headFuel,
            hFuel, hRestRun, hHeadRun, hValues⟩ :=
        Yul.Source.Effectful.evalArgs_append_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      obtain ⟨exprFuel, value, hExprFuel, hHeadEval, hHeadValues⟩ :=
        Yul.Source.Effectful.evalArgs_singleton_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hHeadRun
      obtain ⟨restBounded⟩ :=
        ih
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          (fun candidate hMem =>
            hCost candidate (List.mem_cons_of_mem expr hMem))
          hExpr hRel hDomain hScope hRestRun
      let restPrepared := restBounded.1
      have hSourceEq : source' = middle :=
        FunctionsObserverExpression.deferredSourceEval_state_eq
          hDirect.1 hHeadEval
      subst source'
      have hHeadEvalValues :=
        FunctionsObserverExpression.deferredSourceEvalValues_of_eval
          hDirect.1 hHeadEval
      obtain ⟨_hPre, _hState, hDirectLower⟩ :=
        Expr.lower1Unchecked?_deferred_parts hDirect.1 hHead
      obtain
          ⟨targetAfter, hTargetEval, hFinalRel,
            _hLength, _hFinalDomain⟩ :=
        FunctionsObserverExpression.toLocals_forward_targetDomain
          hDirectLower
          (StateRelation.Replay.rel_of_scopedExact
            restPrepared.relation)
          restPrepared.prepared.prepared.domain hHeadEvalValues
      have hTargetEq :
          targetAfter = restPrepared.prepared.prepared.finalTarget :=
        FunctionsObserverExpression.deferredEval_state_eq
          hDirect.1 hHead hTargetEval
      subst targetAfter
      let prepared :=
        FunctionsObserverExpression.PreparedArgs.direct
          restPrepared.prepared hHead hDirect.1 hTargetEval hFinalRel
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      let result :
          FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel program
            (preRest ++ preHead) (lowerHead :: lowerRest)
            stateHead layout middle target ctx
            (value :: restReversed.reverse) :=
        { prepared := prepared
          relation :=
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.prepared.rel
              (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                restPrepared.relation) }
      refine ⟨⟨result, ?_⟩⟩
      simpa [FunctionsObserverStaticCost.exprListBy, result, prepared,
        restPrepared] using
        PreparedArgs.direct_programBounded
          (headLocal := cost expr)
          restPrepared.prepared restBounded.2
          hHead hDirect.1 hTargetEval hFinalRel
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      rw [List.reverse_cons] at hRun
      obtain
          ⟨middle, restReversed, headValues, headFuel,
            hFuel, hRestRun, hHeadRun, hValues⟩ :=
        Yul.Source.Effectful.evalArgs_append_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      obtain ⟨exprFuel, value, hExprFuel, hHeadEval, hHeadValues⟩ :=
        Yul.Source.Effectful.evalArgs_singleton_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hHeadRun
      obtain ⟨restBounded⟩ :=
        ih
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          (fun candidate hMem =>
            hCost candidate (List.mem_cons_of_mem expr hMem))
          hExpr hRel hDomain hScope hRestRun
      let restPrepared := restBounded.1
      obtain ⟨headBounded⟩ :=
        hExpr (by omega) (hCost expr (by simp))
          (hEligible expr (by simp)) hHead
          restPrepared.relation
          restPrepared.prepared.prepared.domain
          restPrepared.prepared.prepared.scope hHeadEval
      let headPrepared := headBounded.1
      let prepared :=
        FunctionsObserverExpression.PreparedArgs.bound
          restPrepared.prepared headPrepared.prepared hFresh
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      let result :
          FunctionsObserverExpression.ScopedPreparedArgs
            contract transcript codeRel program
            (preRest ++ preHead ++
              [.let_ tmp lowerHead])
            (.var tmp :: lowerRest) stateFresh layout source'
            target ctx (value :: restReversed.reverse) :=
        { prepared := prepared
          relation :=
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.prepared.rel
              (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                headPrepared.relation) }
      refine ⟨⟨result, ?_⟩⟩
      simpa [FunctionsObserverStaticCost.exprListBy, result, prepared,
        restPrepared, headPrepared] using
        PreparedArgs.bound_programBounded
          restPrepared.prepared restBounded.2
          headPrepared.prepared headBounded.2
          (hCost expr (by simp)) (by omega) hFresh

end ScopedPreparedArgs

namespace ScopedPreparedValue

theorem ofLiteral_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {literal : Assembly.Word}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (hLower :
      Expr.lower1Unchecked? before (.Lit literal) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Lit literal) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.Bounded
              (FunctionsObserverStaticCost.expr (.Lit literal))
              fuel result.prepared } := by
  obtain ⟨rfl, rfl, hToLocals⟩ :=
    Expr.lower1Unchecked?_direct_parts
      (offset := 0)
      (by
        simp [Expr.directPureArgSafeAt?,
          Expr.pureAliasArgSafe?, Expr.pendingStackDepth])
      hLower
  obtain ⟨value, hValues, ⟨result⟩⟩ :=
    FunctionsObserverExpression.ScopedPreparedValue.ofLiteral
      hLower hRel hDomain hScope hRun
  refine ⟨value, hValues, ⟨⟨result, ?_⟩⟩⟩
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded]
  exact
    (FunctionsObserverExpression.PreparedValue.requiredFuel_nil_le
      result.prepared).trans
      (by
        have hBudget :=
          FunctionsObserverFuel.executionBudget_ge_sixteen
            (FunctionsObserverStaticCost.expr (.Lit literal)) fuel
        omega)

theorem ofVariable_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {name : Name}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (hLower :
      Expr.lower1Unchecked? before (.Var name) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Var name) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.Bounded
              (FunctionsObserverStaticCost.expr (.Var name))
              fuel result.prepared } := by
  obtain ⟨rfl, rfl, hToLocals⟩ :=
    Expr.lower1Unchecked?_direct_parts
      (offset := 0)
      (by
        simp [Expr.directPureArgSafeAt?,
          Expr.pureAliasArgSafe?, Expr.pendingStackDepth])
      hLower
  obtain ⟨value, hValues, ⟨result⟩⟩ :=
    FunctionsObserverExpression.ScopedPreparedValue.ofVariable
      hLower hRel hDomain hScope hRun
  refine ⟨value, hValues, ⟨⟨result, ?_⟩⟩⟩
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded]
  exact
    (FunctionsObserverExpression.PreparedValue.requiredFuel_nil_le
      result.prepared).trans
      (by
        have hBudget :=
          FunctionsObserverFuel.executionBudget_ge_sixteen
            (FunctionsObserverStaticCost.expr (.Var name)) fuel
        omega)

theorem ofDirectPrimitive_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (hDirect : Expr.List.directPureArgsSafe? args = true)
    (hLower :
      Expr.lower1Unchecked? before (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.Bounded
              (FunctionsObserverStaticCost.expr
                (.Call (.inl prim) args))
              fuel result.prepared } := by
  obtain ⟨rfl, rfl, _hLowering⟩ :=
    Expr.uncheckedDirectPrimitiveLowering_of_lower1Unchecked?
      hDirect hLower
  obtain ⟨value, hValues, ⟨result⟩⟩ :=
    FunctionsObserverExpression.ScopedPreparedValue.ofDirectPrimitive
      hDirect hLower hRel hDomain hScope hRun
  refine ⟨value, hValues, ⟨⟨result, ?_⟩⟩⟩
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded]
  exact
    (FunctionsObserverExpression.PreparedValue.requiredFuel_nil_le
      result.prepared).trans
      (by
        have hBudget :=
          FunctionsObserverFuel.executionBudget_ge_sixteen
            (FunctionsObserverStaticCost.expr
              (.Call (.inl prim) args))
            fuel
        omega)

theorem ofDirectPrimitive_boundedWithStatic
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel staticCost : Nat}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (hDirect : Expr.List.directPureArgsSafe? args = true)
    (hLower :
      Expr.lower1Unchecked? before (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.Bounded
              staticCost fuel result.prepared } := by
  obtain ⟨rfl, rfl, _hLowering⟩ :=
    Expr.uncheckedDirectPrimitiveLowering_of_lower1Unchecked?
      hDirect hLower
  obtain ⟨value, hValues, ⟨result⟩⟩ :=
    FunctionsObserverExpression.ScopedPreparedValue.ofDirectPrimitive
      hDirect hLower hRel hDomain hScope hRun
  refine ⟨value, hValues, ⟨⟨result, ?_⟩⟩⟩
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded]
  exact
    (FunctionsObserverExpression.PreparedValue.requiredFuel_nil_le
      result.prepared).trans
      (by
        have hBudget :=
          FunctionsObserverFuel.executionBudget_ge_sixteen
            staticCost fuel
        omega)

theorem ofBoundPrimitive_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    {Eligible : AstExpr → Prop}
    (hBound : Expr.List.directPureArgsSafe? args = false)
    (hLower :
      Expr.lower1Unchecked? before (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr}
        {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx}
        {value : Assembly.Word},
        exprFuel < fuel →
          Eligible expr →
          Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program
                  exprPre exprLower exprAfter layout exprSource'
                  exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.Bounded
                (FunctionsObserverStaticCost.runtimeExpr
                  sourceProgram expr)
                exprFuel result.prepared })
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.Bounded
              (FunctionsObserverStaticCost.runtimeExpr sourceProgram
                (.Call (.inl prim) args))
              fuel result.prepared } := by
  obtain ⟨value, hValues, ⟨result⟩⟩ :=
    FunctionsObserverExpression.ScopedPreparedValue.ofBoundPrimitive
      hBound hLower hEligible
      (fun hExprFuel hExprEligible hExprLower hExprRel hExprDomain
          hExprScope hExprRun => by
        obtain ⟨bounded⟩ :=
          hExpr hExprFuel hExprEligible hExprLower hExprRel
            hExprDomain hExprScope hExprRun
        exact ⟨bounded.1⟩)
      hRel hDomain hScope hRun
  let hLowering :=
    Expr.uncheckedBoundPrimitiveLowering_of_lower1Unchecked?
      hBound hLower
  cases hLowering with
  | @primitive _ _ _ op _ lowerArgs seq hOp hArgs hSeq hOutputs =>
      obtain
          ⟨callFuel, sourceAfterArgs, reversedValues,
            hFuel, hArgsRun, hPrimRun⟩ :=
        Yul.Source.Effectful.evalValues_primitive_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      cases callFuel with
      | zero =>
          obtain ⟨_hSafe, hPrimCall⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hPrimRun
          simp [ObserverSemantics.SourceReplay.primCall,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ primFuel =>
          obtain ⟨argsBounded⟩ :=
            ScopedPreparedArgs.ofUncheckedLowering_bounded
              (FunctionsObserverStaticCost.runtimeExpr sourceProgram)
              hArgs hEligible
              (fun hExprFuel hExprEligible hExprLower hExprRel
                  hExprDomain hExprScope hExprRun =>
                hExpr (by omega) hExprEligible hExprLower hExprRel
                  hExprDomain hExprScope hExprRun)
              hRel hDomain hScope hArgsRun
          have hRequired :
              result.prepared.requiredFuel ≤
                argsBounded.1.prepared.prepared.requiredFuel :=
            FunctionsObserverExpression.PreparedValue.requiredFuel_le_of_prepared_code_eq
              result.prepared argsBounded.1.prepared.prepared rfl
          have hArgsBound :
              argsBounded.1.prepared.prepared.requiredFuel ≤
                FunctionsObserverFuel.executionBudget
                  (FunctionsObserverStaticCost.runtimeExprList
                    sourceProgram args)
                  primFuel.succ := by
            simpa [FunctionsObserverFuel.PreparedArgs.Bounded,
              FunctionsObserverStaticCost.runtimeExprList_eq_exprListBy] using
              argsBounded.2
          refine ⟨value, hValues, ⟨⟨result, ?_⟩⟩⟩
          dsimp [FunctionsObserverFuel.PreparedValue.Bounded]
          have hDynamic :=
            FunctionsObserverFuel.executionBudget_mono
              (FunctionsObserverStaticCost.runtimeExprList
                sourceProgram args)
              (show primFuel.succ ≤ fuel by omega)
          have hStatic :=
            FunctionsObserverFuel.executionBudget_static_mono
              (show
                FunctionsObserverStaticCost.runtimeExprList
                    sourceProgram args ≤
                  FunctionsObserverStaticCost.runtimeExpr sourceProgram
                    (.Call (.inl prim) args) by
                simp [FunctionsObserverStaticCost.runtimeExpr])
              fuel
          exact
            hRequired.trans
              (hArgsBound.trans (hDynamic.trans hStatic))

theorem ofPrimitive_bounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    {Eligible : AstExpr → Prop}
    (hLower :
      Expr.lower1Unchecked? before (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr}
        {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx}
        {value : Assembly.Word},
        exprFuel < fuel →
          Eligible expr →
          Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program
                  exprPre exprLower exprAfter layout exprSource'
                  exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.Bounded
                (FunctionsObserverStaticCost.runtimeExpr
                  sourceProgram expr)
                exprFuel result.prepared })
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.Bounded
              (FunctionsObserverStaticCost.runtimeExpr sourceProgram
                (.Call (.inl prim) args))
              fuel result.prepared } := by
  cases hDirect : Expr.List.directPureArgsSafe? args with
  | false =>
      exact
        ofBoundPrimitive_bounded hDirect hLower hEligible hExpr
          hRel hDomain hScope hRun
  | true =>
      exact
        ofDirectPrimitive_boundedWithStatic
          (staticCost :=
            FunctionsObserverStaticCost.runtimeExpr sourceProgram
              (.Call (.inl prim) args))
          hDirect hLower
          hRel hDomain hScope hRun

theorem ofLiteral_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel globalCost : Nat}
    {literal : Assembly.Word}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (hLower :
      Expr.lower1Unchecked? before (.Lit literal) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Lit literal) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.ProgramBounded
              globalCost
              (FunctionsObserverStaticCost.expr (.Lit literal))
              fuel result.prepared } := by
  obtain ⟨value, hValues, ⟨bounded⟩⟩ :=
    ofLiteral_bounded hLower hRel hDomain hScope hRun
  exact
    ⟨value, hValues,
      ⟨⟨bounded.1,
        FunctionsObserverFuel.PreparedValue.programBounded_of_bounded
          bounded.2⟩⟩⟩

theorem ofVariable_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel globalCost : Nat}
    {name : EvmYul.Identifier}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (hLower :
      Expr.lower1Unchecked? before (.Var name) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Var name) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.ProgramBounded
              globalCost
              (FunctionsObserverStaticCost.expr (.Var name))
              fuel result.prepared } := by
  obtain ⟨value, hValues, ⟨bounded⟩⟩ :=
    ofVariable_bounded hLower hRel hDomain hScope hRun
  exact
    ⟨value, hValues,
      ⟨⟨bounded.1,
        FunctionsObserverFuel.PreparedValue.programBounded_of_bounded
          bounded.2⟩⟩⟩

theorem ofDirectPrimitive_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel globalCost localCost : Nat}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (hDirect : Expr.List.directPureArgsSafe? args = true)
    (hLower :
      Expr.lower1Unchecked? before (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.ProgramBounded
              globalCost localCost fuel result.prepared } := by
  obtain ⟨value, hValues, ⟨bounded⟩⟩ :=
    ofDirectPrimitive_boundedWithStatic
      (staticCost := localCost)
      hDirect hLower hRel hDomain hScope hRun
  exact
    ⟨value, hValues,
      ⟨⟨bounded.1,
        FunctionsObserverFuel.PreparedValue.programBounded_of_bounded
          bounded.2⟩⟩⟩

theorem ofBoundPrimitive_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel globalCost : Nat}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    {Eligible : AstExpr → Prop}
    (hBound : Expr.List.directPureArgsSafe? args = false)
    (hLower :
      Expr.lower1Unchecked? before (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hCost :
      ∀ expr, expr ∈ args →
        FunctionsObserverStaticCost.expr expr ≤ globalCost)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr}
        {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx}
        {value : Assembly.Word},
        exprFuel < fuel →
          FunctionsObserverStaticCost.expr expr ≤ globalCost →
          Eligible expr →
          Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program
                  exprPre exprLower exprAfter layout exprSource'
                  exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.ProgramBounded
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel result.prepared })
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.ProgramBounded
              globalCost
              (FunctionsObserverStaticCost.expr
                (.Call (.inl prim) args))
              fuel result.prepared } := by
  obtain ⟨value, hValues, ⟨result⟩⟩ :=
    FunctionsObserverExpression.ScopedPreparedValue.ofBoundPrimitive
      (Eligible := fun expr =>
        Eligible expr ∧
          FunctionsObserverStaticCost.expr expr ≤ globalCost)
      hBound hLower
      (fun expr hMem => ⟨hEligible expr hMem, hCost expr hMem⟩)
      (fun hExprFuel hExprEligibleCost hExprLower hExprRel hExprDomain
          hExprScope hExprRun => by
        obtain ⟨bounded⟩ :=
          hExpr hExprFuel hExprEligibleCost.2 hExprEligibleCost.1
            hExprLower hExprRel
            hExprDomain hExprScope hExprRun
        exact ⟨bounded.1⟩)
      hRel hDomain hScope hRun
  let hLowering :=
    Expr.uncheckedBoundPrimitiveLowering_of_lower1Unchecked?
      hBound hLower
  cases hLowering with
  | @primitive _ _ _ op _ lowerArgs seq hOp hArgs hSeq hOutputs =>
      obtain
          ⟨callFuel, sourceAfterArgs, reversedValues,
            hFuel, hArgsRun, hPrimRun⟩ :=
        Yul.Source.Effectful.evalValues_primitive_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      cases callFuel with
      | zero =>
          obtain ⟨_hSafe, hPrimCall⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hPrimRun
          simp [ObserverSemantics.SourceReplay.primCall,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ primFuel =>
          obtain ⟨argsBounded⟩ :=
            ScopedPreparedArgs.ofUncheckedLowering_programBounded
              (globalCost := globalCost)
              FunctionsObserverStaticCost.expr
              hArgs hEligible hCost
              (fun hExprFuel hExprCost hExprEligible hExprLower hExprRel
                  hExprDomain hExprScope hExprRun =>
                hExpr (by omega) hExprCost hExprEligible hExprLower hExprRel
                  hExprDomain hExprScope hExprRun)
              hRel hDomain hScope hArgsRun
          have hRequired :
              result.prepared.requiredFuel ≤
                argsBounded.1.prepared.prepared.requiredFuel :=
            FunctionsObserverExpression.PreparedValue.requiredFuel_le_of_prepared_code_eq
              result.prepared argsBounded.1.prepared.prepared rfl
          have hArgsBound :
              argsBounded.1.prepared.prepared.requiredFuel ≤
                FunctionsObserverFuel.executionBudgetFor
                  globalCost
                  (FunctionsObserverStaticCost.exprList args)
                  primFuel.succ := by
            simpa
              [FunctionsObserverStaticCost.exprList_eq_exprListBy] using
              argsBounded.2
          refine ⟨value, hValues, ⟨⟨result, ?_⟩⟩⟩
          dsimp [FunctionsObserverFuel.PreparedValue.ProgramBounded]
          have hDynamic :=
            FunctionsObserverFuel.executionBudgetFor_mono
              globalCost
              (FunctionsObserverStaticCost.exprList args)
              (show primFuel.succ ≤ fuel by omega)
          have hLocal :=
            FunctionsObserverFuel.executionBudgetFor_local_mono
              globalCost fuel
              (show
                FunctionsObserverStaticCost.exprList args ≤
                  FunctionsObserverStaticCost.expr
                    (.Call (.inl prim) args) by
                simp [FunctionsObserverStaticCost.expr])
          exact
            hRequired.trans
              (hArgsBound.trans (hDynamic.trans hLocal))

theorem ofPrimitive_programBounded
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel globalCost : Nat}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after : Fresh.State}
    {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    {Eligible : AstExpr → Prop}
    (hLower :
      Expr.lower1Unchecked? before (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hCost :
      ∀ expr, expr ∈ args →
        FunctionsObserverStaticCost.expr expr ≤ globalCost)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr}
        {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx}
        {value : Assembly.Word},
        exprFuel < fuel →
          FunctionsObserverStaticCost.expr expr ≤ globalCost →
          Eligible expr →
          Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel program
                  exprPre exprLower exprAfter layout exprSource'
                  exprTarget exprCtx value //
              FunctionsObserverFuel.PreparedValue.ProgramBounded
                globalCost (FunctionsObserverStaticCost.expr expr)
                exprFuel result.prepared })
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          { result :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel program pre lower after layout
                source' target ctx value //
            FunctionsObserverFuel.PreparedValue.ProgramBounded
              globalCost
              (FunctionsObserverStaticCost.expr
                (.Call (.inl prim) args))
              fuel result.prepared } := by
  cases hDirect : Expr.List.directPureArgsSafe? args with
  | false =>
      exact
        ofBoundPrimitive_programBounded
          hDirect hLower hEligible hCost hExpr
          hRel hDomain hScope hRun
  | true =>
      exact
        ofDirectPrimitive_programBounded
          (localCost :=
            FunctionsObserverStaticCost.expr
              (.Call (.inl prim) args))
          hDirect hLower hRel hDomain hScope hRun

end ScopedPreparedValue

end FunctionsObserverExpressionFuel
end Yul
end EvmCompiler
