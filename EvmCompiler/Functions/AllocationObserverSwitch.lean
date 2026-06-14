import EvmCompiler.Functions.AllocationObserverStatement

namespace EvmCompiler
namespace Functions
namespace AllocationObserverStatement

open AllocationObserverRelation

namespace Sequence
namespace RegularStmtInvariantForward

/--
Forward preservation for a regular `switch` execution that selects neither a
case nor a default body.

The proof composes the real Functions allocation lowerer, Locals compiler,
canonical source and Structured semantics, and the activation expression
relation. Branch-selection preservation remains owned by the adjacent compiler
passes.
-/
theorem switch_none_of_components
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript scrutinee source sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = none)
    (hScoped : Functions.Scope.ExprScoped live scrutinee)
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      RegularStmtInvariantForward
        contract transcript lowerCtx lowerFinal localsFinal plan live
        frameBase mode mode sourceProgram sourceCtx
        (.switch scrutinee cases defaultBody)
        source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceAfterScrutinee targetFinal sourceCtx := by
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        hLowerScrutinee, hLowerCases, hLowerDefault, rfl⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        hCompileScrutinee, hCompileCases, hCompileDefault, rfl, rfl⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  have hLoweredSelect :
      Locals.Source.Switch.select
          value loweredCases loweredDefault =
        none :=
    AllocationLowering.lowerSwitch_select_none
      hLowerCases hLowerDefault hSelect
  have hTargetSelect :
      Structured.Switch.select value
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault) =
        none :=
    Locals.Switch.select_none_of_compile
      hCompileCases hCompileDefault hLoweredSelect
  obtain
      ⟨targetWithValue, targetAfterPop,
        hTargetScrutinee, hTargetPop, hTargetAfterPop,
        hPopInvariant⟩ :=
    AllocationObserverExpression.Expr.one_forward
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hInvariant hSafe hScoped hLowerScrutinee hCompileScrutinee
  subst targetAfterPop
  have hSource :=
    Functions.Source.Effectful.Stmt.run_switch_none_of_eval
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := 0)
      hSafe.evalOne_eq hSelect
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 1
        (.switch scrutineeCode
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault))
        target
        (Structured.EffectSemantics.Outcome.regular
          (AllocationObserverRelation.StateRel.popTarget
            target.source.evm.stack targetWithValue)) := by
    simpa [AllocationObserverRelation.StateRel.popTarget] using
      (Structured.EffectSemantics.Stmt.Eval.switch_none
        hTargetScrutinee hTargetPop hTargetSelect)
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts :=
            [(.switch scrutineeCode
              (Expressions.CaseList.toStructured compiledCases)
              (Expressions.Default.toStructured compiledDefault))] }
        target
        (Structured.EffectSemantics.Outcome.regular
          (AllocationObserverRelation.StateRel.popTarget
            target.source.evm.stack targetWithValue)) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCasesShape :=
    AllocationLowering.lowerCases_state_shape hLowerCases
  have hDefaultShape :=
    AllocationLowering.lowerDefault_state_shape hLowerDefault
  exact
    ⟨AllocationObserverRelation.StateRel.popTarget
        target.source.evm.stack targetWithValue,
      1, 2, hSource,
      by
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram 2
            { stmts :=
                [Structured.Stmt.switch
                  (Expressions.Expr.code
                    (results := 1) scrutineeCode).compile
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular
              (AllocationObserverRelation.StateRel.popTarget
                target.source.evm.stack targetWithValue))
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram 2
            { stmts :=
                [Structured.Stmt.switch scrutineeCode
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular
              (AllocationObserverRelation.StateRel.popTarget
                target.source.evm.stack targetWithValue))
        exact hTarget,
      hPopInvariant.transport_state
        (hDefaultShape.1.trans hCasesShape.1)
        (hDefaultShape.2.trans hCasesShape.2),
      SameFrame.refl mode⟩

/--
Forward preservation for a regular `switch` execution that selects a case or
default body.

The selected source body and target block are identified independently by the
allocation and Locals compiler boundaries. The recursive body theorem receives
only their ordinary open-lowering and compilation equations plus the transported
activation invariant.
-/
theorem switch_some_of_components
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {outerPlan bodyPlan : Locals.Allocation.Plan}
    {outerLive bodyLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode bodyMode : ActivationMode}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {selectedBody : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterScrutinee sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript scrutinee source sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selectedBody)
    (hScrutineeScoped :
      Functions.Scope.ExprScoped outerLive scrutinee)
    (hBodyScoped :
      Functions.Scope.Block.Scoped outerLive selectedBody)
    (hSourceScope : sourceCtx.scope = outerLive)
    (hSubset :
      ∀ name, name ∈ outerLive → name ∈ bodyLive)
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx outerPlan outerLive
        frameBase outerMode source target)
    (hBody :
      ∀ {selectedLowered : Locals.Block}
        {selectedStart bodyLowerState : AllocationLowering.State}
        {bodyCode : List Expressions.Stmt}
        {bodyLocals : Locals.Ctx}
        {targetAfterPop :
          Structured.ObserverSemantics.State transcript},
        AllocationLowering.lowerBlockOpen
            lowerCtx returns selectedStart selectedBody =
          some (selectedLowered, bodyLowerState) →
        Locals.Block.compileOpen localsCtx selectedLowered =
          some (bodyCode, bodyLocals) →
        AllocationObserverContext.ActivationInvariant
            contract lowerCtx selectedStart localsCtx outerPlan outerLive
            frameBase outerMode sourceAfterScrutinee targetAfterPop →
        ∃ targetBodyMid,
          RegularBlockInvariantForward
            contract transcript lowerCtx bodyLowerState bodyLocals bodyPlan
            bodyLive frameBase outerMode bodyMode sourceProgram sourceCtx
            selectedBody sourceAfterScrutinee targetProgram
            { stmts := Expressions.StmtList.toStructured bodyCode }
            targetAfterPop sourceBodyFinal targetBodyMid finalCtx)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      RegularStmtInvariantForward
        contract transcript lowerCtx lowerFinal localsFinal outerPlan
        outerLive frameBase outerMode outerMode sourceProgram sourceCtx
        (.switch scrutinee cases defaultBody)
        source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceBodyFinal)
        targetFinal sourceCtx := by
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        hLowerScrutinee, hLowerCases, hLowerDefault, rfl⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        hCompileScrutinee, hCompileCases, hCompileDefault, rfl, rfl⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  obtain
      ⟨selectedLowered, selectedStart, selectedScopedFinal,
        hLoweredSelect, hLowerSelected,
        hSelectedEnv, hSelectedLayout⟩ :=
    AllocationLowering.lowerSwitch_select_some
      hLowerCases hLowerDefault hSelect
  obtain
      ⟨selectedCompiled, selectedCode, selectedLocals,
        hTargetSelect, hCompileSelected, hFinishSelected⟩ :=
    Locals.Switch.select_some_of_compile
      hCompileCases hCompileDefault hLoweredSelect
  obtain
      ⟨bodyLowerState, hLowerBody,
        _hSelectedFinalEnv, _hSelectedFinalSlot,
        _hSelectedFinalLayout⟩ :=
    AllocationLowering.lowerBlockScoped_components hLowerSelected
  obtain
      ⟨targetWithValue, targetAfterPop,
        hTargetScrutinee, hTargetPop, hTargetAfterPop,
        hPopInvariant⟩ :=
    AllocationObserverExpression.Expr.one_forward
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hInvariant hSafe hScrutineeScoped
      hLowerScrutinee hCompileScrutinee
  subst targetAfterPop
  have hSelectedInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx selectedStart localsFinal outerPlan outerLive
        frameBase outerMode sourceAfterScrutinee
        (AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue) :=
    hPopInvariant.transport_state hSelectedEnv hSelectedLayout
  obtain ⟨targetBodyMid, hBodyForward⟩ :=
    hBody
      (targetAfterPop :=
        AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
      hLowerBody hCompileSelected hSelectedInvariant
  obtain
      ⟨targetFinal, bodySourceFuel, bodyTargetFuel,
        hSourceBody, hTargetBody, hFinalInvariant⟩ :=
    RegularScopedBlockInvariantForward.finish_regular
      (targetBlock := selectedCompiled)
      (compiledBody := selectedCode)
      (outerLocals := localsFinal)
      (target :=
        AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
      hBodyForward hSourceScope rfl hSelectedInvariant.compiler
      hSelectedInvariant.planWF hSubset hBodyScoped hLowerBody
      hFinishSelected
  have hSource :=
    Functions.Source.Effectful.Stmt.run_switch_some_of_eval
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := bodySourceFuel)
      hSafe.evalOne_eq hSelect hSourceBody
  have hTargetBodySelected :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyTargetFuel selectedCompiled.toStructured
        (AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
    cases selectedCompiled
    exact hTargetBody
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (bodyTargetFuel + 1)
        (.switch scrutineeCode
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault))
        target
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.Stmt.Eval.switch_some
      hTargetScrutinee hTargetPop
      (by
        simp [AllocationObserverRelation.StateRel.popTarget])
      hTargetSelect hTargetBodySelected
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (bodyTargetFuel + 2)
        { stmts :=
            [(.switch scrutineeCode
              (Expressions.CaseList.toStructured compiledCases)
              (Expressions.Default.toStructured compiledDefault))] }
        target
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCasesShape :=
    AllocationLowering.lowerCases_state_shape hLowerCases
  have hDefaultShape :=
    AllocationLowering.lowerDefault_state_shape hLowerDefault
  exact
    ⟨targetFinal, bodySourceFuel + 1, bodyTargetFuel + 2,
      hSource,
      by
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram (bodyTargetFuel + 2)
            { stmts :=
                [Structured.Stmt.switch
                  (Expressions.Expr.code
                    (results := 1) scrutineeCode).compile
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular targetFinal)
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram (bodyTargetFuel + 2)
            { stmts :=
                [Structured.Stmt.switch scrutineeCode
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular targetFinal)
        exact hTarget,
      hFinalInvariant.transport_state
        ((hDefaultShape.1.trans hCasesShape.1).trans
          hSelectedEnv.symm)
        ((hDefaultShape.2.trans hCasesShape.2).trans
          hSelectedLayout.symm),
      SameFrame.refl outerMode⟩

end RegularStmtInvariantForward

namespace RegularStmtRuntimeInvariantForward

/--
Allocator-aware preservation for a `switch` that selects no body.
-/
theorem switch_none_of_components
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript scrutinee source sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = none)
    (hScoped : Functions.Scope.ExprScoped live scrutinee)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      RegularStmtRuntimeInvariantForward
        contract config allocatorDepth transcript lowerCtx lowerFinal
        localsFinal plan live frameBase mode mode sourceProgram sourceCtx
        (.switch scrutinee cases defaultBody)
        source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceAfterScrutinee targetFinal sourceCtx := by
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        hLowerScrutinee, hLowerCases, hLowerDefault, rfl⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        hCompileScrutinee, hCompileCases, hCompileDefault, rfl, rfl⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  have hLoweredSelect :
      Locals.Source.Switch.select value loweredCases loweredDefault = none :=
    AllocationLowering.lowerSwitch_select_none
      hLowerCases hLowerDefault hSelect
  have hTargetSelect :
      Structured.Switch.select value
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault) =
        none :=
    Locals.Switch.select_none_of_compile
      hCompileCases hCompileDefault hLoweredSelect
  obtain
      ⟨targetWithValue, targetAfterPop,
        hTargetScrutinee, hTargetPop, hTargetAfterPop,
        hPopInvariant, hScrutineeEffect⟩ :=
    AllocationObserverExpression.Expr.one_forward_runtime_with_effect
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hInvariant hSafe hScoped
      hLowerScrutinee hCompileScrutinee
  subst targetAfterPop
  have hSource :=
    Functions.Source.Effectful.Stmt.run_switch_none_of_eval
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := 0)
      hSafe.evalOne_eq hSelect
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 1
        (.switch scrutineeCode
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault))
        target
        (Structured.EffectSemantics.Outcome.regular
          (AllocationObserverRelation.StateRel.popTarget
            target.source.evm.stack targetWithValue)) := by
    simpa [AllocationObserverRelation.StateRel.popTarget] using
      (Structured.EffectSemantics.Stmt.Eval.switch_none
        hTargetScrutinee hTargetPop hTargetSelect)
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts :=
            [(.switch scrutineeCode
              (Expressions.CaseList.toStructured compiledCases)
              (Expressions.Default.toStructured compiledDefault))] }
        target
        (Structured.EffectSemantics.Outcome.regular
          (AllocationObserverRelation.StateRel.popTarget
            target.source.evm.stack targetWithValue)) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCasesShape :=
    AllocationLowering.lowerCases_state_shape hLowerCases
  have hDefaultShape :=
    AllocationLowering.lowerDefault_state_shape hLowerDefault
  exact
    ⟨AllocationObserverRelation.StateRel.popTarget
        target.source.evm.stack targetWithValue,
      1, 2, hSource,
      by
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram 2
            { stmts :=
                [Structured.Stmt.switch scrutineeCode
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular
              (AllocationObserverRelation.StateRel.popTarget
                target.source.evm.stack targetWithValue))
        exact hTarget,
      hPopInvariant.transport_state
        (hDefaultShape.1.trans hCasesShape.1)
        (hDefaultShape.2.trans hCasesShape.2),
      SameFrame.refl mode,
      AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
        hScrutineeEffect⟩

/--
Allocator-aware preservation for a `switch` that selects a case or default
body.
-/
theorem switch_some_of_components
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {current : Locals.Allocation.ScopeId}
    {planning : AllocationSupport.PlanningState}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {outerPlan : Locals.Allocation.Plan}
    {outerLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode : ActivationMode}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {selectedBody : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterScrutinee sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hPlanningAllocation :
      planning.allocation = lowerState.allocation)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript scrutinee source sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selectedBody)
    (hScrutineeScoped :
      Functions.Scope.ExprScoped outerLive scrutinee)
    (hBodyScoped :
      Functions.Scope.Block.Scoped outerLive selectedBody)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ outerLive)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        outerPlan outerLive frameBase outerMode source target)
    (hBody :
      ∀ {selectedLowered : Locals.Block}
        {selectedStart bodyLowerState : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        {bodyCode : List Expressions.Stmt}
        {bodyLocals : Locals.Ctx}
        {targetAfterPop :
          Structured.ObserverSemantics.State transcript},
        selectedPlanning.allocation = selectedStart.allocation →
        selectedStart.allocation.env = lowerState.allocation.env →
        AllocationLowering.StateExtends
          outerLive lowerState selectedStart →
        ({ scope := .lexical current selectedPlanning.nextScope
           state :=
             (AllocationSupport.planBlockOpen
               (.lexical current selectedPlanning.nextScope)
               { selectedPlanning with
                 nextScope := selectedPlanning.nextScope + 1 }
               selectedBody).allocation } :
          AllocationSupport.ScopedAllocation) ∈
          (AllocationSupport.planDefault current
            (AllocationSupport.planCases current planning cases)
            defaultBody).scopes →
        (∀ entry,
          entry ∈
              (AllocationSupport.planBlockOpen
                (.lexical current selectedPlanning.nextScope)
                { selectedPlanning with
                  nextScope := selectedPlanning.nextScope + 1 }
                selectedBody).scopes →
            entry ∈
              (AllocationSupport.planDefault current
                (AllocationSupport.planCases current planning cases)
                defaultBody).scopes) →
        AllocationLowering.lowerBlockOpen
            lowerCtx returns selectedStart selectedBody =
          some (selectedLowered, bodyLowerState) →
        Locals.Block.compileOpen localsCtx selectedLowered =
          some (bodyCode, bodyLocals) →
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx selectedStart localsCtx
            outerPlan outerLive frameBase outerMode sourceAfterScrutinee
            targetAfterPop →
        targetAfterPop.source.returns = target.source.returns →
        ∃ bodyPlan bodyMode targetBodyMid,
          RegularBlockRuntimeInvariantForward
            contract config allocatorDepth transcript lowerCtx
            bodyLowerState bodyLocals bodyPlan
            (Functions.Scope.Block.outEnv outerLive selectedBody) frameBase
            outerMode bodyMode sourceProgram sourceCtx selectedBody
            sourceAfterScrutinee targetProgram
            { stmts := Expressions.StmtList.toStructured bodyCode }
            targetAfterPop sourceBodyFinal targetBodyMid finalCtx)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetFinal,
      RegularStmtRuntimeInvariantForward
        contract config allocatorDepth transcript lowerCtx lowerFinal
        localsFinal outerPlan outerLive frameBase outerMode outerMode
        sourceProgram sourceCtx (.switch scrutinee cases defaultBody)
        source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          outerLive sourceBodyFinal)
        targetFinal sourceCtx := by
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        hLowerScrutinee, hLowerCases, hLowerDefault, rfl⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        hCompileScrutinee, hCompileCases, hCompileDefault, rfl, rfl⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  obtain
      ⟨selectedLowered, selectedStart, selectedScopedFinal,
        selectedPlanning, hLoweredSelect, hLowerSelected,
        hSelectedPlanning, hSelectedEnv, hSelectedLayout,
        hSelectedEntry, hSelectedInner⟩ :=
    AllocationLowering.lowerSwitch_select_some_planning
      hPlanningAllocation hLowerCases hLowerDefault hSelect
  obtain
      ⟨selectedCompiled, selectedCode, selectedLocals,
        hTargetSelect, hCompileSelected, hFinishSelected⟩ :=
    Locals.Switch.select_some_of_compile
      hCompileCases hCompileDefault hLoweredSelect
  obtain
      ⟨bodyLowerState, hLowerBody,
        _hSelectedFinalEnv, _hSelectedFinalSlot,
        _hSelectedFinalLayout⟩ :=
    AllocationLowering.lowerBlockScoped_components hLowerSelected
  obtain
      ⟨targetWithValue, targetAfterPop,
        hTargetScrutinee, hTargetPop, hTargetAfterPop,
        hPopInvariant, hScrutineeEffect⟩ :=
    AllocationObserverExpression.Expr.one_forward_runtime_with_effect
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hInvariant hSafe hScrutineeScoped
      hLowerScrutinee hCompileScrutinee
  subst targetAfterPop
  have hSelectedInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx selectedStart localsFinal
        outerPlan outerLive frameBase outerMode sourceAfterScrutinee
        (AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue) :=
    hPopInvariant.transport_state hSelectedEnv hSelectedLayout
  obtain ⟨bodyPlan, bodyMode, targetBodyMid, hBodyForward⟩ :=
    hBody
      (targetAfterPop :=
        AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
      hSelectedPlanning hSelectedEnv
      (AllocationLowering.StateExtends.of_shape
        hSelectedLayout hSelectedEnv)
      hSelectedEntry hSelectedInner
      hLowerBody hCompileSelected hSelectedInvariant
      (by
        simpa [AllocationObserverRelation.StateRel.popTarget] using
          Structured.ObserverSemantics.Code.run_returns_eq hTargetScrutinee)
  obtain
      ⟨targetFinal, bodySourceFuel, bodyTargetFuel,
        hSourceBody, hTargetBody, hFinalInvariant, hBodyEffect⟩ :=
    RegularScopedBlockRuntimeInvariantForward.finish_regular
      (targetBlock := selectedCompiled)
      (compiledBody := selectedCode)
      (outerLocals := localsFinal)
      (target :=
        AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
      hBodyForward
      hSourceScope
      rfl hSelectedInvariant.activation.compiler
      hSelectedInvariant.activation.planWF
      (fun name hName =>
        Functions.Scope.Block.mem_outEnv hName)
      hBodyScoped hLowerBody
      hFinishSelected
  have hSource :=
    Functions.Source.Effectful.Stmt.run_switch_some_of_eval
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram (ctx := sourceCtx) (fuel := bodySourceFuel)
      hSafe.evalOne_eq hSelect hSourceBody
  have hTargetBodySelected :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyTargetFuel selectedCompiled.toStructured
        (AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
    cases selectedCompiled
    exact hTargetBody
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (bodyTargetFuel + 1)
        (.switch scrutineeCode
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault))
        target
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.Stmt.Eval.switch_some
      hTargetScrutinee hTargetPop
      (by
        simp [AllocationObserverRelation.StateRel.popTarget])
      hTargetSelect hTargetBodySelected
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (bodyTargetFuel + 2)
        { stmts :=
            [(.switch scrutineeCode
              (Expressions.CaseList.toStructured compiledCases)
              (Expressions.Default.toStructured compiledDefault))] }
        target
        (Structured.EffectSemantics.Outcome.regular targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil
  have hCasesShape :=
    AllocationLowering.lowerCases_state_shape hLowerCases
  have hDefaultShape :=
    AllocationLowering.lowerDefault_state_shape hLowerDefault
  exact
    ⟨targetFinal, bodySourceFuel + 1, bodyTargetFuel + 2,
      hSource,
      by
        change
          Structured.ObserverSemantics.Block.Eval
            targetProgram (bodyTargetFuel + 2)
            { stmts :=
                [Structured.Stmt.switch scrutineeCode
                  (Expressions.CaseList.toStructured compiledCases)
                  (Expressions.Default.toStructured compiledDefault)] }
            target
            (Structured.EffectSemantics.Outcome.regular targetFinal)
        exact hTarget,
      hFinalInvariant.transport_state
        ((hDefaultShape.1.trans hCasesShape.1).trans
          hSelectedEnv.symm)
        ((hDefaultShape.2.trans hCasesShape.2).trans
          hSelectedLayout.symm),
      SameFrame.refl outerMode,
      (AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
        hScrutineeEffect).trans hBodyEffect⟩

end RegularStmtRuntimeInvariantForward
end Sequence
end AllocationObserverStatement

namespace AllocationObserverOutcome
namespace NonregularStmtRuntimeForward

open AllocationObserverRelation

/--
Allocator-aware preservation for a selected `switch` body that exits
nonregularly.

The switch pass owns selected planner/lowerer synchronization. The recursive
callback supplies the exact selected-body execution plus its outcome relation
transported to the outer plan; compiler-emitted scoped cleanup is unreachable
for the abrupt target outcome.
-/
theorem switch_some_of_components
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {current : Locals.Allocation.ScopeId}
    {planning : AllocationSupport.PlanningState}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {outerPlan : Locals.Allocation.Plan}
    {outerLive : List Locals.Name}
    {frameBase : Nat}
    {outerMode : ActivationMode}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {selectedBody : Functions.Block}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {P :
      Structured.ObserverSemantics.Outcome (transcript := transcript) → Prop}
    {value : Word}
    (hPlanningAllocation :
      planning.allocation = lowerState.allocation)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript scrutinee source sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selectedBody)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hScrutineeScoped :
      Functions.Scope.ExprScoped outerLive scrutinee)
    (hBodyScoped :
      Functions.Scope.Block.Scoped outerLive selectedBody)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        outerPlan outerLive frameBase outerMode source target)
    (hBody :
      ∀ {selectedLowered : Locals.Block}
        {selectedStart bodyLowerState : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        {bodyCode : List Expressions.Stmt}
        {bodyLocals : Locals.Ctx}
        {targetAfterPop :
          Structured.ObserverSemantics.State transcript},
        selectedPlanning.allocation = selectedStart.allocation →
        selectedStart.allocation.env = lowerState.allocation.env →
        AllocationLowering.StateExtends
          outerLive lowerState selectedStart →
        ({ scope := .lexical current selectedPlanning.nextScope
           state :=
             (AllocationSupport.planBlockOpen
               (.lexical current selectedPlanning.nextScope)
               { selectedPlanning with
                 nextScope := selectedPlanning.nextScope + 1 }
               selectedBody).allocation } :
          AllocationSupport.ScopedAllocation) ∈
          (AllocationSupport.planDefault current
            (AllocationSupport.planCases current planning cases)
            defaultBody).scopes →
        (∀ entry,
          entry ∈
              (AllocationSupport.planBlockOpen
                (.lexical current selectedPlanning.nextScope)
                { selectedPlanning with
                  nextScope := selectedPlanning.nextScope + 1 }
                selectedBody).scopes →
            entry ∈
              (AllocationSupport.planDefault current
                (AllocationSupport.planCases current planning cases)
                defaultBody).scopes) →
        AllocationLowering.lowerBlockOpen
            lowerCtx returns selectedStart selectedBody =
          some (selectedLowered, bodyLowerState) →
        Locals.Block.compileOpen localsCtx selectedLowered =
          some (bodyCode, bodyLocals) →
        AllocationObserverContext.ActivationRuntimeInvariant
            contract config allocatorDepth lowerCtx selectedStart localsCtx
            outerPlan outerLive frameBase outerMode sourceAfterScrutinee
            targetAfterPop →
        targetAfterPop.source.returns = target.source.returns →
        ∃ bodyPlan finalMode targetOutcome finalCtx,
          BlockRuntimeForward contract config allocatorDepth transcript
              bodyPlan
              (outcomeLive returns
                (Functions.Scope.Block.outEnv outerLive selectedBody)
                sourceCtx sourceOutcome.mode)
              frameBase outerMode finalMode sourceProgram sourceCtx
              selectedBody sourceAfterScrutinee targetProgram
              { stmts := Expressions.StmtList.toStructured bodyCode }
              targetAfterPop sourceOutcome targetOutcome finalCtx ∧
            ActivationOutcomeRel contract outerPlan
              (outcomeLive returns outerLive sourceCtx sourceOutcome.mode)
              0 frameBase finalMode sourceOutcome targetOutcome ∧
            P targetOutcome)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ targetOutcome finalMode,
      NonregularStmtRuntimeForward
        contract config allocatorDepth transcript outerPlan
        (outcomeLive returns outerLive sourceCtx sourceOutcome.mode)
        frameBase outerMode finalMode sourceProgram sourceCtx
        (.switch scrutinee cases defaultBody) source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceOutcome targetOutcome sourceCtx ∧
      P targetOutcome := by
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        hLowerScrutinee, hLowerCases, hLowerDefault, rfl⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        hCompileScrutinee, hCompileCases, hCompileDefault, rfl, rfl⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  obtain
      ⟨selectedLowered, selectedStart, selectedScopedFinal,
        selectedPlanning, hLoweredSelect, hLowerSelected,
        hSelectedPlanning, hSelectedEnv, hSelectedLayout,
        hSelectedEntry, hSelectedInner⟩ :=
    AllocationLowering.lowerSwitch_select_some_planning
      hPlanningAllocation hLowerCases hLowerDefault hSelect
  obtain
      ⟨selectedCompiled, selectedCode, selectedLocals,
        hTargetSelect, hCompileSelected, hFinishSelected⟩ :=
    Locals.Switch.select_some_of_compile
      hCompileCases hCompileDefault hLoweredSelect
  obtain
      ⟨bodyLowerState, hLowerBody,
        _hSelectedFinalEnv, _hSelectedFinalSlot,
        _hSelectedFinalLayout⟩ :=
    AllocationLowering.lowerBlockScoped_components hLowerSelected
  obtain
      ⟨targetWithValue, targetAfterPop,
        hTargetScrutinee, hTargetPop, hTargetAfterPop,
        hPopInvariant, hScrutineeEffect⟩ :=
    AllocationObserverExpression.Expr.one_forward_runtime_with_effect
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hInvariant hSafe hScrutineeScoped
      hLowerScrutinee hCompileScrutinee
  subst targetAfterPop
  have hSelectedInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx selectedStart localsFinal
        outerPlan outerLive frameBase outerMode sourceAfterScrutinee
        (AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue) :=
    hPopInvariant.transport_state hSelectedEnv hSelectedLayout
  obtain
      ⟨bodyPlan, finalMode, targetOutcome, finalCtx,
        hBodyForward, hOuterOutcomeRel, hP⟩ :=
    hBody
      (targetAfterPop :=
        AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
      hSelectedPlanning hSelectedEnv
      (AllocationLowering.StateExtends.of_shape
        hSelectedLayout hSelectedEnv)
      hSelectedEntry hSelectedInner
      hLowerBody hCompileSelected hSelectedInvariant
      (by
        simpa [AllocationObserverRelation.StateRel.popTarget] using
          Structured.ObserverSemantics.Code.run_returns_eq hTargetScrutinee)
  rcases hBodyForward with
    ⟨bodySourceFuel, bodyTargetFuel, hSourceOpen, hTargetBody,
      _hBodyOutcomeRel, hSame, hBodyEffect⟩
  have hSourceScoped :=
    Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hSourceOpen hMode
  have hSourceStmt :=
    Functions.Source.Effectful.Stmt.run_switch_some_of_eval
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hSafe.evalOne_eq hSelect hSourceScoped
  obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
    AllocationObserverCleanup.Plain.finishScoped_shape hFinishSelected
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hOuterOutcomeRel.target_nonregular hMode
  have hTargetSelected :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyTargetFuel selectedCompiled.toStructured
        (AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
        targetOutcome := by
    rcases selectedCompiled with ⟨selectedStmts⟩
    change
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyTargetFuel
        { stmts :=
            Expressions.StmtList.toStructured selectedStmts }
        (AllocationObserverRelation.StateRel.popTarget
          target.source.evm.stack targetWithValue)
        targetOutcome
    have hTargetShape' :
        selectedStmts =
          selectedCode ++ [Expressions.Stmt.code cleanup] := by
      simpa using hTargetShape
    rw [hTargetShape']
    simpa [Expressions.StmtList.toStructured_append,
      Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using
      (Structured.EffectSemantics.Block.Eval.append_nonregular
        hTargetBody hTargetMode :
        Structured.ObserverSemantics.Block.Eval
          targetProgram bodyTargetFuel
          { stmts :=
              Expressions.StmtList.toStructured selectedCode ++
                [Structured.Stmt.code cleanup] }
          (AllocationObserverRelation.StateRel.popTarget
            target.source.evm.stack targetWithValue)
          targetOutcome)
  have hTargetStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (bodyTargetFuel + 1)
        (.switch scrutineeCode
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault))
        target targetOutcome :=
    Structured.EffectSemantics.Stmt.Eval.switch_some
      hTargetScrutinee hTargetPop
      (by
        simp [AllocationObserverRelation.StateRel.popTarget])
      hTargetSelect hTargetSelected
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (bodyTargetFuel + 2)
        { stmts :=
            [(.switch scrutineeCode
              (Expressions.CaseList.toStructured compiledCases)
              (Expressions.Default.toStructured compiledDefault))] }
        target targetOutcome :=
    Structured.EffectSemantics.Block.Eval.cons_nonregular
      hTargetStmt hTargetMode
  exact
    ⟨targetOutcome, finalMode,
      ⟨bodySourceFuel + 1, bodyTargetFuel + 2,
        hSourceStmt, hTarget, hMode, hOuterOutcomeRel, hSame,
        (Frame.ActivationEffect.of_allocatorEffect
          hScrutineeEffect).trans hBodyEffect⟩,
      hP⟩

end NonregularStmtRuntimeForward
end AllocationObserverOutcome
end Functions
end EvmCompiler
