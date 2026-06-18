import EvmCompiler.Functions.AllocationInteractionRecursiveCallResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursiveRuntime

open AllocationInteractionCursor
open AllocationInteractionFrame
open AllocationInteractionRelation
open AllocationInteractionRecursive
open AllocationInteractionRecursiveResource

private theorem successful_head
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {source : SourceState}
    (hFuel : 0 < fuel)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program ctx fuel
          { stmts := stmt :: rest } source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Stmt.openRun program ctx (fuel - 1)
        stmt source) := by
  have hFuelEq : fuel - 1 + 1 = fuel := by omega
  have hWhole :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program ctx
          (fuel - 1 + 1) { stmts := stmt :: rest } source) := by
    rw [hFuelEq]
    exact hSuccess
  have hHead :=
    Functions.InteractionSemantics.Block.successful_openRun_cons_head hWhole
  simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead

private theorem recursive_tail
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {contract : MemoryContract.Contract}
    {globalFrameWords sourceFuel : Nat}
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Config} {allocatorDepth frameBase targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          (sourceFuel - 1) sourceBlock source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase
      (sourceFuel - 1) targetExtra mode sourceCtx source target := by
  exact hRecursive cursor (by omega) hBoundary
    (AllocationInteractionFrame.Budget.mono (by omega) hFuelBudget)
    hReserve hSuccess

private theorem successful_expr_eval
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {expr : Functions.Expr 0} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.expr expr) source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval expr source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  exact Simulation.Interaction.Successful.bind_left hSuccess

private theorem successful_let_eval
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {name : Functions.Name} {value : Functions.Expr 1}
    {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.let_ name value) source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval value source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  have hOne := Simulation.Interaction.Successful.bind_left hSuccess
  unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
  exact Simulation.Interaction.Successful.bind_left hOne

private theorem successful_assign_eval
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {name : Functions.Name} {value : Functions.Expr 1}
    {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.assign name value) source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval value source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  split at hSuccess
  next hContains =>
    have hOne := Simulation.Interaction.Successful.bind_left hSuccess
    unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
    exact Simulation.Interaction.Successful.bind_left hOne
  next hContains =>
    exact False.elim
      (Simulation.Interaction.Successful.error_false _ hSuccess)

private theorem successful_if_condition
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {cond : Functions.Expr 1} {body : Functions.Block}
    {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.if_ cond body) source)) :
    0 < fuel ∧
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Expr.openEval cond source) := by
  cases fuel with
  | zero =>
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | succ fuel =>
      rw [Functions.InteractionSemantics.Stmt.openRun_if] at hSuccess
      have hCond := Simulation.Interaction.Successful.bind_left hSuccess
      unfold Functions.InteractionSemantics.Expr.openEvalCondition at hCond
      unfold Locals.InteractionSemantics.Expr.openEvalCondition at hCond
      unfold Locals.Source.Effectful.Expr.Control.evalCondition at hCond
      have hOne := Simulation.Interaction.Successful.bind_left hCond
      unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
      exact ⟨by omega, Simulation.Interaction.Successful.bind_left hOne⟩

private theorem successful_switch_scrutinee
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program ctx fuel
          (.switch scrutinee cases defaultBody) source)) :
    0 < fuel ∧
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Expr.openEval scrutinee source) := by
  cases fuel with
  | zero =>
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | succ fuel =>
      rw [Functions.InteractionSemantics.Stmt.openRun_switch] at hSuccess
      have hOne := Simulation.Interaction.Successful.bind_left hSuccess
      unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
      exact ⟨by omega, Simulation.Interaction.Successful.bind_left hOne⟩

private theorem successful_condition_eval
    {cond : Functions.Expr 1} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Expr.openEvalCondition cond source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval cond source) := by
  unfold Functions.InteractionSemantics.Expr.openEvalCondition at hSuccess
  unfold Locals.InteractionSemantics.Expr.openEvalCondition at hSuccess
  unfold Locals.Source.Effectful.Expr.Control.evalCondition at hSuccess
  have hOne := Simulation.Interaction.Successful.bind_left hSuccess
  unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
  exact Simulation.Interaction.Successful.bind_left hOne

private theorem successful_brk_scope
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel .brk source)) :
    ∃ afterLive, ctx.breakScope? = some afterLive := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  cases hScope : ctx.breakScope? with
  | none =>
      rw [hScope] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | some afterLive => exact ⟨afterLive, rfl⟩

private theorem successful_cont_scope
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel .cont source)) :
    ∃ afterLive, ctx.continueScope? = some afterLive := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  cases hScope : ctx.continueScope? with
  | none =>
      rw [hScope] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | some afterLive => exact ⟨afterLive, rfl⟩

private theorem successful_leave_scope
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel .leave source)) :
    ∃ functionScope, ctx.leaveScope? = some functionScope := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  cases hScope : ctx.leaveScope? with
  | none =>
      rw [hScope] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | some functionScope => exact ⟨functionScope, rfl⟩

private theorem for_capacity_of_reserve
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {sourceFuel targetExtra : Nat}
    (cursor : CoreCursor root scope live
      { stmts := .for_ init cond post body :: rest }
      lowerState localsCtx)
    (hSourceFuel : 2 < sourceFuel)
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra) :
    ForFuelCapacity cursor.forArtifact (sourceFuel - 2)
      ((targetBudget cursor sourceFuel targetExtra - 2) -
        (sourceFuel - 2)) := by
  classical
  let components := cursor.forArtifact
  let loopFuel := sourceFuel - 2
  let nestedFuel := targetBudget cursor sourceFuel targetExtra - 2
  let slack := nestedFuel - loopFuel
  change ForFuelCapacity components loopFuel slack
  obtain ⟨postCleanup, _hPostCleanup, hPostShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape
      components.finishPost
  obtain ⟨bodyCleanup, _hBodyCleanup, hBodyShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape
      components.finishBody
  have hParentShape :
      AllocationInteractionTargetFuel.stmtListNestedSize
          cursor.compiled =
        AllocationInteractionTargetFuel.stmtListSize
            components.initCursor.compiled +
          AllocationInteractionTargetFuel.blockSize components.compiledPost +
          AllocationInteractionTargetFuel.blockSize components.compiledBody +
          AllocationInteractionTargetFuel.stmtListNestedSize
            components.tail.compiled := by
    rw [components.compiled,
      AllocationInteractionTargetFuel.stmtListNestedSize_append,
      components.headCode_eq,
      AllocationInteractionTargetFuel.stmtListNestedSize_append]
    simp [AllocationInteractionTargetFuel.stmtListNestedSize,
      AllocationInteractionTargetFuel.stmtNestedSize,
      AllocationInteractionTargetFuel.blockSize, Locals.codeStmt]
  have hPostBlockSize :
      AllocationInteractionTargetFuel.blockSize components.compiledPost =
        AllocationInteractionTargetFuel.stmtListSize
          components.compiledPost.stmts := by
    cases components.compiledPost
    rfl
  have hBodyBlockSize :
      AllocationInteractionTargetFuel.blockSize components.compiledBody =
        AllocationInteractionTargetFuel.stmtListSize
          components.compiledBody.stmts := by
    cases components.compiledBody
    rfl
  have hPostWithin :
      AllocationInteractionTargetFuel.stmtListSize
          components.postCursor.compiled ≤
        AllocationInteractionTargetFuel.stmtListNestedSize
          cursor.compiled := by
    rw [hParentShape, hPostBlockSize, hPostShape,
      AllocationInteractionTargetFuel.stmtListSize_append]
    omega
  have hBodyWithin :
      AllocationInteractionTargetFuel.stmtListSize
          components.bodyCursor.compiled ≤
        AllocationInteractionTargetFuel.stmtListNestedSize
          cursor.compiled := by
    rw [hParentShape, hBodyBlockSize, hBodyShape,
      AllocationInteractionTargetFuel.stmtListSize_append]
    omega
  have hInitWithin :
      AllocationInteractionTargetFuel.stmtListSize
          components.initCursor.compiled ≤
        AllocationInteractionTargetFuel.stmtListNestedSize
          cursor.compiled := by
    rw [hParentShape]
    omega
  unfold AllocationInteractionTargetFuel.Reserve at hReserve
  have hInitExtra := hInitWithin.trans hReserve
  have hPostExtra := hPostWithin.trans hReserve
  have hBodyExtra := hBodyWithin.trans hReserve
  have hNestedGe : loopFuel ≤ nestedFuel := by
    have hEnough :
        loopFuel + 2 ≤ targetBudget cursor sourceFuel targetExtra := by
      unfold loopFuel targetBudget
      have hStride : 1 ≤ callStride expressions :=
        le_trans (by omega) (eight_le_callStride expressions)
      have hMul :
          sourceFuel ≤ callStride expressions * sourceFuel := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right sourceFuel hStride
      rw [Nat.mul_succ]
      omega
    unfold nestedFuel
    omega
  have hTotalEnough :
      loopFuel + 2 ≤ targetBudget cursor sourceFuel targetExtra := by
    unfold loopFuel targetBudget
    have hStride : 1 ≤ callStride expressions :=
      le_trans (by omega) (eight_le_callStride expressions)
    have hMul :
        sourceFuel ≤ callStride expressions * sourceFuel := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right sourceFuel hStride
    rw [Nat.mul_succ]
    omega
  have hTargetTwo :
      2 ≤ targetBudget cursor sourceFuel targetExtra := by omega
  have hNestedExact :
      nestedFuel + 2 = targetBudget cursor sourceFuel targetExtra := by
    unfold nestedFuel
    exact Nat.sub_add_cancel hTargetTwo
  have hSlackEq : loopFuel + slack = nestedFuel := by
    unfold slack
    exact Nat.add_sub_of_le hNestedGe
  have hInitSizeEq :=
    AllocationInteractionTargetFuel.stmtListSize_eq
      components.initCursor.compiled
  have hPostSizeEq :=
    AllocationInteractionTargetFuel.stmtListSize_eq
      components.postCursor.compiled
  have hBodySizeEq :=
    AllocationInteractionTargetFuel.stmtListSize_eq
      components.bodyCursor.compiled
  have hInitCost :
      AllocationInteractionTargetFuel.stmtListNestedSize
            components.initCursor.compiled +
          components.initCursor.compiled.length ≤ targetExtra := by
    omega
  have hPostCost :
      AllocationInteractionTargetFuel.stmtListNestedSize
            components.postCursor.compiled +
          components.postCursor.compiled.length ≤ targetExtra := by
    omega
  have hBodyCost :
      AllocationInteractionTargetFuel.stmtListNestedSize
            components.bodyCursor.compiled +
          components.bodyCursor.compiled.length ≤ targetExtra := by
    omega
  refine { init := ?_, post := ?_, body := ?_ }
  · rw [hSlackEq]
    have hFuelGap :
        sourceFuel + 1 = (sourceFuel - 2 + 1) + 2 := by omega
    have hMulGap :
        callStride expressions * (sourceFuel + 1) =
          callStride expressions * (sourceFuel - 2 + 1) +
            callStride expressions * 2 := by
      rw [hFuelGap, Nat.mul_add]
    have hBound :
        targetBudget components.initCursor loopFuel
              (AllocationInteractionTargetFuel.stmtListNestedSize
                components.initCursor.compiled) + 2 ≤
          targetBudget cursor sourceFuel targetExtra := by
      unfold loopFuel targetBudget
      have hStride := eight_le_callStride expressions
      have hStrideOne : 1 ≤ callStride expressions := by omega
      have hScaleTwo : 2 ≤ callStride expressions * 2 := by
        simpa using Nat.mul_le_mul_right 2 hStrideOne
      omega
    omega
  · intro fuel hFuelLt
    have hFuelLe : fuel ≤ loopFuel := Nat.le_of_lt hFuelLt
    have hFuelGap :
        sourceFuel + 1 =
          (fuel + 1) + ((loopFuel - fuel) + 2) := by
      unfold loopFuel
      omega
    have hMulGap :
        callStride expressions * (sourceFuel + 1) =
          callStride expressions * (fuel + 1) +
            callStride expressions * ((loopFuel - fuel) + 2) := by
      rw [hFuelGap, Nat.mul_add]
    have hBound :
        targetBudget components.postCursor fuel
              (AllocationInteractionTargetFuel.stmtListNestedSize
                components.postCursor.compiled) +
              (loopFuel - fuel) + 2 ≤
          targetBudget cursor sourceFuel targetExtra := by
      unfold targetBudget
      have hStride := eight_le_callStride expressions
      have hStrideOne : 1 ≤ callStride expressions := by omega
      have hScaleGap :
          loopFuel - fuel + 2 ≤
            callStride expressions * (loopFuel - fuel + 2) := by
        simpa using Nat.mul_le_mul_right (loopFuel - fuel + 2) hStrideOne
      omega
    have hFuelDecomp : fuel + (loopFuel - fuel) = loopFuel :=
      Nat.add_sub_of_le hFuelLe
    omega
  · intro fuel hFuelLt
    have hFuelLe : fuel ≤ loopFuel := Nat.le_of_lt hFuelLt
    have hFuelGap :
        sourceFuel + 1 =
          (fuel + 1) + ((loopFuel - fuel) + 2) := by
      unfold loopFuel
      omega
    have hMulGap :
        callStride expressions * (sourceFuel + 1) =
          callStride expressions * (fuel + 1) +
            callStride expressions * ((loopFuel - fuel) + 2) := by
      rw [hFuelGap, Nat.mul_add]
    have hBound :
        targetBudget components.bodyCursor fuel
              (AllocationInteractionTargetFuel.stmtListNestedSize
                components.bodyCursor.compiled) +
              (loopFuel - fuel) + 2 ≤
          targetBudget cursor sourceFuel targetExtra := by
      unfold targetBudget
      have hStride := eight_le_callStride expressions
      have hStrideOne : 1 ≤ callStride expressions := by omega
      have hScaleGap :
          loopFuel - fuel + 2 ≤
            callStride expressions * (loopFuel - fuel + 2) := by
        simpa using Nat.mul_le_mul_right (loopFuel - fuel + 2) hStrideOne
      omega
    have hFuelDecomp : fuel + (loopFuel - fuel) = loopFuel :=
      Nat.add_sub_of_le hFuelLe
    omega

private theorem expr_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor :
      CoreCursor root scope live { stmts := .expr expr :: rest }
        lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .expr expr :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  have hExprScoped : Functions.Scope.ExprScoped live expr := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped
  have hSafe := hSafety.expr hExprScoped
    hBoundary.semantic.invariant.defined
    (successful_expr_eval hHeadSuccess)
  exact CursorRuntimeAt.expr cursor hSourceFuel hSafe hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess =>
      recursive_tail hRecursive tail (by omega) hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem assign_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor :
      CoreCursor root scope live { stmts := .assign name value :: rest }
        lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .assign name value :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  have hExprScoped : Functions.Scope.ExprScoped live value := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.2
  have hSafe := hSafety.expr hExprScoped
    hBoundary.semantic.invariant.defined
    (successful_assign_eval hHeadSuccess)
  exact CursorRuntimeAt.assign cursor hSourceFuel hSafe hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem let_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor :
      CoreCursor root scope live { stmts := .let_ name value :: rest }
        lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .let_ name value :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  have hExprScoped : Functions.Scope.ExprScoped live value := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.2
  have hSafe := hSafety.expr hExprScoped
    hBoundary.semantic.invariant.defined
    (successful_let_eval hHeadSuccess)
  exact CursorRuntimeAt.let_ cursor hSourceFuel hSafe hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem brk_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live { stmts := .brk :: rest }
      lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .brk :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  obtain ⟨afterLive, hSourceScope⟩ := successful_brk_scope hHeadSuccess
  obtain ⟨targetDepth, afterMode, hTargetDepth, ⟨hTransition⟩⟩ :=
    hBoundary.controlAgreement.brk hSourceScope
  exact CursorRuntimeAt.brk cursor hSourceFuel hSourceScope hTargetDepth
    hTransition hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem cont_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live { stmts := .cont :: rest }
      lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .cont :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  obtain ⟨afterLive, hSourceScope⟩ := successful_cont_scope hHeadSuccess
  obtain ⟨targetDepth, afterMode, hTargetDepth, ⟨hTransition⟩⟩ :=
    hBoundary.controlAgreement.cont hSourceScope
  exact CursorRuntimeAt.cont cursor hSourceFuel hSourceScope hTargetDepth
    hTransition hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem leave_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live { stmts := .leave :: rest }
      lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .leave :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  obtain ⟨functionScope, hSourceScope⟩ :=
    successful_leave_scope hHeadSuccess
  obtain ⟨hTargetDepth, hRetc, hReturnFrame⟩ :=
    hBoundary.controlAgreement.leave hSourceScope
  exact CursorRuntimeAt.leave cursor hSourceFuel hSourceScope
    hBoundary.semantic.control.returnsLive
    (hBoundary.semantic.control.leaveScope functionScope hSourceScope)
    hTargetDepth hRetc hReturnFrame hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem terminal_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live
      { stmts := .terminal kind :: rest } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .terminal kind :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hHeadSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hHeadSuccess
  have hTerminalSuccess :=
    Simulation.Interaction.Successful.bind_left hHeadSuccess
  exact CursorRuntimeAt.terminal cursor hSourceFuel
    (hSafety.terminal hTerminalSuccess) hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem terminalArgs_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live
      { stmts := .terminalArgs kind args :: rest } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .terminalArgs kind args :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hHeadSuccess := successful_head hSourceFuel hSuccess
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hHeadSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hHeadSuccess
  have hArgsSuccess :=
    Simulation.Interaction.Successful.bind_left hHeadSuccess
  have hArgsScoped : Functions.Scope.ExprSeqScoped live args := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped
  have hArgsSafe := hSafety.exprSeq hArgsScoped
    hBoundary.semantic.invariant.defined hArgsSuccess
  have hTerminalContinuations :=
    Simulation.Interaction.Successful.bind_inv hHeadSuccess
  have hTerminalSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              Simulation.MemorySafety.TerminalMemorySafe
                contract kind result.2)
        (Functions.InteractionSemantics.ExprSeq.openEval args source) := by
    apply Simulation.Interaction.AllDone.mono hTerminalContinuations
    intro outcome hOutcome
    cases outcome with
    | error err => trivial
    | ok result =>
        exact hSafety.terminal
          (Simulation.Interaction.Successful.bind_left hOutcome)
  exact CursorRuntimeAt.terminalArgs cursor hSourceFuel hArgsSafe
    hTerminalSafe hBoundary hSuccess
    (fun {afterState afterLocals} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem block_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {body : Functions.Block} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live
      { stmts := .block body :: rest } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .block body :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  exact CursorRuntimeAt.block cursor hSourceFuel hReserve hBoundary hSuccess
    (fun bodyCursor bodyExtra hBodyReserve hBodyBoundary hBodySuccess =>
      hRecursive bodyCursor (by omega) hBodyBoundary
        (AllocationInteractionFrame.Budget.mono (by omega) hFuelBudget)
        hBodyReserve hBodySuccess)
    (fun {afterState} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail (by omega) hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem if_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live
      { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .if_ cond body :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hWholeFuel :=
    Functions.InteractionSemantics.Block.successful_openRun_fuel_pos hSuccess
  have hHeadSuccess := successful_head hWholeFuel hSuccess
  have hSourceFuel : 1 < sourceFuel := by
    have hHeadFuel := (successful_if_condition hHeadSuccess).1
    omega
  have hCondScoped : Functions.Scope.ExprScoped live cond := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.1
  have hCondSafe := hSafety.expr hCondScoped
    hBoundary.semantic.invariant.defined
    (successful_if_condition hHeadSuccess).2
  exact CursorRuntimeAt.if_ cursor hSourceFuel hReserve hCondSafe hBoundary
    hSuccess
    (fun bodyCursor {sourceAfter targetAfter} hTargetCapacity hBodyBoundary
        hBodySuccess => by
      have hBodyRel :=
        RecursiveOpenRuntime.at_targetFuel hRecursive bodyCursor
          (by omega) hTargetCapacity hBodyBoundary
          (AllocationInteractionFrame.Budget.mono (by omega) hFuelBudget)
          hBodySuccess
      have hCleanupFuel :
          2 ≤
            (targetBudget cursor sourceFuel targetExtra - 2) -
              bodyCursor.compiled.length := by
        have hStride := eight_le_callStride expressions
        have hMul := Nat.mul_le_mul hStride
          (show 1 ≤ sourceFuel - 2 + 1 by omega)
        have hEnough :
            bodyCursor.compiled.length + 2 ≤
              targetBudget cursor sourceFuel targetExtra - 2 := by
          exact le_trans (by
            unfold targetBudget
            omega) hTargetCapacity
        omega
      exact ⟨hCleanupFuel, hBodyRel⟩)
    (fun {afterState} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail (by omega) hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem switch_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live
      { stmts := .switch scrutinee cases defaultBody :: rest }
      lowerState localsCtx)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel
          { stmts := .switch scrutinee cases defaultBody :: rest }
          source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hWholeFuel :=
    Functions.InteractionSemantics.Block.successful_openRun_fuel_pos hSuccess
  have hHeadSuccess := successful_head hWholeFuel hSuccess
  have hSourceFuel : 1 < sourceFuel := by
    have hHeadFuel := (successful_switch_scrutinee hHeadSuccess).1
    omega
  have hScrutineeScoped :
      Functions.Scope.ExprScoped live scrutinee := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.1
  have hScrutineeSafe := hSafety.expr hScrutineeScoped
    hBoundary.semantic.invariant.defined
    (successful_switch_scrutinee hHeadSuccess).2
  exact CursorRuntimeAt.switch cursor hSourceFuel hReserve hScrutineeSafe
    hBoundary hSuccess
    (fun {value selected selectedStart selectedPlanning} hSelect bodyCursor
        {sourceAfter targetAfter} hTargetCapacity hBodyBoundary
        hBodySuccess => by
      have hBodyRel :=
        RecursiveOpenRuntime.at_targetFuel hRecursive bodyCursor
          (by omega) hTargetCapacity hBodyBoundary
          (AllocationInteractionFrame.Budget.mono (by omega) hFuelBudget)
          hBodySuccess
      have hCleanupFuel :
          2 ≤
            (targetBudget cursor sourceFuel targetExtra - 2) -
              bodyCursor.compiled.length := by
        have hStride := eight_le_callStride expressions
        have hMul := Nat.mul_le_mul hStride
          (show 1 ≤ sourceFuel - 2 + 1 by omega)
        have hEnough :
            bodyCursor.compiled.length + 2 ≤
              targetBudget cursor sourceFuel targetExtra - 2 := by
          exact le_trans (by
            unfold targetBudget
            omega) hTargetCapacity
        omega
      exact ⟨hCleanupFuel, hBodyRel⟩)
    (fun {afterState} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail (by omega) hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem for_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (cursor : CoreCursor root scope live
      { stmts := .for_ init cond post body :: rest }
      lowerState localsCtx)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel
          { stmts := .for_ init cond post body :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hWholeFuel :=
    Functions.InteractionSemantics.Block.successful_openRun_fuel_pos hSuccess
  have hHeadSuccess := successful_head hWholeFuel hSuccess
  have hHeadFuel :=
    Functions.InteractionSemantics.Stmt.successful_openRun_for_fuel_pos
      hHeadSuccess
  have hHeadFuelEq : sourceFuel - 2 + 1 = sourceFuel - 1 := by omega
  have hInitSuccess :=
    Functions.InteractionSemantics.Stmt.successful_openRun_for_init
      (fuel := sourceFuel - 2) (by
        simpa [hHeadFuelEq] using hHeadSuccess)
  have hInitFuel :=
    Functions.InteractionSemantics.Block.successful_openRun_fuel_pos hInitSuccess
  have hSourceFuel : 2 < sourceFuel := by omega
  exact CursorRuntimeAt.for_ cursor hSourceFuel
    (fun nextSource hDefined hCondSuccess =>
      hSafety.expr cursor.forArtifact.condScoped hDefined
        (successful_condition_eval hCondSuccess))
    hBoundary hFuelBudget hHeadSuccess hSuccess hRecursive
    (for_capacity_of_reserve cursor hSourceFuel hReserve)
    (fun {afterState} tail hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail (by omega) hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

private theorem call_of_recursive
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live targets : List Functions.Name}
    {functionName : Functions.Name}
    {args : List (Functions.Expr 1)} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hProgramScoped : program.Scoped)
    (hSafety :
      AllocationInteractionSafety.SourceSafety program.memoryContract)
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords sourceFuel)
    (cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx)
    (hBoundary :
      Boundary cursor program.memoryContract compilation.recipe.frameWords
        config allocatorDepth frameBase mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel
          { stmts := .call targets functionName args :: rest } source)) :
    CursorRuntimeAt cursor program.memoryContract config allocatorDepth
      frameBase sourceFuel targetExtra mode sourceCtx source target := by
  have hWholeFuel :=
    Functions.InteractionSemantics.Block.successful_openRun_fuel_pos hSuccess
  have hHeadSuccess := successful_head hWholeFuel hSuccess
  have hHeadFuel :=
    Functions.InteractionSemantics.Stmt.successful_openRun_call_fuel_pos
      hHeadSuccess
  have hTargets : targets.Nodup := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.1
  have hHeadFuelEq : sourceFuel - 2 + 1 = sourceFuel - 1 := by omega
  have hCallParts :=
    Functions.InteractionSemantics.Stmt.successful_openRun_call_parts
      program sourceCtx (sourceFuel - 2) targets functionName args source
      hTargets (by simpa [hHeadFuelEq] using hHeadSuccess)
  obtain ⟨outcome, hOutcome⟩ :=
    Simulation.Interaction.AllDone.exists_done hCallParts
  have hSourceFuel : 2 < sourceFuel := by
    cases outcome with
    | error err => exact False.elim hOutcome
    | ok result =>
        obtain ⟨fn, _hFind, hBodySuccess⟩ := hOutcome
        have hBodyFuel :=
          Functions.InteractionSemantics.FunDef.successful_openRunBody_fuel_pos
            hBodySuccess
        omega
  have hArgSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.ArgList.openEval args source) := by
    apply Simulation.Interaction.AllDone.mono hCallParts
    intro result hResult
    cases result with
    | error err => exact hResult
    | ok value => trivial
  have hArgsScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.2.2
  have hArgSafe := hSafety.argList hArgsScoped
    hBoundary.semantic.invariant.defined hArgSuccess
  exact AllocationInteractionRecursiveCallResource.CursorRuntimeAt.call
    cursor hProgramScoped hSourceFuel hArgSafe hBoundary hFuelBudget
    hHeadSuccess hSuccess hRecursive
    (fun tail hExact {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess =>
      recursive_tail hRecursive tail (by omega) hTailBoundary hFuelBudget
        (AllocationInteractionTargetFuel.Reserve.tail hReserve hExact)
        hTailSuccess)

/-- Every successful canonical Functions block implements the pass-owned
recursive runtime, by well-founded induction on source meta-fuel. -/
private theorem complete_at
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    (hProgramScoped : program.Scoped)
    (hSafety :
      AllocationInteractionSafety.SourceSafety program.memoryContract) :
    ∀ sourceFuel : Nat,
      ∀ {root : RootArtifact compilation}
        {scope : Locals.Allocation.ScopeId}
        {live : List Functions.Name}
        {sourceBlock : Functions.Block}
        {lowerState : AllocationLowering.State}
        {localsCtx : Locals.Ctx}
        {config : Config} {allocatorDepth frameBase targetExtra : Nat}
        {mode : ActivationMode}
        {sourceCtx : Functions.Source.Ctx}
        {source : SourceState} {target : TargetState},
        (cursor :
          CoreCursor root scope live sourceBlock lowerState localsCtx) →
        Boundary cursor program.memoryContract compilation.recipe.frameWords
            config allocatorDepth frameBase mode sourceCtx source target →
        AllocationInteractionFrame.Budget config
            (allocatorDepth + sourceFuel) →
        AllocationInteractionTargetFuel.Reserve cursor targetExtra →
        Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              sourceFuel sourceBlock source) →
        CursorRuntimeAt cursor program.memoryContract config allocatorDepth
          frameBase sourceFuel targetExtra mode sourceCtx source target := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro root scope live sourceBlock lowerState localsCtx config
        allocatorDepth frameBase targetExtra mode sourceCtx source target
        cursor hBoundary hFuelBudget hReserve hSuccess
      have hSourceFuel :=
        Functions.InteractionSemantics.Block.successful_openRun_fuel_pos hSuccess
      have hRecursive :
          RecursiveOpenRuntime (compilation := compilation)
            program.memoryContract compilation.recipe.frameWords sourceFuel := by
        intro childRoot childScope childLive childBlock childState childLocals
          childConfig childAllocatorDepth childFrameBase childSourceFuel
          childTargetExtra childMode childSourceCtx childSource childTarget
          childCursor hChildFuel hChildBoundary hChildBudget hChildReserve
          hChildSuccess
        exact ih childSourceFuel hChildFuel childCursor hChildBoundary
          hChildBudget hChildReserve hChildSuccess
      rcases sourceBlock with ⟨stmts⟩
      cases stmts with
      | nil =>
          exact CursorRuntimeAt.nil cursor hSourceFuel hBoundary
      | cons stmt rest =>
          cases stmt with
          | expr expr =>
              exact expr_of_recursive hSafety hRecursive cursor hSourceFuel
                hBoundary hFuelBudget hReserve hSuccess
          | let_ name value =>
              exact let_of_recursive hSafety hRecursive cursor hSourceFuel
                hBoundary hFuelBudget hReserve hSuccess
          | assign name value =>
              exact assign_of_recursive hSafety hRecursive cursor hSourceFuel
                hBoundary hFuelBudget hReserve hSuccess
          | block body =>
              exact block_of_recursive hRecursive cursor hSourceFuel hBoundary
                hFuelBudget hReserve hSuccess
          | if_ cond body =>
              exact if_of_recursive hSafety hRecursive cursor hBoundary
                hFuelBudget hReserve hSuccess
          | switch scrutinee cases defaultBody =>
              exact switch_of_recursive hSafety hRecursive cursor hBoundary
                hFuelBudget hReserve hSuccess
          | for_ init cond post body =>
              exact for_of_recursive hSafety hRecursive cursor hBoundary
                hFuelBudget hReserve hSuccess
          | brk =>
              exact brk_of_recursive hRecursive cursor hSourceFuel hBoundary
                hFuelBudget hReserve hSuccess
          | cont =>
              exact cont_of_recursive hRecursive cursor hSourceFuel hBoundary
                hFuelBudget hReserve hSuccess
          | leave =>
              exact leave_of_recursive hRecursive cursor hSourceFuel hBoundary
                hFuelBudget hReserve hSuccess
          | call targets functionName args =>
              exact call_of_recursive hProgramScoped hSafety hRecursive cursor
                hBoundary hFuelBudget hReserve hSuccess
          | terminal kind =>
              exact terminal_of_recursive hSafety hRecursive cursor hSourceFuel
                hBoundary hFuelBudget hReserve hSuccess
          | terminalArgs kind args =>
              exact terminalArgs_of_recursive hSafety hRecursive cursor
                hSourceFuel hBoundary hFuelBudget hReserve hSuccess

/-- Fuel-bounded root-polymorphic Functions preservation, with recursive calls
discharged internally from the successful source run. -/
theorem complete
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    (hProgramScoped : program.Scoped)
    (hSafety :
      AllocationInteractionSafety.SourceSafety program.memoryContract)
    (fuelBound : Nat) :
    RecursiveOpenRuntime (compilation := compilation)
      program.memoryContract compilation.recipe.frameWords fuelBound := by
  intro root scope live sourceBlock lowerState localsCtx config allocatorDepth
    frameBase sourceFuel targetExtra mode sourceCtx source target cursor
    _hFuelBound hBoundary hFuelBudget hReserve hSuccess
  exact complete_at hProgramScoped hSafety sourceFuel cursor hBoundary
    hFuelBudget hReserve hSuccess

end AllocationInteractionRecursiveRuntime
end Functions
end EvmCompiler
