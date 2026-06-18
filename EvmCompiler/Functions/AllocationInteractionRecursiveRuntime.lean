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
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          (sourceFuel - 1) sourceBlock source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase
      (sourceFuel - 1) targetExtra mode sourceCtx source target := by
  exact hRecursive cursor (by omega) hBoundary
    (AllocationInteractionFrame.Budget.mono (by omega) hFuelBudget) hSuccess

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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (fun {afterState afterLocals} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
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
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .block body :: rest } source)) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  exact CursorRuntimeAt.block cursor hSourceFuel hBoundary hSuccess
    (fun bodyCursor bodyExtra hBodyBoundary hBodySuccess =>
      hRecursive bodyCursor (by omega) hBodyBoundary
        (AllocationInteractionFrame.Budget.mono (by omega) hFuelBudget)
        hBodySuccess)
    (fun {afterState} tail _hExact
        {sourceMid targetMid tailMode} hTailBoundary hTailSuccess =>
      recursive_tail hRecursive tail hSourceFuel hTailBoundary hFuelBudget
        hTailSuccess)

end AllocationInteractionRecursiveRuntime
end Functions
end EvmCompiler
