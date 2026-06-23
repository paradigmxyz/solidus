import EvmCompiler.Functions.AllocationInteractionRecursiveCallResource
import EvmCompiler.Functions.AllocationInteractionSuccessful

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursiveRuntime

open AllocationInteractionCursor
open AllocationInteractionFrame
open AllocationInteractionRelation
open AllocationInteractionRecursive
open AllocationInteractionRecursiveResource
open AllocationInteractionSuccessful


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
    (hSafety : AllocationInteractionSafety.SourceSafety contract)
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
  exact False.elim
    (AllocationInteractionSafety.SourceSafety.uninhabited contract hSafety)

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
  exact False.elim
    (AllocationInteractionSafety.SourceSafety.uninhabited contract hSafety)

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
  exact False.elim
    (AllocationInteractionSafety.SourceSafety.uninhabited contract hSafety)

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
  exact False.elim
    (AllocationInteractionSafety.SourceSafety.uninhabited contract hSafety)

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
  exact False.elim
    (AllocationInteractionSafety.SourceSafety.uninhabited
      program.memoryContract hSafety)

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
              exact block_of_recursive hSafety hRecursive cursor hSourceFuel
                hBoundary hFuelBudget hReserve hSuccess
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
