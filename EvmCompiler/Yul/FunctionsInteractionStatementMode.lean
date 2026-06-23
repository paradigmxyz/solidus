import EvmCompiler.Yul.FunctionsInteractionPreparedConditionMode
import EvmCompiler.Yul.FunctionsInteractionStatement

/-!
Mode-parametric statement leaves for the adjacent Yul-to-Functions pass. The
outcome, scope, and control relations are shared with the ordinary proof; this
module selects only canonical ordinary or allocation-guarded handlers.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionStatementMode

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation
open FunctionsInteractionMode

abbrev ResultRel := FunctionsInteractionStatement.ResultRel
abbrev ScopedResultRel := FunctionsInteractionStatement.ScopedResultRel
abbrev PathScopedResultRel := FunctionsInteractionStatement.PathScopedResultRel
abbrev PathScopedDoneRel := FunctionsInteractionStatement.PathScopedDoneRel
abbrev ScopedDoneRel := FunctionsInteractionStatement.ScopedDoneRel

namespace ControlDoneRel

theorem singleton
    (mode : Mode)
    {used layout : List Functions.Name} {targetFuel : Nat}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {sourceOpen : Yul.InteractionSemantics.Open
      Yul.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {target : Functions.InteractionSemantics.State}
    (hStmt :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel used layout sourceScopes
          canBreak canContinue canLeave)
        sourceOpen
        (Target.Stmt.openRun mode program ctx
          (targetFuel + 1) stmt target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      sourceOpen
      (Target.Block.openRun mode program ctx
        (targetFuel + 2) { stmts := [stmt] } target) := by
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel used layout sourceScopes
          canBreak canContinue canLeave)
        (Simulation.Interaction.bind sourceOpen pure)
        (Simulation.Interaction.bind
          (Target.Stmt.openRun mode program ctx
            (targetFuel + 1) stmt target)
          fun targetResult =>
            match targetResult.1.mode with
            | .regular =>
                Target.Block.openRun mode program targetResult.2
                  (targetFuel + 1) { stmts := [] }
                  targetResult.1.state
            | .brk | .cont | .leave | .halt _ =>
                pure (targetResult.1, ctx)) := by
    apply Simulation.Interaction.ForwardRel.bind_custom hStmt
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError =>
        exact Simulation.Interaction.ForwardRel.done (.error hError)
    | regular hState hDomain hControl hTargetScope =>
        simp only [Simulation.Interaction.bind_done_ok]
        rw [Target.Block.openRun_nil]
        exact Simulation.Interaction.ForwardRel.done
          (.regular hState hDomain hControl hTargetScope)
    | brk hScope hMode hAbrupt =>
        simpa [hMode] using
          (Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.brk hScope hMode hAbrupt))
    | cont hScope hMode hAbrupt =>
        simpa [hMode] using
          (Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.cont hScope hMode hAbrupt))
    | leave hScope hMode hAbrupt =>
        simpa [hMode] using
          (Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.leave hScope hMode hAbrupt))
    | terminal hTerminal =>
        cases hTerminal with
        | stop hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.stop hState))
        | return_ hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.return_ hState))
        | selfdestruct hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.selfdestruct hState))
        | revert hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.revert hState))
  rw [show targetFuel + 2 = (targetFuel + 1) + 1 by omega,
    Target.Block.openRun_cons]
  have hSourceBind :
      Simulation.Interaction.bind sourceOpen pure = sourceOpen :=
    Simulation.Interaction.bind_pure sourceOpen
  rw [hSourceBind] at hBound
  simpa [Target.Stmt.openRun, Target.Block.openRun] using hBound

end ControlDoneRel

/-- Lift a zero-result expression relation through the Functions expression
statement wrapper in either primitive mode. -/
theorem expr_of_evalValues
    {mode : Mode} {fuel targetFuel : Nat}
    {expr : AstExpr} {lower : Locals.Expr 0}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {used layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hEval :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel source 0)
        (Source.evalValues mode fuel expr codeOverride source)
        (Target.Expr.openEval mode lower target))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin used target.vars)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetScope : TargetScopeWithin used ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        (Source.evalValues mode fuel expr codeOverride source)
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Target.Stmt.openRun mode program ctx targetFuel
        (.expr lower) target) := by
  rw [Target.Stmt.openRun_expr]
  have hEvalVars := hEval.strengthen_right
    (Target.Expr.openEval_vars_eq mode lower target)
  apply Simulation.Interaction.ForwardRel.bind_custom hEvalVars
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hDone, hTargetVars⟩
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | @ok sourceResult targetResult hResult =>
      have hState := hResult.1
      have hValues := hResult.2.1
      have hLength := hResult.2.2.1
      have hStore := hResult.2.2.2
      have hSourceValues : sourceResult.2 = [] :=
        List.eq_nil_of_length_eq_zero hLength
      have hTargetValues : targetResult.2 = [] := by
        rw [← hValues, hSourceValues]
      have hTargetVarsEq : targetResult.1.vars = target.vars := by
        simpa using hTargetVars
      have hScopedResult := ScopedStateRel.of_state_store_eq
        hRel hState hStore
      have hDomainResult : TargetDomainWithin used targetResult.1.vars := by
        simpa [hTargetVarsEq] using hDomain
      have hMultifillNil :
          Yul.InteractionSemantics.stateModel.multifill
              [] sourceResult.1 [] = sourceResult.1 := by
        cases sourceResult.1 <;> rfl
      simp only [hSourceValues, hTargetValues,
        Simulation.Interaction.bind_done_ok]
      rw [hMultifillNil]
      exact Simulation.Interaction.ForwardRel.done
        (.regular hScopedResult hDomainResult hControl hTargetScope)

/-- Final zero-result primitive statement after a compiler-owned argument
prelude has produced the exact target values. -/
theorem expr_after_args
    {mode : Mode} (hPrimitive : CompilerSelected mode)
    {primitiveFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {values : List Word}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {used layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target targetAfter : Functions.InteractionSemantics.State}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 0)
    (hLength : values.length = Expressions.Structured.BasicOp.inputs op)
    (hEval : Target.ExprSeq.openEval mode seq target =
      .done (.ok (targetAfter, values)))
    (hRel : ScopedStateRel layout source targetAfter)
    (hDomain : TargetDomainWithin used targetAfter.vars)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetScope : TargetScopeWithin used ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        ((sourcePrimitive mode).eval
          primitiveFuel source prim values.reverse)
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Target.Stmt.openRun mode program ctx targetFuel
        (.expr (Expr.cast hOutputs (.prim op seq))) target) := by
  rw [Target.Stmt.openRun_expr,
    FunctionsInteractionExpressionMode.expr_openEval_cast]
  unfold Target.Expr.openEval Locals.Source.Effectful.Expr.Control.eval
  unfold Target.ExprSeq.openEval at hEval
  rw [hEval]
  simp only [Simulation.Interaction.bind_done_ok,
    Simulation.Interaction.monad_pure_bind]
  have hArgsDone :
      FunctionsInteractionExpressionMode.DoneRel source
          (Expressions.Structured.BasicOp.inputs op)
          (.ok (source, values)) (.ok (targetAfter, values)) :=
    .ok (FunctionsInteractionExpression.ResultRel.of_state
      hRel.state hLength)
  have hArgsRel :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel source
          (Expressions.Structured.BasicOp.inputs op))
        (pure (source, values)) (pure (targetAfter, values)) :=
    Simulation.Interaction.ForwardRel.done hArgsDone
  have hPrimitiveRel :=
    FunctionsInteractionExpressionMode.Expr.primitive_of_args
      mode hPrimitive (primitiveFuel := primitiveFuel)
      hOp hOutputs hArgsRel
  have hEvalRel :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel source 0)
        ((sourcePrimitive mode).eval
          primitiveFuel source prim values.reverse)
        ((targetPrimitive mode).eval op targetAfter values) := by
    simpa using hPrimitiveRel
  have hEvalRelVars := hEvalRel.strengthen_right
    (targetPrimitive_eval_vars_eq mode op targetAfter values)
  apply Simulation.Interaction.ForwardRel.bind_custom hEvalRelVars
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hDone, hTargetVars⟩
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | @ok sourceResult targetResult hResult =>
      have hState := hResult.1
      have hValues := hResult.2.1
      have hResultLength := hResult.2.2.1
      have hStore := hResult.2.2.2
      have hSourceValues : sourceResult.2 = [] := by
        apply List.eq_nil_of_length_eq_zero
        exact hResultLength
      have hTargetValues : targetResult.2 = [] := by
        rw [← hValues, hSourceValues]
      have hTargetVarsEq : targetResult.1.vars = targetAfter.vars := by
        simpa using hTargetVars
      have hScopedResult := ScopedStateRel.of_state_store_eq
        hRel hState hStore
      have hDomainResult : TargetDomainWithin used targetResult.1.vars := by
        simpa [hTargetVarsEq] using hDomain
      have hMultifillNil :
          Yul.InteractionSemantics.stateModel.multifill
              [] sourceResult.1 [] = sourceResult.1 := by
        cases sourceResult.1 <;> rfl
      simp only [hSourceValues, hTargetValues,
        Simulation.Interaction.bind_done_ok]
      rw [hMultifillNil]
      exact Simulation.Interaction.ForwardRel.done
        (.regular hScopedResult hDomainResult hControl hTargetScope)

/-- Control-indexed terminal leaf after prepared arguments, at arbitrary source
primitive fuel and in either semantic mode. -/
theorem terminal_after_args_control
    {mode : Mode} {primitiveFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {kind : Assembly.HaltKind}
    {values : List Word} {seq : Locals.ExprSeq kind.argCount}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {used layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target targetAfter : Functions.InteractionSemantics.State}
    (hTerminal : Prim.terminal? prim = some kind)
    (hLength : values.length = kind.argCount)
    (hEval : Target.ExprSeq.openEval mode seq target =
      .done (.ok (targetAfter, values)))
    (hRel : ScopedStateRel layout source targetAfter) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        ((sourcePrimitive mode).eval
          primitiveFuel source prim values.reverse)
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Target.Stmt.openRun mode program ctx targetFuel
        (.terminalArgs kind seq) target) := by
  rw [Target.Stmt.openRun_terminalArgs, hEval,
    Simulation.Interaction.bind_done_ok]
  have hSourceLength : values.reverse.length = kind.argCount := by
    simpa [List.length_reverse] using hLength
  have hPrimitive := terminalSelectedAnyFuel mode
    (primitiveFuel := primitiveFuel)
    hTerminal hSourceLength hRel.state
  have hPrimitive' :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionTerminal.PrimitiveDoneRel kind)
        ((sourcePrimitive mode).eval
          primitiveFuel source prim values.reverse)
        ((targetPrimitive mode).terminal
          kind targetAfter values) := by
    simpa using hPrimitive
  apply Simulation.Interaction.ForwardRel.bind_custom hPrimitive'
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminalState =>
      exact Simulation.Interaction.ForwardRel.done
        (.terminal hTerminalState)

end FunctionsInteractionStatementMode
end Yul
end EvmCompiler
