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

namespace InitNames

theorem openRun_extra (mode : Mode)
    (names : List Functions.Name)
    (program : Functions.Program)
    (target : Functions.InteractionSemantics.State)
    (ctx : Functions.Source.Ctx) (extra : Nat) :
    ∃ finalVars,
      Functions.Source.Store.insertMany names
          (names.map fun _name => Functions.Source.zero)
          target.vars = some finalVars ∧
      Target.Block.openRun mode program ctx (names.length + extra + 1)
          { stmts := Stmt.initNames names } target =
        pure
          (Functions.Source.Effectful.Outcome.regular
            { shared := target.shared, vars := finalVars },
            { ctx with scope := names.reverse ++ ctx.scope }) := by
  induction names generalizing target ctx with
  | nil =>
      refine ⟨target.vars, rfl, ?_⟩
      simpa [Stmt.initNames] using
        (Target.Block.openRun_nil mode program ctx extra target)
  | cons name rest ih =>
      let targetHead := target.insert name Functions.Source.zero
      let ctxHead := { ctx with scope := name :: ctx.scope }
      obtain ⟨finalVars, hInsert, hTail⟩ :=
        ih (target := targetHead) (ctx := ctxHead)
      refine ⟨finalVars, ?_, ?_⟩
      · simpa [Functions.Source.Store.insertMany, targetHead,
          Locals.Source.State.insert] using hInsert
      · change
          Target.Block.openRun mode program ctx
              ((name :: rest).length + extra + 1)
                { stmts :=
                    .let_ name (.lit Stmt.zero) :: Stmt.initNames rest }
                target = _
        have hHead := Target.Stmt.openRun_let_lit mode program ctx
          (rest.length + extra + 1) name Stmt.zero target
        rw [show (name :: rest).length + extra + 1 =
              (rest.length + extra + 1) + 1 by simp; omega,
          Target.Block.openRun_cons, hHead]
        change
          Target.Block.openRun mode program ctxHead
            (rest.length + extra + 1)
            { stmts := Stmt.initNames rest } targetHead = _
        rw [hTail]
        simp [targetHead, ctxHead, Stmt.initNames,
          List.reverse_cons, List.append_assoc]

end InitNames

theorem let_one
    {mode : Mode} {fuel targetFuel : Nat}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {lower : Locals.Expr 1}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 valueExpr = some lower)
    (hFresh : name ∉ layout)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ScopedDoneRel (name :: layout)
        { ctx with scope := name :: ctx.scope })
      (Source.exec mode fuel
        (.Let [name] (some valueExpr)) codeOverride source)
      (Target.Stmt.openRun mode program ctx targetFuel
        (.let_ name lower) target) := by
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Source.exec_zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ScopedDoneRel (name :: layout)
            { ctx with scope := name :: ctx.scope })
          (right := Target.Stmt.openRun mode program ctx targetFuel
            (.let_ name lower) target)
          hTruncated)
  | succ exprFuel =>
      have hCheck := ScopedStateRel.declarationCheck hRel hFresh
      rw [Source.exec_let_one_succ mode exprFuel name valueExpr
          codeOverride source hCheck,
        Target.Stmt.openRun_let]
      have hEval :=
        (FunctionsInteractionExpressionMode.compilerDirectAt
          mode codeOverride exprFuel).evalValues hLower hRel.state
      apply Simulation.Interaction.ForwardRel.bind hEval
      intro sourceResult targetResult hResult
      rcases hResult with ⟨hState, hValues, hLength, hStore⟩
      obtain ⟨value, hSourceValues⟩ := List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hValues, hSourceValues]
      have hScopedAfterExpr :=
        ScopedStateRel.of_state_store_eq hRel hState hStore
      have hFinal :=
        ScopedStateRel.multifill_single_cons hScopedAfterExpr name value
      have hDone :
          ScopedDoneRel (name :: layout)
              { ctx with scope := name :: ctx.scope }
            (.ok (sourceResult.1.multifill [name] [value]))
            (.ok
              (Functions.Source.Effectful.Outcome.regular
                  (targetResult.1.insert name value),
                { ctx with scope := name :: ctx.scope })) :=
        .ok ⟨ScopedOutcomeRel.regular hFinal, rfl⟩
      rw [hSourceValues, hTargetValues]
      simpa [Yul.InteractionSemantics.stateModel,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.insert] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

theorem assign_one
    {mode : Mode} {fuel targetFuel : Nat}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {lower : Locals.Expr 1}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 valueExpr = some lower)
    (hName : name ∈ layout)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
      (Source.exec mode fuel (.Assign [name] valueExpr) codeOverride source)
      (Target.Stmt.openRun mode program ctx targetFuel
        (.assign name lower) target) := by
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Source.exec_zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ScopedDoneRel layout ctx)
          (right := Target.Stmt.openRun mode program ctx targetFuel
            (.assign name lower) target)
          hTruncated)
  | succ exprFuel =>
      have hCheck := ScopedStateRel.assignmentCheck hRel hName
      have hContains := ScopedStateRel.targetContains hRel hName
      rw [Source.exec_assign_one_succ mode exprFuel name valueExpr
          codeOverride source hCheck,
        Target.Stmt.openRun_assign_of_contains mode program ctx targetFuel
          name lower target hContains]
      rw [Target.Expr.openEvalOne_eq_bind,
        Simulation.Interaction.bind_assoc]
      have hEval :=
        (FunctionsInteractionExpressionMode.compilerDirectAt
          mode codeOverride exprFuel).evalValues hLower hRel.state
      apply Simulation.Interaction.ForwardRel.bind hEval
      intro sourceResult targetResult hResult
      rcases hResult with ⟨hState, hValues, hLength, hStore⟩
      obtain ⟨value, hSourceValues⟩ := List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hValues, hSourceValues]
      have hScopedAfterExpr :=
        ScopedStateRel.of_state_store_eq hRel hState hStore
      have hFinal :=
        ScopedStateRel.multifill_single_visible hScopedAfterExpr hName value
      have hDone :
          ScopedDoneRel layout ctx
            (.ok (sourceResult.1.multifill [name] [value]))
            (.ok
              (Functions.Source.Effectful.Outcome.regular
                (targetResult.1.insert name value), ctx)) :=
        .ok ⟨ScopedOutcomeRel.regular hFinal, rfl⟩
      rw [hSourceValues, hTargetValues]
      simpa [Yul.InteractionSemantics.stateModel,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.withVars,
        Locals.Source.State.withVars] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

theorem brk_control
    {mode : Mode} {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {used layout : List Functions.Name} {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hEnabled : canBreak = true)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode fuel .Break codeOverride source)
      (Target.Stmt.openRun mode program ctx targetFuel .brk target) := by
  have hBreakRel : ScopeOptionRel true sourceScopes.breakScope?
      ctx.breakScope? layout := by
    simpa [hEnabled] using hControl.breakScope
  obtain ⟨sourceScope, targetScope, hSourceScope, hTargetScope,
      hCurrent, hTarget, hTargetUsed⟩ := ScopeOptionRel.enabled_parts hBreakRel
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Source.exec_zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ControlDoneRel used layout sourceScopes
            canBreak canContinue canLeave)
          (right := Target.Stmt.openRun mode program ctx targetFuel .brk target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
      subst source
      have hAbrupt := AbruptOutcomeRel.brk hRel hCurrent hTarget hTargetUsed
      rw [Source.exec_brk_succ,
        Target.Stmt.openRun_brk mode program ctx targetFuel target hTargetScope]
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.brk hSourceScope rfl hAbrupt)

theorem cont_control
    {mode : Mode} {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {used layout : List Functions.Name} {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hEnabled : canContinue = true)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode fuel .Continue codeOverride source)
      (Target.Stmt.openRun mode program ctx targetFuel .cont target) := by
  have hContinueRel : ScopeOptionRel true sourceScopes.continueScope?
      ctx.continueScope? layout := by
    simpa [hEnabled] using hControl.continueScope
  obtain ⟨sourceScope, targetScope, hSourceScope, hTargetScope,
      hCurrent, hTarget, hTargetUsed⟩ :=
    ScopeOptionRel.enabled_parts hContinueRel
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Source.exec_zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ControlDoneRel used layout sourceScopes
            canBreak canContinue canLeave)
          (right := Target.Stmt.openRun mode program ctx targetFuel .cont target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
      subst source
      have hAbrupt := AbruptOutcomeRel.cont hRel hCurrent hTarget hTargetUsed
      rw [Source.exec_cont_succ,
        Target.Stmt.openRun_cont mode program ctx targetFuel target hTargetScope]
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.cont hSourceScope rfl hAbrupt)

theorem leave_control
    {mode : Mode} {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {used layout : List Functions.Name} {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hEnabled : canLeave = true)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode fuel .Leave codeOverride source)
      (Target.Stmt.openRun mode program ctx targetFuel .leave target) := by
  have hLeaveRel : ScopeOptionRel true sourceScopes.leaveScope?
      ctx.leaveScope? layout := by
    simpa [hEnabled] using hControl.leaveScope
  obtain ⟨sourceScope, targetScope, hSourceScope, hTargetScope,
      hCurrent, hTarget, hTargetUsed⟩ := ScopeOptionRel.enabled_parts hLeaveRel
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Source.exec_zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ControlDoneRel used layout sourceScopes
            canBreak canContinue canLeave)
          (right := Target.Stmt.openRun mode program ctx targetFuel .leave target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
      subst source
      have hAbrupt := AbruptOutcomeRel.leave hRel hCurrent hTarget hTargetUsed
      rw [Source.exec_leave_succ,
        Target.Stmt.openRun_leave mode program ctx targetFuel target hTargetScope]
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.leave hSourceScope rfl hAbrupt)

theorem compiled_let_none_control_extra
    {mode : Mode} {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {names : List EvmYul.Identifier}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name} {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.Let names none) = some (lower, after))
    (hNoDup : (identNames names).Nodup)
    (hFresh : ∀ name, name ∈ identNames names → name ∉ layout)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hNames : ∀ name, name ∈ identNames names → name ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hTargetFuel : names.length + 1 ≤ targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used (identNames names ++ layout) sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode (fuel + 1) (.Let names none) codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := lower } target) := by
  have hExtends := Stmt.toFunctionsListUncheckedFuel?_stateExtends hLower
  rcases Stmt.toFunctionsListUncheckedFuel?_let_none_parts hLower with
    ⟨rfl, rfl⟩
  have hCheck : EvmYul.Yul.checkDeclaration source names = .ok () := by
    simpa [identNames_eq_self] using
      ScopedStateRel.declarationCheck_many hRel hNoDup hFresh
  let extra := targetFuel - names.length - 1
  have hFuelEq : names.length + extra + 1 = targetFuel := by
    dsimp [extra]
    omega
  obtain ⟨finalVars, hInsert, hTargetRun⟩ :=
    InitNames.openRun_extra mode (identNames names) program target ctx extra
  have hFinalRel : ScopedStateRel (identNames names ++ layout)
      (source.zeroFill names)
      { shared := target.shared, vars := finalVars } := by
    simpa [identNames_eq_self] using
      hRel.zeroFill_insertMany hNoDup hFresh hInsert
  have hFinalDomain : TargetDomainWithin after.used finalVars :=
    TargetDomainWithin.insertMany_used hDomain hNames hInsert
  let finalCtx : Functions.Source.Ctx :=
    { ctx with scope := (identNames names).reverse ++ ctx.scope }
  have hFinalControl : ControlContextRel sourceScopes
      (identNames names ++ layout) canBreak canContinue canLeave finalCtx := by
    apply ControlContextRel.transport hControl
    · intro candidate hMem
      exact List.mem_append_right _ hMem
    · simpa [finalCtx] using
        (Functions.Source.Ctx.SameControl.scopeUpdate ctx
          ((identNames names).reverse ++ ctx.scope))
    · intro candidate hMem
      rcases List.mem_append.mp hMem with hNames | hLayoutName
      · exact List.mem_append_left _ (List.mem_reverse.mpr hNames)
      · exact List.mem_append_right _
          (hControl.scope candidate hLayoutName)
  have hFinalScope : TargetScopeWithin after.used finalCtx := by
    intro candidate hMem
    rcases List.mem_append.mp hMem with hDeclared | hOuter
    · exact hExtends candidate
        (hNames candidate (List.mem_reverse.mp hDeclared))
    · exact hExtends candidate (hTargetScope candidate hOuter)
  rw [Source.exec_let_none_succ mode fuel names codeOverride source hCheck]
  have hTargetRun' :
      Target.Block.openRun mode program ctx targetFuel
          { stmts := Stmt.initNames (identNames names) } target =
        pure
          (Functions.Source.Effectful.Outcome.regular
            { shared := target.shared, vars := finalVars }, finalCtx) := by
    simpa [identNames_eq_self, finalCtx, hFuelEq] using hTargetRun
  rw [hTargetRun']
  simpa [identNames_eq_self] using
    (Simulation.Interaction.ForwardRel.done
      (ControlDoneRel.regular hFinalRel hFinalDomain hFinalControl hFinalScope))

theorem compiled_brk_control
    {mode : Mode} {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name} {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Break =
      some (lower, after))
    (hEnabled : canBreak = true)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode fuel .Break codeOverride source)
      (Target.Block.openRun mode program ctx (targetFuel + 2)
        { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_break_parts hLower with
    ⟨rfl, rfl⟩
  apply ControlDoneRel.singleton mode
  exact brk_control hEnabled hControl hRel

theorem compiled_cont_control
    {mode : Mode} {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name} {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Continue =
      some (lower, after))
    (hEnabled : canContinue = true)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode fuel .Continue codeOverride source)
      (Target.Block.openRun mode program ctx (targetFuel + 2)
        { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_continue_parts hLower with
    ⟨rfl, rfl⟩
  apply ControlDoneRel.singleton mode
  exact cont_control hEnabled hControl hRel

theorem compiled_leave_control
    {mode : Mode} {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name} {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Leave =
      some (lower, after))
    (hEnabled : canLeave = true)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode fuel .Leave codeOverride source)
      (Target.Block.openRun mode program ctx (targetFuel + 2)
        { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_leave_parts hLower with
    ⟨rfl, rfl⟩
  apply ControlDoneRel.singleton mode
  exact leave_control hEnabled hControl hRel

/-- Final visible assignment after a compiler-owned argument prelude has
produced the exact primitive inputs. This leaf handles arbitrary primitive fuel,
including guarded failures that precede ordinary fuel exhaustion. -/
theorem assign_after_args
    {mode : Mode} (hPrimitive : CompilerSelected mode)
    {primitiveFuel targetFuel : Nat}
    {name : EvmYul.Identifier}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {values : List Word}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {used layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 1)
    (hLength : values.length = Expressions.Structured.BasicOp.inputs op)
    (hEval : Target.ExprSeq.openEval mode seq target =
      .done (.ok (target, values)))
    (hName : identName name ∈ layout)
    (hNameUsed : identName name ∈ used)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin used target.vars)
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
              [name] result.1 result.2)))
      (Target.Stmt.openRun mode program ctx targetFuel
        (.assign (identName name)
          (Expr.cast hOutputs (.prim op seq))) target) := by
  have hTargetEval :
      Target.Expr.openEval mode
          (Expr.cast hOutputs (.prim op seq)) target =
        (targetPrimitive mode).eval op target values := by
    rw [FunctionsInteractionExpressionMode.expr_openEval_cast]
    unfold Target.Expr.openEval Locals.Source.Effectful.Expr.Control.eval
    unfold Target.ExprSeq.openEval at hEval
    rw [hEval]
    rfl
  have hArgsDone :
      FunctionsInteractionExpressionMode.DoneRel source
          (Expressions.Structured.BasicOp.inputs op)
          (.ok (source, values)) (.ok (target, values)) :=
    .ok (FunctionsInteractionExpression.ResultRel.of_state
      hRel.state hLength)
  have hArgsRel :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel source
          (Expressions.Structured.BasicOp.inputs op))
        (pure (source, values)) (pure (target, values)) :=
    Simulation.Interaction.ForwardRel.done hArgsDone
  have hPrimitiveRel :=
    FunctionsInteractionExpressionMode.Expr.primitive_of_args
      mode hPrimitive (primitiveFuel := primitiveFuel)
      hOp hOutputs hArgsRel
  have hEvalRel :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel source 1)
        ((sourcePrimitive mode).eval
          primitiveFuel source prim values.reverse)
        ((targetPrimitive mode).eval op target values) := by
    simpa using hPrimitiveRel
  have hEvalRelVars := hEvalRel.strengthen_right
    (targetPrimitive_eval_vars_eq mode op target values)
  have hContains := hRel.targetContains hName
  rw [Target.Stmt.openRun_assign_of_contains mode program ctx targetFuel
    (identName name) (Expr.cast hOutputs (.prim op seq)) target hContains]
  rw [Target.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc, hTargetEval]
  apply Simulation.Interaction.ForwardRel.bind_custom hEvalRelVars
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hDone, hTargetVars⟩
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.error hError)
  | @ok sourceResult targetResult hResult =>
      have hResultLength : sourceResult.2.length = 1 := hResult.2.2.1
      obtain ⟨value, hSourceValues⟩ :=
        List.length_eq_one_iff.mp hResultLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hResult.2.1, hSourceValues]
      simp only [Simulation.Interaction.bind_done_ok]
      rw [hSourceValues, hTargetValues]
      have hFinalScoped :=
        ScopedStateRel.of_state_store_eq hRel hResult.1 hResult.2.2.2
      have hFinal :=
        hFinalScoped.multifill_single_visible hName value
      have hTargetVarsEq : targetResult.1.vars = target.vars := by
        simpa using hTargetVars
      have hDomainResult : TargetDomainWithin used targetResult.1.vars := by
        simpa [hTargetVarsEq] using hDomain
      have hFinalDomain : TargetDomainWithin used
          (targetResult.1.insert (identName name) value).vars :=
        hDomainResult.insert_used hNameUsed value
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.regular hFinal hFinalDomain hControl hTargetScope)

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
