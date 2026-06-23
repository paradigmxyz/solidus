import EvmCompiler.Yul.FunctionsInteractionStatementMode

/-!
Mode-parametric declaration and assignment bridges over compiler-prepared
one-result conditions. Expression preparation and target sequencing remain
owned by `FunctionsInteractionPreparedConditionMode`.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedStatementMode

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation
open FunctionsInteractionMode

theorem letOneOfCondition
    {mode : Mode} {exprFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {used layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    (hNameFresh : identName name ∉ layout)
    (hNameUsed : identName name ∈ used)
    (hRel : ScopedStateRel layout source target)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hCondition :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedConditionMode.DoneRel layout used ctx)
        (Source.evalValues mode exprFuel expr codeOverride source)
        (FunctionsInteractionPreparedConditionMode.run
          mode program ctx targetFuel pre lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used (identName name :: layout) sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode (exprFuel + 1)
        (.Let [name] (some expr)) codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++ [.let_ (identName name) lower] } target) := by
  have hCheck := hRel.declarationCheck hNameFresh
  rw [Source.exec_let_one_succ mode exprFuel name expr codeOverride source hCheck,
    FunctionsInteractionPreparedConditionMode.run_let mode program ctx
      targetFuel pre (identName name) lower target hTargetFuel]
  apply Simulation.Interaction.ForwardRel.bind_custom hCondition
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.revert hState))
  | @regular sourceAfter values targetAfter truth ctxAfter value
      hValues _hTruth hScoped hDomain hScope hSameControl hTargetScopeAfter =>
      subst values
      simp only [Simulation.Interaction.bind_done_ok]
      let targetFinal := targetAfter.insert (identName name) value
      let ctxFinal :=
        { ctxAfter with scope := identName name :: ctxAfter.scope }
      have hFinal := hScoped.multifill_single_cons (identName name) value
      have hFinalDomain : TargetDomainWithin used targetFinal.vars :=
        hDomain.insert_used hNameUsed value
      have hFinalCtx : ControlContextRel sourceScopes
          (identName name :: layout)
          canBreak canContinue canLeave ctxFinal := by
        apply ControlContextRel.transport hControl
        · intro candidate hMem
          exact List.mem_cons_of_mem _ hMem
        · exact Functions.Source.Ctx.SameControl.trans hSameControl
            (Functions.Source.Ctx.SameControl.scopeUpdate
              ctxAfter (identName name :: ctxAfter.scope))
        · intro candidate hMem
          rcases List.mem_cons.mp hMem with rfl | hTail
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (hScope candidate (hControl.scope candidate hTail))
      have hFinalTargetScope : TargetScopeWithin used ctxFinal := by
        intro candidate hMem
        change candidate ∈ identName name :: ctxAfter.scope at hMem
        rcases List.mem_cons.mp hMem with rfl | hTail
        · exact hNameUsed
        · exact hTargetScopeAfter candidate hTail
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.regular hFinal hFinalDomain hFinalCtx
          hFinalTargetScope)

theorem assignOneOfConditionDirect
    {mode : Mode} {exprFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {lower : Locals.Expr 1}
    {used layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    (hName : identName name ∈ layout)
    (hNameUsed : identName name ∈ used)
    (hRel : ScopedStateRel layout source target)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel : 1 < targetFuel)
    (hCondition :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedConditionMode.DoneRel layout used ctx)
        (Source.evalValues mode exprFuel expr codeOverride source)
        (FunctionsInteractionPreparedConditionMode.run
          mode program ctx targetFuel [] lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode (exprFuel + 1)
        (.Assign [name] expr) codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := [.assign (identName name) lower] } target) := by
  have hCheck := hRel.assignmentCheck hName
  have hContains := hRel.targetContains hName
  rw [Source.exec_assign_one_succ mode exprFuel name expr codeOverride source
      hCheck,
    FunctionsInteractionPreparedConditionMode.run_assign_nil mode program ctx
      targetFuel (identName name) lower target hTargetFuel hContains]
  apply Simulation.Interaction.ForwardRel.bind_custom hCondition
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.revert hState))
  | @regular sourceAfter values targetAfter truth ctxAfter value
      hValues _hTruth hScoped hDomain hScope hSameControl hTargetScopeAfter =>
      subst values
      simp only [Simulation.Interaction.bind_done_ok]
      let targetFinal := targetAfter.insert (identName name) value
      have hFinal := hScoped.multifill_single_visible hName value
      have hFinalDomain : TargetDomainWithin used targetFinal.vars :=
        hDomain.insert_used hNameUsed value
      have hFinalCtx : ControlContextRel sourceScopes layout
          canBreak canContinue canLeave ctxAfter := by
        apply ControlContextRel.transport hControl
        · exact fun _candidate hMem => hMem
        · exact hSameControl
        · intro candidate hMem
          exact hScope candidate (hControl.scope candidate hMem)
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.regular hFinal hFinalDomain hFinalCtx
          hTargetScopeAfter)

theorem assignOneOfPreparedPrimitive
    {mode : Mode} (hPrimitive : CompilerSelected mode)
    {argsFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {prim : EvmYul.Operation .Yul}
    {args : List AstExpr} {op : Structured.BasicOp}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {final : Fresh.State} {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    (hName : identName name ∈ layout)
    (hNameUsed : identName name ∈ final.used)
    (hRel : ScopedStateRel layout source target)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hSeq : Expr.List.toStackSeq? lowerArgs
      (Expressions.Structured.BasicOp.inputs op) = some seq)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 1)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgsMode.DoneRel
          mode layout final lowerArgs.reverse target ctx)
        (Source.evalArgs mode argsFuel args.reverse codeOverride source)
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode (argsFuel + 2)
        (.Assign [name] (.Call (.inl prim) args)) codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++
            [.assign (identName name)
              (Expr.cast hOutputs (.prim op seq))] } target) := by
  have hCheck := hRel.assignmentCheck hName
  rw [show argsFuel + 2 = (argsFuel + 1) + 1 by omega,
    Source.exec_assign_one_succ mode (argsFuel + 1) name
      (.Call (.inl prim) args) codeOverride source hCheck,
    Target.Block.openRun_append]
  unfold Source.evalValues Yul.Source.Canonical.evalValues
    Yul.Source.Effectful.evalValues
  change
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used layout sourceScopes
        canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Source.evalArgs mode argsFuel args.reverse codeOverride source)
          (fun argsResult =>
            (sourcePrimitive mode).eval argsFuel argsResult.1
              prim argsResult.2.reverse))
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [name] result.1 result.2)))
      (Simulation.Interaction.bind
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre } target)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Target.Block.openRun mode program result.2
                (targetFuel - pre.length)
                { stmts :=
                    [.assign (identName name)
                      (Expr.cast hOutputs (.prim op seq))] }
                result.1.state
          | .brk | .cont | .leave | .halt _ => pure result))
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.revert hState))
  | @regular sourceAfter values targetAfter ctxAfter
      hStable hScoped hDomain _hExtends hScope hSameControl
      hTargetScopeAfter =>
      simp only [Simulation.Interaction.bind_done_ok]
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hLength :
          values.length = Expressions.Structured.BasicOp.inputs op :=
        hStable.length.trans (Expr.List.toSeq?_length hDirectSeq)
      have hEval := hStable.exprSeq_openEval hDirectSeq
        (TargetExtends.refl targetAfter.vars)
      have hControlAfter : ControlContextRel sourceScopes layout
          canBreak canContinue canLeave ctxAfter := by
        apply ControlContextRel.transport hControl
        · exact fun _candidate hMem => hMem
        · exact hSameControl
        · intro candidate hMem
          exact hScope candidate (hControl.scope candidate hMem)
      have hStmt := FunctionsInteractionStatementMode.assign_after_args
        hPrimitive (mode := mode) (program := program) (ctx := ctxAfter)
        (primitiveFuel := argsFuel)
        (targetFuel := targetFuel - pre.length - 1)
        hOp hOutputs hLength hEval hName hNameUsed hScoped hDomain
        hControlAfter hTargetScopeAfter
      have hTailFuel : 2 ≤ targetFuel - pre.length := by omega
      have hStmt' :
          Simulation.Interaction.ForwardRel Truncated
            (ControlDoneRel final.used layout sourceScopes
              canBreak canContinue canLeave)
            (Simulation.Interaction.bind
              ((sourcePrimitive mode).eval
                argsFuel sourceAfter prim values.reverse)
              (fun result =>
                pure
                  (Yul.InteractionSemantics.stateModel.multifill
                    [name] result.1 result.2)))
            (Target.Stmt.openRun mode program ctxAfter
              ((targetFuel - pre.length - 2) + 1)
              (.assign (identName name)
                (Expr.cast hOutputs (.prim op seq))) targetAfter) := by
        have hStmtFuelEq :
            targetFuel - pre.length - 1 =
              (targetFuel - pre.length - 2) + 1 := by omega
        simpa only [hStmtFuelEq] using hStmt
      have hSingleton :=
        FunctionsInteractionStatementMode.ControlDoneRel.singleton
          mode (targetFuel := targetFuel - pre.length - 2) hStmt'
      simpa [hTailFuel] using hSingleton

end FunctionsInteractionPreparedStatementMode
end Yul
end EvmCompiler
