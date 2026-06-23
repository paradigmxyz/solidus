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

end FunctionsInteractionPreparedStatementMode
end Yul
end EvmCompiler
