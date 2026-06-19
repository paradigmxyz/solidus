import EvmCompiler.Yul.FunctionsInteractionRecursiveExpression

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedStatement

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation

/-- Attach a one-result declaration directly to the exact-value prepared
condition interface. This is the statement-owned bridge used by the recursive
dispatcher; expression recursion remains entirely in `recursiveCondition`. -/
theorem letOneOfCondition
    {exprFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {used : List Functions.Name} {layout : List Functions.Name}
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
        (FunctionsInteractionPreparedCondition.DoneRel layout used ctx)
        (Yul.InteractionSemantics.evalValues
          exprFuel expr codeOverride source)
        (FunctionsInteractionPreparedCondition.run
          program ctx targetFuel pre lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used (identName name :: layout) sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (exprFuel + 1)
        (.Let [name] (some expr)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
        { stmts := pre ++ [.let_ (identName name) lower] } target) := by
  have hCheck := hRel.declarationCheck hNameFresh
  rw [Yul.InteractionSemantics.Exec.let_one_succ
      exprFuel name expr codeOverride source hCheck,
    FunctionsInteractionPreparedCondition.run_let
      program ctx targetFuel pre (identName name) lower target hTargetFuel]
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

/-- Attach the final source-visible declaration emitted after any recursively
prepared one-result expression. The prelude may contain primitive effects or
nested internal calls; terminal outcomes skip the declaration on both sides. -/
theorem letOneOfPrepared
    {exprFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {fresh : Fresh.State} {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    (hNameFresh : identName name ∉ layout)
    (hNameUsed : identName name ∈ fresh.used)
    (hRel : ScopedStateRel layout source target)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTailFuel : pre.length + 1 < targetFuel)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgs.DoneRel
          layout fresh [lower] target ctx)
        (Yul.InteractionSemantics.evalValues
          exprFuel expr codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel fresh.used (identName name :: layout) sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (exprFuel + 1)
        (.Let [name] (some expr)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
        { stmts := pre ++ [.let_ (identName name) lower] } target) := by
  have hCheck := hRel.declarationCheck hNameFresh
  rw [Yul.InteractionSemantics.Exec.let_one_succ
      exprFuel name expr codeOverride source hCheck,
    Functions.InteractionSemantics.Block.openRun_append]
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
      hStable hScoped hDomain _hExtends hScopeCtx hSameCtx
      hTargetScopeAfter =>
      have hLength : values.length = 1 := by
        simpa using hStable.length
      obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLength
      cases hStable with
      | cons hStableValue _hTail =>
          have hEval := hStableValue targetAfter
            (TargetExtends.refl targetAfter.vars)
          have hEval' :
              Functions.InteractionSemantics.Expr.openEval lower targetAfter =
                .done (.ok (targetAfter, [value])) := by
            simpa [Functions.InteractionSemantics.Expr.openEval] using hEval
          obtain ⟨remaining, hResidual⟩ :
              ∃ remaining, targetFuel - pre.length = remaining + 2 := by
            refine ⟨targetFuel - pre.length - 2, ?_⟩
            omega
          let targetFinal := targetAfter.insert (identName name) value
          let ctxFinal :=
            { ctxAfter with scope := identName name :: ctxAfter.scope }
          have hTargetLet :
              Functions.InteractionSemantics.Block.openRun
                  program ctxAfter (targetFuel - pre.length)
                  { stmts := [.let_ (identName name) lower] } targetAfter =
                pure
                  (Functions.Source.Effectful.Outcome.regular targetFinal,
                    ctxFinal) := by
            rw [hResidual,
              show remaining + 2 = (remaining + 1) + 1 by omega,
              Functions.InteractionSemantics.Block.openRun_cons]
            change
              Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Stmt.openRun
                    program ctxAfter (remaining + 1)
                    (.let_ (identName name) lower) targetAfter) _ = _
            rw [Functions.InteractionSemantics.Stmt.openRun_let,
              hEval', Simulation.Interaction.bind_done_ok]
            simp only [Simulation.Interaction.monad_pure_bind]
            change
              Functions.InteractionSemantics.Block.openRun
                  program ctxFinal (remaining + 1) { stmts := [] }
                  targetFinal =
                pure
                  (Functions.Source.Effectful.Outcome.regular targetFinal,
                    ctxFinal)
            rw [Functions.InteractionSemantics.Block.openRun_nil]
          change
            Simulation.Interaction.ForwardRel Truncated
              (ControlDoneRel fresh.used (identName name :: layout) sourceScopes
                canBreak canContinue canLeave)
              (pure (sourceAfter.multifill [name] [value]))
              (Functions.InteractionSemantics.Block.openRun
                program ctxAfter (targetFuel - pre.length)
                { stmts := [.let_ (identName name) lower] } targetAfter)
          rw [hTargetLet]
          have hFinal := hScoped.multifill_single_cons
            (identName name) value
          have hFinalDomain : TargetDomainWithin fresh.used targetFinal.vars :=
            hDomain.insert_used hNameUsed value
          have hFinalCtx : ControlContextRel sourceScopes
              (identName name :: layout)
              canBreak canContinue canLeave ctxFinal := by
            apply ControlContextRel.transport hControl
            · intro candidate hMem
              exact List.mem_cons_of_mem _ hMem
            · exact Functions.Source.Ctx.SameControl.trans hSameCtx
                (Functions.Source.Ctx.SameControl.scopeUpdate
                  ctxAfter (identName name :: ctxAfter.scope))
            · intro candidate hMem
              rcases List.mem_cons.mp hMem with rfl | hTail
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _
                  (hScopeCtx candidate (hControl.scope candidate hTail))
          have hFinalTargetScope : TargetScopeWithin fresh.used ctxFinal := by
            intro candidate hMem
            change candidate ∈ identName name :: ctxAfter.scope at hMem
            rcases List.mem_cons.mp hMem with rfl | hTail
            · exact hNameUsed
            · exact hTargetScopeAfter candidate hTail
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.regular hFinal hFinalDomain hFinalCtx
              hFinalTargetScope)

/-- Attach the final source-visible assignment emitted after any recursively
prepared one-result expression. -/
theorem assignOneOfPrepared
    {exprFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {fresh : Fresh.State} {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    (hName : identName name ∈ layout)
    (hNameUsed : identName name ∈ fresh.used)
    (hRel : ScopedStateRel layout source target)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTailFuel : pre.length + 1 < targetFuel)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgs.DoneRel
          layout fresh [lower] target ctx)
        (Yul.InteractionSemantics.evalValues
          exprFuel expr codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel fresh.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (exprFuel + 1)
        (.Assign [name] expr) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
        { stmts := pre ++ [.assign (identName name) lower] } target) := by
  have hCheck := hRel.assignmentCheck hName
  rw [Yul.InteractionSemantics.Exec.assign_one_succ
      exprFuel name expr codeOverride source hCheck,
    Functions.InteractionSemantics.Block.openRun_append]
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
      hStable hScoped hDomain _hExtends hScopeCtx hSameCtx
      hTargetScopeAfter =>
      have hLength : values.length = 1 := by
        simpa using hStable.length
      obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLength
      cases hStable with
      | cons hStableValue _hTail =>
          have hEval := hStableValue targetAfter
            (TargetExtends.refl targetAfter.vars)
          have hEval' :
              Functions.InteractionSemantics.Expr.openEval lower targetAfter =
                .done (.ok (targetAfter, [value])) := by
            simpa [Functions.InteractionSemantics.Expr.openEval] using hEval
          have hContains := hScoped.targetContains hName
          obtain ⟨remaining, hResidual⟩ :
              ∃ remaining, targetFuel - pre.length = remaining + 2 := by
            refine ⟨targetFuel - pre.length - 2, ?_⟩
            omega
          let targetFinal := targetAfter.insert (identName name) value
          have hTargetAssign :
              Functions.InteractionSemantics.Block.openRun
                  program ctxAfter (targetFuel - pre.length)
                  { stmts := [.assign (identName name) lower] } targetAfter =
                pure
                  (Functions.Source.Effectful.Outcome.regular targetFinal,
                    ctxAfter) := by
            rw [hResidual,
              show remaining + 2 = (remaining + 1) + 1 by omega,
              Functions.InteractionSemantics.Block.openRun_cons]
            change
              Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Stmt.openRun
                    program ctxAfter (remaining + 1)
                    (.assign (identName name) lower) targetAfter) _ = _
            rw [Functions.InteractionSemantics.Stmt.openRun_assign
                program ctxAfter (remaining + 1) (identName name)
                lower targetAfter hContains,
              hEval', Simulation.Interaction.bind_done_ok]
            simp only [Simulation.Interaction.monad_pure_bind]
            change
              Functions.InteractionSemantics.Block.openRun
                  program ctxAfter (remaining + 1) { stmts := [] }
                  targetFinal =
                pure
                  (Functions.Source.Effectful.Outcome.regular targetFinal,
                    ctxAfter)
            rw [Functions.InteractionSemantics.Block.openRun_nil]
          change
            Simulation.Interaction.ForwardRel Truncated
              (ControlDoneRel fresh.used layout sourceScopes
                canBreak canContinue canLeave)
              (pure (sourceAfter.multifill [name] [value]))
              (Functions.InteractionSemantics.Block.openRun
                program ctxAfter (targetFuel - pre.length)
                { stmts := [.assign (identName name) lower] } targetAfter)
          rw [hTargetAssign]
          have hFinal := hScoped.multifill_single_visible hName value
          have hFinalDomain : TargetDomainWithin fresh.used targetFinal.vars :=
            hDomain.insert_used hNameUsed value
          have hFinalCtx : ControlContextRel sourceScopes layout
              canBreak canContinue canLeave ctxAfter := by
            apply ControlContextRel.transport hControl
            · exact fun _candidate hMem => hMem
            · exact hSameCtx
            · intro candidate hMem
              exact hScopeCtx candidate (hControl.scope candidate hMem)
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.regular hFinal hFinalDomain hFinalCtx
              hTargetScopeAfter)

end FunctionsInteractionPreparedStatement
end Yul
end EvmCompiler
