import EvmCompiler.Yul.FunctionsInteractionRecursiveExpression

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedStatement

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation

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
    (hNameFresh : identName name ∉ layout)
    (hRel : ScopedStateRel layout source target)
    (hTailFuel : pre.length + 1 < targetFuel)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgs.DoneRel
          layout fresh [lower] target)
        (Yul.InteractionSemantics.evalValues
          exprFuel expr codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel
        (identName name :: layout))
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
      exact Simulation.Interaction.ForwardRel.done (.error hError)
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
  | @regular sourceAfter values targetAfter ctxAfter
      hStable hScoped _hDomain _hExtends =>
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
              (FunctionsInteractionStatement.PathScopedDoneRel
                (identName name :: layout))
              (pure (sourceAfter.multifill [name] [value]))
              (Functions.InteractionSemantics.Block.openRun
                program ctxAfter (targetFuel - pre.length)
                { stmts := [.let_ (identName name) lower] } targetAfter)
          rw [hTargetLet]
          have hFinal := hScoped.multifill_single_cons
            (identName name) value
          exact Simulation.Interaction.ForwardRel.done
            (.ok
              ⟨identName name :: layout,
                FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinal,
                fun _hRegular => rfl⟩)

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
    (hName : identName name ∈ layout)
    (hRel : ScopedStateRel layout source target)
    (hTailFuel : pre.length + 1 < targetFuel)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgs.DoneRel
          layout fresh [lower] target)
        (Yul.InteractionSemantics.evalValues
          exprFuel expr codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel layout)
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
      exact Simulation.Interaction.ForwardRel.done (.error hError)
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
  | @regular sourceAfter values targetAfter ctxAfter
      hStable hScoped _hDomain _hExtends =>
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
              (FunctionsInteractionStatement.PathScopedDoneRel layout)
              (pure (sourceAfter.multifill [name] [value]))
              (Functions.InteractionSemantics.Block.openRun
                program ctxAfter (targetFuel - pre.length)
                { stmts := [.assign (identName name) lower] } targetAfter)
          rw [hTargetAssign]
          have hFinal := hScoped.multifill_single_visible hName value
          exact Simulation.Interaction.ForwardRel.done
            (.ok
              ⟨layout,
                FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinal,
                fun _hRegular => rfl⟩)

end FunctionsInteractionPreparedStatement
end Yul
end EvmCompiler
