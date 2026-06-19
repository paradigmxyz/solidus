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

/-- Empty-prelude specialization for a visible assignment. This covers
literals, variables, and inline primitive lowering; prepared primitive
arguments use `assignOneOfPreparedPrimitive` below. -/
theorem assignOneOfConditionDirect
    {exprFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {lower : Locals.Expr 1}
    {used : List Functions.Name} {layout : List Functions.Name}
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
        (FunctionsInteractionPreparedCondition.DoneRel layout used ctx)
        (Yul.InteractionSemantics.evalValues
          exprFuel expr codeOverride source)
        (FunctionsInteractionPreparedCondition.run
          program ctx targetFuel [] lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (exprFuel + 1)
        (.Assign [name] expr) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
        { stmts := [.assign (identName name) lower] } target) := by
  have hCheck := hRel.assignmentCheck hName
  have hContains := hRel.targetContains hName
  rw [Yul.InteractionSemantics.Exec.assign_one_succ
      exprFuel name expr codeOverride source hCheck,
    FunctionsInteractionPreparedCondition.run_assign_nil
      program ctx targetFuel (identName name) lower target
      hTargetFuel hContains]
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

/-- Attach a visible assignment to a primitive whose arguments were prepared by
the ordinary bounded-argument lowering. Factoring at the generated prelude
keeps the Functions existence check before primitive evaluation, exactly as in
the compiler output. -/
theorem assignOneOfPreparedPrimitive
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {argsFuel targetFuel : Nat}
    {name : EvmYul.Identifier} {prim : EvmYul.Operation .Yul}
    {args : List AstExpr} {op : Structured.BasicOp}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {final : Fresh.State}
    {layout : List Functions.Name}
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
        (FunctionsInteractionPreparedArgs.DoneRel
          layout final lowerArgs.reverse target ctx)
        (Yul.InteractionSemantics.evalArgs
          argsFuel args.reverse codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (argsFuel + 2)
        (.Assign [name] (.Call (.inl prim) args)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
        { stmts := pre ++
            [.assign (identName name)
              (Expr.cast hOutputs (.prim op seq))] } target) := by
  have hCheck := hRel.assignmentCheck hName
  rw [show argsFuel + 2 = (argsFuel + 1) + 1 by omega,
    Yul.InteractionSemantics.Exec.assign_one_succ
      (argsFuel + 1) name (.Call (.inl prim) args) codeOverride source hCheck,
    Functions.InteractionSemantics.Block.openRun_append]
  unfold Yul.InteractionSemantics.evalValues
    Yul.Source.Canonical.evalValues Yul.Source.Effectful.evalValues
  simp only
  change
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used layout sourceScopes
        canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs
            argsFuel args.reverse codeOverride source)
          (fun argsResult =>
            (Yul.InteractionSemantics.Primitive.openEval
              argsFuel argsResult.1 prim argsResult.2.reverse)))
        (fun result => pure (result.1.multifill [name] result.2)))
      _
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
      hStable hScoped hDomain _hExtends hScope hSameControl hTargetScopeAfter =>
      cases argsFuel with
      | zero =>
          have hTruncated :
              Truncated
                ({ exception := .OutOfFuel, state := sourceAfter } :
                  Yul.InteractionSemantics.Failure) := by
            trivial
          simpa [Yul.InteractionSemantics.Primitive.openEval,
            Yul.InteractionSemantics.Primitive.fail] using
            (Simulation.Interaction.ForwardRel.truncated
              (doneRel := ControlDoneRel final.used layout sourceScopes
                canBreak canContinue canLeave)
              (right := Functions.InteractionSemantics.Block.openRun
                program ctxAfter (targetFuel - pre.length)
                { stmts :=
                    [.assign (identName name)
                      (Expr.cast hOutputs (.prim op seq))] }
                targetAfter)
              hTruncated)
      | succ primitiveFuel =>
          have hDirectSeq :
              Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) = some seq := by
            simpa [Expr.List.toStackSeq?] using hSeq
          have hSourceLength :
              values.reverse.length =
                Expressions.Structured.BasicOp.inputs op := by
            simpa [List.length_reverse] using
              hStable.length.trans (Expr.List.toSeq?_length hDirectSeq)
          have hPrimitiveRel :=
            hPrimitive (fuel := primitiveFuel)
              (sourceValues := values.reverse) hOp hSourceLength hScoped.state
          have hPrimitiveRel' :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionPrimitive.PrimitiveDoneRel sourceAfter op)
                (Yul.InteractionSemantics.Primitive.openEval
                  (primitiveFuel + 1) sourceAfter prim values.reverse)
                (Locals.InteractionSemantics.Primitive.openEval
                  op targetAfter values) := by
            simpa using hPrimitiveRel
          have hPrimitiveRelVars :=
            hPrimitiveRel'.strengthen_right
              (Locals.InteractionSemantics.Primitive.openEval_vars_eq
                op targetAfter values)
          have hSeqEval := hStable.exprSeq_openEval hDirectSeq
            (TargetExtends.refl targetAfter.vars)
          unfold Locals.InteractionSemantics.ExprSeq.openEval at hSeqEval
          have hTargetEval :
              Functions.InteractionSemantics.Expr.openEval
                  (Expr.cast hOutputs (.prim op seq)) targetAfter =
                Locals.InteractionSemantics.Primitive.openEval
                  op targetAfter values := by
            rw [FunctionsInteractionExpression.expr_openEval_cast]
            unfold Functions.InteractionSemantics.Expr.openEval
              Locals.InteractionSemantics.Expr.openEval
              Locals.Source.Effectful.Expr.Control.eval
            rw [hSeqEval]
            rfl
          have hContains := hScoped.targetContains hName
          have hControlAfter : ControlContextRel sourceScopes layout
              canBreak canContinue canLeave ctxAfter := by
            apply ControlContextRel.transport hControl
            · exact fun _candidate hMem => hMem
            · exact hSameControl
            · intro candidate hMem
              exact hScope candidate (hControl.scope candidate hMem)
          have hStmt :
              Simulation.Interaction.ForwardRel Truncated
                (ControlDoneRel final.used layout sourceScopes
                  canBreak canContinue canLeave)
                (Simulation.Interaction.bind
                  (Yul.InteractionSemantics.Primitive.openEval
                    (primitiveFuel + 1) sourceAfter prim values.reverse)
                  (fun result => pure (result.1.multifill [name] result.2)))
                (Functions.InteractionSemantics.Stmt.openRun
                  program ctxAfter ((targetFuel - pre.length - 2) + 1)
                  (.assign (identName name)
                    (Expr.cast hOutputs (.prim op seq))) targetAfter) := by
            rw [Functions.InteractionSemantics.Stmt.openRun_assign
              program ctxAfter (targetFuel - pre.length - 2 + 1)
              (identName name) (Expr.cast hOutputs (.prim op seq))
              targetAfter hContains]
            rw [hTargetEval]
            apply Simulation.Interaction.ForwardRel.bind_custom hPrimitiveRelVars
            intro sourceDone targetDone hDone
            rcases hDone with ⟨hDone, hTargetVars⟩
            cases hDone with
            | error hError =>
                exact Simulation.Interaction.ForwardRel.done
                  (ControlDoneRel.error hError)
            | @ok sourceResult targetResult hOk =>
                have hLength : sourceResult.2.length = 1 := hOk.2.1.trans hOutputs
                obtain ⟨value, hSourceValues⟩ :=
                  List.length_eq_one_iff.mp hLength
                have hTargetValues : targetResult.2 = [value] := by
                  rw [← hOk.1.2, hSourceValues]
                simp only [Simulation.Interaction.bind_done_ok]
                rw [hSourceValues, hTargetValues]
                have hFinalScoped :=
                  ScopedStateRel.of_state_store_eq hScoped hOk.1.1 hOk.2.2
                have hFinal := hFinalScoped.multifill_single_visible hName value
                have hTargetVarsEq : targetResult.1.vars = targetAfter.vars := by
                  simpa using hTargetVars
                have hDomainResult : TargetDomainWithin final.used
                    targetResult.1.vars := by
                  simpa [hTargetVarsEq] using hDomain
                have hFinalDomain : TargetDomainWithin final.used
                    (targetResult.1.insert (identName name) value).vars :=
                  hDomainResult.insert_used hNameUsed value
                exact Simulation.Interaction.ForwardRel.done
                  (ControlDoneRel.regular hFinal hFinalDomain hControlAfter
                    hTargetScopeAfter)
          have hSingleton :=
            FunctionsInteractionStatement.ControlDoneRel.singleton hStmt
          change
            Simulation.Interaction.ForwardRel Truncated
              (ControlDoneRel final.used layout sourceScopes
                canBreak canContinue canLeave)
              _
              (Functions.InteractionSemantics.Block.openRun
                program ctxAfter (targetFuel - pre.length)
                { stmts :=
                    [.assign (identName name)
                      (Expr.cast hOutputs (.prim op seq))] }
                targetAfter)
          simpa [show targetFuel - pre.length - 2 + 2 =
              targetFuel - pre.length by omega] using hSingleton

end FunctionsInteractionPreparedStatement
end Yul
end EvmCompiler
