import EvmCompiler.Yul.FunctionsInteractionPreparedArgs

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedPrimitive

open FunctionsInteractionPrimitive
open FunctionsInteractionPreparedArgs

/-- Execute one compiler-selected primitive after its recursively prepared
arguments, then store its single result in the fresh bounded-argument local. -/
theorem afterPrepared
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {op : Structured.BasicOp}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {entry : Functions.InteractionSemantics.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hSeq : Expr.List.toStackSeq? lowerArgs
      (Expressions.Structured.BasicOp.inputs op) = some seq)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 1)
    (hFresh : Fresh.fresh? after = some (tmp, final))
    (hLayout : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout after lowerArgs.reverse entry)
        (Yul.InteractionSemantics.evalArgs
          argsFuel args.reverse codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final [.var tmp] entry)
      (Yul.InteractionSemantics.evalValues
        (argsFuel + 1) (.Call (.inl prim) args) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
        { stmts := pre ++
            [.let_ tmp (Expr.cast hOutputs (.prim op seq))] } target) := by
  unfold Yul.InteractionSemantics.evalValues
    Yul.Source.Canonical.evalValues Yul.Source.Effectful.evalValues
  rw [Functions.InteractionSemantics.Block.openRun_append]
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
      hStable hScoped hDomain hExtends =>
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
              (doneRel := DoneRel layout final [.var tmp] entry)
              (right :=
                Functions.InteractionSemantics.Block.openRun
                  program ctxAfter (targetFuel - pre.length)
                  { stmts :=
                    [.let_ tmp (Expr.cast hOutputs (.prim op seq))] }
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
              (sourceValues := values.reverse) hOp hSourceLength
              hScoped.state
          have hPrimitiveRel' :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionPrimitive.PrimitiveDoneRel
                  sourceAfter op)
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
            (FunctionsInteractionRelation.TargetExtends.refl targetAfter.vars)
          unfold Locals.InteractionSemantics.ExprSeq.openEval at hSeqEval
          have hResidual :
              ∃ remaining, targetFuel - pre.length = remaining + 2 := by
            refine ⟨targetFuel - pre.length - 2, ?_⟩
            omega
          obtain ⟨remaining, hResidual⟩ := hResidual
          have hTargetLet :
              Functions.InteractionSemantics.Block.openRun
                  program ctxAfter (targetFuel - pre.length)
                  { stmts :=
                    [.let_ tmp (Expr.cast hOutputs (.prim op seq))] }
                  targetAfter =
                Simulation.Interaction.bind
                  (Locals.InteractionSemantics.Primitive.openEval
                    op targetAfter values)
                  (fun primitiveResult =>
                    match primitiveResult.2 with
                    | [value] =>
                        pure
                          (Functions.Source.Effectful.Outcome.regular
                            (primitiveResult.1.insert tmp value),
                            { ctxAfter with
                              scope := tmp :: ctxAfter.scope })
                    | _ => throw .InvalidInstruction) := by
            rw [hResidual,
              show remaining + 2 = (remaining + 1) + 1 by omega,
              Functions.InteractionSemantics.Block.openRun_cons]
            change
              Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Stmt.openRun
                    program ctxAfter (remaining + 1)
                    (.let_ tmp (Expr.cast hOutputs (.prim op seq)))
                    targetAfter)
                  _ = _
            rw [Functions.InteractionSemantics.Stmt.openRun_let]
            rw [FunctionsInteractionExpression.expr_openEval_cast]
            unfold Functions.InteractionSemantics.Expr.openEval
              Locals.InteractionSemantics.Expr.openEval
              Locals.Source.Effectful.Expr.Control.eval
            rw [hSeqEval]
            simp only [Simulation.Interaction.monad_pure_bind]
            rw [Simulation.Interaction.bind_assoc]
            apply congrArg
            funext primitiveResult
            cases primitiveResult.2 with
            | nil => rfl
            | cons value rest =>
                cases rest with
                | nil =>
                    simp only [Simulation.Interaction.monad_pure_bind]
                    change
                      Functions.InteractionSemantics.Block.openRun
                          program
                          { ctxAfter with scope := tmp :: ctxAfter.scope }
                          (remaining + 1) { stmts := [] }
                          (primitiveResult.1.insert tmp value) =
                        pure
                          (Functions.Source.Effectful.Outcome.regular
                            (primitiveResult.1.insert tmp value),
                            { ctxAfter with
                              scope := tmp :: ctxAfter.scope })
                    rw [Functions.InteractionSemantics.Block.openRun_nil]
                | cons next tail => rfl
          change
            Simulation.Interaction.ForwardRel Truncated
              (DoneRel layout final [.var tmp] entry)
              (Yul.InteractionSemantics.Primitive.openEval
                (primitiveFuel + 1) sourceAfter prim values.reverse)
              (Functions.InteractionSemantics.Block.openRun
                program ctxAfter (targetFuel - pre.length)
                { stmts :=
                  [.let_ tmp (Expr.cast hOutputs (.prim op seq))] }
                targetAfter)
          rw [hTargetLet]
          have hPrimitiveBound :
              Simulation.Interaction.ForwardRel Truncated
                (DoneRel layout final [.var tmp] entry)
                (Simulation.Interaction.bind
                  (Yul.InteractionSemantics.Primitive.openEval
                    (primitiveFuel + 1) sourceAfter prim values.reverse)
                  pure)
                (Simulation.Interaction.bind
                  (Locals.InteractionSemantics.Primitive.openEval
                    op targetAfter values)
                  (fun primitiveResult =>
                    match primitiveResult.2 with
                    | [value] =>
                        pure
                          (Functions.Source.Effectful.Outcome.regular
                            (primitiveResult.1.insert tmp value),
                            { ctxAfter with
                              scope := tmp :: ctxAfter.scope })
                    | _ => throw .InvalidInstruction)) := by
            apply Simulation.Interaction.ForwardRel.bind_custom
              hPrimitiveRelVars
            intro sourcePrimitiveDone targetPrimitiveDone hPrimitiveDone
            rcases hPrimitiveDone with ⟨hPrimitiveDone, hTargetVars⟩
            cases hPrimitiveDone with
            | error hError =>
                exact Simulation.Interaction.ForwardRel.done (.error hError)
            | @ok sourceResult targetResult hResult =>
                have hState := hResult.1.1
                have hValues := hResult.1.2
                have hLength := hResult.2.1
                have hStore := hResult.2.2
                obtain ⟨value, hSourceValues⟩ :=
                  List.length_eq_one_iff.mp
                    (by simpa [hOutputs] using hLength)
                have hTargetValues : targetResult.2 = [value] := by
                  rw [← hValues, hSourceValues]
                simp only [hSourceValues, hTargetValues,
                  Simulation.Interaction.bind_done_ok]
                obtain ⟨hFinalUsed, hTmpFresh⟩ :=
                  Fresh.fresh?_components hFresh
                have hTmpLayout : tmp ∉ layout := by
                  intro hMem
                  exact hTmpFresh (hLayout tmp hMem)
                have hTargetVarsEq :
                    targetResult.1.vars = targetAfter.vars := by
                  simpa using hTargetVars
                have hDomainResult :
                    FunctionsInteractionRelation.TargetDomainWithin
                      after.used targetResult.1.vars := by
                  simpa [hTargetVarsEq] using hDomain
                have hTmpNone : targetResult.1.vars tmp = none :=
                  hDomainResult.lookup_none hTmpFresh
                let targetFinal := targetResult.1.insert tmp value
                have hScopedResult :=
                  FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
                    hScoped hState hStore
                have hScopedFinal :=
                  hScopedResult.insert_private hTmpLayout value
                have hDomainFinal :
                    FunctionsInteractionRelation.TargetDomainWithin
                      final.used targetFinal.vars := by
                  rw [hFinalUsed]
                  exact hDomainResult.insert hTmpFresh
                have hPrimitiveExtends :
                    FunctionsInteractionRelation.TargetExtends
                      targetAfter.vars targetResult.1.vars := by
                  intro name result hLookup
                  simpa [hTargetVarsEq] using hLookup
                have hInsertExtends :=
                  FunctionsInteractionRelation.TargetExtends.insert_fresh
                    (value := value) hTmpNone
                have hExtendsFinal :=
                  FunctionsInteractionRelation.TargetExtends.trans hExtends
                    (FunctionsInteractionRelation.TargetExtends.trans
                      hPrimitiveExtends hInsertExtends)
                have hLookup : targetFinal.vars tmp = some value := by
                  simp [targetFinal, Locals.Source.State.insert,
                    Locals.Source.Store.insert]
                have hStableFinal :
                    FunctionsInteractionExpression.StableArgs
                      [.var tmp] targetFinal sourceResult.2 := by
                  simpa [hSourceValues] using
                    (FunctionsInteractionExpression.StableArgs.cons
                      (FunctionsInteractionExpression.StableValue.var hLookup)
                      (FunctionsInteractionExpression.StableArgs.nil
                        targetFinal))
                exact Simulation.Interaction.ForwardRel.done
                  (.regular
                    hStableFinal
                    hScopedFinal hDomainFinal hExtendsFinal)
          have hSourcePure :
              Simulation.Interaction.bind
                  (Yul.InteractionSemantics.Primitive.openEval
                    (primitiveFuel + 1) sourceAfter prim values.reverse)
                  (fun result => pure result) =
                Yul.InteractionSemantics.Primitive.openEval
                  (primitiveFuel + 1) sourceAfter prim values.reverse := by
            exact Simulation.Interaction.bind_pure _
          rw [hSourcePure] at hPrimitiveBound
          exact hPrimitiveBound

/-- The real bounded primitive-lowering artifact supplies a complete spilled
head once recursively generated operand heads are available at smaller fuel. -/
theorem boundOfLowering
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hLowering : Expr.UncheckedBoundPrimitiveLowering
      before prim args pre lower after)
    (hFresh : Fresh.fresh? after = some (tmp, final))
    (hNested : RecursiveBoundHeads
      argsFuel targetFuel codeOverride program layout)
    (hLayoutBefore : ∀ name, name ∈ layout → name ∈ before.used)
    (hLayoutAfter : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    BoundHeadForward (argsFuel + 2) targetFuel
      (.Call (.inl prim) args) pre lower before after final tmp
      codeOverride program layout := by
  cases hLowering with
  | primitive hOp hArgs hSeq hOutputs =>
      intro _hLower _hFresh source target ctx hScoped hDomain
      have hPrepared :=
        ofUncheckedLowering (ctx := ctx) hArgs hNested hScoped hDomain
          hLayoutBefore (by omega)
      have hValue :=
        afterPrepared hPrimitive (before := before) hOp hSeq hOutputs
          hFresh hLayoutAfter hTargetFuel hPrepared
      exact singletonOfValues hValue

end FunctionsInteractionPreparedPrimitive
end Yul
end EvmCompiler
