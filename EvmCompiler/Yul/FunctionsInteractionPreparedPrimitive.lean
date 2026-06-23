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
        (DoneRel layout after lowerArgs.reverse entry ctx)
        (Yul.InteractionSemantics.evalArgs
          argsFuel args.reverse codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final [.var tmp] entry ctx)
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
      hStable hScoped hDomain hExtends hScope hControl hTargetScopeAfter =>
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
              (doneRel := DoneRel layout final [.var tmp] entry ctx)
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
              (DoneRel layout final [.var tmp] entry ctx)
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
                (DoneRel layout final [.var tmp] entry ctx)
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
                have hTargetScopeFinal :
                    FunctionsInteractionControlRelation.TargetScopeWithin
                      final.used
                      { ctxAfter with scope := tmp :: ctxAfter.scope } := by
                  intro name hName
                  change name ∈ tmp :: ctxAfter.scope at hName
                  rw [hFinalUsed]
                  rcases List.mem_cons.mp hName with rfl | hName
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem tmp
                      (hTargetScopeAfter name hName)
                exact Simulation.Interaction.ForwardRel.done
                  (.regular
                    hStableFinal
                    hScopedFinal hDomainFinal hExtendsFinal
                    (Functions.Source.Ctx.ScopeExtends.trans hScope
                      (Functions.Source.Ctx.ScopeExtends.cons ctxAfter tmp))
                    (Functions.Source.Ctx.SameControl.trans hControl
                      (Functions.Source.Ctx.SameControl.scopeUpdate
                        ctxAfter (tmp :: ctxAfter.scope)))
                    hTargetScopeFinal)
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

/-- Bind a checked one-result source/Locals expression relation into the fresh
Functions local emitted by the bounded-argument compiler. -/
theorem bindDirectEval
    {targetFuel : Nat}
    {lower : Locals.Expr 1}
    {before final : Fresh.State} {tmp : Functions.Name}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceOpen : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Word)}
    (hFresh : Fresh.fresh? before = some (tmp, final))
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hTargetFuel : 1 < targetFuel)
    (hScoped : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx)
    (hEval :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpression.DoneRel source 1)
        sourceOpen
        (Functions.InteractionSemantics.Expr.openEval lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final [.var tmp] target ctx)
      sourceOpen
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := [.let_ tmp lower] } target) := by
  have hEvalVars := hEval.strengthen_right
    (Locals.InteractionSemantics.Expr.openEval_vars_eq lower target)
  have hRemaining : ∃ remaining, targetFuel = remaining + 2 := by
    refine ⟨targetFuel - 2, ?_⟩
    omega
  obtain ⟨remaining, rfl⟩ := hRemaining
  have hTargetLet :
      Functions.InteractionSemantics.Block.openRun
          program ctx (remaining + 2)
          { stmts := [.let_ tmp lower] } target =
        Simulation.Interaction.bind
          (Functions.InteractionSemantics.Expr.openEval lower target)
          (fun result =>
            match result.2 with
            | [value] =>
                pure
                  (Functions.Source.Effectful.Outcome.regular
                    (result.1.insert tmp value),
                    { ctx with scope := tmp :: ctx.scope })
            | _ => throw .InvalidInstruction) := by
    rw [show remaining + 2 = (remaining + 1) + 1 by omega,
      Functions.InteractionSemantics.Block.openRun_cons]
    change
      Simulation.Interaction.bind
          (Functions.InteractionSemantics.Stmt.openRun
            program ctx (remaining + 1) (.let_ tmp lower) target)
          _ = _
    rw [Functions.InteractionSemantics.Stmt.openRun_let,
      Simulation.Interaction.bind_assoc]
    apply congrArg
    funext result
    cases result.2 with
    | nil => rfl
    | cons value rest =>
        cases rest with
        | nil =>
            simp only [Simulation.Interaction.monad_pure_bind]
            change
              Functions.InteractionSemantics.Block.openRun
                  program { ctx with scope := tmp :: ctx.scope }
                  (remaining + 1) { stmts := [] }
                  (result.1.insert tmp value) =
                pure
                  (Functions.Source.Effectful.Outcome.regular
                    (result.1.insert tmp value),
                    { ctx with scope := tmp :: ctx.scope })
            rw [Functions.InteractionSemantics.Block.openRun_nil]
        | cons next tail => rfl
  rw [hTargetLet]
  apply Simulation.Interaction.ForwardRel.bind_right hEvalVars
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
      obtain ⟨value, hSourceValues⟩ :=
        List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hValues, hSourceValues]
      simp only [hTargetValues, Simulation.Interaction.bind_done_ok]
      obtain ⟨hFinalUsed, hTmpFresh⟩ :=
        Fresh.fresh?_components hFresh
      have hTmpLayout : tmp ∉ layout := by
        intro hMem
        exact hTmpFresh (hLayout tmp hMem)
      have hTargetVarsEq : targetResult.1.vars = target.vars := by
        simpa using hTargetVars
      have hDomainResult :
          FunctionsInteractionRelation.TargetDomainWithin
            before.used targetResult.1.vars := by
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
      have hTargetExtends :
          FunctionsInteractionRelation.TargetExtends
            target.vars targetResult.1.vars := by
        intro name result hLookup
        simpa [hTargetVarsEq] using hLookup
      have hInsertExtends :=
        FunctionsInteractionRelation.TargetExtends.insert_fresh
          (value := value) hTmpNone
      have hExtendsFinal :=
        FunctionsInteractionRelation.TargetExtends.trans hTargetExtends
          hInsertExtends
      have hLookup : targetFinal.vars tmp = some value := by
        simp [targetFinal, Locals.Source.State.insert,
          Locals.Source.Store.insert]
      have hStableFinal :
          FunctionsInteractionExpression.StableArgs
            [.var tmp] targetFinal sourceResult.2 := by
        simpa [hSourceValues] using
          (FunctionsInteractionExpression.StableArgs.cons
            (FunctionsInteractionExpression.StableValue.var hLookup)
            (FunctionsInteractionExpression.StableArgs.nil targetFinal))
      have hTargetScopeFinal :
          FunctionsInteractionControlRelation.TargetScopeWithin final.used
            { ctx with scope := tmp :: ctx.scope } := by
        intro name hName
        change name ∈ tmp :: ctx.scope at hName
        rw [hFinalUsed]
        rcases List.mem_cons.mp hName with rfl | hName
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem tmp (hTargetScope name hName)
      exact Simulation.Interaction.ForwardRel.done
        (.regular hStableFinal hScopedFinal hDomainFinal hExtendsFinal
          (Functions.Source.Ctx.ScopeExtends.cons ctx tmp)
          (Functions.Source.Ctx.SameControl.scopeUpdate
            ctx (tmp :: ctx.scope))
          hTargetScopeFinal)

/-- Direct inline operands still use the same open-world primitive theorem;
only the outer bounded-argument result is materialized in a fresh local. -/
theorem boundDirectOfLowering
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {lower : Locals.Expr 1}
    {before final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hLowering : Expr.UncheckedDirectPrimitiveLowering
      before prim args lower)
    (hFresh : Fresh.fresh? before = some (tmp, final))
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hTargetFuel : 1 < targetFuel) :
    BoundHeadForward (argsFuel + 2) targetFuel
      (.Call (.inl prim) args) [] lower before before final tmp
      codeOverride program layout := by
  cases hLowering with
  | @primitive op lowerArgs seq hOp hArgs hSeq hOutputs =>
      intro _hLower _hFresh source target ctx hScoped hDomain hTargetScope
      have hLowerReverse :
          Expr.List.toLocals1? args.reverse =
            some lowerArgs.reverse :=
        Expr.List.toLocals1?_reverse hArgs
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hArgsRel :=
        (FunctionsInteractionExpression.compilerDirectAt
          codeOverride argsFuel).evalArgs
          hLowerReverse hDirectSeq hScoped.state
      have hPrimitiveRel :=
        FunctionsInteractionExpression.Expr.primitive_of_args
          hPrimitive (primitiveFuel := argsFuel) hOp hOutputs hArgsRel
      have hEval :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpression.DoneRel source 1)
            (Yul.InteractionSemantics.evalValues
              (argsFuel + 1) (.Call (.inl prim) args)
              codeOverride source)
            (Functions.InteractionSemantics.Expr.openEval
              (Expr.cast hOutputs (.prim op seq)) target) := by
        rw [FunctionsInteractionExpression.expr_openEval_cast]
        simpa [Yul.InteractionSemantics.evalValues,
          Yul.Source.Canonical.evalValues,
          Yul.Source.Effectful.evalValues,
          Functions.InteractionSemantics.Expr.openEval,
          Locals.InteractionSemantics.Expr.openEval,
          Locals.Source.Effectful.Expr.Control.eval,
          FunctionsInteractionExpression.exprSeq_openEval_seqCast] using
          hPrimitiveRel
      have hValue := bindDirectEval (program := program) (ctx := ctx)
        hFresh hLayout hTargetFuel hScoped hDomain hTargetScope hEval
      exact singletonOfValues hValue

/-- The real bounded primitive-lowering artifact supplies a complete bound
head once recursively generated operand heads are available at smaller fuel. -/
theorem boundOfLowering
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program}
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hLowering : Expr.UncheckedBoundPrimitiveLowering
      before prim args pre lower after)
    (hArgsOk : SolcValidation.ExprsOk?
      profile sourceProgram.contract layout args = true)
    (hFresh : Fresh.fresh? after = some (tmp, final))
    (hNested : RecursiveBoundHeads
      profile sourceProgram argsFuel targetFuel codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel +
        pre.length + 2 ≤ targetFuel)
    (hLayoutBefore : ∀ name, name ∈ layout → name ∈ before.used)
    (hLayoutAfter : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    BoundHeadForward (argsFuel + 2) targetFuel
      (.Call (.inl prim) args) pre lower before after final tmp
      codeOverride program layout := by
  cases hLowering with
  | primitive hOp hArgs hSeq hOutputs =>
      intro _hLower _hFresh source target ctx hScoped hDomain hTargetScope
      have hPrepared :=
        ofUncheckedLowering (ctx := ctx) hArgsOk hArgs hNested hProgramBudget
          hScoped hDomain hTargetScope hLayoutBefore (by omega)
      have hValue :=
        afterPrepared hPrimitive (before := before) hOp hSeq hOutputs
          hFresh hLayoutAfter hTargetFuel hPrepared
      exact singletonOfValues hValue

/-- Exhaustive primitive-head dispatcher for the ordinary unchecked compiler.
The only recursive premise is indexed by strictly smaller operand fuel. -/
theorem boundPrimitive
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program}
    {fuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hLowering : Expr.UncheckedPrimitiveLowering 1
      before prim args pre lower after)
    (hExprOk : SolcValidation.ExprOk? profile sourceProgram.contract layout 1
      (.Call (.inl prim) args) = true)
    (hFresh : Fresh.fresh? after = some (tmp, final))
    (hNested :
      ∀ argsFuel,
        fuel = argsFuel + 2 →
          RecursiveBoundHeads
            profile sourceProgram argsFuel targetFuel codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
        pre.length + 2 ≤ targetFuel)
    (hLayoutBefore : ∀ name, name ∈ layout → name ∈ before.used)
    (hLayoutAfter : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    BoundHeadForward fuel targetFuel
      (.Call (.inl prim) args) pre lower before after final tmp
      codeOverride program layout := by
  by_cases hLow : fuel < 2
  · exact boundHead_lowFuel hLow
  · obtain ⟨argsFuel, hFuel⟩ : ∃ argsFuel, fuel = argsFuel + 2 := by
      refine ⟨fuel - 2, ?_⟩
      omega
    subst fuel
    cases hLowering with
    | direct hDirect hOp hArgs hSeq hOutputs =>
        exact
          boundDirectOfLowering hPrimitive
            (Expr.UncheckedDirectPrimitiveLowering.primitive
              hOp hArgs hSeq hOutputs)
            hFresh hLayoutBefore (by simpa using hTargetFuel)
    | bound hBound hOp hArgs hSeq hOutputs =>
        have hArgsOk :=
          SolcValidation.exprsOk_of_exprOk_primitive hExprOk
        have hArgsBudget :
            FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel +
                pre.length + 2 ≤ targetFuel := by
          have hFuelLe : argsFuel ≤ argsFuel + 2 := by omega
          have hBudgetLe :
              FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel ≤
                FunctionsInteractionStaticCost.programBudget sourceProgram
                  (argsFuel + 2) := by
            unfold FunctionsInteractionStaticCost.programBudget
            exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ hFuelLe
          omega
        exact
          boundOfLowering hPrimitive
            (Expr.UncheckedBoundPrimitiveLowering.primitive
              hOp hArgs hSeq hOutputs)
            hArgsOk hFresh (hNested argsFuel rfl) hArgsBudget
            hLayoutBefore hLayoutAfter
            hTargetFuel

/-- Exhaustive zero-result primitive statement for the ordinary unchecked
compiler. Direct operands remain deferred in the final expression; bounded
operands use the shared recursive argument prelude before the same statement
leaf. -/
theorem zeroOfLowering
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program}
    {fuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 0}
    {before after : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {sourceScopes : FunctionsInteractionControlRelation.SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLowering : Expr.UncheckedPrimitiveLowering 0
      before prim args pre lower after)
    (hExprOk : SolcValidation.ExprOk? profile sourceProgram.contract layout 0
      (.Call (.inl prim) args) = true)
    (hNested :
      ∀ argsFuel,
        fuel = argsFuel + 1 →
          RecursiveBoundHeads profile sourceProgram argsFuel targetFuel
            codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
        pre.length + 2 ≤ targetFuel)
    (hRel : FunctionsInteractionRelation.ScopedStateRel layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : FunctionsInteractionControlRelation.ControlContextRel
      sourceScopes layout canBreak canContinue canLeave ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
        sourceScopes canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec fuel
        (.ExprStmtCall (.Call (.inl prim) args)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
          { stmts := pre ++ [.expr lower] } target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      exact Simulation.Interaction.ForwardRel.truncated hTruncated
  | succ argsFuel =>
      cases hLowering with
      | direct hDirect hOp hArgs hSeq hOutputs =>
          rename_i op lowerArgs seq
          have hLowerReverse :
              Expr.List.toLocals1? args.reverse = some lowerArgs.reverse :=
            Expr.List.toLocals1?_reverse hArgs
          have hDirectSeq :
              Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) = some seq := by
            simpa [Expr.List.toStackSeq?] using hSeq
          have hArgsRel :=
            (FunctionsInteractionExpression.compilerDirectAt
              codeOverride argsFuel).evalArgs
              hLowerReverse hDirectSeq hRel.state
          have hPrimitiveRel :=
            FunctionsInteractionExpression.Expr.primitive_of_args
              hPrimitive (primitiveFuel := argsFuel) hOp hOutputs hArgsRel
          have hEval :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionExpression.DoneRel source 0)
                (Yul.InteractionSemantics.evalValues
                  (argsFuel + 1) (.Call (.inl prim) args)
                  codeOverride source)
                (Functions.InteractionSemantics.Expr.openEval
                  (Expr.cast hOutputs (.prim op seq)) target) := by
            rw [FunctionsInteractionExpression.expr_openEval_cast]
            simpa [Yul.InteractionSemantics.evalValues,
              Yul.Source.Canonical.evalValues,
              Yul.Source.Effectful.evalValues,
              Functions.InteractionSemantics.Expr.openEval,
              Locals.InteractionSemantics.Expr.openEval,
              Locals.Source.Effectful.Expr.Control.eval,
              FunctionsInteractionExpression.exprSeq_openEval_seqCast]
              using hPrimitiveRel
          have hTailFuel : 2 ≤ targetFuel := by
            omega
          have hStmt := FunctionsInteractionStatement.expr_of_evalValues
            (program := program) (ctx := ctx)
            (targetFuel := targetFuel - 1)
            hEval hRel hDomain hControl hTargetScope
          have hStmt' :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionControlRelation.ControlDoneRel
                  before.used layout sourceScopes
                  canBreak canContinue canLeave)
                (Simulation.Interaction.bind
                  (Yul.InteractionSemantics.evalValues
                    (argsFuel + 1) (.Call (.inl prim) args)
                    codeOverride source)
                  (fun result =>
                    pure
                      (Yul.InteractionSemantics.stateModel.multifill
                        [] result.1 result.2)))
                (Functions.InteractionSemantics.Stmt.openRun
                  program ctx ((targetFuel - 2) + 1)
                  (.expr (Expr.cast hOutputs (.prim op seq))) target) := by
            have hStmtFuelEq :
                targetFuel - 1 = (targetFuel - 2) + 1 := by
              omega
            simpa only [hStmtFuelEq] using hStmt
          have hSingleton :=
            FunctionsInteractionStatement.ControlDoneRel.singleton
              (targetFuel := targetFuel - 2) hStmt'
          rw [Yul.InteractionSemantics.Exec.expr_primitive]
          simpa [hTailFuel] using hSingleton
      | bound hBound hOp hArgs hSeq hOutputs =>
          rename_i op lowerArgs seq
          have hArgsOk :=
            SolcValidation.exprsOk_of_exprOk_primitive hExprOk
          have hArgsBudget :
              FunctionsInteractionStaticCost.programBudget
                    sourceProgram argsFuel + pre.length + 2 ≤
                targetFuel := by
            have hBudgetLe :
                FunctionsInteractionStaticCost.programBudget
                    sourceProgram argsFuel ≤
                  FunctionsInteractionStaticCost.programBudget
                    sourceProgram (argsFuel + 1) := by
              unfold FunctionsInteractionStaticCost.programBudget
              exact FunctionsInteractionFuel.executionBudgetFor_mono _ _
                (by omega)
            omega
          have hPrepared :=
            FunctionsInteractionPreparedArgs.ofUncheckedLowering
              (ctx := ctx) hArgsOk hArgs (hNested argsFuel rfl)
              hArgsBudget hRel hDomain hTargetScope hLayout (by omega)
          rw [Yul.InteractionSemantics.Exec.expr_primitive,
            Functions.InteractionSemantics.Block.openRun_append]
          unfold Yul.InteractionSemantics.evalValues
            Yul.Source.Canonical.evalValues
            Yul.Source.Effectful.evalValues
          change
            Simulation.Interaction.ForwardRel Truncated
              (FunctionsInteractionControlRelation.ControlDoneRel
                after.used layout sourceScopes
                canBreak canContinue canLeave)
              (Simulation.Interaction.bind
                (Simulation.Interaction.bind
                  (Yul.InteractionSemantics.evalArgs
                    argsFuel args.reverse codeOverride source)
                  (fun argsResult =>
                    Yul.InteractionSemantics.Primitive.openEval
                      argsFuel argsResult.1 prim argsResult.2.reverse))
                (fun result =>
                  pure
                    (Yul.InteractionSemantics.stateModel.multifill
                      [] result.1 result.2)))
              (Simulation.Interaction.bind
                (Functions.InteractionSemantics.Block.openRun
                  program ctx targetFuel { stmts := pre } target)
                (fun result =>
                  match result.1.mode with
                  | .regular =>
                      Functions.InteractionSemantics.Block.openRun
                        program result.2 (targetFuel - pre.length)
                          { stmts :=
                            [.expr (Expr.cast hOutputs (.prim op seq))] }
                          result.1.state
                  | .brk | .cont | .leave | .halt _ => pure result))
          rw [Simulation.Interaction.bind_assoc]
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
              hStable hScoped hDomainAfter _hExtends hScopeExtends hSameControl
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
                (FunctionsInteractionRelation.TargetExtends.refl
                  targetAfter.vars)
              have hControlAfter :=
                FunctionsInteractionControlRelation.ControlContextRel.transport
                  hControl (fun _name hName => hName) hSameControl
                  (fun name hName =>
                    hScopeExtends name (hControl.scope name hName))
              have hStmt := FunctionsInteractionStatement.expr_after_args
                hPrimitive
                (program := program) (primitiveFuel := argsFuel)
                (targetFuel := targetFuel - pre.length - 1)
                hOp hOutputs hLength hEval hScoped hDomainAfter
                hControlAfter hTargetScopeAfter
              have hTailFuel : 2 ≤ targetFuel - pre.length := by
                omega
              have hStmt' :
                  Simulation.Interaction.ForwardRel Truncated
                    (FunctionsInteractionControlRelation.ControlDoneRel
                      after.used layout sourceScopes
                      canBreak canContinue canLeave)
                    (Simulation.Interaction.bind
                      (Yul.InteractionSemantics.Primitive.openEval
                        argsFuel sourceAfter prim values.reverse)
                      (fun result =>
                        pure
                          (Yul.InteractionSemantics.stateModel.multifill
                            [] result.1 result.2)))
                    (Functions.InteractionSemantics.Stmt.openRun
                      program ctxAfter
                        ((targetFuel - pre.length - 2) + 1)
                        (.expr (Expr.cast hOutputs (.prim op seq)))
                        targetAfter) := by
                have hStmtFuelEq :
                    targetFuel - pre.length - 1 =
                      (targetFuel - pre.length - 2) + 1 := by
                  omega
                simpa only [hStmtFuelEq] using hStmt
              have hSingleton :=
                FunctionsInteractionStatement.ControlDoneRel.singleton
                  (targetFuel := targetFuel - pre.length - 2) hStmt'
              simpa [hTailFuel] using hSingleton

/-- Terminal primitive statement with the ordinary compiler-generated bounded
argument prelude. Argument recursion and terminal execution remain independent
capabilities and meet only through the shared control-indexed result relation. -/
theorem terminalOfLowering
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program}
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq kind.argCount}
    {before after : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {sourceScopes : FunctionsInteractionControlRelation.SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hTerminal : Prim.terminal? prim = some kind)
    (hArgsLowering : Expr.List.UncheckedBoundLowering
      before args pre lowerArgs after)
    (hSeq : Expr.List.toStackSeq? lowerArgs kind.argCount = some seq)
    (hArgsOk : SolcValidation.ExprsOk?
      profile sourceProgram.contract layout args = true)
    (hNested : RecursiveBoundHeads profile sourceProgram argsFuel targetFuel
      codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel +
        pre.length + 2 ≤ targetFuel)
    (hRel : FunctionsInteractionRelation.ScopedStateRel layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
        sourceScopes canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (argsFuel + 1)
        (.ExprStmtCall (.Call (.inl prim) args)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
          { stmts := pre ++ [.terminalArgs kind seq] } target) := by
  have hPrepared :=
    FunctionsInteractionPreparedArgs.ofUncheckedLowering
      (ctx := ctx) hArgsOk hArgsLowering hNested hProgramBudget
      hRel hDomain hTargetScope hLayout (by omega)
  rw [Yul.InteractionSemantics.Exec.expr_primitive,
    Functions.InteractionSemantics.Block.openRun_append]
  unfold Yul.InteractionSemantics.evalValues
    Yul.Source.Canonical.evalValues
    Yul.Source.Effectful.evalValues
  change
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
        sourceScopes canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs
            argsFuel args.reverse codeOverride source)
          (fun argsResult =>
            Yul.InteractionSemantics.Primitive.openEval
              argsFuel argsResult.1 prim argsResult.2.reverse))
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Functions.InteractionSemantics.Block.openRun
                program result.2 (targetFuel - pre.length)
                  { stmts := [.terminalArgs kind seq] } result.1.state
          | .brk | .cont | .leave | .halt _ => pure result))
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminalResult =>
      cases hTerminalResult with
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
      hStable hScoped hDomainAfter _hExtends _hScope _hControl
      _hTargetScope =>
      simp only [Simulation.Interaction.bind_done_ok]
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse kind.argCount = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hLength : values.length = kind.argCount :=
        hStable.length.trans (Expr.List.toSeq?_length hDirectSeq)
      have hEval := hStable.exprSeq_openEval hDirectSeq
        (FunctionsInteractionRelation.TargetExtends.refl targetAfter.vars)
      have hStmt := FunctionsInteractionStatement.terminal_after_args_control
        (program := program) (ctx := ctxAfter) (primitiveFuel := argsFuel)
        (targetFuel := targetFuel - pre.length - 1)
        (used := after.used) (sourceScopes := sourceScopes)
        (canBreak := canBreak) (canContinue := canContinue)
        (canLeave := canLeave)
        hTerminal hLength hEval hScoped
      have hTailFuel : 2 ≤ targetFuel - pre.length := by
        omega
      have hStmt' :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
              sourceScopes canBreak canContinue canLeave)
            (Simulation.Interaction.bind
              (Yul.InteractionSemantics.Primitive.openEval
                argsFuel sourceAfter prim values.reverse)
              (fun result =>
                pure
                  (Yul.InteractionSemantics.stateModel.multifill
                    [] result.1 result.2)))
            (Functions.InteractionSemantics.Stmt.openRun
              program ctxAfter ((targetFuel - pre.length - 2) + 1)
              (.terminalArgs kind seq) targetAfter) := by
        have hStmtFuelEq :
            targetFuel - pre.length - 1 =
              (targetFuel - pre.length - 2) + 1 := by
          omega
        simpa only [hStmtFuelEq] using hStmt
      have hSingleton :=
        FunctionsInteractionStatement.ControlDoneRel.singleton
          (targetFuel := targetFuel - pre.length - 2) hStmt'
      simpa [hTailFuel] using hSingleton

end FunctionsInteractionPreparedPrimitive
end Yul
end EvmCompiler
