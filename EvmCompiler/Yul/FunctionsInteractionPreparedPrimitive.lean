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
    (hEval :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpression.DoneRel source 1)
        sourceOpen
        (Functions.InteractionSemantics.Expr.openEval lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final [.var tmp] target)
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
      exact Simulation.Interaction.ForwardRel.done
        (.regular hStableFinal hScopedFinal hDomainFinal hExtendsFinal)

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
      intro _hLower _hFresh source target ctx hScoped hDomain
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
        hFresh hLayout hTargetFuel hScoped hDomain hEval
      exact singletonOfValues hValue

/-- The real bounded primitive-lowering artifact supplies a complete spilled
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
      intro _hLower _hFresh source target ctx hScoped hDomain
      have hPrepared :=
        ofUncheckedLowering (ctx := ctx) hArgsOk hArgs hNested hProgramBudget
          hScoped hDomain hLayoutBefore (by omega)
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

end FunctionsInteractionPreparedPrimitive
end Yul
end EvmCompiler
