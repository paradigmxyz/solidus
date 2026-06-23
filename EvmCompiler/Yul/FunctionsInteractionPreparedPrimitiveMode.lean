import EvmCompiler.Yul.FunctionsInteractionStatementMode
import EvmCompiler.Yul.FunctionsInteractionPreparedPrimitive

/-!
Mode-parametric compiler-prepared primitive statements. Compiler lowering,
freshness, and bounded-argument artifacts are shared with the ordinary pass;
primitive execution uses the canonical handler selected by `Mode`.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedPrimitiveMode

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionMode
open FunctionsInteractionPreparedArgsMode

/-- Bind a checked one-result expression relation into the fresh Functions
local emitted by bounded-argument lowering. -/
theorem bindDirectEval
    {mode : Mode} {targetFuel : Nat}
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
    (hScoped : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx)
    (hEval :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel source 1)
        sourceOpen (Target.Expr.openEval mode lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout final [.var tmp] target ctx)
      sourceOpen
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := [.let_ tmp lower] } target) := by
  have hEvalVars := hEval.strengthen_right
    (Target.Expr.openEval_vars_eq mode lower target)
  obtain ⟨remaining, rfl⟩ : ∃ remaining, targetFuel = remaining + 2 :=
    ⟨targetFuel - 2, by omega⟩
  have hTargetLet :
      Target.Block.openRun mode program ctx (remaining + 2)
          { stmts := [.let_ tmp lower] } target =
        Simulation.Interaction.bind
          (Target.Expr.openEval mode lower target)
          (fun result =>
            match result.2 with
            | [value] =>
                pure
                  (Functions.Source.Effectful.Outcome.regular
                    (result.1.insert tmp value),
                    { ctx with scope := tmp :: ctx.scope })
            | _ => throw .InvalidInstruction) := by
    rw [show remaining + 2 = (remaining + 1) + 1 by omega,
      Target.Block.openRun_cons]
    change
      Simulation.Interaction.bind
          (Target.Stmt.openRun mode program ctx (remaining + 1)
            (.let_ tmp lower) target)
          _ = _
    rw [Target.Stmt.openRun_let, Simulation.Interaction.bind_assoc]
    apply congrArg
    funext result
    cases result.2 with
    | nil => rfl
    | cons value rest =>
        cases rest with
        | nil =>
            simp only [Simulation.Interaction.monad_pure_bind]
            change
              Target.Block.openRun mode program
                  { ctx with scope := tmp :: ctx.scope }
                  (remaining + 1) { stmts := [] }
                  (result.1.insert tmp value) =
                pure
                  (Functions.Source.Effectful.Outcome.regular
                    (result.1.insert tmp value),
                    { ctx with scope := tmp :: ctx.scope })
            rw [Target.Block.openRun_nil]
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
      have hDomainResult : TargetDomainWithin
          before.used targetResult.1.vars := by
        simpa [hTargetVarsEq] using hDomain
      have hTmpNone : targetResult.1.vars tmp = none :=
        hDomainResult.lookup_none hTmpFresh
      let targetFinal := targetResult.1.insert tmp value
      have hScopedResult := ScopedStateRel.of_state_store_eq
        hScoped hState hStore
      have hScopedFinal :=
        hScopedResult.insert_private hTmpLayout value
      have hDomainFinal : TargetDomainWithin final.used targetFinal.vars := by
        rw [hFinalUsed]
        exact hDomainResult.insert hTmpFresh
      have hTargetExtends : TargetExtends
          target.vars targetResult.1.vars := by
        intro name result hLookup
        simpa [hTargetVarsEq] using hLookup
      have hInsertExtends := TargetExtends.insert_fresh
        (value := value) hTmpNone
      have hExtendsFinal := TargetExtends.trans
        hTargetExtends hInsertExtends
      have hLookup : targetFinal.vars tmp = some value := by
        simp [targetFinal, Locals.Source.State.insert,
          Locals.Source.Store.insert]
      have hStableFinal :
          FunctionsInteractionExpressionMode.StableArgs
            mode [.var tmp] targetFinal sourceResult.2 := by
        simpa [hSourceValues] using
          (FunctionsInteractionExpressionMode.StableArgs.cons
            (FunctionsInteractionExpressionMode.StableValue.var
              (mode := mode) hLookup)
            (FunctionsInteractionExpressionMode.StableArgs.nil targetFinal))
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

/-- Execute one compiler-selected primitive after recursively prepared
arguments, then store its single result in the fresh bounded-argument local. -/
theorem afterPrepared
    {mode : Mode} (hPrimitive : CompilerSelected mode)
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
        (DoneRel mode layout after lowerArgs.reverse entry ctx)
        (Source.evalArgs mode argsFuel args.reverse codeOverride source)
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout final [.var tmp] entry ctx)
      (Source.evalValues mode (argsFuel + 1)
        (.Call (.inl prim) args) codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++
            [.let_ tmp (Expr.cast hOutputs (.prim op seq))] } target) := by
  unfold Source.evalValues Yul.Source.Canonical.evalValues
    Yul.Source.Effectful.evalValues
  rw [Target.Block.openRun_append]
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
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hLength :
          values.length = Expressions.Structured.BasicOp.inputs op :=
        hStable.length.trans (Expr.List.toSeq?_length hDirectSeq)
      have hSeqEval := hStable.exprSeq_openEval hDirectSeq
        (TargetExtends.refl targetAfter.vars)
      have hArgsDone :
          FunctionsInteractionExpressionMode.DoneRel sourceAfter
              (Expressions.Structured.BasicOp.inputs op)
              (.ok (sourceAfter, values)) (.ok (targetAfter, values)) :=
        .ok (FunctionsInteractionExpression.ResultRel.of_state
          hScoped.state hLength)
      have hArgsRel :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpressionMode.DoneRel sourceAfter
              (Expressions.Structured.BasicOp.inputs op))
            (pure (sourceAfter, values))
            (Target.ExprSeq.openEval mode seq targetAfter) := by
        rw [hSeqEval]
        exact Simulation.Interaction.ForwardRel.done hArgsDone
      have hPrimitiveRel :=
        FunctionsInteractionExpressionMode.Expr.primitive_of_args
          mode hPrimitive (primitiveFuel := argsFuel)
          hOp hOutputs hArgsRel
      have hExprRel :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpressionMode.DoneRel sourceAfter 1)
            ((sourcePrimitive mode).eval
              argsFuel sourceAfter prim values.reverse)
            (Target.Expr.openEval mode
              (Expr.cast hOutputs (.prim op seq)) targetAfter) := by
        rw [FunctionsInteractionExpressionMode.expr_openEval_cast]
        simpa [Target.Expr.openEval,
          Locals.Source.Effectful.Expr.Control.eval] using hPrimitiveRel
      have hResidualFuel : 1 < targetFuel - pre.length := by omega
      have hValue := bindDirectEval
        (mode := mode) (program := program) (ctx := ctxAfter)
        hFresh hLayout hResidualFuel hScoped hDomain
        hTargetScopeAfter hExprRel
      exact Simulation.Interaction.ForwardRel.mono hValue
        (fun _sourceDone _targetDone hValueDone =>
          DoneRel.transport_entry hScope hControl
            (DoneRel.transport_target_entry hExtends hValueDone))

theorem boundDirectOfLowering
    {mode : Mode} (hPrimitive : CompilerSelected mode)
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
    BoundHeadForward mode (argsFuel + 2) targetFuel
      (.Call (.inl prim) args) [] lower before before final tmp
      codeOverride program layout := by
  cases hLowering with
  | @primitive op lowerArgs seq hOp hArgs hSeq hOutputs =>
      intro _hLower _hFresh source target ctx hScoped hDomain hTargetScope
      have hLowerReverse :
          Expr.List.toLocals1? args.reverse = some lowerArgs.reverse :=
        Expr.List.toLocals1?_reverse hArgs
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hArgsRel :=
        (FunctionsInteractionExpressionMode.compilerDirectAt
          mode codeOverride argsFuel).evalArgs
          hLowerReverse hDirectSeq hScoped.state
      have hPrimitiveRel :=
        FunctionsInteractionExpressionMode.Expr.primitive_of_args
          mode hPrimitive (primitiveFuel := argsFuel)
          hOp hOutputs hArgsRel
      have hEval :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpressionMode.DoneRel source 1)
            (Source.evalValues mode (argsFuel + 1)
              (.Call (.inl prim) args) codeOverride source)
            (Target.Expr.openEval mode
              (Expr.cast hOutputs (.prim op seq)) target) := by
        rw [FunctionsInteractionExpressionMode.expr_openEval_cast]
        simpa [Source.evalValues, Yul.Source.Canonical.evalValues,
          Yul.Source.Effectful.evalValues, Target.Expr.openEval,
          Locals.Source.Effectful.Expr.Control.eval,
          FunctionsInteractionExpressionMode.exprSeq_openEval_seqCast] using
          hPrimitiveRel
      have hValue := bindDirectEval
        (mode := mode) (program := program) (ctx := ctx)
        hFresh hLayout hTargetFuel hScoped hDomain hTargetScope hEval
      exact singletonOfValues mode hValue

theorem boundOfLowering
    {mode : Mode} (hPrimitive : CompilerSelected mode)
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
    (hNested : RecursiveBoundHeads mode
      profile sourceProgram argsFuel targetFuel codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel +
        pre.length + 2 ≤ targetFuel)
    (hLayoutBefore : ∀ name, name ∈ layout → name ∈ before.used)
    (hLayoutAfter : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    BoundHeadForward mode (argsFuel + 2) targetFuel
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
      exact singletonOfValues mode hValue

theorem boundPrimitive
    {mode : Mode} (hPrimitive : CompilerSelected mode)
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
          RecursiveBoundHeads mode
            profile sourceProgram argsFuel targetFuel
            codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
        pre.length + 2 ≤ targetFuel)
    (hLayoutBefore : ∀ name, name ∈ layout → name ∈ before.used)
    (hLayoutAfter : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    BoundHeadForward mode fuel targetFuel
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
            FunctionsInteractionStaticCost.programBudget
                  sourceProgram argsFuel + pre.length + 2 ≤ targetFuel := by
          have hFuelLe : argsFuel ≤ argsFuel + 2 := by omega
          have hBudgetLe :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram argsFuel ≤
                FunctionsInteractionStaticCost.programBudget
                  sourceProgram (argsFuel + 2) := by
            unfold FunctionsInteractionStaticCost.programBudget
            exact FunctionsInteractionFuel.executionBudgetFor_mono
              _ _ hFuelLe
          omega
        exact
          boundOfLowering hPrimitive
            (Expr.UncheckedBoundPrimitiveLowering.primitive
              hOp hArgs hSeq hOutputs)
            hArgsOk hFresh (hNested argsFuel rfl) hArgsBudget
            hLayoutBefore hLayoutAfter hTargetFuel

theorem zeroOfLowering
    {mode : Mode} (hPrimitive : CompilerSelected mode)
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
          RecursiveBoundHeads mode profile sourceProgram argsFuel targetFuel
            codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
        pre.length + 2 ≤ targetFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : FunctionsInteractionControlRelation.ControlContextRel
      sourceScopes layout canBreak canContinue canLeave ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
        sourceScopes canBreak canContinue canLeave)
      (Source.exec mode fuel
        (.ExprStmtCall (.Call (.inl prim) args)) codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++ [.expr lower] } target) := by
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Source.exec_zero]
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
            (FunctionsInteractionExpressionMode.compilerDirectAt
              mode codeOverride argsFuel).evalArgs
              hLowerReverse hDirectSeq hRel.state
          have hPrimitiveRel :=
            FunctionsInteractionExpressionMode.Expr.primitive_of_args
              mode hPrimitive (primitiveFuel := argsFuel)
              hOp hOutputs hArgsRel
          have hEval :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionExpressionMode.DoneRel source 0)
                (Source.evalValues mode (argsFuel + 1)
                  (.Call (.inl prim) args) codeOverride source)
                (Target.Expr.openEval mode
                  (Expr.cast hOutputs (.prim op seq)) target) := by
            rw [FunctionsInteractionExpressionMode.expr_openEval_cast]
            simpa [Source.evalValues, Yul.Source.Canonical.evalValues,
              Yul.Source.Effectful.evalValues, Target.Expr.openEval,
              Locals.Source.Effectful.Expr.Control.eval,
              FunctionsInteractionExpressionMode.exprSeq_openEval_seqCast]
              using hPrimitiveRel
          have hTailFuel : 2 ≤ targetFuel := by omega
          have hStmt := FunctionsInteractionStatementMode.expr_of_evalValues
            (mode := mode) (program := program) (ctx := ctx)
            (targetFuel := targetFuel - 1)
            hEval hRel hDomain hControl hTargetScope
          have hStmt' :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionControlRelation.ControlDoneRel
                  before.used layout sourceScopes
                  canBreak canContinue canLeave)
                (Simulation.Interaction.bind
                  (Source.evalValues mode (argsFuel + 1)
                    (.Call (.inl prim) args) codeOverride source)
                  (fun result =>
                    pure
                      (Yul.InteractionSemantics.stateModel.multifill
                        [] result.1 result.2)))
                (Target.Stmt.openRun mode program ctx
                  ((targetFuel - 2) + 1)
                  (.expr (Expr.cast hOutputs (.prim op seq))) target) := by
            have hStmtFuelEq :
                targetFuel - 1 = (targetFuel - 2) + 1 := by omega
            simpa only [hStmtFuelEq] using hStmt
          have hSingleton :=
            FunctionsInteractionStatementMode.ControlDoneRel.singleton
              mode (targetFuel := targetFuel - 2) hStmt'
          rw [Source.exec_expr_primitive]
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
              exact FunctionsInteractionFuel.executionBudgetFor_mono
                _ _ (by omega)
            omega
          have hPrepared :=
            ofUncheckedLowering (ctx := ctx) hArgsOk hArgs
              (hNested argsFuel rfl) hArgsBudget hRel hDomain
              hTargetScope hLayout (by omega)
          rw [Source.exec_expr_primitive,
            Target.Block.openRun_append]
          unfold Source.evalValues Yul.Source.Canonical.evalValues
            Yul.Source.Effectful.evalValues
          change
            Simulation.Interaction.ForwardRel Truncated
              (FunctionsInteractionControlRelation.ControlDoneRel
                after.used layout sourceScopes
                canBreak canContinue canLeave)
              (Simulation.Interaction.bind
                (Simulation.Interaction.bind
                  (Source.evalArgs mode argsFuel args.reverse
                    codeOverride source)
                  (fun argsResult =>
                    (sourcePrimitive mode).eval argsFuel argsResult.1
                      prim argsResult.2.reverse))
                (fun result =>
                  pure
                    (Yul.InteractionSemantics.stateModel.multifill
                      [] result.1 result.2)))
              (Simulation.Interaction.bind
                (Target.Block.openRun mode program ctx targetFuel
                  { stmts := pre } target)
                (fun result =>
                  match result.1.mode with
                  | .regular =>
                      Target.Block.openRun mode program result.2
                        (targetFuel - pre.length)
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
              hStable hScoped hDomainAfter _hExtends hScopeExtends
              hSameControl hTargetScopeAfter =>
              simp only [Simulation.Interaction.bind_done_ok]
              have hDirectSeq :
                  Expr.List.toSeq? lowerArgs.reverse
                      (Expressions.Structured.BasicOp.inputs op) =
                    some seq := by
                simpa [Expr.List.toStackSeq?] using hSeq
              have hLength :
                  values.length =
                    Expressions.Structured.BasicOp.inputs op :=
                hStable.length.trans
                  (Expr.List.toSeq?_length hDirectSeq)
              have hEval := hStable.exprSeq_openEval hDirectSeq
                (TargetExtends.refl targetAfter.vars)
              have hControlAfter :=
                FunctionsInteractionControlRelation.ControlContextRel.transport
                  hControl (fun _name hName => hName) hSameControl
                  (fun name hName =>
                    hScopeExtends name (hControl.scope name hName))
              have hStmt :=
                FunctionsInteractionStatementMode.expr_after_args
                  hPrimitive (mode := mode) (program := program)
                  (primitiveFuel := argsFuel)
                  (targetFuel := targetFuel - pre.length - 1)
                  hOp hOutputs hLength hEval hScoped hDomainAfter
                  hControlAfter hTargetScopeAfter
              have hTailFuel : 2 ≤ targetFuel - pre.length := by omega
              have hStmt' :
                  Simulation.Interaction.ForwardRel Truncated
                    (FunctionsInteractionControlRelation.ControlDoneRel
                      after.used layout sourceScopes
                      canBreak canContinue canLeave)
                    (Simulation.Interaction.bind
                      ((sourcePrimitive mode).eval
                        argsFuel sourceAfter prim values.reverse)
                      (fun result =>
                        pure
                          (Yul.InteractionSemantics.stateModel.multifill
                            [] result.1 result.2)))
                    (Target.Stmt.openRun mode program ctxAfter
                      ((targetFuel - pre.length - 2) + 1)
                      (.expr (Expr.cast hOutputs (.prim op seq)))
                      targetAfter) := by
                have hStmtFuelEq :
                    targetFuel - pre.length - 1 =
                      (targetFuel - pre.length - 2) + 1 := by omega
                simpa only [hStmtFuelEq] using hStmt
              have hSingleton :=
                FunctionsInteractionStatementMode.ControlDoneRel.singleton
                  mode (targetFuel := targetFuel - pre.length - 2) hStmt'
              simpa [hTailFuel] using hSingleton

/-- Terminal primitive statement with the compiler-generated bounded argument
prelude, shared by ordinary and allocation-guarded primitive semantics. -/
theorem terminalOfLowering
    {mode : Mode}
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
    (hNested : RecursiveBoundHeads mode profile sourceProgram argsFuel targetFuel
      codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel +
        pre.length + 2 ≤ targetFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
        sourceScopes canBreak canContinue canLeave)
      (Source.exec mode (argsFuel + 1)
        (.ExprStmtCall (.Call (.inl prim) args)) codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++ [.terminalArgs kind seq] } target) := by
  have hPrepared :=
    ofUncheckedLowering (ctx := ctx) hArgsOk hArgsLowering hNested
      hProgramBudget hRel hDomain hTargetScope hLayout (by omega)
  rw [Source.exec_expr_primitive, Target.Block.openRun_append]
  unfold Source.evalValues Yul.Source.Canonical.evalValues
    Yul.Source.Effectful.evalValues
  change
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
        sourceScopes canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Source.evalArgs mode argsFuel args.reverse codeOverride source)
          (fun argsResult =>
            (sourcePrimitive mode).eval argsFuel argsResult.1
              prim argsResult.2.reverse))
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Simulation.Interaction.bind
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre } target)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Target.Block.openRun mode program result.2
                (targetFuel - pre.length)
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
        (TargetExtends.refl targetAfter.vars)
      have hStmt :=
        FunctionsInteractionStatementMode.terminal_after_args_control
          (mode := mode) (program := program) (ctx := ctxAfter)
          (primitiveFuel := argsFuel)
          (targetFuel := targetFuel - pre.length - 1)
          (used := after.used) (sourceScopes := sourceScopes)
          (canBreak := canBreak) (canContinue := canContinue)
          (canLeave := canLeave)
          hTerminal hLength hEval hScoped
      have hTailFuel : 2 ≤ targetFuel - pre.length := by omega
      have hStmt' :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionControlRelation.ControlDoneRel after.used layout
              sourceScopes canBreak canContinue canLeave)
            (Simulation.Interaction.bind
              ((sourcePrimitive mode).eval
                argsFuel sourceAfter prim values.reverse)
              (fun result =>
                pure
                  (Yul.InteractionSemantics.stateModel.multifill
                    [] result.1 result.2)))
            (Target.Stmt.openRun mode program ctxAfter
              ((targetFuel - pre.length - 2) + 1)
              (.terminalArgs kind seq) targetAfter) := by
        have hStmtFuelEq :
            targetFuel - pre.length - 1 =
              (targetFuel - pre.length - 2) + 1 := by omega
        simpa only [hStmtFuelEq] using hStmt
      have hSingleton :=
        FunctionsInteractionStatementMode.ControlDoneRel.singleton
          mode (targetFuel := targetFuel - pre.length - 2) hStmt'
      simpa [hTailFuel] using hSingleton

end FunctionsInteractionPreparedPrimitiveMode
end Yul
end EvmCompiler
