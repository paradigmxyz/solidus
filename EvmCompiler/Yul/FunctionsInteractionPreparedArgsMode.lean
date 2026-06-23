import EvmCompiler.Yul.FunctionsInteractionExpressionMode
import EvmCompiler.Yul.FunctionsInteractionPreparedArgs

/-!
Mode-parametric compiler-prepared argument preservation. The syntax lowering,
freshness artifacts, state relations, and control relations are shared with the
ordinary adjacent pass; only canonical source/target primitive handlers and
their delayed-expression evidence are indexed by `Mode`.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedArgsMode

open FunctionsInteractionPrimitive
open FunctionsInteractionMode

inductive DoneRel (mode : Mode)
    (layout : List Functions.Name) (fresh : Fresh.State)
    (lower : List (Locals.Expr 1))
    (entry : Functions.InteractionSemantics.State)
    (entryCtx : Functions.Source.Ctx) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Word) →
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Prop where
  | error {source target} :
      ErrorRel source target →
        DoneRel mode layout fresh lower entry entryCtx
          (.error source) (.error target)
  | regular {source values target ctx} :
      FunctionsInteractionExpressionMode.StableArgs mode lower target values →
      FunctionsInteractionRelation.ScopedStateRel layout source target →
      FunctionsInteractionRelation.TargetDomainWithin fresh.used target.vars →
      FunctionsInteractionRelation.TargetExtends entry.vars target.vars →
      Functions.Source.Ctx.ScopeExtends entryCtx ctx →
      Functions.Source.Ctx.SameControl entryCtx ctx →
      FunctionsInteractionControlRelation.TargetScopeWithin fresh.used ctx →
      DoneRel mode layout fresh lower entry entryCtx (.ok (source, values))
        (.ok (Functions.Source.Effectful.Outcome.regular target, ctx))
  | terminal {source target ctx} :
      FunctionsInteractionRelation.TerminalFailureRel source target →
        DoneRel mode layout fresh lower entry entryCtx
          (.error source) (.ok (target, ctx))

namespace DoneRel

theorem transport_entry
    {mode : Mode} {layout : List Functions.Name} {fresh : Fresh.State}
    {lower : List (Locals.Expr 1)}
    {entry : Functions.InteractionSemantics.State}
    {beforeCtx afterCtx : Functions.Source.Ctx}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      (Yul.InteractionSemantics.State × List Word)}
    {targetDone : Except EVMException
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hScopeEntry : Functions.Source.Ctx.ScopeExtends beforeCtx afterCtx)
    (hControlEntry : Functions.Source.Ctx.SameControl beforeCtx afterCtx)
    (hDone : DoneRel mode layout fresh lower entry afterCtx
      sourceDone targetDone) :
    DoneRel mode layout fresh lower entry beforeCtx sourceDone targetDone := by
  cases hDone with
  | error hError => exact .error hError
  | regular hStable hScoped hDomain hExtends hScope hControl hTargetScope =>
      exact .regular hStable hScoped hDomain hExtends
        (Functions.Source.Ctx.ScopeExtends.trans hScopeEntry hScope)
        (Functions.Source.Ctx.SameControl.trans hControlEntry hControl)
        hTargetScope
  | terminal hTerminal => exact .terminal hTerminal

theorem transport_target_entry
    {mode : Mode} {layout : List Functions.Name} {fresh : Fresh.State}
    {lower : List (Locals.Expr 1)}
    {before entry : Functions.InteractionSemantics.State}
    {entryCtx : Functions.Source.Ctx}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      (Yul.InteractionSemantics.State × List Word)}
    {targetDone : Except EVMException
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hEntry : FunctionsInteractionRelation.TargetExtends
      before.vars entry.vars)
    (hDone : DoneRel mode layout fresh lower entry entryCtx
      sourceDone targetDone) :
    DoneRel mode layout fresh lower before entryCtx sourceDone targetDone := by
  cases hDone with
  | error hError => exact .error hError
  | regular hStable hScoped hDomain hExtends hScope hControl hTargetScope =>
      exact .regular hStable hScoped hDomain
        (FunctionsInteractionRelation.TargetExtends.trans hEntry hExtends)
        hScope hControl hTargetScope
  | terminal hTerminal => exact .terminal hTerminal

end DoneRel

inductive PreparedArgsDoneRel (mode : Mode)
    (layout : List Functions.Name) {results : Nat}
    (seq : Locals.ExprSeq results) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Word) →
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Prop where
  | error {source target} :
      ErrorRel source target →
        PreparedArgsDoneRel mode layout seq (.error source) (.error target)
  | regular {source values target targetAfter ctx} :
      values.length = results →
      Target.ExprSeq.openEval mode seq target =
        .done (.ok (targetAfter, values)) →
      FunctionsInteractionRelation.ScopedStateRel
        layout source targetAfter →
      PreparedArgsDoneRel mode layout seq (.ok (source, values))
        (.ok (Functions.Source.Effectful.Outcome.regular target, ctx))
  | terminal {source target ctx} :
      FunctionsInteractionRelation.TerminalFailureRel source target →
        PreparedArgsDoneRel mode layout seq
          (.error source) (.ok (target, ctx))

namespace PreparedArgsDoneRel

theorem regular_of_stable
    {mode : Mode} {layout : List Functions.Name} {results : Nat}
    {lower : List (Locals.Expr 1)} {seq : Locals.ExprSeq results}
    {source : Yul.InteractionSemantics.State} {values : List Word}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hSeq : Expr.List.toSeq? lower results = some seq)
    (hStable : FunctionsInteractionExpressionMode.StableArgs
      mode lower target values)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    PreparedArgsDoneRel mode layout seq (.ok (source, values))
      (.ok (Functions.Source.Effectful.Outcome.regular target, ctx)) := by
  apply PreparedArgsDoneRel.regular
  · exact hStable.length.trans (Expr.List.toSeq?_length hSeq)
  · exact hStable.exprSeq_openEval hSeq
      (FunctionsInteractionRelation.TargetExtends.refl target.vars)
  · exact hRel

end PreparedArgsDoneRel

theorem to_terminal
    {mode : Mode} {layout : List Functions.Name} {fresh : Fresh.State}
    {lowerArgs : List (Locals.Expr 1)} {results : Nat}
    {seq : Locals.ExprSeq results}
    {entry : Functions.InteractionSemantics.State}
    {entryCtx : Functions.Source.Ctx}
    {sourceOpen : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Word)}
    {targetOpen : Functions.InteractionSemantics.Open
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hSeq : Expr.List.toSeq? lowerArgs results = some seq)
    (hPrepared : Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh lowerArgs entry entryCtx)
      sourceOpen targetOpen) :
    Simulation.Interaction.ForwardRel Truncated
      (PreparedArgsDoneRel mode layout seq) sourceOpen targetOpen := by
  apply Simulation.Interaction.ForwardRel.mono hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .error hError
  | regular hStable hRel _hDomain _hExtends _hScope _hControl _hTargetScope =>
      exact PreparedArgsDoneRel.regular_of_stable hSeq hStable hRel
  | terminal hTerminal => exact .terminal hTerminal

theorem nil
    (mode : Mode) {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name} {fresh : Fresh.State}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      fresh.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin fresh.used ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh [] target ctx)
      (Source.evalArgs mode fuel [] codeOverride source)
      (Target.Block.openRun mode program ctx
        (targetFuel + 1) { stmts := [] } target) := by
  rw [Target.Block.openRun_nil]
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      unfold Source.evalArgs Yul.Source.Canonical.evalArgs
      simp only [Yul.Source.Effectful.evalArgs,
        Yul.Source.Effectful.Control.fail]
      exact Simulation.Interaction.ForwardRel.truncated hTruncated
  | succ fuel =>
      have hDone : DoneRel mode layout fresh [] target ctx
          (.ok (source, []))
          (.ok (Functions.Source.Effectful.Outcome.regular target, ctx)) :=
        .regular (.nil target) hRel hDomain
          (FunctionsInteractionRelation.TargetExtends.refl target.vars)
          (Functions.Source.Ctx.ScopeExtends.refl ctx)
          (Functions.Source.Ctx.SameControl.refl ctx) hTargetScope
      simpa [Source.evalArgs, Yul.Source.Canonical.evalArgs,
        Yul.Source.Effectful.evalArgs] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

theorem singletonTarget
    {mode : Mode} {layout : List Functions.Name} {fresh : Fresh.State}
    {lower : List (Locals.Expr 1)}
    {entry target : Functions.InteractionSemantics.State}
    {entryCtx : Functions.Source.Ctx} {targetFuel : Nat}
    {sourceOpen : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Word)}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    (hStmt : Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh lower entry entryCtx) sourceOpen
      (Target.Stmt.openRun mode program ctx
        (targetFuel + 1) stmt target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh lower entry entryCtx) sourceOpen
      (Target.Block.openRun mode program ctx
        (targetFuel + 2) { stmts := [stmt] } target) := by
  have hBound : Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh lower entry entryCtx)
      (Simulation.Interaction.bind sourceOpen pure)
      (Simulation.Interaction.bind
        (Target.Stmt.openRun mode program ctx
          (targetFuel + 1) stmt target)
        fun targetResult =>
          match targetResult.1.mode with
          | .regular =>
              Target.Block.openRun mode program targetResult.2
                (targetFuel + 1) { stmts := [] } targetResult.1.state
          | .brk | .cont | .leave | .halt _ =>
              pure (targetResult.1, ctx)) := by
    apply Simulation.Interaction.ForwardRel.bind_custom hStmt
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError =>
        exact Simulation.Interaction.ForwardRel.done (.error hError)
    | regular hStable hScoped hDomain hExtends hScope hControl hTargetScope =>
        simp only
        rw [Target.Block.openRun_nil]
        exact Simulation.Interaction.ForwardRel.done
          (.regular hStable hScoped hDomain hExtends hScope hControl
            hTargetScope)
    | terminal hTerminal =>
        simp only
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
  simpa [Target.Stmt.openRun] using hBound

theorem deferred
    (mode : Mode) {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {before after : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hSafe : Expr.deferredBoundArgSafe? expr = true)
    (hLower : Expr.lower1Unchecked? before expr =
      some (pre, lower, after))
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout after [lower] target ctx)
      (Source.evalValues mode fuel expr codeOverride source)
      (Target.Block.openRun mode program ctx
        (targetFuel + 1) { stmts := pre } target) := by
  obtain ⟨rfl, rfl, hDirect⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hLower
  rw [Target.Block.openRun_nil]
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      unfold Source.evalValues Yul.Source.Canonical.evalValues
      simp only [Yul.Source.Effectful.evalValues,
        Yul.Source.Effectful.Control.fail]
      exact Simulation.Interaction.ForwardRel.truncated hTruncated
  | succ fuel =>
      cases expr with
      | Lit value =>
          simp [Expr.toLocals?, Expr.cast] at hDirect
          subst lower
          have hDone : DoneRel mode layout after [.lit value] target ctx
              (.ok (source, [value]))
              (.ok (Functions.Source.Effectful.Outcome.regular target, ctx)) :=
            .regular
              (.cons
                (FunctionsInteractionExpressionMode.StableValue.lit
                  mode target value)
                (.nil target))
              hRel hDomain
              (FunctionsInteractionRelation.TargetExtends.refl target.vars)
              (Functions.Source.Ctx.ScopeExtends.refl ctx)
              (Functions.Source.Ctx.SameControl.refl ctx)
              (hTargetScope.mono
                (Expr.lower1Unchecked?_stateExtends hLower))
          simpa [Source.evalValues, Yul.Source.Canonical.evalValues,
            Yul.Source.Effectful.evalValues] using
            (Simulation.Interaction.ForwardRel.done
              (truncated := Truncated) hDone)
      | Var name =>
          simp [Expr.toLocals?, Expr.cast] at hDirect
          subst lower
          cases hLookup : source.lookup? name with
          | none =>
              have hTruncated : Truncated
                  ({ exception := .UnknownIdentifier name, state := source } :
                    Yul.InteractionSemantics.Failure) := by
                trivial
              simpa [Source.evalValues, Yul.Source.Canonical.evalValues,
                Yul.Source.Effectful.evalValues,
                Yul.InteractionSemantics.stateModel,
                Yul.Source.Effectful.Control.fail, hLookup] using
                (Simulation.Interaction.ForwardRel.truncated
                  (doneRel := DoneRel mode layout after
                    [.var (identName name)] target ctx)
                  (right := pure
                    (Functions.Source.Effectful.Outcome.regular target, ctx))
                  hTruncated)
          | some value =>
              have hTarget := hRel.state.lookup hLookup
              have hDone : DoneRel mode layout after
                  [.var (identName name)] target ctx
                  (.ok (source, [value]))
                  (.ok
                    (Functions.Source.Effectful.Outcome.regular target, ctx)) :=
                .regular
                  (.cons
                    (FunctionsInteractionExpressionMode.StableValue.var
                      (mode := mode) hTarget)
                    (.nil target))
                  hRel hDomain
                  (FunctionsInteractionRelation.TargetExtends.refl target.vars)
                  (Functions.Source.Ctx.ScopeExtends.refl ctx)
                  (Functions.Source.Ctx.SameControl.refl ctx)
                  (hTargetScope.mono
                    (Expr.lower1Unchecked?_stateExtends hLower))
              simpa [Source.evalValues, Yul.Source.Canonical.evalValues,
                Yul.Source.Effectful.evalValues,
                Yul.InteractionSemantics.stateModel, hLookup] using
                (Simulation.Interaction.ForwardRel.done
                  (truncated := Truncated) hDone)
      | Call callee args =>
          simp [Expr.deferredBoundArgSafe?] at hSafe

theorem deferred_arg
    (mode : Mode) {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {before after : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hSafe : Expr.deferredBoundArgSafe? expr = true)
    (hLower : Expr.lower1Unchecked? before expr =
      some (pre, lower, after))
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout after [lower] target ctx)
      (Source.evalArgs mode fuel [expr] codeOverride source)
      (Target.Block.openRun mode program ctx
        (targetFuel + 1) { stmts := pre } target) := by
  obtain ⟨rfl, rfl, hDirect⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hLower
  rw [Target.Block.openRun_nil]
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      unfold Source.evalArgs Yul.Source.Canonical.evalArgs
      simp only [Yul.Source.Effectful.evalArgs,
        Yul.Source.Effectful.Control.fail]
      exact Simulation.Interaction.ForwardRel.truncated hTruncated
  | succ tailFuel =>
      cases tailFuel with
      | zero =>
          rw [Source.evalArgs_one_cons]
          have hHead := deferred mode
            (fuel := 0) (targetFuel := targetFuel)
            (codeOverride := codeOverride) (program := program) (ctx := ctx)
            hSafe hLower hRel hDomain hTargetScope
          rw [Target.Block.openRun_nil] at hHead
          apply Simulation.Interaction.ForwardRel.bind_custom hHead
          intro sourceDone targetDone hDone
          cases hDone with
          | error hError =>
              exact Simulation.Interaction.ForwardRel.done (.error hError)
          | @regular sourceValues values targetAfter targetCtx
              hStable hScoped hFinalDomain hExtends hScope hControl
              _hTargetScope =>
              have hTruncated : Truncated
                  ({ exception := .OutOfFuel, state := sourceValues } :
                    Yul.InteractionSemantics.Failure) := by
                trivial
              simpa [Yul.InteractionSemantics.Primitive.fail] using
                (Simulation.Interaction.ForwardRel.truncated
                  (doneRel := DoneRel mode layout after [lower] target ctx)
                  (right := pure
                    (Functions.Source.Effectful.Outcome.regular targetAfter,
                      targetCtx)) hTruncated)
          | terminal hTerminal =>
              exact Simulation.Interaction.ForwardRel.done
                (.terminal hTerminal)
      | succ residualFuel =>
          rw [show residualFuel + 1 + 1 = residualFuel + 2 by omega,
            Source.evalArgs_succ_succ_cons]
          have hHead := deferred mode
            (fuel := residualFuel + 1) (targetFuel := targetFuel)
            (codeOverride := codeOverride) (program := program) (ctx := ctx)
            hSafe hLower hRel hDomain hTargetScope
          rw [Target.Block.openRun_nil] at hHead
          have hBound : Simulation.Interaction.ForwardRel Truncated
              (DoneRel mode layout after [lower] target ctx)
              (Simulation.Interaction.bind
                (Source.evalValues mode (residualFuel + 1) expr
                  codeOverride source)
                (fun headResult =>
                  Simulation.Interaction.bind
                    (Source.evalArgs mode residualFuel []
                      codeOverride headResult.1)
                    (fun tailResult =>
                      pure (tailResult.1,
                        headResult.2.head! :: tailResult.2))))
              (Simulation.Interaction.bind
                (pure (Functions.Source.Effectful.Outcome.regular target, ctx))
                pure) := by
            apply Simulation.Interaction.ForwardRel.bind_custom hHead
            intro sourceDone targetDone hDone
            cases hDone with
            | error hError =>
                exact Simulation.Interaction.ForwardRel.done (.error hError)
            | @regular sourceAfter values targetAfter targetCtx
                hStable hScoped hFinalDomain hExtends hScope hControl
                hTargetScopeAfter =>
                cases residualFuel with
                | zero =>
                    have hTruncated : Truncated
                        ({ exception := .OutOfFuel, state := sourceAfter } :
                          Yul.InteractionSemantics.Failure) := by
                      trivial
                    unfold Source.evalArgs Yul.Source.Canonical.evalArgs
                    simp only [Yul.Source.Effectful.evalArgs,
                      Yul.Source.Effectful.Control.fail]
                    exact Simulation.Interaction.ForwardRel.truncated
                      hTruncated
                | succ fuel =>
                    have hTail :
                        Source.evalArgs mode (fuel + 1) []
                            codeOverride sourceAfter =
                          pure (sourceAfter, []) := by
                      simp [Source.evalArgs, Yul.Source.Canonical.evalArgs,
                        Yul.Source.Effectful.evalArgs]
                    have hLength : values.length = 1 := by
                      simpa using hStable.length
                    obtain ⟨value, rfl⟩ :=
                      List.length_eq_one_iff.mp hLength
                    simpa [hTail] using
                      (Simulation.Interaction.ForwardRel.done
                        (truncated := Truncated)
                        (DoneRel.regular hStable hScoped hFinalDomain
                          hExtends hScope hControl hTargetScopeAfter))
            | terminal hTerminal =>
                exact Simulation.Interaction.ForwardRel.done
                  (.terminal hTerminal)
          simpa using hBound

theorem singletonOfValues
    (mode : Mode) {headFuel : Nat}
    {expr : AstExpr} {lower : Locals.Expr 1} {fresh : Fresh.State}
    {entry : Functions.InteractionSemantics.State}
    {entryCtx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {targetOpen : Functions.InteractionSemantics.Open
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hHead : Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh [lower] entry entryCtx)
      (Source.evalValues mode headFuel expr codeOverride source)
      targetOpen) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh [lower] entry entryCtx)
      (Source.evalArgs mode (headFuel + 1) [expr] codeOverride source)
      targetOpen := by
  have hBound : Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout fresh [lower] entry entryCtx)
      (Source.evalArgs mode (headFuel + 1) [expr] codeOverride source)
      (Simulation.Interaction.bind targetOpen pure) := by
    cases headFuel with
    | zero =>
        rw [Source.evalArgs_one_cons]
        apply Simulation.Interaction.ForwardRel.bind_custom hHead
        intro sourceDone targetDone hDone
        cases hDone with
        | error hError =>
            exact Simulation.Interaction.ForwardRel.done (.error hError)
        | terminal hTerminal =>
            exact Simulation.Interaction.ForwardRel.done (.terminal hTerminal)
        | @regular sourceAfter values targetAfter ctxAfter
            _hStable _hScoped _hDomain _hExtends _hScope _hControl
            _hTargetScope =>
            have hTruncated : Truncated
                ({ exception := .OutOfFuel, state := sourceAfter } :
                  Yul.InteractionSemantics.Failure) := by
              trivial
            simpa [Yul.InteractionSemantics.Primitive.fail] using
              (Simulation.Interaction.ForwardRel.truncated
                (doneRel := DoneRel mode layout fresh [lower] entry entryCtx)
                (right := pure
                  (Functions.Source.Effectful.Outcome.regular
                    targetAfter, ctxAfter)) hTruncated)
    | succ tailFuel =>
        rw [show tailFuel + 1 + 1 = tailFuel + 2 by omega,
          Source.evalArgs_succ_succ_cons]
        apply Simulation.Interaction.ForwardRel.bind_custom hHead
        intro sourceDone targetDone hDone
        cases hDone with
        | error hError =>
            exact Simulation.Interaction.ForwardRel.done (.error hError)
        | terminal hTerminal =>
            exact Simulation.Interaction.ForwardRel.done (.terminal hTerminal)
        | @regular sourceAfter values targetAfter ctxAfter
            hStable hScoped hDomain hExtends hScope hControl hTargetScope =>
            cases tailFuel with
            | zero =>
                have hTruncated : Truncated
                    ({ exception := .OutOfFuel, state := sourceAfter } :
                      Yul.InteractionSemantics.Failure) := by
                  trivial
                unfold Source.evalArgs Yul.Source.Canonical.evalArgs
                simp only [Yul.Source.Effectful.evalArgs,
                  Yul.Source.Effectful.Control.fail]
                exact Simulation.Interaction.ForwardRel.truncated hTruncated
            | succ remaining =>
                have hTail :
                    Source.evalArgs mode (remaining + 1) []
                        codeOverride sourceAfter = pure (sourceAfter, []) := by
                  simp [Source.evalArgs, Yul.Source.Canonical.evalArgs,
                    Yul.Source.Effectful.evalArgs]
                have hLength : values.length = 1 := by
                  simpa using hStable.length
                obtain ⟨value, rfl⟩ :=
                  List.length_eq_one_iff.mp hLength
                simpa [hTail] using
                  (Simulation.Interaction.ForwardRel.done
                    (truncated := Truncated)
                    (DoneRel.regular hStable hScoped hDomain hExtends
                      hScope hControl hTargetScope))
  have hTargetPure :
      Simulation.Interaction.bind targetOpen (fun result => pure result) =
        targetOpen := Simulation.Interaction.bind_pure _
  rw [hTargetPure] at hBound
  exact hBound

theorem direct
    (mode : Mode) {fuel targetFuel : Nat}
    {expr : AstExpr} {rest : List AstExpr}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)} {lowerHead : Locals.Expr 1}
    {initial stateRest stateHead : Fresh.State}
    {entry : Functions.InteractionSemantics.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hSafe : Expr.deferredBoundArgSafe? expr = true)
    (hHead : Expr.lower1Unchecked? stateRest expr =
      some (preHead, lowerHead, stateHead))
    (hRest : Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout stateRest lowerRest.reverse entry ctx)
      (Source.evalArgs mode fuel rest.reverse codeOverride source)
      (Target.Block.openRun mode program ctx
        targetFuel { stmts := preRest } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout stateHead
        (lowerHead :: lowerRest).reverse entry ctx)
      (Source.evalArgs mode fuel (expr :: rest).reverse codeOverride source)
      (Target.Block.openRun mode program ctx
        targetFuel { stmts := preRest ++ preHead } target) := by
  obtain ⟨rfl, rfl, hDirect⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hHead
  simp only [List.append_nil, List.reverse_cons]
  rw [Source.evalArgs_append]
  have hBound : Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout stateHead
        (lowerRest.reverse ++ [lowerHead]) entry ctx)
      (Simulation.Interaction.bind
        (Source.evalArgs mode fuel rest.reverse codeOverride source)
        (fun restResult =>
          Simulation.Interaction.bind
            (Source.evalArgs mode (fuel - 2 * rest.reverse.length)
              [expr] codeOverride restResult.1)
            (fun headResult =>
              pure (headResult.1,
                restResult.2 ++ headResult.2))))
      (Simulation.Interaction.bind
        (Target.Block.openRun mode program ctx
          targetFuel { stmts := preRest } target)
        pure) := by
    apply Simulation.Interaction.ForwardRel.bind_custom hRest
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError =>
        exact Simulation.Interaction.ForwardRel.done (.error hError)
    | terminal hTerminal =>
        exact Simulation.Interaction.ForwardRel.done (.terminal hTerminal)
    | @regular sourceRest restValues targetRest ctxRest
        hStableRest hScopedRest hDomainRest hExtendsRest
        hScopeRest hControlRest hTargetScopeRest =>
        have hHeadRel := deferred_arg mode
          (fuel := fuel - 2 * rest.reverse.length) (targetFuel := 0)
          (codeOverride := codeOverride) (program := program) (ctx := ctxRest)
          hSafe hHead hScopedRest hDomainRest hTargetScopeRest
        rw [Target.Block.openRun_nil] at hHeadRel
        apply Simulation.Interaction.ForwardRel.bind_custom hHeadRel
        intro headSourceDone headTargetDone hHeadDone
        cases hHeadDone with
        | error hError =>
            exact Simulation.Interaction.ForwardRel.done (.error hError)
        | terminal hTerminal =>
            exact Simulation.Interaction.ForwardRel.done (.terminal hTerminal)
        | @regular sourceAfter headValues targetAfter ctxAfter
            hStableHead hScopedHead hDomainHead hExtendsHead
            hScopeHead hControlHead hTargetScopeHead =>
            have hStableRest' := hStableRest.mono hExtendsHead
            have hStableFinal := hStableRest'.append hStableHead
            have hExtendsFinal :=
              FunctionsInteractionRelation.TargetExtends.trans
                hExtendsRest hExtendsHead
            exact Simulation.Interaction.ForwardRel.done
              (.regular hStableFinal hScopedHead hDomainHead hExtendsFinal
                (Functions.Source.Ctx.ScopeExtends.trans
                  hScopeRest hScopeHead)
                (Functions.Source.Ctx.SameControl.trans
                  hControlRest hControlHead)
                hTargetScopeHead)
  have hTargetPure :
      Simulation.Interaction.bind
          (Target.Block.openRun mode program ctx
            targetFuel { stmts := preRest } target)
          (fun result => pure result) =
        Target.Block.openRun mode program ctx
          targetFuel { stmts := preRest } target :=
    Simulation.Interaction.bind_pure _
  rw [hTargetPure] at hBound
  exact hBound

/-- Recursive expression-owner capability consumed by bounded argument
lowering after the already prepared tail. -/
def BoundHeadForward
    (mode : Mode) (fuel targetFuel : Nat)
    (expr : AstExpr) (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (before after final : Fresh.State) (tmp : Functions.Name)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (program : Functions.Program) (layout : List Functions.Name) : Prop :=
  Expr.lower1Unchecked? before expr = some (pre, lower, after) →
  Fresh.fresh? after = some (tmp, final) →
  ∀ {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State}
      {ctx : Functions.Source.Ctx},
    FunctionsInteractionRelation.ScopedStateRel layout source target →
    FunctionsInteractionRelation.TargetDomainWithin
        before.used target.vars →
    FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx →
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel mode layout final [.var tmp] target ctx)
        (Source.evalArgs mode fuel [expr] codeOverride source)
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre ++ [.let_ tmp lower] } target)

/-- With fewer than two list-fuel units, a singleton argument computation is
source-truncated before any completed head result needs relating. -/
theorem boundHead_lowFuel
    {mode : Mode} {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hFuel : fuel < 2) :
    BoundHeadForward mode fuel targetFuel expr pre lower before after final tmp
      codeOverride program layout := by
  intro _hLower _hFresh source target ctx _hScoped _hDomain _hTargetScope
  cases fuel with
  | zero =>
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Source.evalArgs, Yul.Source.Canonical.evalArgs,
        Yul.Source.Effectful.evalArgs,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.Source.Effectful.Control.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel mode layout final [.var tmp] target ctx)
          (right := Target.Block.openRun mode program ctx targetFuel
            { stmts := pre ++ [.let_ tmp lower] } target)
          hTruncated)
  | succ remaining =>
      have hRemaining : remaining = 0 := by omega
      subst remaining
      rw [Source.evalArgs_one_cons]
      have hEvalZero :
          Source.evalValues mode 0 expr codeOverride source =
            Yul.InteractionSemantics.Primitive.fail source .OutOfFuel := by
        unfold Source.evalValues Yul.Source.Canonical.evalValues
          Yul.Source.Effectful.evalValues
        rfl
      rw [hEvalZero]
      have hTruncated : Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel mode layout final [.var tmp] target ctx)
          (right := Target.Block.openRun mode program ctx targetFuel
            { stmts := pre ++ [.let_ tmp lower] } target)
          hTruncated)

/-- Adjacent expression-owner interface before the bounded-argument owner
stores the delayed value in its compiler-private temporary. -/
def HeadValueForward
    (mode : Mode) (fuel targetFuel : Nat)
    (expr : AstExpr) (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (before after : Fresh.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (program : Functions.Program) (layout : List Functions.Name) : Prop :=
  Expr.lower1Unchecked? before expr = some (pre, lower, after) →
  ∀ {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State}
      {ctx : Functions.Source.Ctx},
    FunctionsInteractionRelation.ScopedStateRel layout source target →
    FunctionsInteractionRelation.TargetDomainWithin
        before.used target.vars →
    FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx →
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel mode layout after [lower] target ctx)
        (Source.evalArgs mode fuel [expr] codeOverride source)
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre } target)

/-- Deferred literals and variables satisfy the expression-owner interface
without executing a generated prelude. -/
theorem deferredHeadValue
    {mode : Mode} {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {before after : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hTargetFuel : 0 < targetFuel)
    (hSafe : Expr.deferredBoundArgSafe? expr = true) :
    HeadValueForward mode fuel targetFuel expr pre lower before after
      codeOverride program layout := by
  intro hLower source target ctx hScoped hDomain hTargetScope
  cases targetFuel with
  | zero => omega
  | succ remaining =>
      simpa [Nat.succ_eq_add_one] using
        (deferred_arg mode
          (fuel := fuel) (targetFuel := remaining)
          (codeOverride := codeOverride) (program := program) (ctx := ctx)
          hSafe hLower hScoped hDomain hTargetScope)

/-- Store an expression owner's stable delayed value in the fresh temporary
owned by bounded-argument lowering. -/
theorem bindHeadValue
    {mode : Mode} {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hLayout : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hValue : HeadValueForward mode fuel targetFuel expr pre lower
      before after codeOverride program layout) :
    BoundHeadForward mode fuel targetFuel expr pre lower before after final tmp
      codeOverride program layout := by
  intro hLower hFresh source target ctx hScoped hDomain hTargetScope
  rw [Target.Block.openRun_append]
  have hValueRel := hValue hLower (ctx := ctx) hScoped hDomain hTargetScope
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel mode layout final [.var tmp] target ctx)
        (Simulation.Interaction.bind
          (Source.evalArgs mode fuel [expr] codeOverride source) pure)
        (Simulation.Interaction.bind
          (Target.Block.openRun mode program ctx targetFuel
            { stmts := pre } target)
          (fun result =>
            match result.1.mode with
            | .regular =>
                Target.Block.openRun mode program result.2
                  (targetFuel - pre.length)
                  { stmts := [.let_ tmp lower] } result.1.state
            | .brk | .cont | .leave | .halt _ => pure result)) := by
    apply Simulation.Interaction.ForwardRel.bind_custom hValueRel
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
        hStable hScopedAfter hDomainAfter hExtendsAfter
        hScopeAfter hControlAfter hTargetScopeAfter =>
        have hLength : values.length = 1 := by
          simpa using hStable.length
        obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLength
        cases hStable with
        | cons hStableValue _hStableTail =>
            obtain ⟨hFinalUsed, hTmpFresh⟩ :=
              Fresh.fresh?_components hFresh
            have hTmpLayout : tmp ∉ layout := by
              intro hMem
              exact hTmpFresh (hLayout tmp hMem)
            have hTmpNone : targetAfter.vars tmp = none :=
              hDomainAfter.lookup_none hTmpFresh
            let targetFinal := targetAfter.insert tmp value
            let ctxFinal := { ctxAfter with scope := tmp :: ctxAfter.scope }
            have hResidual :
                ∃ remaining, targetFuel - pre.length = remaining + 2 := by
              refine ⟨targetFuel - pre.length - 2, ?_⟩
              omega
            obtain ⟨remaining, hResidual⟩ := hResidual
            have hEval := hStableValue targetAfter
              (FunctionsInteractionRelation.TargetExtends.refl
                targetAfter.vars)
            have hTargetLet :
                Target.Block.openRun mode program ctxAfter
                    (targetFuel - pre.length)
                    { stmts := [.let_ tmp lower] } targetAfter =
                  pure
                    (Functions.Source.Effectful.Outcome.regular
                      targetFinal, ctxFinal) := by
              rw [hResidual,
                show remaining + 2 = (remaining + 1) + 1 by omega,
                Target.Block.openRun_cons]
              change
                Simulation.Interaction.bind
                    (Target.Stmt.openRun mode program ctxAfter
                      (remaining + 1) (.let_ tmp lower) targetAfter)
                    _ = _
              rw [Target.Stmt.openRun_let, hEval,
                Simulation.Interaction.bind_done_ok]
              simp only [Simulation.Interaction.monad_pure_bind]
              change
                Target.Block.openRun mode program ctxFinal
                    (remaining + 1) { stmts := [] } targetFinal =
                  pure
                    (Functions.Source.Effectful.Outcome.regular
                      targetFinal, ctxFinal)
              rw [Target.Block.openRun_nil]
            change
              Simulation.Interaction.ForwardRel Truncated
                (DoneRel mode layout final [.var tmp] target ctx)
                (pure (sourceAfter, [value]))
                (Target.Block.openRun mode program ctxAfter
                  (targetFuel - pre.length)
                  { stmts := [.let_ tmp lower] } targetAfter)
            rw [hTargetLet]
            have hScopedFinal :=
              hScopedAfter.insert_private hTmpLayout value
            have hDomainFinal :
                FunctionsInteractionRelation.TargetDomainWithin
                  final.used targetFinal.vars := by
              rw [hFinalUsed]
              exact hDomainAfter.insert hTmpFresh
            have hInsertExtends :=
              FunctionsInteractionRelation.TargetExtends.insert_fresh
                (value := value) hTmpNone
            have hExtendsFinal :=
              FunctionsInteractionRelation.TargetExtends.trans
                hExtendsAfter hInsertExtends
            have hLookup : targetFinal.vars tmp = some value := by
              simp [targetFinal, Locals.Source.State.insert,
                Locals.Source.Store.insert]
            have hTargetScopeFinal :
                FunctionsInteractionControlRelation.TargetScopeWithin
                  final.used ctxFinal := by
              intro name hName
              change name ∈ tmp :: ctxAfter.scope at hName
              rw [hFinalUsed]
              rcases List.mem_cons.mp hName with rfl | hName
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem tmp
                  (hTargetScopeAfter name hName)
            exact Simulation.Interaction.ForwardRel.done
              (.regular
                (.cons
                  (FunctionsInteractionExpressionMode.StableValue.var
                    (mode := mode) hLookup)
                  (.nil targetFinal))
                hScopedFinal hDomainFinal hExtendsFinal
                (Functions.Source.Ctx.ScopeExtends.trans hScopeAfter
                  (Functions.Source.Ctx.ScopeExtends.cons ctxAfter tmp))
                (Functions.Source.Ctx.SameControl.trans hControlAfter
                  (Functions.Source.Ctx.SameControl.scopeUpdate
                    ctxAfter (tmp :: ctxAfter.scope)))
                hTargetScopeFinal)
  have hSourcePure :
      Simulation.Interaction.bind
          (Source.evalArgs mode fuel [expr] codeOverride source)
          (fun result => pure result) =
        Source.evalArgs mode fuel [expr] codeOverride source :=
    Simulation.Interaction.bind_pure _
  rw [hSourcePure] at hBound
  exact hBound

/-- A deferred expression can still enter the compiler's spilling branch when
the delayed argument window is full. -/
theorem boundDeferred
    {mode : Mode} {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hSafe : Expr.deferredBoundArgSafe? expr = true)
    (hLayout : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    BoundHeadForward mode fuel targetFuel expr pre lower before after final tmp
      codeOverride program layout :=
  bindHeadValue hLayout hTargetFuel
    (deferredHeadValue (by omega) hSafe)

/-- Compose a recursively prepared tail with one generated, fresh-bound head.
Recursive expression reasoning remains behind `BoundHeadForward`. -/
theorem bound
    {mode : Mode} {fuel targetFuel : Nat}
    {expr : AstExpr} {rest : List AstExpr}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)} {lowerHead : Locals.Expr 1}
    {initial stateRest stateHead stateFresh : Fresh.State}
    {tmp : Functions.Name}
    {entry : Functions.InteractionSemantics.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hHead : Expr.lower1Unchecked? stateRest expr =
      some (preHead, lowerHead, stateHead))
    (hFresh : Fresh.fresh? stateHead = some (tmp, stateFresh))
    (hHeadForward : BoundHeadForward mode
      (fuel - 2 * rest.reverse.length)
      (targetFuel - preRest.length)
      expr preHead lowerHead stateRest stateHead stateFresh tmp
      codeOverride program layout)
    (hRest :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel mode layout stateRest lowerRest.reverse entry ctx)
        (Source.evalArgs mode fuel rest.reverse codeOverride source)
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := preRest } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout stateFresh
        (.var tmp :: lowerRest).reverse entry ctx)
      (Source.evalArgs mode fuel (expr :: rest).reverse
        codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := preRest ++ preHead ++ [.let_ tmp lowerHead] } target) := by
  simp only [List.reverse_cons]
  rw [Source.evalArgs_append, List.append_assoc,
    Target.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_custom hRest
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
  | @regular sourceRest restValues targetRest ctxRest
      hStableRest hScopedRest hDomainRest hExtendsRest
      hScopeRest hControlRest hTargetScopeRest =>
      have hHeadRel :=
        hHeadForward hHead hFresh (ctx := ctxRest)
          hScopedRest hDomainRest hTargetScopeRest
      have hHeadBound :
          Simulation.Interaction.ForwardRel Truncated
            (DoneRel mode layout stateFresh
              (lowerRest.reverse ++ [.var tmp]) entry ctx)
            (Simulation.Interaction.bind
              (Source.evalArgs mode
                (fuel - 2 * rest.reverse.length) [expr]
                codeOverride sourceRest)
              (fun headResult =>
                pure (headResult.1,
                  restValues ++ headResult.2)))
            (Simulation.Interaction.bind
              (Target.Block.openRun mode program ctxRest
                (targetFuel - preRest.length)
                { stmts := preHead ++ [.let_ tmp lowerHead] }
                targetRest)
              pure) := by
        apply Simulation.Interaction.ForwardRel.bind_custom hHeadRel
        intro headSourceDone headTargetDone hHeadDone
        cases hHeadDone with
        | error hError =>
            exact Simulation.Interaction.ForwardRel.done (.error hError)
        | terminal hTerminal =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal hTerminal)
        | @regular sourceAfter headValues targetAfter ctxAfter
            hStableHead hScopedHead hDomainHead hExtendsHead
            hScopeHead hControlHead hTargetScopeHead =>
            have hStableRest' := hStableRest.mono hExtendsHead
            have hStableFinal := hStableRest'.append hStableHead
            have hExtendsFinal :=
              FunctionsInteractionRelation.TargetExtends.trans
                hExtendsRest hExtendsHead
            exact Simulation.Interaction.ForwardRel.done
              (.regular hStableFinal hScopedHead hDomainHead hExtendsFinal
                (Functions.Source.Ctx.ScopeExtends.trans
                  hScopeRest hScopeHead)
                (Functions.Source.Ctx.SameControl.trans
                  hControlRest hControlHead)
                hTargetScopeHead)
      have hTargetPure :
          Simulation.Interaction.bind
              (Target.Block.openRun mode program ctxRest
                (targetFuel - preRest.length)
                { stmts := preHead ++ [.let_ tmp lowerHead] }
                targetRest)
              (fun result => pure result) =
            Target.Block.openRun mode program ctxRest
              (targetFuel - preRest.length)
              { stmts := preHead ++ [.let_ tmp lowerHead] }
              targetRest :=
        Simulation.Interaction.bind_pure _
      rw [hTargetPure] at hHeadBound
      exact hHeadBound

/-- Fuel-indexed recursive expression capability consumed privately by the
compiler-owned bounded-argument induction. -/
def RecursiveBoundHeads
    (mode : Mode) (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (fuel targetFuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (program : Functions.Program) (layout : List Functions.Name) : Prop :=
  ∀ {expr : AstExpr} {rest : List AstExpr}
    {preRest preHead : List Functions.Stmt}
    {lowerHead : Locals.Expr 1}
    {stateRest stateHead stateFresh : Fresh.State}
    {tmp : Functions.Name},
    SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr = true →
      Expr.lower1Unchecked? stateRest expr =
        some (preHead, lowerHead, stateHead) →
      Fresh.fresh? stateHead = some (tmp, stateFresh) →
        preHead.length + 1 < targetFuel - preRest.length →
        (∀ name, name ∈ layout → name ∈ stateRest.used) →
        (∀ name, name ∈ layout → name ∈ stateHead.used) →
        FunctionsInteractionStaticCost.programBudget sourceProgram
              (fuel - 2 * rest.reverse.length) +
            preRest.length + preHead.length + 2 ≤ targetFuel →
          BoundHeadForward mode
            (fuel - 2 * rest.reverse.length)
            (targetFuel - preRest.length)
            expr preHead lowerHead stateRest stateHead stateFresh tmp
            codeOverride program layout

/-- Preservation for the complete compiler-owned bounded argument artifact.
Only a generated, fresh-bound expression head is delegated to the recursive
expression owner; empty and deferred branches are discharged here. -/
theorem ofUncheckedLowering
    {mode : Mode}
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program}
    {fuel targetFuel : Nat}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {initial final : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hArgsOk : SolcValidation.ExprsOk?
      profile sourceProgram.contract layout args = true)
    (hLowering : Expr.List.UncheckedBoundLowering
      initial args pre lowerArgs final)
    (hBound : RecursiveBoundHeads mode
      profile sourceProgram fuel targetFuel codeOverride program layout)
    (hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
        pre.length + 2 ≤ targetFuel)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      initial.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hTargetFuel : pre.length < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel mode layout final lowerArgs.reverse target ctx)
      (Source.evalArgs mode fuel args.reverse codeOverride source)
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre } target) := by
  induction hLowering with
  | nil =>
      cases targetFuel with
      | zero => simp at hTargetFuel
      | succ remaining =>
          simpa using
            (nil mode (fuel := fuel) (targetFuel := remaining)
              (codeOverride := codeOverride) (program := program)
              (ctx := ctx) hRel hDomain hTargetScope)
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      have hOkParts :
          SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr = true ∧
            SolcValidation.ExprsOk? profile sourceProgram.contract layout rest = true := by
        simpa [SolcValidation.ExprsOk?] using hArgsOk
      have hRestOk :
          SolcValidation.ExprsOk? profile sourceProgram.contract layout rest = true :=
        hOkParts.2
      obtain ⟨rfl, rfl, _hLower⟩ :=
        Expr.lower1Unchecked?_deferred_parts hDirect.1 hHead
      have hRestFuel : preRest.length < targetFuel := by
        simpa using hTargetFuel
      have hRestBudget :
          FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
              preRest.length + 2 ≤ targetFuel := by
        simpa using hProgramBudget
      have hRestForward := ih hRestOk hRestBudget hRestFuel
      exact direct mode (initial := initial) hDirect.1 hHead hRestForward
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead _hDirect hFresh ih =>
      have hOkParts :
          SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr = true ∧
            SolcValidation.ExprsOk? profile sourceProgram.contract layout rest = true := by
        simpa [SolcValidation.ExprsOk?] using hArgsOk
      have hRestFuel : preRest.length < targetFuel := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hTargetFuel
        omega
      have hRestBudget :
          FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
              preRest.length + 2 ≤ targetFuel := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hProgramBudget
        omega
      have hRestForward := ih hOkParts.2 hRestBudget hRestFuel
      have hHeadFuel :
          preHead.length + 1 < targetFuel - preRest.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hTargetFuel
        omega
      have hRestExtends : Fresh.Extends initial stateRest :=
        hRest.stateExtends (fun hExpr =>
          Expr.lower1Unchecked?_stateExtends hExpr)
      have hHeadExtends : Fresh.Extends stateRest stateHead :=
        Expr.lower1Unchecked?_stateExtends hHead
      have hRestLayout :
          ∀ name, name ∈ layout → name ∈ stateRest.used := by
        intro name hMem
        exact hRestExtends name (hLayout name hMem)
      have hHeadLayout :
          ∀ name, name ∈ layout → name ∈ stateHead.used := by
        intro name hMem
        exact hHeadExtends name (hRestLayout name hMem)
      have hHeadFuelLe : fuel - 2 * rest.reverse.length ≤ fuel := by
        omega
      have hHeadProgramLe :
          FunctionsInteractionStaticCost.programBudget sourceProgram
              (fuel - 2 * rest.reverse.length) ≤
            FunctionsInteractionStaticCost.programBudget sourceProgram fuel := by
        unfold FunctionsInteractionStaticCost.programBudget
        exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ hHeadFuelLe
      have hHeadBudget :
          FunctionsInteractionStaticCost.programBudget sourceProgram
                (fuel - 2 * rest.reverse.length) +
              preRest.length + preHead.length + 2 ≤ targetFuel := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hProgramBudget
        omega
      exact bound (initial := initial) hHead hFresh
        (hBound hOkParts.1 hHead hFresh hHeadFuel
          hRestLayout hHeadLayout hHeadBudget)
        hRestForward

end FunctionsInteractionPreparedArgsMode
end Yul
end EvmCompiler
