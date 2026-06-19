import EvmCompiler.Yul.FunctionsInteractionStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedArgs

open FunctionsInteractionPrimitive

/-- Recursive argument-lowering result owned by the Yul-to-Functions pass.
The expression list is already in execution order (`lowerArgs.reverse`). -/
inductive DoneRel
    (layout : List Functions.Name) (fresh : Fresh.State)
    (lower : List (Locals.Expr 1))
    (entry : Functions.InteractionSemantics.State) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Word) →
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Prop where
  | error {source target} :
      FunctionsInteractionPrimitive.ErrorRel source target →
        DoneRel layout fresh lower entry (.error source) (.error target)
  | regular {source values target ctx} :
      FunctionsInteractionExpression.StableArgs lower target values →
      FunctionsInteractionRelation.ScopedStateRel layout source target →
      FunctionsInteractionRelation.TargetDomainWithin fresh.used target.vars →
      FunctionsInteractionRelation.TargetExtends entry.vars target.vars →
      DoneRel layout fresh lower entry (.ok (source, values))
        (.ok (Functions.Source.Effectful.Outcome.regular target, ctx))
  | terminal {source target ctx} :
      FunctionsInteractionRelation.TerminalFailureRel source target →
        DoneRel layout fresh lower entry (.error source) (.ok (target, ctx))

/-- Forget recursive freshness/stability bookkeeping once the compiler's
dependent argument sequence has been constructed. -/
theorem to_terminal
    {layout : List Functions.Name} {fresh : Fresh.State}
    {lowerArgs : List (Locals.Expr 1)} {results : Nat}
    {seq : Locals.ExprSeq results}
    {entry : Functions.InteractionSemantics.State}
    {sourceOpen : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Word)}
    {targetOpen : Functions.InteractionSemantics.Open
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hSeq : Expr.List.toSeq? lowerArgs results = some seq)
    (hPrepared : Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout fresh lowerArgs entry) sourceOpen targetOpen) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PreparedArgsDoneRel layout seq)
      sourceOpen targetOpen := by
  apply Simulation.Interaction.ForwardRel.mono hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .error hError
  | regular hStable hRel _hDomain _hExtends =>
      exact
        FunctionsInteractionStatement.PreparedArgsDoneRel.regular_of_stable
          hSeq hStable hRel
  | terminal hTerminal => exact .terminal hTerminal

/-- Empty argument lowering is the identity prepared-argument computation. -/
theorem nil
    {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name} {fresh : Fresh.State}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      fresh.used target.vars) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout fresh [] target)
      (Yul.InteractionSemantics.evalArgs
        fuel [] codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 1) { stmts := [] } target) := by
  rw [Functions.InteractionSemantics.Block.openRun_nil]
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.evalArgs,
        Yul.Source.Canonical.evalArgs,
        Yul.Source.Effectful.evalArgs,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.Source.Effectful.Control.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel layout fresh [] target)
          (right := pure
            (Functions.Source.Effectful.Outcome.regular target, ctx))
          hTruncated)
  | succ fuel =>
      have hDone :
          DoneRel layout fresh [] target (.ok (source, []))
            (.ok
              (Functions.Source.Effectful.Outcome.regular target, ctx)) :=
        .regular (.nil target) hRel hDomain
          (FunctionsInteractionRelation.TargetExtends.refl target.vars)
      simpa [Yul.InteractionSemantics.evalArgs,
        Yul.Source.Canonical.evalArgs,
        Yul.Source.Effectful.evalArgs] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

/-- A prepared computation targeting one Functions statement also targets the
canonical singleton block around that statement. -/
theorem singletonTarget
    {layout : List Functions.Name} {fresh : Fresh.State}
    {lower : List (Locals.Expr 1)}
    {entry target : Functions.InteractionSemantics.State}
    {targetFuel : Nat}
    {sourceOpen :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Word)}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    (hStmt :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout fresh lower entry) sourceOpen
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx (targetFuel + 1) stmt target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout fresh lower entry) sourceOpen
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := [stmt] } target) := by
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout fresh lower entry)
        (Simulation.Interaction.bind sourceOpen pure)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Stmt.openRun
            program ctx (targetFuel + 1) stmt target)
          fun targetResult =>
            match targetResult.1.mode with
            | .regular =>
                Functions.InteractionSemantics.Block.openRun
                  program targetResult.2 (targetFuel + 1)
                    { stmts := [] } targetResult.1.state
            | .brk | .cont | .leave | .halt _ =>
                pure (targetResult.1, ctx)) := by
    apply Simulation.Interaction.ForwardRel.bind_custom hStmt
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError =>
        exact Simulation.Interaction.ForwardRel.done (.error hError)
    | regular hStable hScoped hDomain hExtends =>
        simp only
        rw [Functions.InteractionSemantics.Block.openRun_nil]
        exact Simulation.Interaction.ForwardRel.done
          (DoneRel.regular hStable hScoped hDomain hExtends)
    | terminal hTerminal =>
        simp only
        cases hTerminal with
        | stop hState =>
            exact Simulation.Interaction.ForwardRel.done
              (DoneRel.terminal (.stop hState))
        | return_ hState =>
            exact Simulation.Interaction.ForwardRel.done
              (DoneRel.terminal (.return_ hState))
        | selfdestruct hState =>
            exact Simulation.Interaction.ForwardRel.done
              (DoneRel.terminal (.selfdestruct hState))
        | revert hState =>
            exact Simulation.Interaction.ForwardRel.done
              (DoneRel.terminal (.revert hState))
  rw [show targetFuel + 2 = (targetFuel + 1) + 1 by omega,
    Functions.InteractionSemantics.Block.openRun_cons]
  have hSourceBind :
      Simulation.Interaction.bind sourceOpen pure = sourceOpen :=
    Simulation.Interaction.bind_pure sourceOpen
  rw [hSourceBind] at hBound
  simpa [Functions.InteractionSemantics.Stmt.openRun,
    Functions.InteractionSemantics.Block.openRun_nil] using hBound

/-- A deferred literal or variable needs no generated target prelude. Its
source evaluation produces one stable delayed target value. -/
theorem deferred
    {fuel targetFuel : Nat}
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
      before.used target.vars) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout after [lower] target)
      (Yul.InteractionSemantics.evalValues
        fuel expr codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 1) { stmts := pre } target) := by
  obtain ⟨rfl, rfl, hDirect⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hLower
  rw [Functions.InteractionSemantics.Block.openRun_nil]
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.evalValues,
        Yul.Source.Canonical.evalValues,
        Yul.Source.Effectful.evalValues,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.Source.Effectful.Control.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel layout after [lower] target)
          (right := pure
            (Functions.Source.Effectful.Outcome.regular target, ctx))
          hTruncated)
  | succ fuel =>
      cases expr with
      | Lit value =>
          simp [Expr.toLocals?, Expr.cast] at hDirect
          subst lower
          have hDone :
              DoneRel layout after [.lit value] target
                (.ok (source, [value]))
                (.ok
                  (Functions.Source.Effectful.Outcome.regular target,
                    ctx)) :=
            .regular
              (.cons (FunctionsInteractionExpression.StableValue.lit
                target value) (.nil target))
              hRel hDomain
              (FunctionsInteractionRelation.TargetExtends.refl target.vars)
          simpa [Yul.InteractionSemantics.evalValues,
            Yul.Source.Canonical.evalValues,
            Yul.Source.Effectful.evalValues] using
            (Simulation.Interaction.ForwardRel.done
              (truncated := Truncated) hDone)
      | Var name =>
          simp [Expr.toLocals?, Expr.cast] at hDirect
          subst lower
          cases hLookup : source.lookup? name with
          | none =>
              have hTruncated :
                  Truncated
                    ({ exception := .UnknownIdentifier name,
                        state := source } :
                      Yul.InteractionSemantics.Failure) := by
                trivial
              simpa [Yul.InteractionSemantics.evalValues,
                Yul.InteractionSemantics.stateModel,
                Yul.Source.Canonical.evalValues,
                Yul.Source.Effectful.evalValues,
                Yul.Source.Effectful.Control.fail, hLookup] using
                (Simulation.Interaction.ForwardRel.truncated
                  (doneRel := DoneRel layout after [.var (identName name)]
                    target)
                  (right := pure
                    (Functions.Source.Effectful.Outcome.regular target,
                      ctx))
                  hTruncated)
          | some value =>
              have hTarget := hRel.state.lookup hLookup
              have hDone :
                  DoneRel layout after [.var (identName name)] target
                    (.ok (source, [value]))
                    (.ok
                      (Functions.Source.Effectful.Outcome.regular target,
                        ctx)) :=
                .regular
                  (.cons
                    (FunctionsInteractionExpression.StableValue.var hTarget)
                    (.nil target))
                  hRel hDomain
                  (FunctionsInteractionRelation.TargetExtends.refl
                    target.vars)
              simpa [Yul.InteractionSemantics.evalValues,
                Yul.InteractionSemantics.stateModel,
                Yul.Source.Canonical.evalValues,
                Yul.Source.Effectful.evalValues, hLookup] using
                (Simulation.Interaction.ForwardRel.done
                  (truncated := Truncated) hDone)
      | Call callee args =>
          simp [Expr.deferredBoundArgSafe?] at hSafe

/-- Singleton list wrapper for a deferred argument. This isolates the two
units of list fuel consumed around the expression evaluator. -/
theorem deferred_arg
    {fuel targetFuel : Nat}
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
      before.used target.vars) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout after [lower] target)
      (Yul.InteractionSemantics.evalArgs
        fuel [expr] codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 1) { stmts := pre } target) := by
  obtain ⟨rfl, rfl, hDirect⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hLower
  rw [Functions.InteractionSemantics.Block.openRun_nil]
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.evalArgs,
        Yul.Source.Canonical.evalArgs,
        Yul.Source.Effectful.evalArgs,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.Source.Effectful.Control.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel layout after [lower] target)
          (right := pure
            (Functions.Source.Effectful.Outcome.regular target, ctx))
          hTruncated)
  | succ tailFuel =>
      cases tailFuel with
      | zero =>
          rw [Yul.InteractionSemantics.EvalArgs.one_cons]
          have hHead := deferred
            (fuel := 0) (targetFuel := targetFuel)
            (codeOverride := codeOverride) (program := program) (ctx := ctx)
            hSafe hLower hRel hDomain
          rw [Functions.InteractionSemantics.Block.openRun_nil] at hHead
          apply Simulation.Interaction.ForwardRel.bind_custom hHead
          intro sourceDone targetDone hDone
          cases hDone with
          | error hError =>
              exact Simulation.Interaction.ForwardRel.done (.error hError)
          | @regular sourceValues values targetAfter targetCtx
              hStable hScoped hFinalDomain hExtends =>
              have hTruncated :
                  Truncated
                    ({ exception := .OutOfFuel,
                        state := sourceValues } :
                      Yul.InteractionSemantics.Failure) := by
                trivial
              simpa [Yul.InteractionSemantics.Primitive.fail] using
                (Simulation.Interaction.ForwardRel.truncated
                  (doneRel := DoneRel layout after [lower] target)
                  (right := pure
                    (Functions.Source.Effectful.Outcome.regular targetAfter,
                      targetCtx))
                  hTruncated)
          | terminal hTerminal =>
              exact Simulation.Interaction.ForwardRel.done
                (.terminal hTerminal)
      | succ residualFuel =>
          rw [show residualFuel + 1 + 1 = residualFuel + 2 by omega,
            Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
          have hHead := deferred
            (fuel := residualFuel + 1) (targetFuel := targetFuel)
            (codeOverride := codeOverride) (program := program) (ctx := ctx)
            hSafe hLower hRel hDomain
          rw [Functions.InteractionSemantics.Block.openRun_nil] at hHead
          have hBound :
              Simulation.Interaction.ForwardRel Truncated
                (DoneRel layout after [lower] target)
                (Simulation.Interaction.bind
                  (Yul.InteractionSemantics.evalValues
                    (residualFuel + 1) expr codeOverride source)
                  (fun headResult =>
                    Simulation.Interaction.bind
                      (Yul.InteractionSemantics.evalArgs residualFuel []
                        codeOverride headResult.1)
                      (fun tailResult =>
                        pure
                          (tailResult.1,
                            headResult.2.head! :: tailResult.2))))
                (Simulation.Interaction.bind
                  (pure
                    (Functions.Source.Effectful.Outcome.regular target, ctx))
                  pure) := by
            apply Simulation.Interaction.ForwardRel.bind_custom hHead
            intro sourceDone targetDone hDone
            cases hDone with
            | error hError =>
                exact Simulation.Interaction.ForwardRel.done (.error hError)
            | @regular sourceAfter values targetAfter targetCtx
                hStable hScoped hFinalDomain hExtends =>
                cases residualFuel with
                | zero =>
                    have hTruncated :
                        Truncated
                          ({ exception := .OutOfFuel,
                              state := sourceAfter } :
                            Yul.InteractionSemantics.Failure) := by
                      trivial
                    simpa [Yul.InteractionSemantics.evalArgs,
                      Yul.Source.Canonical.evalArgs,
                      Yul.Source.Effectful.evalArgs,
                      Yul.InteractionSemantics.Primitive.fail,
                      Yul.Source.Effectful.Control.fail] using
                      (Simulation.Interaction.ForwardRel.truncated
                        (doneRel := DoneRel layout after [lower] target)
                        (right := pure
                          (Functions.Source.Effectful.Outcome.regular
                            targetAfter, targetCtx))
                        hTruncated)
                | succ fuel =>
                    have hTail :
                        Yul.InteractionSemantics.evalArgs (fuel + 1) []
                            codeOverride sourceAfter =
                          pure (sourceAfter, []) := by
                      simp [Yul.InteractionSemantics.evalArgs,
                        Yul.Source.Canonical.evalArgs,
                        Yul.Source.Effectful.evalArgs]
                    have hLength : values.length = 1 := by
                      simpa using hStable.length
                    obtain ⟨value, rfl⟩ :=
                      List.length_eq_one_iff.mp hLength
                    simpa [hTail] using
                      (Simulation.Interaction.ForwardRel.done
                        (truncated := Truncated)
                        (DoneRel.regular hStable hScoped hFinalDomain
                          hExtends))
            | terminal hTerminal =>
                exact Simulation.Interaction.ForwardRel.done
                  (.terminal hTerminal)
          simpa using hBound

/-- Wrap an already proved one-result expression computation in the canonical
singleton argument-list evaluator. This owns the list evaluator's trailing
fuel unit and is independent of how the expression itself is compiled. -/
theorem singletonOfValues
    {headFuel : Nat}
    {expr : AstExpr} {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {entry : Functions.InteractionSemantics.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {targetOpen : Functions.InteractionSemantics.Open
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hHead :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout fresh [lower] entry)
        (Yul.InteractionSemantics.evalValues
          headFuel expr codeOverride source)
        targetOpen) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout fresh [lower] entry)
      (Yul.InteractionSemantics.evalArgs
        (headFuel + 1) [expr] codeOverride source)
      targetOpen := by
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout fresh [lower] entry)
        (Yul.InteractionSemantics.evalArgs
          (headFuel + 1) [expr] codeOverride source)
        (Simulation.Interaction.bind targetOpen pure) := by
    cases headFuel with
    | zero =>
        rw [Yul.InteractionSemantics.EvalArgs.one_cons]
        apply Simulation.Interaction.ForwardRel.bind_custom hHead
        intro sourceDone targetDone hDone
        cases hDone with
        | error hError =>
            exact Simulation.Interaction.ForwardRel.done (.error hError)
        | terminal hTerminal =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal hTerminal)
        | @regular sourceAfter values targetAfter ctxAfter
            _hStable _hScoped _hDomain _hExtends =>
            have hTruncated :
                Truncated
                  ({ exception := .OutOfFuel,
                      state := sourceAfter } :
                    Yul.InteractionSemantics.Failure) := by
              trivial
            simpa [Yul.InteractionSemantics.Primitive.fail] using
              (Simulation.Interaction.ForwardRel.truncated
                (doneRel := DoneRel layout fresh [lower] entry)
                (right := pure
                  (Functions.Source.Effectful.Outcome.regular
                    targetAfter, ctxAfter))
                hTruncated)
    | succ tailFuel =>
        rw [show tailFuel + 1 + 1 = tailFuel + 2 by omega,
          Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
        apply Simulation.Interaction.ForwardRel.bind_custom hHead
        intro sourceDone targetDone hDone
        cases hDone with
        | error hError =>
            exact Simulation.Interaction.ForwardRel.done (.error hError)
        | terminal hTerminal =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal hTerminal)
        | @regular sourceAfter values targetAfter ctxAfter
            hStable hScoped hDomain hExtends =>
            cases tailFuel with
            | zero =>
                have hTruncated :
                    Truncated
                      ({ exception := .OutOfFuel,
                          state := sourceAfter } :
                        Yul.InteractionSemantics.Failure) := by
                  trivial
                simpa [Yul.InteractionSemantics.evalArgs,
                  Yul.Source.Canonical.evalArgs,
                  Yul.Source.Effectful.evalArgs,
                  Yul.InteractionSemantics.Primitive.fail,
                  Yul.Source.Effectful.Control.fail] using
                  (Simulation.Interaction.ForwardRel.truncated
                    (doneRel := DoneRel layout fresh [lower] entry)
                    (right := pure
                      (Functions.Source.Effectful.Outcome.regular
                        targetAfter, ctxAfter))
                    hTruncated)
            | succ remaining =>
                have hTail :
                    Yul.InteractionSemantics.evalArgs
                        (remaining + 1) [] codeOverride sourceAfter =
                      pure (sourceAfter, []) := by
                  simp [Yul.InteractionSemantics.evalArgs,
                    Yul.Source.Canonical.evalArgs,
                    Yul.Source.Effectful.evalArgs]
                have hLength : values.length = 1 := by
                  simpa using hStable.length
                obtain ⟨value, rfl⟩ :=
                  List.length_eq_one_iff.mp hLength
                simpa [hTail] using
                  (Simulation.Interaction.ForwardRel.done
                    (truncated := Truncated)
                    (DoneRel.regular hStable hScoped hDomain hExtends))
  have hTargetPure :
      Simulation.Interaction.bind targetOpen (fun result => pure result) =
        targetOpen := by
    exact Simulation.Interaction.bind_pure _
  rw [hTargetPure] at hBound
  exact hBound

/-- Compose a recursively prepared tail with one compiler-deferred head.
This is the semantic counterpart of `UncheckedBoundLowering.direct`. -/
theorem direct
    {fuel targetFuel : Nat}
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
    (hRest :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout stateRest lowerRest.reverse entry)
        (Yul.InteractionSemantics.evalArgs
          fuel rest.reverse codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := preRest } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout stateHead (lowerHead :: lowerRest).reverse entry)
      (Yul.InteractionSemantics.evalArgs
        fuel (expr :: rest).reverse codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := preRest ++ preHead } target) := by
  obtain ⟨rfl, rfl, hDirect⟩ :=
    Expr.lower1Unchecked?_deferred_parts hSafe hHead
  simp only [List.append_nil, List.reverse_cons]
  rw [Yul.InteractionSemantics.EvalArgs.append]
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout stateHead (lowerRest.reverse ++ [lowerHead]) entry)
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs
            fuel rest.reverse codeOverride source)
          (fun restResult =>
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.evalArgs
                (fuel - 2 * rest.reverse.length) [expr]
                codeOverride restResult.1)
              (fun headResult =>
                pure
                  (headResult.1,
                    restResult.2 ++ headResult.2))))
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRun
            program ctx targetFuel { stmts := preRest } target)
          pure) := by
    apply Simulation.Interaction.ForwardRel.bind_custom hRest
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError =>
        exact Simulation.Interaction.ForwardRel.done (.error hError)
    | terminal hTerminal =>
        exact Simulation.Interaction.ForwardRel.done (.terminal hTerminal)
    | @regular sourceRest restValues targetRest ctxRest
        hStableRest hScopedRest hDomainRest hExtendsRest =>
        have hHeadRel := deferred_arg
          (fuel := fuel - 2 * rest.reverse.length)
          (targetFuel := 0)
          (codeOverride := codeOverride) (program := program)
          (ctx := ctxRest)
          hSafe hHead hScopedRest hDomainRest
        rw [Functions.InteractionSemantics.Block.openRun_nil] at hHeadRel
        apply Simulation.Interaction.ForwardRel.bind_custom hHeadRel
        intro headSourceDone headTargetDone hHeadDone
        cases hHeadDone with
        | error hError =>
            exact Simulation.Interaction.ForwardRel.done (.error hError)
        | terminal hTerminal =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal hTerminal)
        | @regular sourceAfter headValues targetAfter ctxAfter
            hStableHead hScopedHead hDomainHead hExtendsHead =>
            have hStableRest' := hStableRest.mono hExtendsHead
            have hStableFinal := hStableRest'.append hStableHead
            have hExtendsFinal :=
              FunctionsInteractionRelation.TargetExtends.trans
                hExtendsRest hExtendsHead
            exact Simulation.Interaction.ForwardRel.done
              (.regular
                hStableFinal
                hScopedHead hDomainHead hExtendsFinal)
  have hTargetPure :
      Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRun
            program ctx targetFuel { stmts := preRest } target)
          (fun result => pure result) =
        Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := preRest } target := by
    exact Simulation.Interaction.bind_pure _
  rw [hTargetPure] at hBound
  exact hBound

/-- Recursive capability needed by the spilling branch of bounded argument
lowering. The expression owner proves this for one generated head; the list
owner only sequences it after the already prepared tail. -/
def BoundHeadForward
    (fuel targetFuel : Nat)
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
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout final [.var tmp] target)
        (Yul.InteractionSemantics.evalArgs
          fuel [expr] codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel
          { stmts := pre ++ [.let_ tmp lower] } target)

/-- With fewer than two list-fuel units, a singleton argument computation is
source-truncated before any completed head result needs relating. -/
theorem boundHead_lowFuel
    {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hFuel : fuel < 2) :
    BoundHeadForward fuel targetFuel expr pre lower before after final tmp
      codeOverride program layout := by
  intro _hLower _hFresh source target ctx _hScoped _hDomain
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.evalArgs,
        Yul.Source.Canonical.evalArgs,
        Yul.Source.Effectful.evalArgs,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.Source.Effectful.Control.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel layout final [.var tmp] target)
          (right := Functions.InteractionSemantics.Block.openRun
            program ctx targetFuel
            { stmts := pre ++ [.let_ tmp lower] } target)
          hTruncated)
  | succ remaining =>
      have hRemaining : remaining = 0 := by omega
      subst remaining
      rw [Yul.InteractionSemantics.EvalArgs.one_cons]
      have hEvalZero :
          Yul.InteractionSemantics.evalValues
              0 expr codeOverride source =
            Yul.InteractionSemantics.Primitive.fail source .OutOfFuel := by
        unfold Yul.InteractionSemantics.evalValues
          Yul.Source.Canonical.evalValues
          Yul.Source.Effectful.evalValues
        rfl
      rw [hEvalZero]
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel layout final [.var tmp] target)
          (right := Functions.InteractionSemantics.Block.openRun
            program ctx targetFuel
            { stmts := pre ++ [.let_ tmp lower] } target)
          hTruncated)

/-- Adjacent expression-owner interface before the bounded-argument owner
stores the delayed value in its compiler-private temporary. -/
def HeadValueForward
    (fuel targetFuel : Nat)
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
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout after [lower] target)
        (Yul.InteractionSemantics.evalArgs
          fuel [expr] codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)

/-- Deferred literals and variables satisfy the expression-owner interface
without executing a generated prelude. -/
theorem deferredHeadValue
    {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {before after : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hTargetFuel : 0 < targetFuel)
    (hSafe : Expr.deferredBoundArgSafe? expr = true) :
    HeadValueForward fuel targetFuel expr pre lower before after
      codeOverride program layout := by
  intro hLower source target ctx hScoped hDomain
  cases targetFuel with
  | zero => omega
  | succ remaining =>
      simpa [Nat.succ_eq_add_one] using
        (deferred_arg
          (fuel := fuel) (targetFuel := remaining)
          (codeOverride := codeOverride) (program := program) (ctx := ctx)
          hSafe hLower hScoped hDomain)

/-- Store an expression owner's stable delayed value in the fresh temporary
owned by bounded-argument lowering. -/
theorem bindHeadValue
    {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hLayout : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hValue : HeadValueForward fuel targetFuel expr pre lower
      before after codeOverride program layout) :
    BoundHeadForward fuel targetFuel expr pre lower before after final tmp
      codeOverride program layout := by
  intro hLower hFresh source target ctx hScoped hDomain
  rw [Functions.InteractionSemantics.Block.openRun_append]
  have hValueRel := hValue hLower (ctx := ctx) hScoped hDomain
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout final [.var tmp] target)
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs
            fuel [expr] codeOverride source)
          pure)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRun
            program ctx targetFuel { stmts := pre } target)
          (fun result =>
            match result.1.mode with
            | .regular =>
                Functions.InteractionSemantics.Block.openRun
                  program result.2 (targetFuel - pre.length)
                  { stmts := [.let_ tmp lower] } result.1.state
            | .brk | .cont | .leave | .halt _ =>
                pure result)) := by
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
        hStable hScopedAfter hDomainAfter hExtendsAfter =>
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
                have hEval' :
                    Functions.InteractionSemantics.Expr.openEval
                        lower targetAfter =
                      .done (.ok (targetAfter, [value])) := by
                  simpa [Functions.InteractionSemantics.Expr.openEval]
                    using hEval
                have hTargetLet :
                    Functions.InteractionSemantics.Block.openRun
                        program ctxAfter (targetFuel - pre.length)
                        { stmts := [.let_ tmp lower] } targetAfter =
                      pure
                        (Functions.Source.Effectful.Outcome.regular
                          targetFinal, ctxFinal) := by
                  rw [hResidual,
                    show remaining + 2 = (remaining + 1) + 1 by omega,
                    Functions.InteractionSemantics.Block.openRun_cons]
                  change
                    Simulation.Interaction.bind
                        (Functions.InteractionSemantics.Stmt.openRun
                          program ctxAfter (remaining + 1)
                          (.let_ tmp lower) targetAfter)
                        _ = _
                  rw [Functions.InteractionSemantics.Stmt.openRun_let,
                    hEval', Simulation.Interaction.bind_done_ok]
                  simp only [Simulation.Interaction.monad_pure_bind]
                  change
                    Functions.InteractionSemantics.Block.openRun
                        program ctxFinal (remaining + 1)
                        { stmts := [] } targetFinal =
                      pure
                        (Functions.Source.Effectful.Outcome.regular
                          targetFinal, ctxFinal)
                  rw [Functions.InteractionSemantics.Block.openRun_nil]
                change
                  Simulation.Interaction.ForwardRel Truncated
                    (DoneRel layout final [.var tmp] target)
                    (pure (sourceAfter, [value]))
                    (Functions.InteractionSemantics.Block.openRun
                      program ctxAfter (targetFuel - pre.length)
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
                exact Simulation.Interaction.ForwardRel.done
                  (.regular
                    (.cons
                      (FunctionsInteractionExpression.StableValue.var hLookup)
                      (.nil targetFinal))
                    hScopedFinal hDomainFinal hExtendsFinal)
  have hSourcePure :
      Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs
            fuel [expr] codeOverride source)
          (fun result => pure result) =
        Yul.InteractionSemantics.evalArgs
          fuel [expr] codeOverride source := by
    exact Simulation.Interaction.bind_pure _
  rw [hSourcePure] at hBound
  exact hBound

/-- A deferred expression can still enter the compiler's spilling branch when
the delayed argument window is full. -/
theorem boundDeferred
    {fuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {before after final : Fresh.State} {tmp : Functions.Name}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {layout : List Functions.Name}
    (hSafe : Expr.deferredBoundArgSafe? expr = true)
    (hLayout : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    BoundHeadForward fuel targetFuel expr pre lower before after final tmp
      codeOverride program layout :=
  bindHeadValue hLayout hTargetFuel
    (deferredHeadValue (by omega) hSafe)

/-- Compose a recursively prepared tail with one generated, fresh-bound head.
This is the semantic counterpart of `UncheckedBoundLowering.bound`; recursive
expression reasoning remains behind `BoundHeadForward`. -/
theorem bound
    {fuel targetFuel : Nat}
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
    (hHeadForward : BoundHeadForward
      (fuel - 2 * rest.reverse.length)
      (targetFuel - preRest.length)
      expr preHead lowerHead stateRest stateHead stateFresh tmp
      codeOverride program layout)
    (hRest :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout stateRest lowerRest.reverse entry)
        (Yul.InteractionSemantics.evalArgs
          fuel rest.reverse codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := preRest } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout stateFresh (.var tmp :: lowerRest).reverse entry)
      (Yul.InteractionSemantics.evalArgs
        fuel (expr :: rest).reverse codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
        { stmts := preRest ++ preHead ++ [.let_ tmp lowerHead] } target) := by
  simp only [List.reverse_cons]
  rw [Yul.InteractionSemantics.EvalArgs.append,
    List.append_assoc,
    Functions.InteractionSemantics.Block.openRun_append]
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
      hStableRest hScopedRest hDomainRest hExtendsRest =>
      have hHeadRel :=
        hHeadForward hHead hFresh (ctx := ctxRest)
          hScopedRest hDomainRest
      have hHeadBound :
          Simulation.Interaction.ForwardRel Truncated
            (DoneRel layout stateFresh
              (lowerRest.reverse ++ [.var tmp]) entry)
            (Simulation.Interaction.bind
              (Yul.InteractionSemantics.evalArgs
                (fuel - 2 * rest.reverse.length) [expr]
                codeOverride sourceRest)
              (fun headResult =>
                pure
                  (headResult.1,
                    restValues ++ headResult.2)))
            (Simulation.Interaction.bind
              (Functions.InteractionSemantics.Block.openRun
                program ctxRest (targetFuel - preRest.length)
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
            hStableHead hScopedHead hDomainHead hExtendsHead =>
            have hStableRest' := hStableRest.mono hExtendsHead
            have hStableFinal := hStableRest'.append hStableHead
            have hExtendsFinal :=
              FunctionsInteractionRelation.TargetExtends.trans
                hExtendsRest hExtendsHead
            exact Simulation.Interaction.ForwardRel.done
              (.regular
                hStableFinal hScopedHead hDomainHead hExtendsFinal)
      have hTargetPure :
          Simulation.Interaction.bind
              (Functions.InteractionSemantics.Block.openRun
                program ctxRest (targetFuel - preRest.length)
                { stmts := preHead ++ [.let_ tmp lowerHead] }
                targetRest)
              (fun result => pure result) =
            Functions.InteractionSemantics.Block.openRun
              program ctxRest (targetFuel - preRest.length)
              { stmts := preHead ++ [.let_ tmp lowerHead] }
              targetRest := by
        exact Simulation.Interaction.bind_pure _
      rw [hTargetPure] at hHeadBound
      exact hHeadBound

/-- Fuel-indexed recursive expression capability consumed privately by the
compiler-owned bounded-argument induction. -/
def RecursiveBoundHeads
    (profile : SolcValidation.DialectProfile)
    (contract : AstContract) (fuel targetFuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (program : Functions.Program) (layout : List Functions.Name) : Prop :=
  ∀ {expr : AstExpr} {rest : List AstExpr}
    {preRest preHead : List Functions.Stmt}
    {lowerHead : Locals.Expr 1}
    {stateRest stateHead stateFresh : Fresh.State}
    {tmp : Functions.Name},
    SolcValidation.ExprOk? profile contract layout 1 expr = true →
      Expr.lower1Unchecked? stateRest expr =
        some (preHead, lowerHead, stateHead) →
      Fresh.fresh? stateHead = some (tmp, stateFresh) →
        preHead.length + 1 < targetFuel - preRest.length →
        (∀ name, name ∈ layout → name ∈ stateRest.used) →
        (∀ name, name ∈ layout → name ∈ stateHead.used) →
          BoundHeadForward
            (fuel - 2 * rest.reverse.length)
            (targetFuel - preRest.length)
            expr preHead lowerHead stateRest stateHead stateFresh tmp
            codeOverride program layout

/-- Preservation for the complete compiler-owned bounded argument artifact.
Only a generated, fresh-bound expression head is delegated to the recursive
expression owner; empty and deferred branches are discharged here. -/
theorem ofUncheckedLowering
    {profile : SolcValidation.DialectProfile} {contract : AstContract}
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
      profile contract layout args = true)
    (hLowering : Expr.List.UncheckedBoundLowering
      initial args pre lowerArgs final)
    (hBound : RecursiveBoundHeads
      profile contract fuel targetFuel codeOverride program layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hTargetFuel : pre.length < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final lowerArgs.reverse target)
      (Yul.InteractionSemantics.evalArgs
        fuel args.reverse codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := pre } target) := by
  induction hLowering with
  | nil =>
      cases targetFuel with
      | zero => simp at hTargetFuel
      | succ remaining =>
          simpa using
            (nil (fuel := fuel) (targetFuel := remaining)
              (codeOverride := codeOverride) (program := program)
              (ctx := ctx) hRel hDomain)
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      have hOkParts :
          SolcValidation.ExprOk? profile contract layout 1 expr = true ∧
            SolcValidation.ExprsOk? profile contract layout rest = true := by
        simpa [SolcValidation.ExprsOk?] using hArgsOk
      have hRestOk :
          SolcValidation.ExprsOk? profile contract layout rest = true := by
        exact hOkParts.2
      obtain ⟨rfl, rfl, _hLower⟩ :=
        Expr.lower1Unchecked?_deferred_parts hDirect.1 hHead
      have hRestFuel : preRest.length < targetFuel := by
        simpa using hTargetFuel
      have hRestForward := ih hRestOk hRestFuel
      exact direct (initial := initial) hDirect.1 hHead hRestForward
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead _hDirect hFresh ih =>
      have hOkParts :
          SolcValidation.ExprOk? profile contract layout 1 expr = true ∧
            SolcValidation.ExprsOk? profile contract layout rest = true := by
        simpa [SolcValidation.ExprsOk?] using hArgsOk
      have hRestFuel : preRest.length < targetFuel := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hTargetFuel
        omega
      have hRestForward := ih hOkParts.2 hRestFuel
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
      exact bound (initial := initial) hHead hFresh
        (hBound hOkParts.1 hHead hFresh hHeadFuel
          hRestLayout hHeadLayout)
        hRestForward

end FunctionsInteractionPreparedArgs
end Yul
end EvmCompiler
