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

/-- Preservation for the complete compiler-owned bounded argument artifact.
Only a generated, fresh-bound expression head is delegated to the recursive
expression owner; empty and deferred branches are discharged here. -/
theorem ofUncheckedLowering
    {fuel targetFuel : Nat}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {initial final : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLowering : Expr.List.UncheckedBoundLowering
      initial args pre lowerArgs final)
    (hBound :
      ∀ {expr : AstExpr} {rest : List AstExpr}
        {preRest preHead : List Functions.Stmt}
        {lowerHead : Locals.Expr 1}
        {stateRest stateHead stateFresh : Fresh.State}
        {tmp : Functions.Name},
        Expr.lower1Unchecked? stateRest expr =
            some (preHead, lowerHead, stateHead) →
          Fresh.fresh? stateHead = some (tmp, stateFresh) →
            BoundHeadForward
              (fuel - 2 * rest.reverse.length)
              (targetFuel - preRest.length)
              expr preHead lowerHead stateRest stateHead stateFresh tmp
              codeOverride program layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      initial.used target.vars)
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
      obtain ⟨rfl, rfl, _hLower⟩ :=
        Expr.lower1Unchecked?_deferred_parts hDirect.1 hHead
      have hRestFuel : preRest.length < targetFuel := by
        simpa using hTargetFuel
      have hRestForward := ih hRestFuel
      exact direct (initial := initial) hDirect.1 hHead hRestForward
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead _hDirect hFresh ih =>
      have hRestFuel : preRest.length < targetFuel := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hTargetFuel
        omega
      have hRestForward := ih hRestFuel
      exact bound (initial := initial) hHead hFresh
        (hBound hHead hFresh) hRestForward

end FunctionsInteractionPreparedArgs
end Yul
end EvmCompiler
