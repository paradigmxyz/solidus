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

end FunctionsInteractionPreparedArgs
end Yul
end EvmCompiler
