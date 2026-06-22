import EvmCompiler.Locals.InteractionSemantics

/-!
Successful refinement for the monad-polymorphic Locals evaluator instantiated
with open interactions.  This is the open-world counterpart of
`Locals.Source.Effectful.PrimitiveSemantics.SuccessRefines` for `Except`.
-/

namespace EvmCompiler
namespace Locals
namespace InteractionRefinement

abbrev Open (alpha : Type) := Simulation.Interaction EVMException alpha
abbrev PrimitiveSemantics (state : Type) :=
  Locals.Source.Effectful.Control.PrimitiveSemantics Open state

namespace PrimitiveSemantics

/-- Every successful open effect produced by `source` is exactly the same
interaction tree under `target`. Unsafe/error branches need not agree. -/
structure SuccessRefines {state : Type}
    (source target : PrimitiveSemantics state) : Prop where
  eval :
    forall op initial values,
      Simulation.Interaction.Successful (source.eval op initial values) ->
        source.eval op initial values = target.eval op initial values
  terminal :
    forall kind initial values,
      Simulation.Interaction.Successful
          (source.terminal kind initial values) ->
        source.terminal kind initial values =
          target.terminal kind initial values

end PrimitiveSemantics

theorem bind_eq_of_successful
    {source target : Type}
    {prefixSource prefixTarget : Simulation.Interaction EVMException source}
    {nextSource nextTarget : source ->
      Simulation.Interaction EVMException target}
    (hSuccessful : Simulation.Interaction.Successful
      (Simulation.Interaction.bind prefixSource nextSource))
    (hPrefix : prefixSource = prefixTarget)
    (hNext : forall value,
      Simulation.Interaction.Successful (nextSource value) ->
        nextSource value = nextTarget value) :
    Simulation.Interaction.bind prefixSource nextSource =
      Simulation.Interaction.bind prefixTarget nextTarget := by
  rw [hPrefix]
  apply Simulation.Interaction.AllDone.bind_congr
    (show Simulation.Interaction.AllDone _ prefixTarget by
      simpa [hPrefix] using
        Simulation.Interaction.Successful.bind_inv hSuccessful)
  intro value hValue
  exact hNext value hValue

namespace Expr

mutual
  theorem eval_eq_of_successRefines
      {state : Type} (model : Locals.Source.Effectful.StateModel state)
      {sourcePrim targetPrim : PrimitiveSemantics state}
      (hRefines : sourcePrim.SuccessRefines targetPrim) :
      forall {results : Nat} (expr : Locals.Expr results) (initial : state),
        Simulation.Interaction.Successful
            (Locals.Source.Effectful.Expr.Control.eval
              model sourcePrim expr initial) ->
          Locals.Source.Effectful.Expr.Control.eval
              model sourcePrim expr initial =
            Locals.Source.Effectful.Expr.Control.eval
              model targetPrim expr initial := by
    intro results expr initial hSuccessful
    cases expr with
    | lit value => rfl
    | var name => rfl
    | code code => rfl
    | prim op args =>
        simp only [Locals.Source.Effectful.Expr.Control.eval]
        apply bind_eq_of_successful hSuccessful
        · exact ExprSeq.eval_eq_of_successRefines model hRefines args initial
            (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro result hPrimitive
          exact hRefines.eval op result.1 result.2 hPrimitive

  theorem ExprSeq.eval_eq_of_successRefines
      {state : Type} (model : Locals.Source.Effectful.StateModel state)
      {sourcePrim targetPrim : PrimitiveSemantics state}
      (hRefines : sourcePrim.SuccessRefines targetPrim) :
      forall {results : Nat} (exprs : Locals.ExprSeq results) (initial : state),
        Simulation.Interaction.Successful
            (Locals.Source.Effectful.Expr.Control.ExprSeq.eval
              model sourcePrim exprs initial) ->
          Locals.Source.Effectful.Expr.Control.ExprSeq.eval
              model sourcePrim exprs initial =
            Locals.Source.Effectful.Expr.Control.ExprSeq.eval
              model targetPrim exprs initial := by
    intro results exprs initial hSuccessful
    cases exprs with
    | nil => rfl
    | cons head tail =>
        simp only [Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
        apply bind_eq_of_successful hSuccessful
        · exact eval_eq_of_successRefines model hRefines head initial
            (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro headResult hTailSuccessful
          apply bind_eq_of_successful hTailSuccessful
          · exact ExprSeq.eval_eq_of_successRefines model hRefines tail
              headResult.1
              (Simulation.Interaction.Successful.bind_left hTailSuccessful)
          · intro _result _hPure
            rfl
end

theorem evalOne_eq_of_successRefines
    {state : Type} (model : Locals.Source.Effectful.StateModel state)
    {sourcePrim targetPrim : PrimitiveSemantics state}
    (hRefines : sourcePrim.SuccessRefines targetPrim)
    {results : Nat} (expr : Locals.Expr results) (initial : state)
    (hSuccessful : Simulation.Interaction.Successful
      (Locals.Source.Effectful.Expr.Control.evalOne
        model sourcePrim expr initial)) :
    Locals.Source.Effectful.Expr.Control.evalOne
        model sourcePrim expr initial =
      Locals.Source.Effectful.Expr.Control.evalOne
        model targetPrim expr initial := by
  unfold Locals.Source.Effectful.Expr.Control.evalOne
  apply bind_eq_of_successful hSuccessful
  · exact eval_eq_of_successRefines model hRefines expr initial
      (Simulation.Interaction.Successful.bind_left hSuccessful)
  · intro _result _hContinuation
    rfl

theorem evalCondition_eq_of_successRefines
    {state : Type} (model : Locals.Source.Effectful.StateModel state)
    {sourcePrim targetPrim : PrimitiveSemantics state}
    (hRefines : sourcePrim.SuccessRefines targetPrim)
    (expr : Locals.Expr 1) (initial : state)
    (hSuccessful : Simulation.Interaction.Successful
      (Locals.Source.Effectful.Expr.Control.evalCondition
        model sourcePrim expr initial)) :
    Locals.Source.Effectful.Expr.Control.evalCondition
        model sourcePrim expr initial =
      Locals.Source.Effectful.Expr.Control.evalCondition
        model targetPrim expr initial := by
  unfold Locals.Source.Effectful.Expr.Control.evalCondition
  apply bind_eq_of_successful hSuccessful
  · exact evalOne_eq_of_successRefines model hRefines expr initial
      (Simulation.Interaction.Successful.bind_left hSuccessful)
  · intro _result _hContinuation
    rfl

end Expr

end InteractionRefinement
end Locals
end EvmCompiler
