import EvmCompiler.Locals.InteractionSemantics

namespace EvmCompiler
namespace Locals
namespace InteractionStatePreservation

abbrev State := Locals.InteractionSemantics.State

/-- Every successful state-carrying leaf retains the initial named locals. -/
def ResultVars {α : Type} (initial : State) :
    Except EVMException (State × α) → Prop
  | .error _ => True
  | .ok result => result.1.vars = initial.vars

abbrev EvalVars (initial : State) :=
  ResultVars (α := List Word) initial

theorem primitive_openEval_vars
    (op : Structured.BasicOp) (state : State) (values : List Word) :
    Simulation.Interaction.AllDone (EvalVars state)
      (Locals.InteractionSemantics.Primitive.openEval op state values) := by
  by_cases hLength :
      values.length = Expressions.Structured.BasicOp.inputs op
  · by_cases hSupported :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true
    · simp only [Locals.InteractionSemantics.Primitive.openEval,
        hLength, hSupported, ↓reduceIte]
      apply Simulation.Interaction.AllDone.map
        (Locals.InteractionSemantics.Primitive.finish state)
        (Simulation.Interaction.AllDone.trivial _)
      · intro _err _hTrivial
        trivial
      · intro target _hTrivial
        simp [ResultVars, Locals.InteractionSemantics.Primitive.finish,
          Locals.Source.State.withShared]
    · have hUnsupported :
          Locals.InteractionSemantics.Primitive.supportsOpen op = false := by
        exact Bool.eq_false_of_not_eq_true hSupported
      simp only [Locals.InteractionSemantics.Primitive.openEval,
        hLength, hUnsupported, ↓reduceIte]
      exact .done trivial
  · simp only [Locals.InteractionSemantics.Primitive.openEval,
      hLength, ↓reduceIte]
    exact .done trivial

mutual
  theorem expr_openEval_vars {results : Nat}
      (expr : Locals.Expr results) (state : State) :
      Simulation.Interaction.AllDone (EvalVars state)
        (Locals.InteractionSemantics.Expr.openEval expr state) := by
    cases expr with
    | lit value =>
        exact .done rfl
    | var name =>
        unfold Locals.InteractionSemantics.Expr.openEval
        simp only [Locals.Source.Effectful.Expr.Control.eval]
        cases hValue : state.vars name with
        | none =>
            simp only [Locals.InteractionSemantics.stateModel,
              Locals.Source.Effectful.Ordinary.stateModel,
              Locals.Source.Effectful.StateModel.vars, id_eq, hValue]
            change Simulation.Interaction.AllDone (EvalVars state)
              (.done (.error .InvalidInstruction))
            exact .done trivial
        | some value =>
            simp only [Locals.InteractionSemantics.stateModel,
              Locals.Source.Effectful.Ordinary.stateModel,
              Locals.Source.Effectful.StateModel.vars, id_eq, hValue]
            change Simulation.Interaction.AllDone (EvalVars state)
              (.done (.ok (state, [value])))
            exact .done rfl
    | code code =>
        change Simulation.Interaction.AllDone (EvalVars state)
          (.done (.error .InvalidInstruction))
        exact .done trivial
    | prim op args =>
        unfold Locals.InteractionSemantics.Expr.openEval
        simp only [Locals.Source.Effectful.Expr.Control.eval]
        apply Simulation.Interaction.AllDone.bind
          (exprSeq_openEval_vars args state)
        · intro _err _hVars
          trivial
        · intro result hArgsVars
          apply
            (primitive_openEval_vars op result.1 result.2).mono
          intro outcome hPrimitiveVars
          cases outcome with
          | error err =>
              trivial
          | ok final =>
              exact hPrimitiveVars.trans hArgsVars

  theorem exprSeq_openEval_vars {results : Nat}
      (exprs : Locals.ExprSeq results) (state : State) :
      Simulation.Interaction.AllDone (EvalVars state)
        (Locals.InteractionSemantics.ExprSeq.openEval exprs state) := by
    cases exprs with
    | nil =>
        exact .done rfl
    | cons head tail =>
        unfold Locals.InteractionSemantics.ExprSeq.openEval
        simp only [Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
        apply Simulation.Interaction.AllDone.bind
          (expr_openEval_vars head state)
        · intro _err _hVars
          trivial
        · intro headResult hHeadVars
          apply Simulation.Interaction.AllDone.bind
            (exprSeq_openEval_vars tail headResult.1)
          · intro _err _hVars
            trivial
          · intro tailResult hTailVars
            apply Simulation.Interaction.AllDone.done
            exact hTailVars.trans hHeadVars
end

theorem expr_openEvalOne_vars {results : Nat}
    (expr : Locals.Expr results) (state : State) :
    Simulation.Interaction.AllDone (ResultVars (α := Word) state)
      (Locals.InteractionSemantics.Expr.openEvalOne expr state) := by
  unfold Locals.InteractionSemantics.Expr.openEvalOne
    Locals.Source.Effectful.Expr.Control.evalOne
  apply Simulation.Interaction.AllDone.bind
    (expr_openEval_vars expr state)
  · intro _err _hVars
    trivial
  · intro result hVars
    rcases result with ⟨after, values⟩
    cases values with
    | nil =>
        change Simulation.Interaction.AllDone
          (ResultVars (α := Word) state)
          (.done (.error .InvalidInstruction))
        exact .done trivial
    | cons value rest =>
        cases rest with
        | nil =>
            change Simulation.Interaction.AllDone
              (ResultVars (α := Word) state)
              (.done (.ok (after, value)))
            exact .done hVars
        | cons other tail =>
            change Simulation.Interaction.AllDone
              (ResultVars (α := Word) state)
              (.done (.error .InvalidInstruction))
            exact .done trivial

theorem expr_openEvalCondition_vars
    (expr : Locals.Expr 1) (state : State) :
    Simulation.Interaction.AllDone (ResultVars (α := Bool) state)
      (Locals.InteractionSemantics.Expr.openEvalCondition expr state) := by
  unfold Locals.InteractionSemantics.Expr.openEvalCondition
    Locals.Source.Effectful.Expr.Control.evalCondition
  apply Simulation.Interaction.AllDone.bind
    (expr_openEvalOne_vars expr state)
  · intro _err _hVars
    trivial
  · intro result hVars
    exact .done hVars

end InteractionStatePreservation
end Locals
end EvmCompiler
