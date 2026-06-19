import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Locals
namespace InteractionArity

def OutputLength (results : Nat) :
    Except EVMException
      (Locals.InteractionSemantics.State × List Word) → Prop
  | .error _ => True
  | .ok result => result.2.length = results

mutual
  /-- Every successful branch of a typed Locals expression returns exactly its
  indexed number of values. -/
  theorem Expr.openEval_length {results : Nat}
      (expr : Locals.Expr results)
      (state : Locals.InteractionSemantics.State) :
      Simulation.Interaction.AllDone (OutputLength results)
        (Locals.InteractionSemantics.Expr.openEval expr state) := by
    cases expr with
    | lit value => exact .done rfl
    | var name =>
        unfold Locals.InteractionSemantics.Expr.openEval
          Locals.Source.Effectful.Expr.Control.eval
        cases hLookup : state.vars name with
        | none =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => Simulation.Interaction.pure (state, [value])
              | none =>
                  throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done True.intro
        | some value =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => Simulation.Interaction.pure (state, [value])
              | none =>
                  throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done rfl
    | code code => exact .done trivial
    | prim op args =>
        unfold Locals.InteractionSemantics.Expr.openEval
          Locals.Source.Effectful.Expr.Control.eval
        apply Simulation.Interaction.AllDone.bind
          (ExprSeq.openEval_length args state)
        · intro _error _hError
          trivial
        · intro result hArgs
          rcases result with ⟨afterArgs, values⟩
          change Simulation.Interaction.AllDone
            (OutputLength (Expressions.Structured.BasicOp.outputs op))
            (Locals.InteractionSemantics.Primitive.openEval
              op afterArgs values)
          by_cases hSupports :
              Locals.InteractionSemantics.Primitive.supportsOpen op = true
          · exact
              Locals.InteractionPreservation.Primitive.openEval_length
                hArgs hSupports
          · unfold Locals.InteractionSemantics.Primitive.openEval
            change values.length =
              Expressions.Structured.BasicOp.inputs op at hArgs
            simp only [hArgs, hSupports, if_pos, if_neg]
            exact .done True.intro

  /-- Typed expression sequences preserve the sum of their indexed output
  arities on every successful open-world branch. -/
  theorem ExprSeq.openEval_length {results : Nat}
      (exprs : Locals.ExprSeq results)
      (state : Locals.InteractionSemantics.State) :
      Simulation.Interaction.AllDone (OutputLength results)
        (Locals.InteractionSemantics.ExprSeq.openEval exprs state) := by
    cases exprs with
    | nil => exact .done rfl
    | @cons headResults tailResults head tail =>
        unfold Locals.InteractionSemantics.ExprSeq.openEval
          Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        apply Simulation.Interaction.AllDone.bind
          (Expr.openEval_length head state)
        · intro _error _hError
          trivial
        · intro headResult hHead
          rcases headResult with ⟨afterHead, headValues⟩
          apply Simulation.Interaction.AllDone.bind
            (ExprSeq.openEval_length tail afterHead)
          · intro _error _hError
            trivial
          · intro tailResult hTail
            rcases tailResult with ⟨afterTail, tailValues⟩
            change headValues.length = headResults at hHead
            change tailValues.length = tailResults at hTail
            apply Simulation.Interaction.AllDone.done
            change (headValues ++ tailValues).length =
              headResults + tailResults
            simp only [List.length_append, hHead, hTail]
end

namespace Expr

theorem openEvalOne_iszero_eq_map
    (expr : Locals.Expr 1)
    (state : Locals.InteractionSemantics.State) :
    Locals.InteractionSemantics.Expr.openEvalOne
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      Simulation.Interaction.map
        (fun result => (result.1, EvmYul.UInt256.isZero result.2))
        (Locals.InteractionSemantics.Expr.openEvalOne expr state) := by
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind]
  unfold Simulation.Interaction.map
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  have hArgs :
      Locals.InteractionSemantics.ExprSeq.openEval
          (Locals.ExprSeq.cons expr .nil) state =
        Locals.InteractionSemantics.Expr.openEval expr state := by
    unfold Locals.InteractionSemantics.ExprSeq.openEval
      Locals.Source.Effectful.Expr.Control.ExprSeq.eval
    change
      Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEval expr state)
          (fun result =>
            Simulation.Interaction.pure
              (result.1, result.2 ++ [])) =
        Locals.InteractionSemantics.Expr.openEval expr state
    calc
      _ = Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEval expr state)
          Simulation.Interaction.pure := by
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Locals.InteractionSemantics.Expr.openEval expr state))
        intro result _hResult
        rcases result with ⟨afterExpr, values⟩
        simp only [List.append_nil]
      _ = _ := Simulation.Interaction.bind_pure _
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.ExprSeq.openEval
            (Locals.ExprSeq.cons expr .nil) state)
          (fun result =>
            Locals.InteractionSemantics.Primitive.openEval
              .iszero result.1 result.2))
        (fun result =>
          match result.2 with
          | [value] => Simulation.Interaction.pure (result.1, value)
          | _ => throw EvmYul.EVM.ExecutionException.InvalidInstruction) =
      Simulation.Interaction.bind
        (Locals.InteractionSemantics.Expr.openEval expr state)
        (fun result =>
          Simulation.Interaction.bind
            (match result.2 with
            | [value] => Simulation.Interaction.pure (result.1, value)
            | _ => throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            (fun value =>
              Simulation.Interaction.pure
                (value.1, EvmYul.UInt256.isZero value.2)))
  rw [hArgs]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Expr.openEval_length expr state)
  intro result hLength
  rcases result with ⟨afterExpr, values⟩
  change values.length = 1 at hLength
  cases values with
  | nil => simp at hLength
  | cons value rest =>
      cases rest with
      | nil =>
          simp only [Locals.InteractionSemantics.Primitive.openEval_iszero]
          rfl
      | cons next tail => simp at hLength

theorem openEvalCondition_iszero_eq_map_openEvalOne
    (expr : Locals.Expr 1)
    (state : Locals.InteractionSemantics.State) :
    Locals.InteractionSemantics.Expr.openEvalCondition
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      Simulation.Interaction.map
        (fun result =>
          (result.1, result.2 == EvmYul.UInt256.ofNat 0))
        (Locals.InteractionSemantics.Expr.openEvalOne expr state) := by
  rw [Locals.InteractionSemantics.Expr.openEvalCondition_eq_map_openEvalOne,
    openEvalOne_iszero_eq_map]
  unfold Simulation.Interaction.map
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Locals.InteractionSemantics.Expr.openEvalOne expr state))
  intro result _hResult
  rcases result with ⟨afterExpr, value⟩
  change
    Simulation.Interaction.pure
        (afterExpr,
          EvmYul.UInt256.isZero value != EvmYul.UInt256.ofNat 0) =
      Simulation.Interaction.pure
        (afterExpr, value == EvmYul.UInt256.ofNat 0)
  congr 2
  unfold EvmYul.UInt256.isZero EvmYul.UInt256.fromBool
    Bool.toUInt256 EvmYul.UInt256.eq0
  split
  · rename_i h
    change (value == EvmYul.UInt256.ofNat 0) = true at h
    rw [h]
    decide
  · rename_i h
    have h' : (value == EvmYul.UInt256.ofNat 0) = false :=
      Bool.eq_false_of_not_eq_true (by simpa using h)
    rw [h']
    decide

end Expr

end InteractionArity
end Locals
end EvmCompiler
