import EvmCompiler.Yul.FunctionsInteractionMode
import EvmCompiler.Locals.InteractionArity

/-!
Typed output-arity facts for the shared ordinary/guarded Functions semantics.
The guarded primitive handler either rejects an unsafe operation or delegates
to the ordinary handler, so it cannot introduce a successful result of the
wrong arity.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionArityMode

open FunctionsInteractionMode

abbrev OutputLength := Locals.InteractionArity.OutputLength

theorem ordinaryPrimitive_length
    {op : Structured.BasicOp}
    {state : Functions.InteractionSemantics.State}
    {values : List Word}
    (hInputs : values.length = Expressions.Structured.BasicOp.inputs op) :
    Simulation.Interaction.AllDone
      (OutputLength (Expressions.Structured.BasicOp.outputs op))
      (Locals.InteractionSemantics.Primitive.openEval
        op state values) := by
  by_cases hSupports :
      Locals.InteractionSemantics.Primitive.supportsOpen op = true
  · exact
      Locals.InteractionPreservation.Primitive.openEval_length
        hInputs hSupports
  · unfold Locals.InteractionSemantics.Primitive.openEval
    simp only [hInputs, hSupports, if_pos, if_neg]
    exact .done True.intro

theorem primitive_length (mode : Mode)
    {op : Structured.BasicOp}
    {state : Functions.InteractionSemantics.State}
    {values : List Word}
    (hInputs : values.length = Expressions.Structured.BasicOp.inputs op) :
    Simulation.Interaction.AllDone
      (OutputLength (Expressions.Structured.BasicOp.outputs op))
      ((targetPrimitive mode).eval op state values) := by
  cases mode with
  | ordinary => exact ordinaryPrimitive_length hInputs
  | guarded contract =>
      change Simulation.Interaction.AllDone _
        (Functions.AllocationInteractionSafeSemantics.openEval
          contract op state values)
      by_cases hSafe :
          Functions.AllocationInteractionPrimitive.PrimitiveSafe
            contract op state values
      · rw [Functions.AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
          hSafe]
        exact ordinaryPrimitive_length hInputs
      · unfold Functions.AllocationInteractionSafeSemantics.openEval
        simp only [hSafe, if_false]
        exact .done True.intro

mutual
  theorem Expr.openEval_length (mode : Mode) {results : Nat}
      (expr : Functions.Expr results)
      (state : Functions.InteractionSemantics.State) :
      Simulation.Interaction.AllDone (OutputLength results)
        (FunctionsInteractionMode.Target.Expr.openEval mode expr state) := by
    cases expr with
    | lit value => exact .done rfl
    | var name =>
        unfold FunctionsInteractionMode.Target.Expr.openEval
          Locals.Source.Effectful.Expr.Control.eval
        cases hLookup : state.vars name with
        | none =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => pure (state, [value])
              | none =>
                  throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done True.intro
        | some value =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => pure (state, [value])
              | none =>
                  throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done rfl
    | code code => exact .done trivial
    | prim op args =>
        unfold FunctionsInteractionMode.Target.Expr.openEval
          Locals.Source.Effectful.Expr.Control.eval
        apply Simulation.Interaction.AllDone.bind
          (ExprSeq.openEval_length mode args state)
        · intro _error _hError
          trivial
        · intro result hArgs
          rcases result with ⟨afterArgs, values⟩
          change Simulation.Interaction.AllDone
            (OutputLength (Expressions.Structured.BasicOp.outputs op))
            ((targetPrimitive mode).eval op afterArgs values)
          exact primitive_length mode hArgs

  theorem ExprSeq.openEval_length (mode : Mode) {results : Nat}
      (exprs : Locals.ExprSeq results)
      (state : Functions.InteractionSemantics.State) :
      Simulation.Interaction.AllDone (OutputLength results)
        (FunctionsInteractionMode.Target.ExprSeq.openEval
          mode exprs state) := by
    cases exprs with
    | nil => exact .done rfl
    | @cons headResults tailResults head tail =>
        unfold FunctionsInteractionMode.Target.ExprSeq.openEval
          Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        apply Simulation.Interaction.AllDone.bind
          (Expr.openEval_length mode head state)
        · intro _error _hError
          trivial
        · intro headResult hHead
          rcases headResult with ⟨afterHead, headValues⟩
          apply Simulation.Interaction.AllDone.bind
            (ExprSeq.openEval_length mode tail afterHead)
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

theorem openEvalOne_iszero_eq_map (mode : Mode)
    (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State) :
    FunctionsInteractionMode.Target.Expr.openEvalOne mode
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      Simulation.Interaction.map
        (fun result => (result.1, EvmYul.UInt256.isZero result.2))
        (FunctionsInteractionMode.Target.Expr.openEvalOne
          mode expr state) := by
  rw [FunctionsInteractionMode.Target.Expr.openEvalOne_eq_bind]
  unfold Simulation.Interaction.map
  rw [FunctionsInteractionMode.Target.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  have hArgs :
      FunctionsInteractionMode.Target.ExprSeq.openEval mode
          (Locals.ExprSeq.cons expr .nil) state =
        FunctionsInteractionMode.Target.Expr.openEval mode expr state := by
    unfold FunctionsInteractionMode.Target.ExprSeq.openEval
      Locals.Source.Effectful.Expr.Control.ExprSeq.eval
    change
      Simulation.Interaction.bind
          (FunctionsInteractionMode.Target.Expr.openEval mode expr state)
          (fun result => pure (result.1, result.2 ++ [])) =
        FunctionsInteractionMode.Target.Expr.openEval mode expr state
    calc
      _ = Simulation.Interaction.bind
          (FunctionsInteractionMode.Target.Expr.openEval mode expr state)
          pure := by
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (FunctionsInteractionMode.Target.Expr.openEval
              mode expr state))
        intro result _hResult
        rcases result with ⟨afterExpr, values⟩
        simp only [List.append_nil]
      _ = _ := Simulation.Interaction.bind_pure _
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (FunctionsInteractionMode.Target.ExprSeq.openEval mode
            (Locals.ExprSeq.cons expr .nil) state)
          (fun result =>
            (targetPrimitive mode).eval .iszero result.1 result.2))
        (fun result =>
          match result.2 with
          | [value] => pure (result.1, value)
          | _ => throw .InvalidInstruction) =
      Simulation.Interaction.bind
        (FunctionsInteractionMode.Target.Expr.openEval mode expr state)
        (fun result =>
          Simulation.Interaction.bind
            (match result.2 with
            | [value] => pure (result.1, value)
            | _ => throw .InvalidInstruction)
            (fun value =>
              pure (value.1, EvmYul.UInt256.isZero value.2)))
  rw [hArgs, Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Expr.openEval_length mode expr state)
  intro result hLength
  rcases result with ⟨afterExpr, values⟩
  change values.length = 1 at hLength
  cases values with
  | nil => simp at hLength
  | cons value rest =>
      cases rest with
      | nil =>
          rw [targetPrimitive_iszero]
          simp only [Locals.InteractionSemantics.Primitive.openEval_iszero]
          rfl
      | cons next tail => simp at hLength

theorem openEvalCondition_iszero_eq_map_openEvalOne (mode : Mode)
    (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State) :
    FunctionsInteractionMode.Target.Expr.openEvalCondition mode
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      Simulation.Interaction.map
        (fun result =>
          (result.1, result.2 == EvmYul.UInt256.ofNat 0))
        (FunctionsInteractionMode.Target.Expr.openEvalOne
          mode expr state) := by
  rw [FunctionsInteractionMode.Target.Expr.openEvalCondition_eq_map_openEvalOne,
    openEvalOne_iszero_eq_map]
  unfold Simulation.Interaction.map
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (FunctionsInteractionMode.Target.Expr.openEvalOne mode expr state))
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

end FunctionsInteractionArityMode
end Yul
end EvmCompiler
