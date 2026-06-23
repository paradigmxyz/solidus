import EvmCompiler.Yul.Compiler
import EvmCompiler.Yul.SolcValidation
import EvmCompiler.Yul.FunctionsInteractionClosedPrimitive

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionExpression

open FunctionsInteractionRelation
open FunctionsInteractionPrimitive

def ResultRel (entry : Yul.InteractionSemantics.State) (results : Nat)
    (source : Yul.InteractionSemantics.State × List Word)
    (target : Functions.InteractionSemantics.State × List Word) : Prop :=
  FunctionsInteractionRelation.StateRel source.1 target.1 ∧
    source.2 = target.2 ∧ source.2.length = results ∧
    source.1.store = entry.store

abbrev DoneRel (entry : Yul.InteractionSemantics.State) (results : Nat) :=
  Simulation.Interaction.ExceptRel
    FunctionsInteractionPrimitive.ErrorRel (ResultRel entry results)

namespace ResultRel

theorem of_state
    {results : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {values : List Word}
    (hRel : FunctionsInteractionRelation.StateRel source target)
    (hLength : values.length = results) :
    ResultRel source results (source, values) (target, values) :=
  ⟨hRel, rfl, hLength, rfl⟩

end ResultRel

namespace Expr

theorem primitive_of_args
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {results : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceArgs :
      Yul.InteractionSemantics.Open
        (Yul.InteractionSemantics.State × List Word)}
    {targetArgs :
      Functions.InteractionSemantics.Open
        (Functions.InteractionSemantics.State × List Word)}
    {sourceInitial : Yul.InteractionSemantics.State}
    {primitiveFuel : Nat}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hOutputs :
      Expressions.Structured.BasicOp.outputs op = results)
    (hArgs :
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated
        (DoneRel sourceInitial (Expressions.Structured.BasicOp.inputs op))
        sourceArgs targetArgs) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated (DoneRel sourceInitial results)
      (Simulation.Interaction.bind sourceArgs fun result =>
        Yul.InteractionSemantics.Primitive.openEval
          primitiveFuel result.1 prim result.2.reverse)
      (Simulation.Interaction.bind targetArgs fun result =>
        Locals.InteractionSemantics.Primitive.openEval
          op result.1 result.2) := by
  apply Simulation.Interaction.ForwardRel.bind hArgs
  intro sourceResult targetResult hResult
  rcases hResult with ⟨hState, hValues, hLength, hArgsStore⟩
  cases primitiveFuel with
  | zero =>
      have hTruncated :
          FunctionsInteractionPrimitive.Truncated
            ({ exception := .OutOfFuel, state := sourceResult.1 } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel sourceInitial results)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op targetResult.1 targetResult.2)
          hTruncated)
  | succ fuel =>
      have hPrimitiveRel :=
        hPrimitive (fuel := fuel)
          (sourceValues := sourceResult.2.reverse) hOp
          (by simpa [List.length_reverse] using hLength)
          hState
      have hPrimitiveRel' :
          Simulation.Interaction.ForwardRel
            FunctionsInteractionPrimitive.Truncated
            (FunctionsInteractionPrimitive.PrimitiveDoneRel sourceResult.1 op)
            (Yul.InteractionSemantics.Primitive.openEval
              (fuel + 1) sourceResult.1 prim sourceResult.2.reverse)
            (Locals.InteractionSemantics.Primitive.openEval
              op targetResult.1 targetResult.2) := by
        simpa [hValues] using hPrimitiveRel
      apply Simulation.Interaction.ForwardRel.mono hPrimitiveRel'
      intro sourceDone targetDone hDone
      cases hDone with
      | error hError => exact .error hError
      | ok hOk =>
          exact .ok
            ⟨hOk.1.1, hOk.1.2, hOk.2.1.trans hOutputs,
              hOk.2.2.trans hArgsStore⟩

theorem fuel_zero
    {results : Nat} (expr : AstExpr) (lower : Locals.Expr results)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : Yul.InteractionSemantics.State)
    (target : Functions.InteractionSemantics.State) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated (DoneRel source results)
      (Yul.InteractionSemantics.evalValues
        0 expr codeOverride source)
      (Locals.InteractionSemantics.Expr.openEval lower target) := by
  have hTruncated :
      FunctionsInteractionPrimitive.Truncated
        ({ exception := .OutOfFuel, state := source } :
          Yul.InteractionSemantics.Failure) := by
    trivial
  simpa [Yul.InteractionSemantics.evalValues,
    Yul.Source.Effectful.evalValues,
    Yul.Source.Effectful.Control.fail] using
    (Simulation.Interaction.ForwardRel.truncated
      (doneRel := DoneRel source results)
      (right := Locals.InteractionSemantics.Expr.openEval lower target)
      hTruncated)

theorem lit
    {results : Nat} {value : Word} {lower : Locals.Expr results}
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      EvmCompiler.Yul.Expr.toLocals? results (.Lit value) = some lower)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated (DoneRel source results)
      (Yul.InteractionSemantics.evalValues
        (fuel + 1) (.Lit value) codeOverride source)
      (Locals.InteractionSemantics.Expr.openEval lower target) := by
  by_cases hResults : 1 = results
  · cases hResults
    simp [EvmCompiler.Yul.Expr.toLocals?, EvmCompiler.Yul.Expr.cast]
      at hLower
    subst lower
    have hDone :
        DoneRel source 1 (.ok (source, [value])) (.ok (target, [value])) :=
      .ok (ResultRel.of_state hRel rfl)
    simpa [Yul.InteractionSemantics.evalValues,
      Yul.Source.Effectful.evalValues,
      Locals.InteractionSemantics.Expr.openEval,
      Locals.Source.Effectful.Expr.Control.eval] using
      (Simulation.Interaction.ForwardRel.done
        (truncated := FunctionsInteractionPrimitive.Truncated) hDone)
  · simp [EvmCompiler.Yul.Expr.toLocals?, hResults] at hLower

theorem var
    {results : Nat} {name : EvmYul.Identifier}
    {lower : Locals.Expr results} {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      EvmCompiler.Yul.Expr.toLocals? results (.Var name) = some lower)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated (DoneRel source results)
      (Yul.InteractionSemantics.evalValues
        (fuel + 1) (.Var name) codeOverride source)
      (Locals.InteractionSemantics.Expr.openEval lower target) := by
  by_cases hResults : 1 = results
  · cases hResults
    simp [EvmCompiler.Yul.Expr.toLocals?, EvmCompiler.Yul.Expr.cast]
      at hLower
    subst lower
    cases hLookup : source.lookup? name with
    | none =>
        have hTruncated :
            FunctionsInteractionPrimitive.Truncated
              ({ exception := .UnknownIdentifier name, state := source } :
                Yul.InteractionSemantics.Failure) := by
          trivial
        simpa [Yul.InteractionSemantics.evalValues,
          Yul.InteractionSemantics.stateModel,
          Yul.Source.Effectful.evalValues,
          Yul.Source.Effectful.Control.fail, hLookup] using
          (Simulation.Interaction.ForwardRel.truncated
            (doneRel := DoneRel source 1)
            (right := Locals.InteractionSemantics.Expr.openEval
              (.var (identName name)) target)
            hTruncated)
    | some value =>
        have hTarget := FunctionsInteractionRelation.StateRel.lookup hRel hLookup
        have hDone :
            DoneRel source 1 (.ok (source, [value]))
              (.ok (target, [value])) :=
          .ok (ResultRel.of_state hRel rfl)
        simpa [Yul.InteractionSemantics.evalValues,
          Yul.InteractionSemantics.stateModel,
          Yul.Source.Effectful.evalValues,
          Locals.InteractionSemantics.Expr.openEval,
          Locals.Source.Effectful.Expr.Control.eval,
          Locals.InteractionSemantics.stateModel,
          Locals.Source.Effectful.Ordinary.stateModel,
          Locals.Source.Effectful.StateModel.vars,
          identName, hLookup, hTarget] using
          (Simulation.Interaction.ForwardRel.done
            (truncated := FunctionsInteractionPrimitive.Truncated) hDone)
  · simp [EvmCompiler.Yul.Expr.toLocals?, hResults] at hLower

/-- A source-visible variable cannot take the generic unknown-identifier
truncation branch. The scoped relation derives its source lookup internally. -/
theorem var_scoped
    {results : Nat} {name : EvmYul.Identifier}
    {lower : Locals.Expr results} {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      EvmCompiler.Yul.Expr.toLocals? results (.Var name) = some lower)
    (hVisible : identName name ∈ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated (DoneRel source results)
      (Yul.InteractionSemantics.evalValues
        (fuel + 1) (.Var name) codeOverride source)
      (Locals.InteractionSemantics.Expr.openEval lower target) := by
  by_cases hResults : 1 = results
  · cases hResults
    simp [EvmCompiler.Yul.Expr.toLocals?, EvmCompiler.Yul.Expr.cast]
      at hLower
    subst lower
    obtain ⟨value, hLookup⟩ := hRel.sourceLookup_of_mem hVisible
    have hLookup' : source.lookup? name = some value := by
      simpa [identName] using hLookup
    have hTarget := hRel.state.lookup hLookup'
    have hDone :
        DoneRel source 1 (.ok (source, [value]))
          (.ok (target, [value])) :=
      .ok (ResultRel.of_state hRel.state rfl)
    simpa [Yul.InteractionSemantics.evalValues,
      Yul.InteractionSemantics.stateModel,
      Yul.Source.Canonical.evalValues,
      Yul.Source.Effectful.evalValues,
      Locals.InteractionSemantics.Expr.openEval,
      Locals.Source.Effectful.Expr.Control.eval,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Locals.Source.Effectful.StateModel.vars,
      identName, hLookup', hTarget] using
      (Simulation.Interaction.ForwardRel.done
        (truncated := FunctionsInteractionPrimitive.Truncated) hDone)
  · simp [EvmCompiler.Yul.Expr.toLocals?, hResults] at hLower

end Expr

namespace Args

theorem fuel_zero
    {results : Nat} (args : List AstExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : Yul.InteractionSemantics.State)
    (seq : Locals.ExprSeq results)
    (target : Functions.InteractionSemantics.State) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated (DoneRel source results)
      (Yul.InteractionSemantics.evalArgs
        0 args codeOverride source)
      (Locals.InteractionSemantics.ExprSeq.openEval seq target) := by
  have hTruncated :
      FunctionsInteractionPrimitive.Truncated
        ({ exception := .OutOfFuel, state := source } :
          Yul.InteractionSemantics.Failure) := by
    trivial
  simpa [Yul.InteractionSemantics.evalArgs,
    Yul.Source.Effectful.evalArgs,
    Yul.Source.Effectful.Control.fail] using
    (Simulation.Interaction.ForwardRel.truncated
      (doneRel := DoneRel source results)
      (right := Locals.InteractionSemantics.ExprSeq.openEval seq target)
      hTruncated)

theorem cons
    {results : Nat}
    {sourceInitial : Yul.InteractionSemantics.State}
    {sourceHead :
      Yul.InteractionSemantics.Open
        (Yul.InteractionSemantics.State × List Word)}
    {targetHead :
      Functions.InteractionSemantics.Open
        (Functions.InteractionSemantics.State × List Word)}
    {sourceTail : Yul.InteractionSemantics.State →
      Yul.InteractionSemantics.Open
        (Yul.InteractionSemantics.State × List Word)}
    {targetTail : Functions.InteractionSemantics.State →
      Functions.InteractionSemantics.Open
        (Functions.InteractionSemantics.State × List Word)}
    (hHead :
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated (DoneRel sourceInitial 1)
        sourceHead targetHead)
    (hTail :
      ∀ {source target},
        FunctionsInteractionRelation.StateRel source target →
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated (DoneRel source results)
          (sourceTail source) (targetTail target)) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated
        (DoneRel sourceInitial (results + 1))
      (Simulation.Interaction.bind sourceHead fun head =>
        Simulation.Interaction.bind (sourceTail head.1) fun tail =>
          pure (tail.1, head.2.head! :: tail.2))
      (Simulation.Interaction.bind targetHead fun head =>
        Simulation.Interaction.bind (targetTail head.1) fun tail =>
          pure (tail.1, head.2 ++ tail.2)) := by
  apply Simulation.Interaction.ForwardRel.bind hHead
  intro sourceHeadResult targetHeadResult hHeadResult
  rcases hHeadResult with
    ⟨hHeadState, hHeadValues, hHeadLength, hHeadStore⟩
  apply Simulation.Interaction.ForwardRel.bind (hTail hHeadState)
  intro sourceTailResult targetTailResult hTailResult
  rcases hTailResult with
    ⟨hTailState, hTailValues, hTailLength, hTailStore⟩
  apply Simulation.Interaction.ForwardRel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ⟨hTailState, ?_, ?_, hTailStore.trans hHeadStore⟩
  · have hSingleton :
        sourceHeadResult.2 = [sourceHeadResult.2.head!] := by
      obtain ⟨head, hHeadEq⟩ :=
        List.length_eq_one_iff.mp hHeadLength
      rw [hHeadEq]
      rfl
    rw [← hHeadValues, hSingleton, hTailValues]
    rfl
  · simp only [List.length_cons, hTailLength]

/-- Compose direct arguments while retaining exact source lexical definedness
for the tail. Pure direct expressions preserve the source variable store, so
the scoped relation is reconstructed from the head result rather than supplied
as generated evidence. -/
theorem cons_scoped
    {results : Nat} {layout : List Functions.Name}
    {sourceInitial : Yul.InteractionSemantics.State}
    {targetInitial : Functions.InteractionSemantics.State}
    {sourceHead :
      Yul.InteractionSemantics.Open
        (Yul.InteractionSemantics.State × List Word)}
    {targetHead :
      Functions.InteractionSemantics.Open
        (Functions.InteractionSemantics.State × List Word)}
    {sourceTail : Yul.InteractionSemantics.State →
      Yul.InteractionSemantics.Open
        (Yul.InteractionSemantics.State × List Word)}
    {targetTail : Functions.InteractionSemantics.State →
      Functions.InteractionSemantics.Open
        (Functions.InteractionSemantics.State × List Word)}
    (hInitial : FunctionsInteractionRelation.ScopedStateRel
      layout sourceInitial targetInitial)
    (hHead :
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated (DoneRel sourceInitial 1)
        sourceHead targetHead)
    (hTail :
      ∀ {source target},
        FunctionsInteractionRelation.ScopedStateRel layout source target →
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated (DoneRel source results)
          (sourceTail source) (targetTail target)) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated
        (DoneRel sourceInitial (results + 1))
      (Simulation.Interaction.bind sourceHead fun head =>
        Simulation.Interaction.bind (sourceTail head.1) fun tail =>
          pure (tail.1, head.2.head! :: tail.2))
      (Simulation.Interaction.bind targetHead fun head =>
        Simulation.Interaction.bind (targetTail head.1) fun tail =>
          pure (tail.1, head.2 ++ tail.2)) := by
  apply Simulation.Interaction.ForwardRel.bind hHead
  intro sourceHeadResult targetHeadResult hHeadResult
  rcases hHeadResult with
    ⟨hHeadState, hHeadValues, hHeadLength, hHeadStore⟩
  have hHeadScoped :=
    FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
      hInitial hHeadState hHeadStore
  apply Simulation.Interaction.ForwardRel.bind (hTail hHeadScoped)
  intro sourceTailResult targetTailResult hTailResult
  rcases hTailResult with
    ⟨hTailState, hTailValues, hTailLength, hTailStore⟩
  apply Simulation.Interaction.ForwardRel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ⟨hTailState, ?_, ?_, hTailStore.trans hHeadStore⟩
  · have hSingleton :
        sourceHeadResult.2 = [sourceHeadResult.2.head!] := by
      obtain ⟨head, hHeadEq⟩ :=
        List.length_eq_one_iff.mp hHeadLength
      rw [hHeadEq]
      rfl
    rw [← hHeadValues, hSingleton, hTailValues]
    rfl
  · simp only [List.length_cons, hTailLength]

theorem cons_truncated
    {results : Nat}
    {sourceInitial : Yul.InteractionSemantics.State}
    {sourceHead :
      Yul.InteractionSemantics.Open
        (Yul.InteractionSemantics.State × List Word)}
    {targetHead :
      Functions.InteractionSemantics.Open
        (Functions.InteractionSemantics.State × List Word)}
    {targetTail : Functions.InteractionSemantics.State →
      Functions.InteractionSemantics.Open
        (Functions.InteractionSemantics.State × List Word)}
    (hHead :
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated (DoneRel sourceInitial 1)
        sourceHead targetHead) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated
        (DoneRel sourceInitial (results + 1))
      (Simulation.Interaction.bind sourceHead fun head =>
        Yul.InteractionSemantics.Primitive.fail head.1 .OutOfFuel)
      (Simulation.Interaction.bind targetHead fun head =>
        Simulation.Interaction.bind (targetTail head.1) fun tail =>
          pure (tail.1, head.2 ++ tail.2)) := by
  apply Simulation.Interaction.ForwardRel.bind hHead
  intro sourceHeadResult targetHeadResult hHeadResult
  have hTruncated :
      FunctionsInteractionPrimitive.Truncated
        ({ exception := .OutOfFuel, state := sourceHeadResult.1 } :
          Yul.InteractionSemantics.Failure) := by
    trivial
  simpa [Yul.InteractionSemantics.Primitive.fail] using
    (Simulation.Interaction.ForwardRel.truncated
      (doneRel := DoneRel sourceInitial (results + 1))
      (right :=
        Simulation.Interaction.bind (targetTail targetHeadResult.1) fun tail =>
          pure (tail.1, targetHeadResult.2 ++ tail.2))
      hTruncated)

end Args

theorem exprSeq_openEval_seqCast
    {left right : Nat} (h : left = right)
    (exprs : Locals.ExprSeq left)
    (state : Functions.InteractionSemantics.State) :
    Locals.InteractionSemantics.ExprSeq.openEval
        (EvmCompiler.Yul.Expr.seqCast h exprs) state =
      Locals.InteractionSemantics.ExprSeq.openEval exprs state := by
  cases h
  rfl

/-- Result-arity casts inserted by Yul lowering do not change canonical
Locals expression evaluation. -/
theorem expr_openEval_cast
    {left right : Nat} (h : left = right)
    (expr : Locals.Expr left)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval
        (EvmCompiler.Yul.Expr.cast h expr) state =
      Functions.InteractionSemantics.Expr.openEval expr state := by
  cases h
  rfl

/-- A delayed one-result expression is insensitive to shared-state changes
and to insertion of later compiler-private locals. -/
def StableValue (expr : Locals.Expr 1)
    (base : Functions.InteractionSemantics.State) (value : Word) : Prop :=
  ∀ candidate,
    FunctionsInteractionRelation.TargetExtends
        base.vars candidate.vars →
      Locals.InteractionSemantics.Expr.openEval expr candidate =
        .done (.ok (candidate, [value]))

inductive StableArgs :
    List (Locals.Expr 1) → Functions.InteractionSemantics.State →
      List Word → Prop where
  | nil (base) : StableArgs [] base []
  | cons {head rest base value values} :
      StableValue head base value →
      StableArgs rest base values →
      StableArgs (head :: rest) base (value :: values)

namespace StableValue

theorem mono
    {expr : Locals.Expr 1}
    {base candidate : Functions.InteractionSemantics.State}
    {value : Word}
    (hStable : StableValue expr base value)
    (hExtends : FunctionsInteractionRelation.TargetExtends
      base.vars candidate.vars) :
    StableValue expr candidate value := by
  intro final hFinal
  exact hStable final
    (FunctionsInteractionRelation.TargetExtends.trans hExtends hFinal)

theorem lit (base : Functions.InteractionSemantics.State) (value : Word) :
    StableValue (.lit value) base value := by
  intro candidate _hExtends
  rfl

theorem var
    {base : Functions.InteractionSemantics.State}
    {name : Functions.Name} {value : Word}
    (hLookup : base.vars name = some value) :
    StableValue (.var name) base value := by
  intro candidate hExtends
  have hCandidate := hExtends name value hLookup
  simp [Locals.InteractionSemantics.Expr.openEval,
    Locals.Source.Effectful.Expr.Control.eval,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.vars, hCandidate,
    Simulation.Interaction.pure]
  rfl

end StableValue

namespace StableArgs

theorem length
    {args : List (Locals.Expr 1)}
    {base : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs args base values) :
    values.length = args.length := by
  induction hStable with
  | nil => rfl
  | cons _hHead _hTail ih => simp [ih]

theorem mono
    {args : List (Locals.Expr 1)}
    {base candidate : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs args base values)
    (hExtends : FunctionsInteractionRelation.TargetExtends
      base.vars candidate.vars) :
    StableArgs args candidate values := by
  induction hStable generalizing candidate with
  | nil => exact .nil candidate
  | cons hHead hTail ih =>
      exact .cons (hHead.mono hExtends) (ih hExtends)

theorem append
    {left right : List (Locals.Expr 1)}
    {base : Functions.InteractionSemantics.State}
    {leftValues rightValues : List Word}
    (hLeft : StableArgs left base leftValues)
    (hRight : StableArgs right base rightValues) :
    StableArgs (left ++ right) base (leftValues ++ rightValues) := by
  induction hLeft generalizing right rightValues with
  | nil => simpa using hRight
  | cons hHead hTail ih =>
      simpa using StableArgs.cons hHead (ih hRight)

/-- Stable delayed arguments can be reindexed between Yul's reverse
evaluation order and Functions' source argument order. -/
theorem reverse
    {args : List (Locals.Expr 1)}
    {base : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs args base values) :
    StableArgs args.reverse base values.reverse := by
  induction hStable with
  | nil base => simpa using (StableArgs.nil base)
  | @cons head rest base value values hHead hTail ih =>
      simpa [List.reverse_cons] using
        ih.append (StableArgs.cons hHead (.nil base))

theorem openEval
    {args : List (Locals.Expr 1)}
    {base candidate : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs args base values)
    (hExtends : FunctionsInteractionRelation.TargetExtends
      base.vars candidate.vars) :
    Functions.InteractionSemantics.ArgList.openEval args candidate =
      .done (.ok (candidate, values)) := by
  induction hStable generalizing candidate with
  | nil => rfl
  | @cons head rest base value values hHead hTail ih =>
      have hHeadEval := hHead candidate hExtends
      unfold Locals.InteractionSemantics.Expr.openEval at hHeadEval
      have hHeadEval' :
          Locals.Source.Effectful.Expr.Control.eval
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              head candidate =
            .done (.ok (candidate, [value])) := by
        simpa [Functions.InteractionSemantics.stateModel,
          Functions.InteractionSemantics.primitiveSemantics] using hHeadEval
      have hHeadOne :
          Locals.Source.Effectful.Expr.Control.evalOne
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              head candidate =
            .done (.ok (candidate, value)) := by
        unfold Locals.Source.Effectful.Expr.Control.evalOne
        change
          Simulation.Interaction.bind
              (Locals.Source.Effectful.Expr.Control.eval
                Functions.InteractionSemantics.stateModel
                Functions.InteractionSemantics.primitiveSemantics
                head candidate)
              (fun result =>
                match result.2 with
                | [actual] => pure (result.1, actual)
                | _ => throw EvmYul.EVM.ExecutionException.InvalidInstruction) =
            .done (.ok (candidate, value))
        rw [hHeadEval', Simulation.Interaction.bind_done_ok]
        rfl
      unfold Functions.InteractionSemantics.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval
        Functions.Source.Effectful.ArgList.Control.eval
      have hTailEval := ih hExtends
      unfold Functions.InteractionSemantics.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval at hTailEval
      change
        Simulation.Interaction.bind
            (Locals.Source.Effectful.Expr.Control.evalOne
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              head candidate)
            (fun headResult =>
              Simulation.Interaction.bind
                (Functions.Source.Effectful.ArgList.Control.eval
                  Functions.InteractionSemantics.stateModel
                  Functions.InteractionSemantics.primitiveSemantics
                  rest headResult.1)
                (fun tailResult =>
                  pure (tailResult.1, headResult.2 :: tailResult.2))) =
          .done (.ok (candidate, value :: values))
      rw [hHeadOne, Simulation.Interaction.bind_done_ok,
        hTailEval, Simulation.Interaction.bind_done_ok]
      rfl

theorem exprSeq_openEval
    {args : List (Locals.Expr 1)} {results : Nat}
    {seq : Locals.ExprSeq results}
    {base candidate : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs args base values)
    (hSeq : EvmCompiler.Yul.Expr.List.toSeq? args results = some seq)
    (hExtends : FunctionsInteractionRelation.TargetExtends
      base.vars candidate.vars) :
    Locals.InteractionSemantics.ExprSeq.openEval seq candidate =
      .done (.ok (candidate, values)) := by
  induction hStable generalizing results seq candidate with
  | nil =>
      cases results with
      | zero =>
          simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
          subst seq
          rfl
      | succ results =>
          simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
  | @cons head rest base value values hHead hTail ih =>
      cases results with
      | zero =>
          simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
      | succ tailResults =>
          cases hTailSeq :
              EvmCompiler.Yul.Expr.List.toSeq? rest tailResults with
          | none =>
              simp [EvmCompiler.Yul.Expr.List.toSeq?, hTailSeq] at hSeq
          | some tail =>
              simp [EvmCompiler.Yul.Expr.List.toSeq?, hTailSeq] at hSeq
              subst seq
              rw [exprSeq_openEval_seqCast]
              have hHeadEval := hHead candidate hExtends
              unfold Locals.InteractionSemantics.Expr.openEval at hHeadEval
              unfold Locals.InteractionSemantics.ExprSeq.openEval
                Locals.Source.Effectful.Expr.Control.ExprSeq.eval
              have hTailEval := ih hTailSeq hExtends
              unfold Locals.InteractionSemantics.ExprSeq.openEval at hTailEval
              change
                Simulation.Interaction.bind
                    (Locals.Source.Effectful.Expr.Control.eval
                      Locals.InteractionSemantics.stateModel
                      Locals.InteractionSemantics.primitiveSemantics
                      head candidate)
                    (fun headResult =>
                      Simulation.Interaction.bind
                        (Locals.Source.Effectful.Expr.Control.ExprSeq.eval
                          Locals.InteractionSemantics.stateModel
                          Locals.InteractionSemantics.primitiveSemantics
                          tail headResult.1)
                        (fun tailResult =>
                          pure
                            (tailResult.1,
                              headResult.2 ++ tailResult.2))) =
                  .done (.ok (candidate, value :: values))
              rw [hHeadEval, Simulation.Interaction.bind_done_ok,
                hTailEval, Simulation.Interaction.bind_done_ok]
              rfl

end StableArgs

structure DirectAt
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) : Prop where
  evalValues :
    ∀ {results : Nat} {expr : AstExpr} {lower : Locals.Expr results}
      {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State},
      EvmCompiler.Yul.Expr.toLocals? results expr = some lower →
      FunctionsInteractionRelation.StateRel source target →
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated (DoneRel source results)
        (Yul.InteractionSemantics.evalValues
          fuel expr codeOverride source)
        (Locals.InteractionSemantics.Expr.openEval lower target)
  evalArgs :
    ∀ {args : List AstExpr} {lower : List (Locals.Expr 1)}
      {results : Nat} {seq : Locals.ExprSeq results}
      {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State},
      EvmCompiler.Yul.Expr.List.toLocals1? args = some lower →
      EvmCompiler.Yul.Expr.List.toSeq? lower results = some seq →
      FunctionsInteractionRelation.StateRel source target →
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated (DoneRel source results)
        (Yul.InteractionSemantics.evalArgs
          fuel args codeOverride source)
        (Locals.InteractionSemantics.ExprSeq.openEval seq target)

theorem directAt
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) : DirectAt hPrimitive codeOverride fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          exact
            { evalValues := by
                intro results expr lower source target hLower hRel
                exact Expr.fuel_zero expr lower codeOverride source target
              evalArgs := by
                intro args lower results seq source target hLower hSeq hRel
                exact Args.fuel_zero args codeOverride source seq target }
      | succ previous =>
          have hPrevious : DirectAt hPrimitive codeOverride previous :=
            ih previous (Nat.lt_succ_self previous)
          refine { evalValues := ?_, evalArgs := ?_ }
          · intro results expr lower source target hLower hRel
            cases expr with
            | Lit value => exact Expr.lit hLower hRel
            | Var name => exact Expr.var hLower hRel
            | Call callee args =>
                cases callee with
                | inr functionName =>
                    simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
                | inl prim =>
                    cases hOp : Prim.toBasicOp? prim with
                    | none =>
                        simp [EvmCompiler.Yul.Expr.toLocals?, hOp] at hLower
                    | some op =>
                        cases hArgsLower :
                            EvmCompiler.Yul.Expr.List.toLocals1? args with
                        | none =>
                            simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                              hArgsLower] at hLower
                        | some lowerArgs =>
                            cases hSeq :
                                EvmCompiler.Yul.Expr.List.toStackSeq?
                                  lowerArgs
                                  (Expressions.Structured.BasicOp.inputs op) with
                            | none =>
                                simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                  hArgsLower, hSeq] at hLower
                            | some seq =>
                                by_cases hOutputs :
                                    Expressions.Structured.BasicOp.outputs op =
                                      results
                                · cases hOutputs
                                  simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                    hArgsLower, hSeq] at hLower
                                  subst lower
                                  have hLowerReverse :
                                      EvmCompiler.Yul.Expr.List.toLocals1?
                                          args.reverse =
                                        some lowerArgs.reverse :=
                                    EvmCompiler.Yul.Expr.List.toLocals1?_reverse
                                      hArgsLower
                                  have hDirectSeq :
                                      EvmCompiler.Yul.Expr.List.toSeq?
                                          lowerArgs.reverse
                                          (Expressions.Structured.BasicOp.inputs
                                            op) =
                                        some seq := by
                                    simpa [EvmCompiler.Yul.Expr.List.toStackSeq?]
                                      using hSeq
                                  have hArgsRel :=
                                    hPrevious.evalArgs hLowerReverse hDirectSeq
                                      hRel
                                  have hPrimitiveRel :=
                                    Expr.primitive_of_args hPrimitive
                                      (primitiveFuel := previous)
                                      (Prim.toUncheckedBasicOp?_of_toBasicOp?
                                        hOp)
                                      rfl hArgsRel
                                  simpa [Yul.InteractionSemantics.evalValues,
                                    Yul.Source.Effectful.evalValues,
                                    Locals.InteractionSemantics.Expr.openEval,
                                    Locals.Source.Effectful.Expr.Control.eval,
                                    EvmCompiler.Yul.Expr.cast,
                                    exprSeq_openEval_seqCast] using hPrimitiveRel
                                · simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                    hArgsLower, hSeq, hOutputs] at hLower
          · intro args lower results seq source target hLower hSeq hRel
            cases args with
            | nil =>
                simp [EvmCompiler.Yul.Expr.List.toLocals1?] at hLower
                subst lower
                cases results with
                | zero =>
                    simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
                    subst seq
                    have hDone :
                        DoneRel source 0 (.ok (source, []))
                          (.ok (target, [])) :=
                      .ok (ResultRel.of_state hRel rfl)
                    simpa [Yul.InteractionSemantics.evalArgs,
                      Yul.Source.Effectful.evalArgs,
                      Locals.InteractionSemantics.ExprSeq.openEval,
                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval] using
                      (Simulation.Interaction.ForwardRel.done
                        (truncated :=
                          FunctionsInteractionPrimitive.Truncated) hDone)
                | succ results =>
                    simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
            | cons head rest =>
                cases hHeadLower : EvmCompiler.Yul.Expr.toLocals? 1 head with
                | none =>
                    simp [EvmCompiler.Yul.Expr.List.toLocals1?, hHeadLower]
                      at hLower
                | some lowerHead =>
                    cases hRestLower :
                        EvmCompiler.Yul.Expr.List.toLocals1? rest with
                    | none =>
                        simp [EvmCompiler.Yul.Expr.List.toLocals1?, hHeadLower,
                          hRestLower] at hLower
                    | some lowerRest =>
                        simp [EvmCompiler.Yul.Expr.List.toLocals1?, hHeadLower,
                          hRestLower] at hLower
                        subst lower
                        cases results with
                        | zero =>
                            simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
                        | succ tailResults =>
                            cases hTailSeq :
                                EvmCompiler.Yul.Expr.List.toSeq?
                                  lowerRest tailResults with
                            | none =>
                                simp [EvmCompiler.Yul.Expr.List.toSeq?,
                                  hTailSeq] at hSeq
                            | some tailSeq =>
                                rw [EvmCompiler.Yul.Expr.List.toSeq?, hTailSeq]
                                  at hSeq
                                injection hSeq with hSeqEq
                                subst seq
                                have hHeadRel :=
                                  hPrevious.evalValues hHeadLower hRel
                                cases previous with
                                | zero =>
                                    have hCombined :=
                                      Args.cons_truncated
                                        (results := tailResults)
                                        (targetTail := fun state =>
                                          Locals.InteractionSemantics.ExprSeq.openEval
                                            tailSeq state)
                                        hHeadRel
                                    rw [Yul.InteractionSemantics.EvalArgs.one_cons]
                                    rw [exprSeq_openEval_seqCast]
                                    simpa [
                                      Locals.InteractionSemantics.ExprSeq.openEval,
                                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
                                      using
                                      hCombined
                                | succ tailFuel =>
                                    have hTail :
                                        DirectAt hPrimitive codeOverride
                                          tailFuel :=
                                      ih tailFuel (by omega)
                                    have hTailRel :
                                        ∀ {source target},
                                          FunctionsInteractionRelation.StateRel
                                              source target →
                                            Simulation.Interaction.ForwardRel
                                              FunctionsInteractionPrimitive.Truncated
                                              (DoneRel source tailResults)
                                              (Yul.InteractionSemantics.evalArgs
                                                tailFuel rest codeOverride source)
                                              (Locals.InteractionSemantics.ExprSeq.openEval
                                                tailSeq target) := by
                                      intro sourceMid targetMid hMid
                                      exact hTail.evalArgs hRestLower hTailSeq hMid
                                    have hCombined :=
                                      Args.cons (results := tailResults)
                                        (sourceTail := fun state =>
                                          Yul.InteractionSemantics.evalArgs
                                            tailFuel rest codeOverride state)
                                        (targetTail := fun state =>
                                          Locals.InteractionSemantics.ExprSeq.openEval
                                            tailSeq state)
                                        hHeadRel hTailRel
                                    rw [show tailFuel.succ + 1 = tailFuel + 2 by
                                      omega]
                                    rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
                                    rw [exprSeq_openEval_seqCast]
                                    simpa [
                                      Locals.InteractionSemantics.ExprSeq.openEval,
                                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
                                      using
                                      hCombined

/-- Validation-aware direct expression capability. Unlike `DirectAt`, this
interface carries the source lexical layout, so accepted variables are proved
defined instead of treating a missing lookup as semantic truncation. -/
structure ScopedDirectAt
    (profile : SolcValidation.DialectProfile)
    (contract : AstContract)
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) : Prop where
  evalValues :
    ∀ {results : Nat} {expr : AstExpr} {lower : Locals.Expr results}
      {layout : List Functions.Name}
      {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State},
      SolcValidation.ExprOk? profile contract layout results expr = true →
      EvmCompiler.Yul.Expr.toLocals? results expr = some lower →
      FunctionsInteractionRelation.ScopedStateRel layout source target →
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated (DoneRel source results)
        (Yul.InteractionSemantics.evalValues
          fuel expr codeOverride source)
        (Locals.InteractionSemantics.Expr.openEval lower target)
  evalArgs :
    ∀ {args : List AstExpr} {lower : List (Locals.Expr 1)}
      {results : Nat} {seq : Locals.ExprSeq results}
      {layout : List Functions.Name}
      {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State},
      SolcValidation.ExprsOk? profile contract layout args = true →
      EvmCompiler.Yul.Expr.List.toLocals1? args = some lower →
      EvmCompiler.Yul.Expr.List.toSeq? lower results = some seq →
      FunctionsInteractionRelation.ScopedStateRel layout source target →
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated (DoneRel source results)
        (Yul.InteractionSemantics.evalArgs
          fuel args codeOverride source)
        (Locals.InteractionSemantics.ExprSeq.openEval seq target)

theorem scopedDirectAt
    (profile : SolcValidation.DialectProfile)
    (contract : AstContract)
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) :
    ScopedDirectAt profile contract hPrimitive codeOverride fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          exact
            { evalValues := by
                intro results expr lower layout source target _hOk hLower hRel
                exact Expr.fuel_zero expr lower codeOverride source target
              evalArgs := by
                intro args lower results seq layout source target _hOk hLower
                  hSeq hRel
                exact Args.fuel_zero args codeOverride source seq target }
      | succ previous =>
          have hPrevious :
              ScopedDirectAt profile contract hPrimitive codeOverride
                previous :=
            ih previous (Nat.lt_succ_self previous)
          refine { evalValues := ?_, evalArgs := ?_ }
          · intro results expr lower layout source target hOk hLower hRel
            cases expr with
            | Lit value => exact Expr.lit hLower hRel.state
            | Var name =>
                exact Expr.var_scoped hLower
                  (SolcValidation.exprOk_var_mem hOk) hRel
            | Call callee args =>
                cases callee with
                | inr functionName =>
                    simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
                | inl prim =>
                    have hArgsOk :=
                      SolcValidation.exprsOk_of_exprOk_primitive hOk
                    cases hOp : Prim.toBasicOp? prim with
                    | none =>
                        simp [EvmCompiler.Yul.Expr.toLocals?, hOp] at hLower
                    | some op =>
                        cases hArgsLower :
                            EvmCompiler.Yul.Expr.List.toLocals1? args with
                        | none =>
                            simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                              hArgsLower] at hLower
                        | some lowerArgs =>
                            cases hSeq :
                                EvmCompiler.Yul.Expr.List.toStackSeq?
                                  lowerArgs
                                  (Expressions.Structured.BasicOp.inputs op) with
                            | none =>
                                simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                  hArgsLower, hSeq] at hLower
                            | some seq =>
                                by_cases hOutputs :
                                    Expressions.Structured.BasicOp.outputs op =
                                      results
                                · cases hOutputs
                                  simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                    hArgsLower, hSeq] at hLower
                                  subst lower
                                  have hLowerReverse :
                                      EvmCompiler.Yul.Expr.List.toLocals1?
                                          args.reverse =
                                        some lowerArgs.reverse :=
                                    EvmCompiler.Yul.Expr.List.toLocals1?_reverse
                                      hArgsLower
                                  have hDirectSeq :
                                      EvmCompiler.Yul.Expr.List.toSeq?
                                          lowerArgs.reverse
                                          (Expressions.Structured.BasicOp.inputs
                                            op) =
                                        some seq := by
                                    simpa [EvmCompiler.Yul.Expr.List.toStackSeq?]
                                      using hSeq
                                  have hArgsOkReverse :
                                      SolcValidation.ExprsOk? profile contract
                                          layout args.reverse = true := by
                                    simpa [SolcValidation.ExprsOk?] using
                                      SolcValidation.exprsOk_reverse hArgsOk
                                  have hArgsRel :=
                                    hPrevious.evalArgs hArgsOkReverse
                                      hLowerReverse hDirectSeq hRel
                                  have hPrimitiveRel :=
                                    Expr.primitive_of_args hPrimitive
                                      (primitiveFuel := previous)
                                      (Prim.toUncheckedBasicOp?_of_toBasicOp?
                                        hOp)
                                      rfl hArgsRel
                                  simpa [Yul.InteractionSemantics.evalValues,
                                    Yul.Source.Effectful.evalValues,
                                    Locals.InteractionSemantics.Expr.openEval,
                                    Locals.Source.Effectful.Expr.Control.eval,
                                    EvmCompiler.Yul.Expr.cast,
                                    exprSeq_openEval_seqCast] using hPrimitiveRel
                                · simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                    hArgsLower, hSeq, hOutputs] at hLower
          · intro args lower results seq layout source target hOk hLower hSeq
              hRel
            cases args with
            | nil =>
                simp [EvmCompiler.Yul.Expr.List.toLocals1?] at hLower
                subst lower
                cases results with
                | zero =>
                    simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
                    subst seq
                    have hDone :
                        DoneRel source 0 (.ok (source, []))
                          (.ok (target, [])) :=
                      .ok (ResultRel.of_state hRel.state rfl)
                    simpa [Yul.InteractionSemantics.evalArgs,
                      Yul.Source.Effectful.evalArgs,
                      Locals.InteractionSemantics.ExprSeq.openEval,
                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval] using
                      (Simulation.Interaction.ForwardRel.done
                        (truncated :=
                          FunctionsInteractionPrimitive.Truncated) hDone)
                | succ results =>
                    simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
            | cons head rest =>
                have hOkParts :
                    SolcValidation.ExprOk? profile contract layout 1 head =
                        true ∧
                      SolcValidation.ExprsOk? profile contract layout rest =
                        true := by
                  simpa [SolcValidation.ExprsOk?] using hOk
                cases hHeadLower : EvmCompiler.Yul.Expr.toLocals? 1 head with
                | none =>
                    simp [EvmCompiler.Yul.Expr.List.toLocals1?, hHeadLower]
                      at hLower
                | some lowerHead =>
                    cases hRestLower :
                        EvmCompiler.Yul.Expr.List.toLocals1? rest with
                    | none =>
                        simp [EvmCompiler.Yul.Expr.List.toLocals1?, hHeadLower,
                          hRestLower] at hLower
                    | some lowerRest =>
                        simp [EvmCompiler.Yul.Expr.List.toLocals1?, hHeadLower,
                          hRestLower] at hLower
                        subst lower
                        cases results with
                        | zero =>
                            simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
                        | succ tailResults =>
                            cases hTailSeq :
                                EvmCompiler.Yul.Expr.List.toSeq?
                                  lowerRest tailResults with
                            | none =>
                                simp [EvmCompiler.Yul.Expr.List.toSeq?,
                                  hTailSeq] at hSeq
                            | some tailSeq =>
                                rw [EvmCompiler.Yul.Expr.List.toSeq?, hTailSeq]
                                  at hSeq
                                injection hSeq with hSeqEq
                                subst seq
                                have hHeadRel :=
                                  hPrevious.evalValues hOkParts.1 hHeadLower
                                    hRel
                                cases previous with
                                | zero =>
                                    have hCombined :=
                                      Args.cons_truncated
                                        (results := tailResults)
                                        (targetTail := fun state =>
                                          Locals.InteractionSemantics.ExprSeq.openEval
                                            tailSeq state)
                                        hHeadRel
                                    rw [Yul.InteractionSemantics.EvalArgs.one_cons]
                                    rw [exprSeq_openEval_seqCast]
                                    simpa [
                                      Locals.InteractionSemantics.ExprSeq.openEval,
                                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
                                      using hCombined
                                | succ tailFuel =>
                                    have hTail :
                                        ScopedDirectAt profile contract
                                          hPrimitive codeOverride tailFuel :=
                                      ih tailFuel (by omega)
                                    have hTailRel :
                                        ∀ {source target},
                                          FunctionsInteractionRelation.ScopedStateRel
                                              layout source target →
                                            Simulation.Interaction.ForwardRel
                                              FunctionsInteractionPrimitive.Truncated
                                              (DoneRel source tailResults)
                                              (Yul.InteractionSemantics.evalArgs
                                                tailFuel rest codeOverride source)
                                              (Locals.InteractionSemantics.ExprSeq.openEval
                                                tailSeq target) := by
                                      intro sourceMid targetMid hMid
                                      exact hTail.evalArgs hOkParts.2 hRestLower
                                        hTailSeq hMid
                                    have hCombined :=
                                      Args.cons_scoped
                                        (results := tailResults) hRel hHeadRel
                                        hTailRel
                                    rw [show tailFuel.succ + 1 = tailFuel + 2 by
                                      omega]
                                    rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
                                    rw [exprSeq_openEval_seqCast]
                                    simpa [
                                      Locals.InteractionSemantics.ExprSeq.openEval,
                                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
                                      using hCombined

/-- Concrete adjacent expression preservation for the ordinary compiler's
complete primitive surface. -/
theorem compilerDirectAt
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) :
    DirectAt FunctionsInteractionClosedPrimitive.compilerSelected
      codeOverride fuel :=
  directAt FunctionsInteractionClosedPrimitive.compilerSelected
    codeOverride fuel

/-- Validation-aware specialization for the ordinary compiler's complete
direct primitive surface. -/
theorem compilerScopedDirectAt
    (profile : SolcValidation.DialectProfile)
    (contract : AstContract)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) :
    ScopedDirectAt profile contract
      FunctionsInteractionClosedPrimitive.compilerSelected
      codeOverride fuel :=
  scopedDirectAt profile contract
    FunctionsInteractionClosedPrimitive.compilerSelected codeOverride fuel

end FunctionsInteractionExpression
end Yul
end EvmCompiler
