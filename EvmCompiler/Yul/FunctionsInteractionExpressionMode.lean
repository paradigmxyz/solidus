import EvmCompiler.Yul.FunctionsInteractionExpression
import EvmCompiler.Yul.FunctionsInteractionMode

/-!
Mode-parametric expression preservation for the adjacent Yul-to-Functions
pass. This module reuses the ordinary pass's relations and generic interaction
combinators while selecting only the canonical primitive handlers through
`FunctionsInteractionMode`.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionExpressionMode

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionMode

abbrev DoneRel := FunctionsInteractionExpression.DoneRel

namespace Expr

theorem primitive_of_args
    (mode : Mode) (hPrimitive : CompilerSelected mode)
    {results : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceArgs : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Word)}
    {targetArgs : Functions.InteractionSemantics.Open
      (Functions.InteractionSemantics.State × List Word)}
    {sourceInitial : Yul.InteractionSemantics.State}
    {primitiveFuel : Nat}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = results)
    (hArgs : Simulation.Interaction.ForwardRel Truncated
      (DoneRel sourceInitial (Expressions.Structured.BasicOp.inputs op))
      sourceArgs targetArgs) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel sourceInitial results)
      (Simulation.Interaction.bind sourceArgs fun result =>
        (sourcePrimitive mode).eval
          primitiveFuel result.1 prim result.2.reverse)
      (Simulation.Interaction.bind targetArgs fun result =>
        (targetPrimitive mode).eval op result.1 result.2) := by
  apply Simulation.Interaction.ForwardRel.bind hArgs
  intro sourceResult targetResult hResult
  rcases hResult with ⟨hState, hValues, hLength, hArgsStore⟩
  cases primitiveFuel with
  | zero =>
      cases mode with
      | ordinary =>
          have hTruncated : Truncated
              ({ exception := .OutOfFuel, state := sourceResult.1 } :
                Yul.InteractionSemantics.Failure) := by
            trivial
          simpa [sourcePrimitive,
            Yul.InteractionSemantics.Primitive.openEval,
            Yul.InteractionSemantics.Primitive.fail] using
            (Simulation.Interaction.ForwardRel.truncated
              (doneRel := DoneRel sourceInitial results)
              (right :=
                (targetPrimitive .ordinary).eval
                  op targetResult.1 targetResult.2)
              hTruncated)
      | guarded contract =>
          by_cases hSourceSafe :
              AllocationInteractionSafeSemantics.PrimitiveSafe
                contract prim sourceResult.1 sourceResult.2.reverse
          · have hTruncated : Truncated
                ({ exception := .OutOfFuel, state := sourceResult.1 } :
                  Yul.InteractionSemantics.Failure) := by
              trivial
            rw [show
              (sourcePrimitive (.guarded contract)).eval
                  0 sourceResult.1 prim sourceResult.2.reverse =
                Yul.InteractionSemantics.Primitive.openEval
                  0 sourceResult.1 prim sourceResult.2.reverse by
              exact
                AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
                  hSourceSafe]
            exact Simulation.Interaction.ForwardRel.truncated hTruncated
          · have hTargetUnsafe :
                ¬ Functions.AllocationInteractionPrimitive.PrimitiveSafe
                  contract op targetResult.1 targetResult.2 := by
              intro hTargetSafe
              apply hSourceSafe
              rw [FunctionsAllocationInteractionSafety.Primitive.safe_eq_functions
                hOp hState]
              simpa [hValues] using hTargetSafe
            change Simulation.Interaction.ForwardRel Truncated
              (DoneRel sourceInitial results)
              (AllocationInteractionSafeSemantics.openEval
                contract 0 sourceResult.1 prim sourceResult.2.reverse)
              (Functions.AllocationInteractionSafeSemantics.openEval
                contract op targetResult.1 targetResult.2)
            unfold AllocationInteractionSafeSemantics.openEval
              Functions.AllocationInteractionSafeSemantics.openEval
            simp only [hSourceSafe, hTargetUnsafe, ↓reduceIte]
            exact Simulation.Interaction.ForwardRel.done
              (.error (by simp [FunctionsInteractionPrimitive.ErrorRel]))
  | succ fuel =>
      have hPrimitiveRel :=
        hPrimitive (fuel := fuel)
          (sourceValues := sourceResult.2.reverse) hOp
          (by simpa [List.length_reverse] using hLength) hState
      have hPrimitiveRel' :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionPrimitive.PrimitiveDoneRel sourceResult.1 op)
            ((sourcePrimitive mode).eval
              (fuel + 1) sourceResult.1 prim sourceResult.2.reverse)
            ((targetPrimitive mode).eval
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
    (mode : Mode) {results : Nat} (expr : AstExpr)
    (lower : Locals.Expr results)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : Yul.InteractionSemantics.State)
    (target : Functions.InteractionSemantics.State) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel source results)
      (Source.evalValues mode 0 expr codeOverride source)
      (Target.Expr.openEval mode lower target) := by
  have hTruncated : Truncated
      ({ exception := .OutOfFuel, state := source } :
        Yul.InteractionSemantics.Failure) := by
    trivial
  unfold Source.evalValues Yul.Source.Canonical.evalValues
  simp only [Yul.Source.Effectful.evalValues,
    Yul.Source.Effectful.Control.fail]
  exact Simulation.Interaction.ForwardRel.truncated hTruncated

theorem lit
    (mode : Mode) {results : Nat} {value : Word}
    {lower : Locals.Expr results} {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? results (.Lit value) = some lower)
    (hRel : StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel source results)
      (Source.evalValues mode (fuel + 1) (.Lit value) codeOverride source)
      (Target.Expr.openEval mode lower target) := by
  by_cases hResults : 1 = results
  · cases hResults
    simp [EvmCompiler.Yul.Expr.toLocals?, EvmCompiler.Yul.Expr.cast] at hLower
    subst lower
    have hDone : DoneRel source 1
        (.ok (source, [value])) (.ok (target, [value])) :=
      .ok (FunctionsInteractionExpression.ResultRel.of_state hRel rfl)
    cases mode <;>
      simpa [Source.evalValues, sourcePrimitive,
        Yul.Source.Canonical.evalValues,
        Yul.Source.Effectful.evalValues,
        Target.Expr.openEval, targetPrimitive,
        Locals.Source.Effectful.Expr.Control.eval] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)
  · simp [EvmCompiler.Yul.Expr.toLocals?, hResults] at hLower

theorem var
    (mode : Mode) {results : Nat} {name : EvmYul.Identifier}
    {lower : Locals.Expr results} {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? results (.Var name) = some lower)
    (hRel : StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel source results)
      (Source.evalValues mode (fuel + 1) (.Var name) codeOverride source)
      (Target.Expr.openEval mode lower target) := by
  by_cases hResults : 1 = results
  · cases hResults
    simp [EvmCompiler.Yul.Expr.toLocals?, EvmCompiler.Yul.Expr.cast] at hLower
    subst lower
    cases hLookup : source.lookup? name with
    | none =>
        have hTruncated : Truncated
            ({ exception := .UnknownIdentifier name, state := source } :
              Yul.InteractionSemantics.Failure) := by
          trivial
        simpa [Source.evalValues, Yul.Source.Canonical.evalValues,
          Yul.Source.Effectful.evalValues,
          Yul.Source.Effectful.Control.fail,
          Yul.InteractionSemantics.stateModel, hLookup] using
          (Simulation.Interaction.ForwardRel.truncated
            (doneRel := DoneRel source 1)
            (right := Target.Expr.openEval mode
              (.var (identName name)) target) hTruncated)
    | some value =>
        have hTarget := StateRel.lookup hRel hLookup
        have hDone : DoneRel source 1
            (.ok (source, [value])) (.ok (target, [value])) :=
          .ok (FunctionsInteractionExpression.ResultRel.of_state hRel rfl)
        cases mode <;>
          simpa [Source.evalValues, sourcePrimitive,
            Yul.Source.Canonical.evalValues,
            Yul.Source.Effectful.evalValues,
            Yul.InteractionSemantics.stateModel,
            Target.Expr.openEval, targetPrimitive,
            Locals.Source.Effectful.Expr.Control.eval,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.vars,
            identName, hLookup, hTarget] using
            (Simulation.Interaction.ForwardRel.done
              (truncated := Truncated) hDone)
  · simp [EvmCompiler.Yul.Expr.toLocals?, hResults] at hLower

end Expr

namespace Args

theorem fuel_zero
    (mode : Mode) {results : Nat} (args : List AstExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : Yul.InteractionSemantics.State)
    (seq : Locals.ExprSeq results)
    (target : Functions.InteractionSemantics.State) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel source results)
      (Source.evalArgs mode 0 args codeOverride source)
      (Target.ExprSeq.openEval mode seq target) := by
  have hTruncated : Truncated
      ({ exception := .OutOfFuel, state := source } :
        Yul.InteractionSemantics.Failure) := by
    trivial
  unfold Source.evalArgs Yul.Source.Canonical.evalArgs
  simp only [Yul.Source.Effectful.evalArgs,
    Yul.Source.Effectful.Control.fail]
  exact Simulation.Interaction.ForwardRel.truncated hTruncated

end Args

theorem exprSeq_openEval_seqCast
    (mode : Mode) {left right : Nat} (h : left = right)
    (exprs : Locals.ExprSeq left)
    (state : Functions.InteractionSemantics.State) :
    Target.ExprSeq.openEval mode
        (EvmCompiler.Yul.Expr.seqCast h exprs) state =
      Target.ExprSeq.openEval mode exprs state := by
  cases h
  rfl

def StableValue (mode : Mode) (expr : Locals.Expr 1)
    (base : Functions.InteractionSemantics.State) (value : Word) : Prop :=
  ∀ candidate,
    TargetExtends base.vars candidate.vars →
      Target.Expr.openEval mode expr candidate =
        .done (.ok (candidate, [value]))

inductive StableArgs (mode : Mode) :
    List (Locals.Expr 1) → Functions.InteractionSemantics.State →
      List Word → Prop where
  | nil (base) : StableArgs mode [] base []
  | cons {head rest base value values} :
      StableValue mode head base value →
      StableArgs mode rest base values →
      StableArgs mode (head :: rest) base (value :: values)

namespace StableValue

theorem mono
    {mode : Mode} {expr : Locals.Expr 1}
    {base candidate : Functions.InteractionSemantics.State}
    {value : Word}
    (hStable : StableValue mode expr base value)
    (hExtends : TargetExtends base.vars candidate.vars) :
    StableValue mode expr candidate value := by
  intro final hFinal
  exact hStable final (TargetExtends.trans hExtends hFinal)

theorem lit (mode : Mode) (base : Functions.InteractionSemantics.State)
    (value : Word) : StableValue mode (.lit value) base value := by
  intro candidate _hExtends
  rfl

theorem var
    {mode : Mode} {base : Functions.InteractionSemantics.State}
    {name : Functions.Name} {value : Word}
    (hLookup : base.vars name = some value) :
    StableValue mode (.var name) base value := by
  intro candidate hExtends
  have hCandidate := hExtends name value hLookup
  simp [Target.Expr.openEval,
    Locals.Source.Effectful.Expr.Control.eval,
    Functions.InteractionSemantics.stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.vars, hCandidate,
    Simulation.Interaction.pure]
  rfl

end StableValue

namespace StableArgs

theorem length
    {mode : Mode} {args : List (Locals.Expr 1)}
    {base : Functions.InteractionSemantics.State} {values : List Word}
    (hStable : StableArgs mode args base values) :
    values.length = args.length := by
  induction hStable with
  | nil => rfl
  | cons _hHead _hTail ih => simp [ih]

theorem mono
    {mode : Mode} {args : List (Locals.Expr 1)}
    {base candidate : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs mode args base values)
    (hExtends : TargetExtends base.vars candidate.vars) :
    StableArgs mode args candidate values := by
  induction hStable generalizing candidate with
  | nil => exact .nil candidate
  | cons hHead hTail ih =>
      exact .cons (hHead.mono hExtends) (ih hExtends)

theorem append
    {mode : Mode} {left right : List (Locals.Expr 1)}
    {base : Functions.InteractionSemantics.State}
    {leftValues rightValues : List Word}
    (hLeft : StableArgs mode left base leftValues)
    (hRight : StableArgs mode right base rightValues) :
    StableArgs mode (left ++ right) base (leftValues ++ rightValues) := by
  induction hLeft generalizing right rightValues with
  | nil => simpa using hRight
  | cons hHead hTail ih =>
      simpa using StableArgs.cons hHead (ih hRight)

theorem reverse
    {mode : Mode} {args : List (Locals.Expr 1)}
    {base : Functions.InteractionSemantics.State} {values : List Word}
    (hStable : StableArgs mode args base values) :
    StableArgs mode args.reverse base values.reverse := by
  induction hStable with
  | nil base => simpa using (StableArgs.nil base)
  | @cons head rest base value values hHead hTail ih =>
      simpa [List.reverse_cons] using
        ih.append (StableArgs.cons hHead (.nil base))

theorem openEval
    {mode : Mode} {args : List (Locals.Expr 1)}
    {base candidate : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs mode args base values)
    (hExtends : TargetExtends base.vars candidate.vars) :
    Target.ArgList.openEval mode args candidate =
      .done (.ok (candidate, values)) := by
  induction hStable generalizing candidate with
  | nil => rfl
  | @cons head rest base value values hHead hTail ih =>
      have hHeadEval := hHead candidate hExtends
      have hHeadOne :
          Locals.Source.Effectful.Expr.Control.evalOne
              Functions.InteractionSemantics.stateModel
              (targetPrimitive mode) head candidate =
            .done (.ok (candidate, value)) := by
        unfold Locals.Source.Effectful.Expr.Control.evalOne
        change
          Simulation.Interaction.bind
              (Target.Expr.openEval mode head candidate)
              (fun result =>
                match result.2 with
                | [actual] => pure (result.1, actual)
                | _ => throw EvmYul.EVM.ExecutionException.InvalidInstruction) =
            .done (.ok (candidate, value))
        rw [hHeadEval, Simulation.Interaction.bind_done_ok]
        rfl
      unfold Target.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval
        Functions.Source.Effectful.ArgList.Control.eval
      have hTailEval := ih hExtends
      unfold Target.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval at hTailEval
      change
        Simulation.Interaction.bind
            (Locals.Source.Effectful.Expr.Control.evalOne
              Functions.InteractionSemantics.stateModel
              (targetPrimitive mode) head candidate)
            (fun headResult =>
              Simulation.Interaction.bind
                (Functions.Source.Effectful.ArgList.Control.eval
                  Functions.InteractionSemantics.stateModel
                  (targetPrimitive mode) rest headResult.1)
                (fun tailResult =>
                  pure (tailResult.1,
                    headResult.2 :: tailResult.2))) =
          .done (.ok (candidate, value :: values))
      rw [hHeadOne, Simulation.Interaction.bind_done_ok,
        hTailEval, Simulation.Interaction.bind_done_ok]
      rfl

theorem exprSeq_openEval
    {mode : Mode} {args : List (Locals.Expr 1)} {results : Nat}
    {seq : Locals.ExprSeq results}
    {base candidate : Functions.InteractionSemantics.State}
    {values : List Word}
    (hStable : StableArgs mode args base values)
    (hSeq : EvmCompiler.Yul.Expr.List.toSeq? args results = some seq)
    (hExtends : TargetExtends base.vars candidate.vars) :
    Target.ExprSeq.openEval mode seq candidate =
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
              unfold Target.Expr.openEval at hHeadEval
              unfold Target.ExprSeq.openEval
                Locals.Source.Effectful.Expr.Control.ExprSeq.eval
              have hTailEval := ih hTailSeq hExtends
              unfold Target.ExprSeq.openEval at hTailEval
              change
                Simulation.Interaction.bind
                    (Locals.Source.Effectful.Expr.Control.eval
                      Functions.InteractionSemantics.stateModel
                      (targetPrimitive mode) head candidate)
                    (fun headResult =>
                      Simulation.Interaction.bind
                        (Locals.Source.Effectful.Expr.Control.ExprSeq.eval
                          Functions.InteractionSemantics.stateModel
                          (targetPrimitive mode) tail headResult.1)
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
    (mode : Mode) (hPrimitive : CompilerSelected mode)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) : Prop where
  evalValues :
    ∀ {results : Nat} {expr : AstExpr} {lower : Locals.Expr results}
      {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State},
      EvmCompiler.Yul.Expr.toLocals? results expr = some lower →
      StateRel source target →
      Simulation.Interaction.ForwardRel Truncated (DoneRel source results)
        (Source.evalValues mode fuel expr codeOverride source)
        (Target.Expr.openEval mode lower target)
  evalArgs :
    ∀ {args : List AstExpr} {lower : List (Locals.Expr 1)}
      {results : Nat} {seq : Locals.ExprSeq results}
      {source : Yul.InteractionSemantics.State}
      {target : Functions.InteractionSemantics.State},
      EvmCompiler.Yul.Expr.List.toLocals1? args = some lower →
      EvmCompiler.Yul.Expr.List.toSeq? lower results = some seq →
      StateRel source target →
      Simulation.Interaction.ForwardRel Truncated (DoneRel source results)
        (Source.evalArgs mode fuel args codeOverride source)
        (Target.ExprSeq.openEval mode seq target)

theorem directAt
    (mode : Mode) (hPrimitive : CompilerSelected mode)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) : DirectAt mode hPrimitive codeOverride fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          exact
            { evalValues := by
                intro results expr lower source target hLower _hRel
                exact Expr.fuel_zero mode expr lower codeOverride source target
              evalArgs := by
                intro args lower results seq source target _hLower _hSeq _hRel
                exact Args.fuel_zero mode args codeOverride source seq target }
      | succ previous =>
          have hPrevious : DirectAt mode hPrimitive codeOverride previous :=
            ih previous (Nat.lt_succ_self previous)
          refine { evalValues := ?_, evalArgs := ?_ }
          · intro results expr lower source target hLower hRel
            cases expr with
            | Lit value => exact Expr.lit mode hLower hRel
            | Var name => exact Expr.var mode hLower hRel
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
                                            op) = some seq := by
                                    simpa [EvmCompiler.Yul.Expr.List.toStackSeq?]
                                      using hSeq
                                  have hArgsRel :=
                                    hPrevious.evalArgs hLowerReverse hDirectSeq
                                      hRel
                                  have hPrimitiveRel :=
                                    Expr.primitive_of_args mode hPrimitive
                                      (primitiveFuel := previous)
                                      (Prim.toUncheckedBasicOp?_of_toBasicOp?
                                        hOp)
                                      rfl hArgsRel
                                  simpa [Source.evalValues,
                                    Yul.Source.Canonical.evalValues,
                                    Yul.Source.Effectful.evalValues,
                                    Target.Expr.openEval,
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
                    have hDone : DoneRel source 0
                        (.ok (source, [])) (.ok (target, [])) :=
                      .ok
                        (FunctionsInteractionExpression.ResultRel.of_state
                          hRel rfl)
                    simpa [Source.evalArgs,
                      Yul.Source.Canonical.evalArgs,
                      Yul.Source.Effectful.evalArgs,
                      Target.ExprSeq.openEval,
                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval] using
                      (Simulation.Interaction.ForwardRel.done
                        (truncated := Truncated) hDone)
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
                                      FunctionsInteractionExpression.Args.cons_truncated
                                        (results := tailResults)
                                        (targetTail := fun state =>
                                          Target.ExprSeq.openEval mode
                                            tailSeq state)
                                        hHeadRel
                                    rw [Source.evalArgs_one_cons]
                                    rw [exprSeq_openEval_seqCast]
                                    simpa [Target.ExprSeq.openEval,
                                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
                                      using hCombined
                                | succ tailFuel =>
                                    have hTail :
                                        DirectAt mode hPrimitive codeOverride
                                          tailFuel :=
                                      ih tailFuel (by omega)
                                    have hTailRel : ∀ {source target},
                                        StateRel source target →
                                          Simulation.Interaction.ForwardRel
                                            Truncated
                                            (DoneRel source tailResults)
                                            (Source.evalArgs mode tailFuel rest
                                              codeOverride source)
                                            (Target.ExprSeq.openEval mode
                                              tailSeq target) := by
                                      intro sourceMid targetMid hMid
                                      exact hTail.evalArgs hRestLower hTailSeq hMid
                                    have hCombined :=
                                      FunctionsInteractionExpression.Args.cons
                                        (results := tailResults)
                                        (sourceTail := fun state =>
                                          Source.evalArgs mode tailFuel rest
                                            codeOverride state)
                                        (targetTail := fun state =>
                                          Target.ExprSeq.openEval mode
                                            tailSeq state)
                                        hHeadRel hTailRel
                                    rw [show tailFuel.succ + 1 = tailFuel + 2 by
                                      omega]
                                    rw [Source.evalArgs_succ_succ_cons]
                                    rw [exprSeq_openEval_seqCast]
                                    simpa [Target.ExprSeq.openEval,
                                      Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
                                      using hCombined

theorem compilerDirectAt (mode : Mode)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (fuel : Nat) :
    DirectAt mode (FunctionsInteractionMode.compilerSelected mode)
      codeOverride fuel :=
  directAt mode (FunctionsInteractionMode.compilerSelected mode)
    codeOverride fuel

end FunctionsInteractionExpressionMode
end Yul
end EvmCompiler
