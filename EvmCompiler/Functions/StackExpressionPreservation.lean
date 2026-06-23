import EvmCompiler.Functions.StackRelation
import EvmCompiler.Expressions.TargetFuelSafety

/-!
Expression preservation specialized to the dynamic stack-layout relation.
The primitive/open-world proof remains owned by Locals.
-/

namespace EvmCompiler
namespace Functions
namespace StackExpressionPreservation

open StackRelation
open Assembly.InteractionFuelSafety

theorem openEval_compileCode
    {results : Nat} (expr : Locals.Expr results)
    (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Locals.InteractionPreservation.Expr.OutcomeRel results source target)
      (Locals.InteractionSemantics.Expr.openEval expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  exact
    Locals.InteractionPreservation.Expr.openEval_compileCode
      expr ctx 0 hScoped hSupported hCompile hRel.expr

theorem openEvalZero_compileCode
    (expr : Locals.Expr 0) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        StructuralErrorRel
        (fun sourceResult targetResult =>
          StateRel ctx.layout suffix returns sourceResult.1 targetResult))
      (Locals.InteractionSemantics.Expr.openEval expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  have hBase :=
    openEval_compileCode expr ctx hScoped hSupported hCompile hRel
  have hSafe :=
    Structured.InteractionFuelSafety.Code.openRun code target
  apply Simulation.Interaction.Rel.mono
    (NotOutOfFuel.refineExceptRel hBase hSafe)
  intro sourceResult targetResult hResult
  cases hResult with
  | error hError => exact .error hError
  | ok hOk => exact .ok (hRel.ofExprResultZero hOk)

theorem openEvalOne_compileCode
    (expr : Locals.Expr 1) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Locals.InteractionPreservation.Expr.OneOutcomeRel source target)
      (Locals.InteractionSemantics.Expr.openEvalOne expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  exact
    Locals.InteractionPreservation.Expr.openEvalOne_compileCode
      expr ctx 0 hScoped hSupported hCompile hRel.expr

structure OnePoppedResultRel
    (layout : Locals.Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (source : Locals.Source.State × Word)
    (target : Structured.RunState × Word) : Prop where
  value : source.2 = target.2
  state : StateRel layout suffix returns source.1 target.1

abbrev OnePoppedOutcomeRel
    (layout : Locals.Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    StructuralErrorRel
    (OnePoppedResultRel layout suffix returns)

theorem openEvalOnePop_compileCode
    (expr : Locals.Expr 1) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hInitial : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OnePoppedOutcomeRel ctx.layout suffix returns)
      (Locals.InteractionSemantics.Expr.openEvalOne expr source)
      (Expressions.InteractionSemantics.Expr.openRunOne (.code code) target) := by
  have hOne :=
    openEvalOne_compileCode expr ctx hScoped hSupported hCompile hInitial
  have hOneSafe :=
    NotOutOfFuel.refineExceptRel hOne
      (Structured.InteractionFuelSafety.Code.openRun code target)
  unfold Expressions.InteractionSemantics.Expr.openRunOne
  rw [← Simulation.Interaction.bind_pure
    (Locals.InteractionSemantics.Expr.openEvalOne expr source)]
  apply Simulation.Interaction.Rel.bind hOneSafe
  intro sourceResult targetAfterExpr hResult
  rcases sourceResult with ⟨sourceFinal, value⟩
  let targetFinal :=
    targetAfterExpr.withEVM
      { targetAfterExpr.evm with stack := target.evm.stack }
  have hTargetStack :
      targetAfterExpr.evm.stack = value :: target.evm.stack := by
    simpa using hResult.stack
  have hPop : targetAfterExpr.evm.stack.pop =
      some (target.evm.stack, value) := by
    rw [hTargetStack]
    rfl
  rw [hPop]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    { value := rfl
      state := StateRel.ofExprResultOnePop hInitial hResult }

structure ConditionResultRel
    (layout : Locals.Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (source : Locals.Source.State × Bool)
    (target : Structured.RunState × Bool) : Prop where
  condition : source.2 = target.2
  state : StateRel layout suffix returns source.1 target.1

abbrev ConditionOutcomeRel
    (layout : Locals.Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    StructuralErrorRel
    (ConditionResultRel layout suffix returns)

theorem openEvalCondition_compileCode
    (expr : Locals.Expr 1) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hInitial : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (ConditionOutcomeRel ctx.layout suffix returns)
      (Locals.InteractionSemantics.Expr.openEvalCondition expr source)
      (Expressions.InteractionSemantics.Expr.openRunCondition (.code code) target) := by
  have hOne :=
    openEvalOne_compileCode expr ctx hScoped hSupported hCompile hInitial
  have hOneSafe :=
    NotOutOfFuel.refineExceptRel hOne
      (Structured.InteractionFuelSafety.Code.openRun code target)
  unfold Locals.InteractionSemantics.Expr.openEvalCondition
    Locals.Source.Effectful.Expr.Control.evalCondition
  unfold Expressions.InteractionSemantics.Expr.openRunCondition
    Expressions.EffectSemantics.Control.Expr.runCondition
    Expressions.EffectSemantics.Control.Expr.run
  apply Simulation.Interaction.Rel.bind hOneSafe
  intro sourceResult targetAfterExpr hResult
  rcases sourceResult with ⟨sourceFinal, value⟩
  let targetFinal :=
    targetAfterExpr.withEVM
      { targetAfterExpr.evm with stack := target.evm.stack }
  have hTargetStack :
      targetAfterExpr.evm.stack = value :: target.evm.stack := by
    simpa using hResult.stack
  have hPop :
      Structured.EffectSemantics.Control.Code.popCondition
          (M := Simulation.Interaction EVMException)
          Structured.EffectSemantics.Ordinary.runStateModel targetAfterExpr =
        Simulation.Interaction.pure
          (targetFinal, value != EvmYul.UInt256.ofNat 0) := by
    unfold Structured.EffectSemantics.Control.Code.popCondition
    rw [Structured.EffectSemantics.Ordinary.runStateModel_evm, hTargetStack]
    rfl
  rw [hPop]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    { condition := rfl
      state := StateRel.ofExprResultOnePop hInitial hResult }

theorem openEvalOne_fresh_compileCode
    (expr : Locals.Expr 1) (ctx : Locals.Ctx) (name : Name)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hFresh : name ∉ ctx.layout)
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        StructuralErrorRel
        (fun sourceResult targetResult =>
          StateRel (name :: ctx.layout) suffix returns
            (sourceResult.1.insert name sourceResult.2) targetResult))
      (Locals.InteractionSemantics.Expr.openEvalOne expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  have hBase :=
    Locals.InteractionPreservation.Expr.openEvalOne_compileCode
      expr ctx 0 hScoped hSupported hCompile hRel.expr
  have hSafe :=
    Structured.InteractionFuelSafety.Code.openRun code target
  apply Simulation.Interaction.Rel.mono
    (NotOutOfFuel.refineExceptRel hBase hSafe)
  intro sourceResult targetResult hResult
  cases hResult with
  | error hError => exact .error hError
  | ok hOk => exact .ok (hRel.ofExprResultOneInsert hFresh hOk)

theorem openEvalSeq_compileCode
    {results : Nat} (exprs : Locals.ExprSeq results)
    (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprSeqScoped ctx.layout exprs)
    (hSupported : Locals.InteractionSemantics.ExprSeq.OpenSupported exprs)
    (hCompile : Locals.ExprSeq.compileCode ctx 0 exprs = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Locals.InteractionPreservation.Expr.OutcomeRel results source target)
      (Locals.InteractionSemantics.ExprSeq.openEval exprs source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  exact
    Locals.InteractionPreservation.Expr.openEvalSeq_compileCode
      exprs ctx 0 hScoped hSupported hCompile hRel.expr

end StackExpressionPreservation
end Functions
end EvmCompiler
