import EvmCompiler.Functions.AllocationInteractionSafeSemantics

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionSafeExpression

open AllocationInteractionRelation

mutual
  /-- Allocation safety indexed by the canonical open semantics. -/
  def ExprSafe (contract : MemoryContract.Contract) {results : Nat}
      (expr : Functions.Expr results)
      (source : Functions.InteractionSemantics.State) : Prop :=
    match expr with
    | .lit _ => True
    | .var name => ∃ value, source.vars name = some value
    | .code _ => False
    | .prim op args =>
        Locals.InteractionSemantics.Primitive.supportsOpen op = true ∧
          ExprSeqSafe contract args source ∧
          Simulation.Interaction.AllDone
            (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
            (Locals.InteractionSemantics.ExprSeq.openEval args source)

  def ExprSeqSafe (contract : MemoryContract.Contract) {results : Nat}
      (exprs : Locals.ExprSeq results)
      (source : Functions.InteractionSemantics.State) : Prop :=
    match exprs with
    | .nil => True
    | .cons head tail =>
        ExprSafe contract head source ∧
          Simulation.Interaction.AllDone
            (fun outcome =>
              match outcome with
              | .error _ => True
              | .ok result => ExprSeqSafe contract tail result.1)
            (Locals.InteractionSemantics.Expr.openEval head source)
end

structure ExprChecked (contract : MemoryContract.Contract) {results : Nat}
    (expr : Functions.Expr results)
    (source : Functions.InteractionSemantics.State) : Prop where
  safety : ExprSafe contract expr source
  ordinary :
    AllocationInteractionSafeSemantics.Expr.openEval contract expr source =
      Locals.Source.Effectful.Expr.Control.eval
        Locals.InteractionSemantics.stateModel
        Locals.InteractionSemantics.primitiveSemantics expr source

structure ExprSeqChecked (contract : MemoryContract.Contract) {results : Nat}
    (exprs : Locals.ExprSeq results)
    (source : Functions.InteractionSemantics.State) : Prop where
  safety : ExprSeqSafe contract exprs source
  ordinary :
    AllocationInteractionSafeSemantics.ExprSeq.openEval contract exprs source =
      Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        Locals.InteractionSemantics.stateModel
        Locals.InteractionSemantics.primitiveSemantics exprs source

structure ConditionChecked (contract : MemoryContract.Contract)
    (expr : Functions.Expr 1)
    (source : Functions.InteractionSemantics.State) : Prop where
  safety : ExprSafe contract expr source
  ordinary :
    AllocationInteractionSafeSemantics.Expr.openEvalCondition
        contract expr source =
      Locals.InteractionSemantics.Expr.openEvalCondition expr source

structure ValueChecked (contract : MemoryContract.Contract)
    (expr : Functions.Expr 1)
    (source : Functions.InteractionSemantics.State) : Prop where
  safety : ExprSafe contract expr source
  ordinary :
    AllocationInteractionSafeSemantics.Expr.openEvalOne contract expr source =
      Locals.InteractionSemantics.Expr.openEvalOne expr source

mutual
  private def checkedExprHeight :
      {results : Nat} → Functions.Expr results → Nat
    | _, .lit _ => 1
    | _, .var _ => 1
    | _, .code _ => 1
    | _, .prim _ args => checkedExprSeqHeight args + 1

  private def checkedExprSeqHeight :
      {results : Nat} → Locals.ExprSeq results → Nat
    | _, .nil => 1
    | _, .cons head tail =>
        checkedExprHeight head + checkedExprSeqHeight tail + 1
end

mutual
  theorem exprChecked_of_successfulFuel
      {contract : MemoryContract.Contract} (fuel : Nat)
      {results : Nat} {live : List Functions.Name}
      {expr : Functions.Expr results}
      {source : Functions.InteractionSemantics.State}
      (hFuel : checkedExprHeight expr ≤ fuel)
      (hScoped : Functions.Scope.ExprScoped live expr)
      (hDefined : LiveDefined live source)
      (hSuccess : Simulation.Interaction.Successful
        (AllocationInteractionSafeSemantics.Expr.openEval
          contract expr source)) :
      ExprChecked contract expr source := by
    cases expr with
    | lit value =>
        exact ⟨True.intro, rfl⟩
    | var name =>
        exact ⟨hDefined name hScoped, rfl⟩
    | code code =>
        exact False.elim hScoped
    | prim op args =>
        unfold AllocationInteractionSafeSemantics.Expr.openEval at hSuccess
        simp only [Locals.Source.Effectful.Expr.Control.eval] at hSuccess
        have hArgsSuccess :=
          Simulation.Interaction.Successful.bind_left hSuccess
        have hArgs := exprSeqChecked_of_successfulFuel (fuel - 1)
          (by simp only [checkedExprHeight] at hFuel; omega)
          hScoped hDefined hArgsSuccess
        have hContinuations :=
          Simulation.Interaction.Successful.bind_inv hSuccess
        have hPrimitiveSafetySafe :
            Simulation.Interaction.AllDone
              (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
              (AllocationInteractionSafeSemantics.ExprSeq.openEval
                contract args source) := by
          apply Simulation.Interaction.AllDone.mono hContinuations
          intro outcome hOutcome
          cases outcome with
          | error error => trivial
          | ok result =>
              exact
                AllocationInteractionSafeSemantics.Primitive.safe_of_successful
                  hOutcome
        have hPrimitiveSafety :
            Simulation.Interaction.AllDone
              (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
              (Locals.InteractionSemantics.ExprSeq.openEval
                args source) := by
          have hSafe := hPrimitiveSafetySafe
          rw [hArgs.ordinary] at hSafe
          exact hSafe
        have hSupports :
            Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
          obtain ⟨outcome, hOutcome⟩ :=
            Simulation.Interaction.AllDone.exists_done hContinuations
          cases outcome with
          | error error => exact False.elim hOutcome
          | ok result =>
              exact
                AllocationInteractionSafeSemantics.Primitive.supportsOpen_of_successful
                  hOutcome
        refine ⟨⟨hSupports, hArgs.safety, hPrimitiveSafety⟩, ?_⟩
        unfold AllocationInteractionSafeSemantics.Expr.openEval
        simp only [Locals.Source.Effectful.Expr.Control.eval]
        have hArgsOrdinary := hArgs.ordinary
        unfold AllocationInteractionSafeSemantics.ExprSeq.openEval
          at hArgsOrdinary
        rw [hArgsOrdinary]
        have hContinuationsOrdinary := hContinuations
        rw [hArgsOrdinary] at hContinuationsOrdinary
        apply Simulation.Interaction.AllDone.bind_congr
          hContinuationsOrdinary
        intro result hResult
        simpa only [AllocationInteractionSafeSemantics.primitiveSemantics,
          Locals.InteractionSemantics.primitiveSemantics] using
          AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
            (AllocationInteractionSafeSemantics.Primitive.safe_of_successful
              hResult)
  termination_by fuel
  decreasing_by
    all_goals
      simp only [checkedExprHeight] at hFuel
      omega

  theorem exprSeqChecked_of_successfulFuel
      {contract : MemoryContract.Contract} (fuel : Nat)
      {results : Nat} {live : List Functions.Name}
      {exprs : Locals.ExprSeq results}
      {source : Functions.InteractionSemantics.State}
      (hFuel : checkedExprSeqHeight exprs ≤ fuel)
      (hScoped : Functions.Scope.ExprSeqScoped live exprs)
      (hDefined : LiveDefined live source)
      (hSuccess : Simulation.Interaction.Successful
        (AllocationInteractionSafeSemantics.ExprSeq.openEval
          contract exprs source)) :
      ExprSeqChecked contract exprs source := by
    cases exprs with
    | nil =>
        exact ⟨True.intro, rfl⟩
    | @cons left right head tail =>
        unfold AllocationInteractionSafeSemantics.ExprSeq.openEval at hSuccess
        simp only [Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
          at hSuccess
        have hHeadSuccess :=
          Simulation.Interaction.Successful.bind_left hSuccess
        have hHead := exprChecked_of_successfulFuel (fuel - 1)
          (by simp only [checkedExprSeqHeight] at hFuel; omega)
          hScoped.1 hDefined hHeadSuccess
        have hContinuations :=
          Simulation.Interaction.Successful.bind_inv hSuccess
        have hVarsSafe :=
          AllocationInteractionSafeSemantics.Expr.openEval_vars_eq
            contract head source
        have hCombinedSafe :=
          Simulation.Interaction.AllDone.inter hContinuations hVarsSafe
        have hHeadOrdinary := hHead.ordinary
        unfold AllocationInteractionSafeSemantics.Expr.openEval
          at hHeadOrdinary
        have hCombined := hCombinedSafe
        rw [hHeadOrdinary] at hCombined
        have hTailSafety :
            Simulation.Interaction.AllDone
              (fun outcome =>
                match outcome with
                | .error _ => True
                | .ok result =>
                    ExprSeqSafe
                      contract tail result.1)
              (Locals.InteractionSemantics.Expr.openEval
                head source) := by
          apply Simulation.Interaction.AllDone.mono hCombined
          intro outcome hOutcome
          cases outcome with
          | error error => trivial
          | ok result =>
              have hTail := exprSeqChecked_of_successfulFuel (fuel - 1)
                (by simp only [checkedExprSeqHeight] at hFuel; omega)
                hScoped.2 (hDefined.congr_vars hOutcome.2)
                (Simulation.Interaction.Successful.bind_left hOutcome.1)
              exact hTail.safety
        refine ⟨⟨hHead.safety, hTailSafety⟩, ?_⟩
        unfold AllocationInteractionSafeSemantics.ExprSeq.openEval
        simp only [Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
        rw [hHeadOrdinary]
        apply Simulation.Interaction.AllDone.bind_congr hCombined
        intro headResult hOutcome
        have hTail := exprSeqChecked_of_successfulFuel (fuel - 1)
          (by simp only [checkedExprSeqHeight] at hFuel; omega)
          hScoped.2 (hDefined.congr_vars hOutcome.2)
          (Simulation.Interaction.Successful.bind_left hOutcome.1)
        have hTailOrdinary := hTail.ordinary
        unfold AllocationInteractionSafeSemantics.ExprSeq.openEval
          at hTailOrdinary
        rw [hTailOrdinary]
  termination_by fuel
  decreasing_by
    all_goals
      simp only [checkedExprSeqHeight] at hFuel
      omega
end

theorem exprChecked_of_successful
    {contract : MemoryContract.Contract} {results : Nat}
    {live : List Functions.Name} {expr : Functions.Expr results}
    {source : Functions.InteractionSemantics.State}
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hDefined : LiveDefined live source)
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Expr.openEval
        contract expr source)) :
    ExprChecked contract expr source :=
  exprChecked_of_successfulFuel (checkedExprHeight expr) (Nat.le_refl _)
    hScoped hDefined hSuccess

theorem conditionChecked_of_successful
    {contract : MemoryContract.Contract}
    {live : List Functions.Name} {expr : Functions.Expr 1}
    {source : Functions.InteractionSemantics.State}
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hDefined : LiveDefined live source)
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Expr.openEvalCondition
        contract expr source)) :
    ConditionChecked contract expr source := by
  have hOneSuccess := Simulation.Interaction.Successful.bind_left hSuccess
  have hEvalSuccess :=
    Simulation.Interaction.Successful.bind_left hOneSuccess
  have hChecked := exprChecked_of_successful hScoped hDefined hEvalSuccess
  refine ⟨hChecked.safety, ?_⟩
  have hEval :
      Locals.Source.Effectful.Expr.Control.eval
          Functions.InteractionSemantics.stateModel
          (AllocationInteractionSafeSemantics.primitiveSemantics contract)
          expr source =
        Locals.Source.Effectful.Expr.Control.eval
          Locals.InteractionSemantics.stateModel
          Locals.InteractionSemantics.primitiveSemantics expr source := by
    simpa [AllocationInteractionSafeSemantics.Expr.openEval] using
      hChecked.ordinary
  unfold AllocationInteractionSafeSemantics.Expr.openEvalCondition
    Locals.InteractionSemantics.Expr.openEvalCondition
    Locals.Source.Effectful.Expr.Control.evalCondition
    Locals.Source.Effectful.Expr.Control.evalOne
  rw [hEval]

theorem valueChecked_of_successful
    {contract : MemoryContract.Contract}
    {live : List Functions.Name} {expr : Functions.Expr 1}
    {source : Functions.InteractionSemantics.State}
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hDefined : LiveDefined live source)
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Expr.openEvalOne
        contract expr source)) :
    ValueChecked contract expr source := by
  have hEvalSuccess := Simulation.Interaction.Successful.bind_left hSuccess
  have hChecked := exprChecked_of_successful hScoped hDefined hEvalSuccess
  refine ⟨hChecked.safety, ?_⟩
  have hEval :
      Locals.Source.Effectful.Expr.Control.eval
          Functions.InteractionSemantics.stateModel
          (AllocationInteractionSafeSemantics.primitiveSemantics contract)
          expr source =
        Locals.Source.Effectful.Expr.Control.eval
          Locals.InteractionSemantics.stateModel
          Locals.InteractionSemantics.primitiveSemantics expr source := by
    simpa [AllocationInteractionSafeSemantics.Expr.openEval] using
      hChecked.ordinary
  unfold AllocationInteractionSafeSemantics.Expr.openEvalOne
    Locals.InteractionSemantics.Expr.openEvalOne
    Locals.Source.Effectful.Expr.Control.evalOne
  rw [hEval]

theorem exprSeqChecked_of_successful
    {contract : MemoryContract.Contract} {results : Nat}
    {live : List Functions.Name} {exprs : Locals.ExprSeq results}
    {source : Functions.InteractionSemantics.State}
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hDefined : LiveDefined live source)
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.ExprSeq.openEval
        contract exprs source)) :
    ExprSeqChecked contract exprs source :=
  exprSeqChecked_of_successfulFuel (checkedExprSeqHeight exprs)
    (Nat.le_refl _) hScoped hDefined hSuccess

end AllocationInteractionSafeExpression
end Functions
end EvmCompiler

