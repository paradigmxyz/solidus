import EvmCompiler.Functions.AllocationInteractionPrimitive
import EvmCompiler.Functions.AllocationInteractionSafeExpression
import EvmCompiler.Functions.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionSafety

abbrev SourceState := AllocationInteractionRelation.SourceState
abbrev Word := Assembly.Word

/-- Canonical local allocation-safety predicates. Their proofs are derived
from successful guarded execution, rather than from the legacy global oracle. -/
abbrev ExprSafe := AllocationInteractionSafeExpression.ExprSafe
abbrev ExprSeqSafe := AllocationInteractionSafeExpression.ExprSeqSafe

/-- Source-facing safety for canonical left-to-right call arguments. -/
def ArgListSafe (contract : MemoryContract.Contract) :
    List (Functions.Expr 1) → SourceState → Prop
  | [], _source => True
  | arg :: rest, source =>
      ExprSafe contract arg source ∧
        Simulation.Interaction.AllDone
          (fun outcome =>
            match outcome with
            | .error _ => True
            | .ok result => ArgListSafe contract rest result.1)
          (Functions.InteractionSemantics.Expr.openEvalOne arg source)

/-- Reached guarded argument evaluation supplies exactly the local safety
needed by call lowering. No unrelated expression or state is quantified. -/
theorem argList_of_successful
    {contract : MemoryContract.Contract} :
    ∀ {live : List Functions.Name} {args : List (Functions.Expr 1)}
      {source : SourceState},
      (∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg) →
      AllocationInteractionRelation.LiveDefined live source →
      Simulation.Interaction.Successful
        (AllocationInteractionSafeSemantics.ArgList.openEval
          contract args source) →
      ArgListSafe contract args source := by
  intro live args
  induction args with
  | nil =>
      intro source _hScoped _hDefined _hSuccess
      trivial
  | cons arg rest ih =>
      intro source hScoped hDefined hSuccess
      unfold AllocationInteractionSafeSemantics.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval
        Functions.Source.Effectful.ArgList.Control.eval at hSuccess
      have hHeadSuccess := Simulation.Interaction.Successful.bind_left hSuccess
      have hChecked :=
        AllocationInteractionSafeExpression.valueChecked_of_successful
          (hScoped arg (by simp)) hDefined hHeadSuccess
      refine ⟨hChecked.safety, ?_⟩
      have hContinuations :=
        Simulation.Interaction.Successful.bind_inv hSuccess
      have hVars :=
        AllocationInteractionSafeSemantics.Expr.openEvalOne_vars_eq
          contract arg source
      change Simulation.Interaction.AllDone _
        (Locals.InteractionSemantics.Expr.openEvalOne arg source)
      rw [← hChecked.ordinary]
      apply Simulation.Interaction.AllDone.mono
        (Simulation.Interaction.AllDone.inter hContinuations hVars)
      intro outcome hOutcome
      cases outcome with
      | error _ => trivial
      | ok result =>
          rcases result with ⟨afterArg, value⟩
          have hRestSuccessRaw :=
            Simulation.Interaction.Successful.bind_left hOutcome.1
          have hRestSuccess :
              Simulation.Interaction.Successful
                (AllocationInteractionSafeSemantics.ArgList.openEval
                  contract rest afterArg) := by
            simpa [AllocationInteractionSafeSemantics.ArgList.openEval,
              Functions.Source.Canonical.ArgList.eval] using hRestSuccessRaw
          exact
            ih (fun expr hMem => hScoped expr (by simp [hMem]))
              (hDefined.congr_vars hOutcome.2) hRestSuccess

end AllocationInteractionSafety
end Functions
end EvmCompiler
