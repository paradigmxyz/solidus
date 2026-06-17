import EvmCompiler.Functions.AllocationObserverProgram
import EvmCompiler.Yul.FunctionsObserverPreservation
import EvmCompiler.Yul.FunctionsObserverTraceAdequacy

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverResourceSafety

/-!
Source-facing resource safety for the adjacent Yul-to-Functions boundary.

The public premise is computed from the Yul program and its memory contract.
It contains no allocation plan, emitted code, artifact certificate, or target
execution evidence. The three-word budget margin covers the selected main
setup frame, the Functions run itself, and the strict `FuelSafe` successor.
-/

abbrev Trace := Assembly.ResourceTrace

noncomputable def executionBudget
    (program : Yul.Program) (sourceFuel : Nat) : Nat :=
  FunctionsObserverFuel.executionBudgetFor
    (FunctionsObserverStaticCost.program program)
    (FunctionsObserverStaticCost.program program)
    sourceFuel

noncomputable def requiredFrameWords? (program : Yul.Program) :
    Option Nat := do
  let targetProgram ← Program.toObjectsWithObservers? program
  let recipe ←
    Functions.AllocationSupport.planRecipeCore?
      targetProgram.toFunctions
  some recipe.frameWords

noncomputable def SourceReservationSafe
    (program : Yul.Program) (sourceFuel : Nat) : Prop :=
  match program.memoryContract.scratch? with
  | none => True
  | some reservation =>
      match requiredFrameWords? program with
      | none => False
      | some frameWords =>
          (executionBudget program sourceFuel + 3) * frameWords ≤
            reservation.usableWords

noncomputable def SourceExecutionResourceSafe
    (program : Yul.Program) (source : EvmYul.Yul.State)
    (transcript : Trace) : Prop :=
  ∃ result : ObserverSemantics.SourceReplay.Result transcript,
    ∃ sourceFuel,
      ObserverSafety.SafeSemantics.Program.run
          program.memoryContract sourceFuel program source transcript =
        .ok result ∧
      result.state.cursor ≤ transcript.length ∧
      SourceReservationSafe program sourceFuel

theorem SourceExecutionResourceSafe.executionSafe
    {program : Yul.Program} {source : EvmYul.Yul.State}
    {transcript : Trace}
    (hSafe : SourceExecutionResourceSafe program source transcript) :
    FunctionsObserverTraceAdequacy.SourceExecutionSafe
      program source transcript := by
  rcases hSafe with
    ⟨result, sourceFuel, hRun, hCursor, _hReservation⟩
  exact ⟨result, sourceFuel, hRun, hCursor⟩

theorem SourceReservationSafe.selectedFuelSafe
    {program : Yul.Program}
    {targetProgram : Objects.Program}
    {allocation : Locals.Allocation.ProgramPlan}
    {sourceFuel targetFuel : Nat}
    (hLower :
      Program.toObjectsWithObservers? program = some targetProgram)
    (hSafe : SourceReservationSafe program sourceFuel)
    (hTargetFuel :
      targetFuel ≤ executionBudget program sourceFuel) :
    (Functions.AllocationObserverProgram.selectedResourceMode
        allocation targetProgram.toFunctions).FuelSafe
      (Functions.AllocationObserverProgram.selectedMainSetupDepth
          allocation targetProgram.toFunctions +
        (targetFuel + 1)) := by
  have hContract :
      targetProgram.toFunctions.memoryContract =
        program.memoryContract :=
    FunctionsObserverCompiler.memoryContract_of_toObjectsWithObservers?
      hLower
  cases hScratch : program.memoryContract.scratch? with
  | none =>
      apply
        Functions.AllocationObserverProgram.selectedResourceMode_fuelSafe_of_no_scratch
      simpa [hContract] using hScratch
  | some reservation =>
      cases hRecipe :
          Functions.AllocationSupport.planRecipeCore?
            targetProgram.toFunctions with
      | none =>
          simp [SourceReservationSafe, requiredFrameWords?,
            hScratch, hLower, hRecipe] at hSafe
      | some recipe =>
          have hReservation :
              targetProgram.toFunctions.memoryContract.scratch? =
                some reservation := by
            simpa [hContract] using hScratch
          have hCapacity :
              (executionBudget program sourceFuel + 3) *
                  recipe.frameWords ≤
                reservation.usableWords := by
            simpa [SourceReservationSafe, requiredFrameWords?,
              hScratch, hLower, hRecipe] using hSafe
          apply
            Functions.AllocationObserverProgram.selectedResourceMode_fuelSafe_of_recipe_capacity
              hRecipe hReservation
          apply Nat.le_trans _ hCapacity
          apply Nat.mul_le_mul_right recipe.frameWords
          have hSetup :
              Functions.AllocationObserverProgram.selectedMainSetupDepth
                  allocation targetProgram.toFunctions ≤
                1 :=
            Functions.AllocationObserverProgram.selectedMainSetupDepth_le_one
              allocation targetProgram.toFunctions
          omega

end FunctionsObserverResourceSafety
end Yul
end EvmCompiler
