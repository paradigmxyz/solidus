import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionFuel

/-!
Source-facing target-fuel accounting for the adjacent Yul-to-Functions pass.

One Yul source step may expand into many Functions steps, and an internal call
may enter a much larger function body. `targetBudgetFor` therefore carries a
whole-program static bound while decreasing only with canonical source fuel.
It is proof accounting, not a second evaluator or compiler artifact.
-/

def targetBudgetFor (globalCost : Nat) : Nat → Nat
  | 0 => 16
  | fuel + 1 =>
      16 * ((globalCost + 1) * targetBudgetFor globalCost fuel + 1)

def executionBudgetFor
    (globalCost localCost sourceFuel : Nat) : Nat :=
  (localCost + 1) * targetBudgetFor globalCost sourceFuel

theorem targetBudgetFor_ge_sixteen
    (globalCost sourceFuel : Nat) :
    16 ≤ targetBudgetFor globalCost sourceFuel := by
  induction sourceFuel with
  | zero =>
      simp [targetBudgetFor]
  | succ sourceFuel ih =>
      simp only [targetBudgetFor]
      omega

theorem targetBudgetFor_step_le
    (globalCost sourceFuel : Nat) :
    targetBudgetFor globalCost sourceFuel ≤
      targetBudgetFor globalCost (sourceFuel + 1) := by
  have hPositive := targetBudgetFor_ge_sixteen globalCost sourceFuel
  simp only [targetBudgetFor]
  nlinarith

theorem targetBudgetFor_mono
    (globalCost : Nat) {left right : Nat}
    (hLe : left ≤ right) :
    targetBudgetFor globalCost left ≤
      targetBudgetFor globalCost right := by
  induction right generalizing left with
  | zero =>
      have hLeft : left = 0 := by omega
      subst left
      rfl
  | succ right ih =>
      by_cases hEq : left = right + 1
      · subst left
        rfl
      · exact
          le_trans (ih (by omega))
            (targetBudgetFor_step_le globalCost right)

theorem executionBudgetFor_ge_sixteen
    (globalCost localCost sourceFuel : Nat) :
    16 ≤ executionBudgetFor globalCost localCost sourceFuel := by
  have hTarget := targetBudgetFor_ge_sixteen globalCost sourceFuel
  simp only [executionBudgetFor]
  nlinarith

theorem executionBudgetFor_mono
    (globalCost localCost : Nat) {left right : Nat}
    (hLe : left ≤ right) :
    executionBudgetFor globalCost localCost left ≤
      executionBudgetFor globalCost localCost right := by
  exact Nat.mul_le_mul_left _ (targetBudgetFor_mono globalCost hLe)

theorem executionBudgetFor_local_mono
    (globalCost sourceFuel : Nat)
    {left right : Nat} (hLe : left ≤ right) :
    executionBudgetFor globalCost left sourceFuel ≤
      executionBudgetFor globalCost right sourceFuel := by
  exact Nat.mul_le_mul_right (targetBudgetFor globalCost sourceFuel) (by omega)

theorem executionBudgetFor_le_global_at
    (globalCost : Nat) {localCost childFuel parentFuel : Nat}
    (hCost : localCost ≤ globalCost)
    (hFuel : childFuel ≤ parentFuel) :
    executionBudgetFor globalCost localCost childFuel ≤
      executionBudgetFor globalCost globalCost parentFuel := by
  exact
    (executionBudgetFor_mono globalCost localCost hFuel).trans
      (executionBudgetFor_local_mono globalCost parentFuel hCost)

theorem eight_executionBudgetsFor_add_eight_le_target_of_lt
    (globalCost childCost : Nat)
    {childFuel parentFuel : Nat}
    (hCost : childCost ≤ globalCost)
    (hFuel : childFuel < parentFuel) :
    8 * executionBudgetFor globalCost childCost childFuel + 8 ≤
      targetBudgetFor globalCost parentFuel := by
  cases parentFuel with
  | zero =>
      omega
  | succ parentFuel =>
      have hChildFuel : childFuel ≤ parentFuel := by omega
      have hDynamic := targetBudgetFor_mono globalCost hChildFuel
      have hStatic : childCost + 1 ≤ globalCost + 1 := by omega
      have hScaled := Nat.mul_le_mul hStatic hDynamic
      simp only [executionBudgetFor, targetBudgetFor]
      simp only [executionBudgetFor] at hScaled
      nlinarith

theorem executionBudgetFor_add_eight_le_target_of_lt
    (globalCost childCost : Nat)
    {childFuel parentFuel : Nat}
    (hCost : childCost ≤ globalCost)
    (hFuel : childFuel < parentFuel) :
    executionBudgetFor globalCost childCost childFuel + 8 ≤
      targetBudgetFor globalCost parentFuel := by
  have hMain :=
    eight_executionBudgetsFor_add_eight_le_target_of_lt
      globalCost childCost hCost hFuel
  have hPositive :=
    executionBudgetFor_ge_sixteen globalCost childCost childFuel
  omega

theorem targetBudgetFor_le_executionBudgetFor
    (globalCost localCost sourceFuel : Nat) :
    targetBudgetFor globalCost sourceFuel ≤
      executionBudgetFor globalCost localCost sourceFuel := by
  have hPositive := targetBudgetFor_ge_sixteen globalCost sourceFuel
  simp only [executionBudgetFor]
  nlinarith

theorem executionBudgetFor_add_local
    (globalCost left right sourceFuel : Nat) :
    executionBudgetFor globalCost left sourceFuel +
        executionBudgetFor globalCost right sourceFuel =
      executionBudgetFor globalCost (left + right + 1) sourceFuel := by
  simp [executionBudgetFor, Nat.add_mul, two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem two_executionBudgetsFor_add_eight_le_target_of_lt
    (globalCost leftCost rightCost : Nat)
    {leftFuel rightFuel parentFuel : Nat}
    (hLeftCost : leftCost ≤ globalCost)
    (hRightCost : rightCost ≤ globalCost)
    (hLeftFuel : leftFuel < parentFuel)
    (hRightFuel : rightFuel < parentFuel) :
    executionBudgetFor globalCost leftCost leftFuel +
        executionBudgetFor globalCost rightCost rightFuel + 8 ≤
      targetBudgetFor globalCost parentFuel := by
  cases parentFuel with
  | zero => omega
  | succ parentFuel =>
      have hLeftFuelLe : leftFuel ≤ parentFuel := by omega
      have hRightFuelLe : rightFuel ≤ parentFuel := by omega
      have hLeftDynamic :=
        targetBudgetFor_mono globalCost hLeftFuelLe
      have hRightDynamic :=
        targetBudgetFor_mono globalCost hRightFuelLe
      have hLeftStatic : leftCost + 1 ≤ globalCost + 1 := by omega
      have hRightStatic : rightCost + 1 ≤ globalCost + 1 := by omega
      have hLeftScaled := Nat.mul_le_mul hLeftStatic hLeftDynamic
      have hRightScaled := Nat.mul_le_mul hRightStatic hRightDynamic
      simp only [executionBudgetFor, targetBudgetFor]
      simp only [executionBudgetFor] at hLeftScaled hRightScaled
      nlinarith

theorem executionBudgetFor_child_add_eight_le
    (globalCost parentLocal childCost : Nat)
    {childFuel parentFuel : Nat}
    (hCost : childCost ≤ globalCost)
    (hFuel : childFuel < parentFuel) :
    executionBudgetFor globalCost parentLocal parentFuel +
        executionBudgetFor globalCost childCost childFuel + 8 ≤
      executionBudgetFor globalCost (parentLocal + 1) parentFuel := by
  have hChild :=
    executionBudgetFor_add_eight_le_target_of_lt
      globalCost childCost hCost hFuel
  calc
    executionBudgetFor globalCost parentLocal parentFuel +
          executionBudgetFor globalCost childCost childFuel + 8 ≤
        executionBudgetFor globalCost parentLocal parentFuel +
          targetBudgetFor globalCost parentFuel := by omega
    _ = executionBudgetFor globalCost (parentLocal + 1) parentFuel := by
      simpa [executionBudgetFor] using
        executionBudgetFor_add_local globalCost parentLocal 0 parentFuel

theorem executionBudgetFor_two_children_add_eight_le
    (globalCost parentLocal leftCost rightCost : Nat)
    {leftFuel rightFuel parentFuel : Nat}
    (hLeftCost : leftCost ≤ globalCost)
    (hRightCost : rightCost ≤ globalCost)
    (hLeftFuel : leftFuel < parentFuel)
    (hRightFuel : rightFuel < parentFuel) :
    executionBudgetFor globalCost parentLocal parentFuel +
        executionBudgetFor globalCost leftCost leftFuel +
        executionBudgetFor globalCost rightCost rightFuel + 8 ≤
      executionBudgetFor globalCost (parentLocal + 1) parentFuel := by
  have hChildren :=
    two_executionBudgetsFor_add_eight_le_target_of_lt
      globalCost leftCost rightCost
      hLeftCost hRightCost hLeftFuel hRightFuel
  calc
    executionBudgetFor globalCost parentLocal parentFuel +
          executionBudgetFor globalCost leftCost leftFuel +
          executionBudgetFor globalCost rightCost rightFuel + 8 ≤
        executionBudgetFor globalCost parentLocal parentFuel +
          targetBudgetFor globalCost parentFuel := by omega
    _ = executionBudgetFor globalCost (parentLocal + 1) parentFuel := by
      simpa [executionBudgetFor] using
        executionBudgetFor_add_local globalCost parentLocal 0 parentFuel

end FunctionsInteractionFuel
end Yul
end EvmCompiler
