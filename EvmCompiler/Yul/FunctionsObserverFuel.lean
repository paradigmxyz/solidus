import EvmCompiler.Yul.FunctionsObserverExpression
import EvmCompiler.Yul.FunctionsObserverOutcome

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverFuel

/-!
Quantitative interface for the adjacent Yul-to-Functions observer pass.

The existing forward simulation chooses sufficient target fuel existentially.
`targetBudget` amplifies dynamic source fuel across strictly smaller recursive
runs. `executionBudget` also carries a source-derived static expansion factor:
one Yul step can emit an unbounded number of Functions statements as source
syntax grows, for example a multi-name declaration. Pass-owned preservation
theorems must account for both dimensions without changing either canonical
semantics.
-/

def targetBudget : Nat → Nat
  | 0 => 16
  | fuel + 1 => 16 * (targetBudget fuel + 1)

theorem targetBudget_ge_sixteen (fuel : Nat) :
    16 ≤ targetBudget fuel := by
  induction fuel with
  | zero =>
      simp [targetBudget]
  | succ fuel ih =>
      simp only [targetBudget]
      omega

def executionBudget (staticCost sourceFuel : Nat) : Nat :=
  (staticCost + 1) * targetBudget sourceFuel

/--
Program-indexed dynamic amplification.

The `globalCost` parameter bounds the local static cost of every construct that
can be reached through a recursive source evaluation. This lets one source-fuel
level absorb recursive calls whose bodies are much larger than the call site,
without charging the callee body to the call expression's local syntax cost.
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
  have hPositive :=
    targetBudgetFor_ge_sixteen globalCost sourceFuel
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
          le_trans
            (ih (by omega))
            (targetBudgetFor_step_le globalCost right)

theorem executionBudgetFor_ge_sixteen
    (globalCost localCost sourceFuel : Nat) :
    16 ≤ executionBudgetFor globalCost localCost sourceFuel := by
  have hTarget :=
    targetBudgetFor_ge_sixteen globalCost sourceFuel
  simp only [executionBudgetFor]
  nlinarith

theorem targetBudgetFor_le_executionBudgetFor
    (globalCost localCost sourceFuel : Nat) :
    targetBudgetFor globalCost sourceFuel ≤
      executionBudgetFor globalCost localCost sourceFuel := by
  have hPositive :=
    targetBudgetFor_ge_sixteen globalCost sourceFuel
  simp only [executionBudgetFor]
  nlinarith

theorem localCost_le_executionBudgetFor
    (globalCost localCost sourceFuel : Nat) :
    localCost ≤ executionBudgetFor globalCost localCost sourceFuel := by
  have hTarget :=
    targetBudgetFor_ge_sixteen globalCost sourceFuel
  simp only [executionBudgetFor]
  nlinarith

theorem targetBudgetFor_add_localCost_le_executionBudgetFor
    (globalCost localCost sourceFuel : Nat) :
    targetBudgetFor globalCost sourceFuel + localCost ≤
      executionBudgetFor globalCost localCost sourceFuel := by
  have hTarget :=
    targetBudgetFor_ge_sixteen globalCost sourceFuel
  simp only [executionBudgetFor]
  nlinarith

theorem executionBudgetFor_mono
    (globalCost localCost : Nat) {left right : Nat}
    (hLe : left ≤ right) :
    executionBudgetFor globalCost localCost left ≤
      executionBudgetFor globalCost localCost right := by
  exact
    Nat.mul_le_mul_left _
      (targetBudgetFor_mono globalCost hLe)

theorem executionBudgetFor_local_mono
    (globalCost sourceFuel : Nat)
    {left right : Nat} (hLe : left ≤ right) :
    executionBudgetFor globalCost left sourceFuel ≤
      executionBudgetFor globalCost right sourceFuel := by
  exact
    Nat.mul_le_mul_right
      (targetBudgetFor globalCost sourceFuel) (by omega)

theorem executionBudgetFor_add_local
    (globalCost left right sourceFuel : Nat) :
    executionBudgetFor globalCost left sourceFuel +
        executionBudgetFor globalCost right sourceFuel =
      executionBudgetFor globalCost (left + right + 1) sourceFuel := by
  simp [executionBudgetFor, Nat.add_mul, two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem executionBudgetFor_add_one_local
    (globalCost localCost sourceFuel : Nat) :
    executionBudgetFor globalCost (localCost + 1) sourceFuel =
      executionBudgetFor globalCost localCost sourceFuel +
        targetBudgetFor globalCost sourceFuel := by
  simp [executionBudgetFor, Nat.add_mul, two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

/--
A source-fuel step absorbs up to eight recursive child executions, even when
each child's local static cost is as large as the whole program.
-/
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
      have hDynamic :=
        targetBudgetFor_mono globalCost hChildFuel
      have hStatic : childCost + 1 ≤ globalCost + 1 := by omega
      have hScaled :=
        Nat.mul_le_mul hStatic hDynamic
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
    executionBudgetFor_ge_sixteen
      globalCost childCost childFuel
  omega

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
  | zero =>
      omega
  | succ parentFuel =>
      have hLeftFuelLe : leftFuel ≤ parentFuel := by omega
      have hRightFuelLe : rightFuel ≤ parentFuel := by omega
      have hLeftDynamic :=
        targetBudgetFor_mono globalCost hLeftFuelLe
      have hRightDynamic :=
        targetBudgetFor_mono globalCost hRightFuelLe
      have hLeftStatic : leftCost + 1 ≤ globalCost + 1 := by omega
      have hRightStatic : rightCost + 1 ≤ globalCost + 1 := by omega
      have hLeftScaled :=
        Nat.mul_le_mul hLeftStatic hLeftDynamic
      have hRightScaled :=
        Nat.mul_le_mul hRightStatic hRightDynamic
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
          targetBudgetFor globalCost parentFuel := by
      omega
    _ = executionBudgetFor globalCost (parentLocal + 1) parentFuel := by
      simpa [executionBudgetFor] using
        executionBudgetFor_add_local
          globalCost parentLocal 0 parentFuel

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
          targetBudgetFor globalCost parentFuel := by
      omega
    _ = executionBudgetFor globalCost (parentLocal + 1) parentFuel := by
      simpa [executionBudgetFor] using
        executionBudgetFor_add_local
          globalCost parentLocal 0 parentFuel

theorem targetBudget_le_targetBudgetFor
    (globalCost sourceFuel : Nat) :
    targetBudget sourceFuel ≤
      targetBudgetFor globalCost sourceFuel := by
  induction sourceFuel with
  | zero =>
      rfl
  | succ sourceFuel ih =>
      have hPositive :=
        targetBudgetFor_ge_sixteen globalCost sourceFuel
      simp only [targetBudget, targetBudgetFor]
      nlinarith

theorem executionBudget_le_executionBudgetFor
    (globalCost localCost sourceFuel : Nat) :
    executionBudget localCost sourceFuel ≤
      executionBudgetFor globalCost localCost sourceFuel := by
  exact
    Nat.mul_le_mul_left _
      (targetBudget_le_targetBudgetFor globalCost sourceFuel)

theorem targetBudget_mono {left right : Nat}
    (hLe : left ≤ right) :
    targetBudget left ≤ targetBudget right := by
  induction right generalizing left with
  | zero =>
      have hLeft : left = 0 := by omega
      subst left
      rfl
  | succ right ih =>
      by_cases hEq : left = right + 1
      · subst left
        rfl
      · have hLeft : left ≤ right := by omega
        have hRec := ih hLeft
        simp only [targetBudget]
        omega

/--
One target-fuel level absorbs up to eight recursive child budgets and eight
units of compiler-owned wrapper overhead.
-/
theorem eight_mul_add_eight_le_of_lt
    {child parent : Nat} (hLt : child < parent) :
    8 * targetBudget child + 8 ≤ targetBudget parent := by
  cases parent with
  | zero =>
      omega
  | succ parent =>
      have hChild : child ≤ parent := by omega
      have hMono := targetBudget_mono hChild
      have hPositive := targetBudget_ge_sixteen parent
      simp only [targetBudget]
      omega

theorem child_add_eight_le_of_lt
    {child parent : Nat} (hLt : child < parent) :
    targetBudget child + 8 ≤ targetBudget parent := by
  have hMain := eight_mul_add_eight_le_of_lt hLt
  have hPositive := targetBudget_ge_sixteen child
  omega

theorem two_children_add_eight_le_of_lt
    {left right parent : Nat}
    (hLeft : left < parent) (hRight : right < parent) :
    targetBudget left + targetBudget right + 8 ≤
      targetBudget parent := by
  cases parent with
  | zero =>
      omega
  | succ parent =>
      have hLeftLe : left ≤ parent := by omega
      have hRightLe : right ≤ parent := by omega
      have hLeftMono := targetBudget_mono hLeftLe
      have hRightMono := targetBudget_mono hRightLe
      have hPositive := targetBudget_ge_sixteen parent
      simp only [targetBudget]
      omega

theorem three_children_add_eight_le_of_lt
    {first second third parent : Nat}
    (hFirst : first < parent)
    (hSecond : second < parent)
    (hThird : third < parent) :
    targetBudget first + targetBudget second +
        targetBudget third + 8 ≤
      targetBudget parent := by
  cases parent with
  | zero =>
      omega
  | succ parent =>
      have hFirstLe : first ≤ parent := by omega
      have hSecondLe : second ≤ parent := by omega
      have hThirdLe : third ≤ parent := by omega
      have hFirstMono := targetBudget_mono hFirstLe
      have hSecondMono := targetBudget_mono hSecondLe
      have hThirdMono := targetBudget_mono hThirdLe
      have hPositive := targetBudget_ge_sixteen parent
      simp only [targetBudget]
      omega

theorem targetBudget_le_executionBudget
    (staticCost sourceFuel : Nat) :
    targetBudget sourceFuel ≤ executionBudget staticCost sourceFuel := by
  have hPositive := targetBudget_ge_sixteen sourceFuel
  simp only [executionBudget]
  nlinarith

theorem executionBudget_ge_sixteen
    (staticCost sourceFuel : Nat) :
    16 ≤ executionBudget staticCost sourceFuel := by
  exact
    le_trans (targetBudget_ge_sixteen sourceFuel)
      (targetBudget_le_executionBudget staticCost sourceFuel)

theorem staticCost_le_executionBudget
    (staticCost sourceFuel : Nat) :
    staticCost ≤ executionBudget staticCost sourceFuel := by
  have hPositive := targetBudget_ge_sixteen sourceFuel
  simp only [executionBudget]
  nlinarith

theorem executionBudget_mono
    (staticCost : Nat) {left right : Nat}
    (hLe : left ≤ right) :
    executionBudget staticCost left ≤ executionBudget staticCost right := by
  exact Nat.mul_le_mul_left _ (targetBudget_mono hLe)

theorem executionBudget_static_mono
    {left right : Nat} (hLe : left ≤ right) (sourceFuel : Nat) :
    executionBudget left sourceFuel ≤
      executionBudget right sourceFuel := by
  exact Nat.mul_le_mul_right (targetBudget sourceFuel) (by omega)

theorem executionBudget_add_static
    (left right sourceFuel : Nat) :
    executionBudget left sourceFuel +
        executionBudget right sourceFuel =
      executionBudget (left + right + 1) sourceFuel := by
  simp [executionBudget, Nat.add_mul, two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem executionBudget_child_add_eight_le_of_lt
    (staticCost : Nat) {child parent : Nat}
    (hLt : child < parent) :
    executionBudget staticCost child + 8 ≤
      executionBudget staticCost parent := by
  have hMain := child_add_eight_le_of_lt hLt
  have hScaled := Nat.mul_le_mul_left (staticCost + 1) hMain
  simp only [executionBudget, Nat.mul_add] at hScaled ⊢
  nlinarith

theorem executionBudget_static_children_add_eight_le_of_lt
    (leftStatic rightStatic : Nat) {child parent : Nat}
    (hLt : child < parent) :
    executionBudget leftStatic parent +
        executionBudget rightStatic child + 8 ≤
      executionBudget (leftStatic + rightStatic + 1) parent := by
  have hChild :=
    executionBudget_child_add_eight_le_of_lt rightStatic hLt
  rw [← executionBudget_add_static leftStatic rightStatic parent]
  omega

theorem executionBudget_static_two_children_add_eight_le_of_lt
    (leftStatic rightStatic : Nat)
    {left right parent : Nat}
    (hLeft : left < parent) (hRight : right < parent) :
    executionBudget leftStatic left +
        executionBudget rightStatic right + 8 ≤
      executionBudget (leftStatic + rightStatic + 1) parent := by
  have hLeftBudget :=
    executionBudget_child_add_eight_le_of_lt leftStatic hLeft
  have hRightBudget :=
    executionBudget_mono rightStatic (Nat.le_of_lt hRight)
  rw [← executionBudget_add_static leftStatic rightStatic parent]
  omega

theorem executionBudget_two_children_add_eight_le_of_lt
    (staticCost : Nat) {left right parent : Nat}
    (hLeft : left < parent) (hRight : right < parent) :
    executionBudget staticCost left +
        executionBudget staticCost right + 8 ≤
      executionBudget staticCost parent := by
  have hMain := two_children_add_eight_le_of_lt hLeft hRight
  have hScaled := Nat.mul_le_mul_left (staticCost + 1) hMain
  simp only [executionBudget, Nat.mul_add] at hScaled ⊢
  nlinarith

def Prepared.Bounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (staticCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.Prepared
        contract transcript codeRel program pre fresh source target ctx) :
    Prop :=
  result.requiredFuel ≤ executionBudget staticCost sourceFuel

def PreparedValue.Bounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Assembly.Word}
    (staticCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program pre lower fresh
        source target ctx value) : Prop :=
  result.requiredFuel ≤ executionBudget staticCost sourceFuel

def PreparedExpression.Bounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {results : Nat}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr results}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (staticCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedExpression
        contract transcript codeRel program pre lower fresh
        source target ctx values) : Prop :=
  result.requiredFuel ≤ executionBudget staticCost sourceFuel

def PreparedArgs.Bounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (staticCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program pre lower fresh
        source target ctx values) : Prop :=
  result.prepared.requiredFuel ≤ executionBudget staticCost sourceFuel

def ScopedOpenResult.Bounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (staticCost sourceFuel : Nat)
    (result :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl)) : Prop :=
  result.requiredFuel ≤ executionBudget staticCost sourceFuel

def Prepared.ProgramBounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (globalCost localCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.Prepared
        contract transcript codeRel program pre fresh source target ctx) :
    Prop :=
  result.requiredFuel ≤
    executionBudgetFor globalCost localCost sourceFuel

def PreparedValue.ProgramBounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Assembly.Word}
    (globalCost localCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program pre lower fresh
        source target ctx value) : Prop :=
  result.requiredFuel ≤
    executionBudgetFor globalCost localCost sourceFuel

def PreparedExpression.ProgramBounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {results : Nat}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr results}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (globalCost localCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedExpression
        contract transcript codeRel program pre lower fresh
        source target ctx values) : Prop :=
  result.requiredFuel ≤
    executionBudgetFor globalCost localCost sourceFuel

def PreparedArgs.ProgramBounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    (globalCost localCost sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program pre lower fresh
        source target ctx values) : Prop :=
  result.prepared.requiredFuel ≤
    executionBudgetFor globalCost localCost sourceFuel

def ScopedOpenResult.ProgramBounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (globalCost localCost sourceFuel : Nat)
    (result :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl)) : Prop :=
  result.requiredFuel ≤
    executionBudgetFor globalCost localCost sourceFuel

/--
Any successful run of the same lowered block bounds a related result's least
fuel. Functions determinism identifies the caller-supplied terminal pair with
the one stored in the outcome-indexed result.
-/
theorem ScopedOpenResult.requiredFuel_le_of_successful_run
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx runCtx : Functions.Source.Ctx}
    {outcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (result :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl))
    {fuel : Nat}
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel { stmts := lower } target =
        .ok (outcome, runCtx)) :
    result.requiredFuel ≤ fuel := by
  obtain ⟨storedFuel, hStored⟩ := result.run
  have hUnique :=
    Functions.Source.Effectful.Block.runOpen_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hRun hStored
  have hOutcome : outcome = result.outcome :=
    congrArg Prod.fst hUnique
  have hCtx : runCtx = result.finalCtx :=
    congrArg Prod.snd hUnique
  apply
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_le_of_run
      result
  simpa [hOutcome, hCtx] using hRun

theorem Prepared.programBounded_of_bounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {globalCost localCost sourceFuel : Nat}
    {result :
      FunctionsObserverExpression.Prepared
        contract transcript codeRel program pre fresh source target ctx}
    (hBounded : Prepared.Bounded localCost sourceFuel result) :
    Prepared.ProgramBounded globalCost localCost sourceFuel result :=
  hBounded.trans
    (executionBudget_le_executionBudgetFor
      globalCost localCost sourceFuel)

theorem PreparedValue.programBounded_of_bounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Assembly.Word}
    {globalCost localCost sourceFuel : Nat}
    {result :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program pre lower fresh
        source target ctx value}
    (hBounded : PreparedValue.Bounded localCost sourceFuel result) :
    PreparedValue.ProgramBounded globalCost localCost sourceFuel result :=
  hBounded.trans
    (executionBudget_le_executionBudgetFor
      globalCost localCost sourceFuel)

theorem PreparedArgs.programBounded_of_bounded
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt}
    {lower : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {values : List Assembly.Word}
    {globalCost localCost sourceFuel : Nat}
    {result :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program pre lower fresh
        source target ctx values}
    (hBounded : PreparedArgs.Bounded localCost sourceFuel result) :
    PreparedArgs.ProgramBounded globalCost localCost sourceFuel result :=
  hBounded.trans
    (executionBudget_le_executionBudgetFor
      globalCost localCost sourceFuel)

theorem ScopedOpenResult.programBounded_of_bounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {lower : List Functions.Stmt}
    {initial final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {globalCost localCost sourceFuel : Nat}
    {result :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl)}
    (hBounded : ScopedOpenResult.Bounded localCost sourceFuel result) :
    ScopedOpenResult.ProgramBounded
      globalCost localCost sourceFuel result :=
  hBounded.trans
    (executionBudget_le_executionBudgetFor
      globalCost localCost sourceFuel)

theorem ScopedOpenResult.empty_bounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {fresh : Fresh.State}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (staticCost sourceFuel : Nat)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        fresh.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin fresh.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin fresh.used layout)
    (hLayoutScope :
      FunctionsObserverOutcome.LayoutWithinScope layout ctx) :
    ScopedOpenResult.Bounded staticCost sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.empty
        (contract := contract) (program := program)
        (sourceControl := sourceControl)
        hRel hDomain hScope hLayout hLayoutScope) := by
  have hFuel :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_empty_le
      (contract := contract) (program := program)
      (sourceControl := sourceControl)
      hRel hDomain hScope hLayout hLayoutScope
  have hBudget := executionBudget_ge_sixteen staticCost sourceFuel
  exact le_trans hFuel (by omega)

theorem ScopedOpenResult.appendRegular_bounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceMiddle sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {staticCost : Nat}
    {leftSourceFuel rightSourceFuel sourceFuel : Nat}
    (left :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program leftLower initial middle entryLayout
        sourceMiddle target ctx (sourceControl := sourceControl))
    (hRegular : left.outcome.mode = .regular)
    (right :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program rightLower middle final
        left.finalLayout sourceFinal left.outcome.state left.finalCtx
        (sourceControl := sourceControl))
    (hLeft : ScopedOpenResult.Bounded staticCost leftSourceFuel left)
    (hRight : ScopedOpenResult.Bounded staticCost rightSourceFuel right)
    (hLeftFuel : leftSourceFuel < sourceFuel)
    (hRightFuel : rightSourceFuel < sourceFuel) :
    ScopedOpenResult.Bounded staticCost sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.appendRegular
        left hRegular right) := by
  have hCompose :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_appendRegular_le
      left hRegular right
  have hBudget :=
    executionBudget_two_children_add_eight_le_of_lt
      staticCost hLeftFuel hRightFuel
  dsimp [ScopedOpenResult.Bounded] at hLeft hRight ⊢
  omega

theorem ScopedOpenResult.appendNonregular_bounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {staticCost : Nat}
    {childFuel sourceFuel : Nat}
    (left :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program leftLower initial middle entryLayout
        sourceFinal target ctx (sourceControl := sourceControl))
    (hNonregular : left.outcome.mode ≠ .regular)
    (hSuffixFresh : Fresh.Extends middle final)
    (hLeft : ScopedOpenResult.Bounded staticCost childFuel left)
    (hFuel : childFuel < sourceFuel) :
    ScopedOpenResult.Bounded staticCost sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.appendNonregular
        (rightLower := rightLower) left hNonregular hSuffixFresh) := by
  have hCompose :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_appendNonregular_le
      (rightLower := rightLower) left hNonregular hSuffixFresh
  have hMono :=
    executionBudget_mono staticCost (Nat.le_of_lt hFuel)
  dsimp [ScopedOpenResult.Bounded] at hLeft ⊢
  omega

theorem ScopedOpenResult.empty_programBounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {fresh : Fresh.State}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (globalCost localCost sourceFuel : Nat)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        fresh.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin fresh.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin fresh.used layout)
    (hLayoutScope :
      FunctionsObserverOutcome.LayoutWithinScope layout ctx) :
    ScopedOpenResult.ProgramBounded globalCost localCost sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.empty
        (contract := contract) (program := program)
        (sourceControl := sourceControl)
        hRel hDomain hScope hLayout hLayoutScope) := by
  exact
    ScopedOpenResult.programBounded_of_bounded
      (ScopedOpenResult.empty_bounded
        localCost sourceFuel hRel hDomain hScope hLayout hLayoutScope)

theorem ScopedOpenResult.appendRegular_programBounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceMiddle sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {globalCost leftLocal rightLocal resultLocal : Nat}
    {leftSourceFuel rightSourceFuel sourceFuel : Nat}
    (left :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program leftLower initial middle entryLayout
        sourceMiddle target ctx (sourceControl := sourceControl))
    (hRegular : left.outcome.mode = .regular)
    (right :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program rightLower middle final
        left.finalLayout sourceFinal left.outcome.state left.finalCtx
        (sourceControl := sourceControl))
    (hLeft :
      ScopedOpenResult.ProgramBounded
        globalCost leftLocal leftSourceFuel left)
    (hRight :
      ScopedOpenResult.ProgramBounded
        globalCost rightLocal rightSourceFuel right)
    (hLeftCost : leftLocal ≤ globalCost)
    (hRightCost : rightLocal ≤ globalCost)
    (hLeftFuel : leftSourceFuel < sourceFuel)
    (hRightFuel : rightSourceFuel < sourceFuel) :
    ScopedOpenResult.ProgramBounded globalCost resultLocal sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.appendRegular
        left hRegular right) := by
  have hCompose :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_appendRegular_le
      left hRegular right
  have hChildren :=
    two_executionBudgetsFor_add_eight_le_target_of_lt
      globalCost leftLocal rightLocal
      hLeftCost hRightCost hLeftFuel hRightFuel
  have hParent :=
    targetBudgetFor_le_executionBudgetFor
      globalCost resultLocal sourceFuel
  dsimp [ScopedOpenResult.ProgramBounded] at hLeft hRight ⊢
  omega

theorem ScopedOpenResult.appendNonregular_programBounded
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {globalCost childLocal resultLocal : Nat}
    {childFuel sourceFuel : Nat}
    (left :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program leftLower initial middle entryLayout
        sourceFinal target ctx (sourceControl := sourceControl))
    (hNonregular : left.outcome.mode ≠ .regular)
    (hSuffixFresh : Fresh.Extends middle final)
    (hLeft :
      ScopedOpenResult.ProgramBounded
        globalCost childLocal childFuel left)
    (hChildCost : childLocal ≤ globalCost)
    (hFuel : childFuel < sourceFuel) :
    ScopedOpenResult.ProgramBounded globalCost resultLocal sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.appendNonregular
        (rightLower := rightLower) left hNonregular hSuffixFresh) := by
  have hCompose :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_appendNonregular_le
      (rightLower := rightLower) left hNonregular hSuffixFresh
  have hChild :=
    executionBudgetFor_add_eight_le_target_of_lt
      globalCost childLocal hChildCost hFuel
  have hParent :=
    targetBudgetFor_le_executionBudgetFor
      globalCost resultLocal sourceFuel
  dsimp [ScopedOpenResult.ProgramBounded] at hLeft ⊢
  omega

end FunctionsObserverFuel
end Yul
end EvmCompiler
