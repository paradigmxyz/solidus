import EvmCompiler.Yul.FunctionsObserverExpression
import EvmCompiler.Yul.FunctionsObserverOutcome

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverFuel

/-!
Quantitative interface for the adjacent Yul-to-Functions observer pass.

The existing forward simulation chooses sufficient target fuel existentially.
This module supplies a source-fuel-indexed budget large enough for local
compiler wrappers and a bounded number of strictly smaller recursive runs.
Pass-owned preservation theorems can expose bounds against this budget without
changing either canonical semantics.
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
    (sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.Prepared
        contract transcript codeRel program pre fresh source target ctx) :
    Prop :=
  result.requiredFuel ≤ targetBudget sourceFuel

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
    (sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedValue
        contract transcript codeRel program pre lower fresh
        source target ctx value) : Prop :=
  result.requiredFuel ≤ targetBudget sourceFuel

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
    (sourceFuel : Nat)
    (result :
      FunctionsObserverExpression.PreparedExpression
        contract transcript codeRel program pre lower fresh
        source target ctx values) : Prop :=
  result.requiredFuel ≤ targetBudget sourceFuel

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
    (sourceFuel : Nat)
    (result :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program lower initial final entryLayout
        sourceFinal target ctx (sourceControl := sourceControl)) : Prop :=
  result.requiredFuel ≤ targetBudget sourceFuel

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
    (sourceFuel : Nat)
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
    ScopedOpenResult.Bounded sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.empty
        (contract := contract) (program := program)
        (sourceControl := sourceControl)
        hRel hDomain hScope hLayout hLayoutScope) := by
  have hFuel :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_empty_le
      (contract := contract) (program := program)
      (sourceControl := sourceControl)
      hRel hDomain hScope hLayout hLayoutScope
  have hBudget := targetBudget_ge_sixteen sourceFuel
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
    (hLeft : ScopedOpenResult.Bounded leftSourceFuel left)
    (hRight : ScopedOpenResult.Bounded rightSourceFuel right)
    (hLeftFuel : leftSourceFuel < sourceFuel)
    (hRightFuel : rightSourceFuel < sourceFuel) :
    ScopedOpenResult.Bounded sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.appendRegular
        left hRegular right) := by
  have hCompose :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_appendRegular_le
      left hRegular right
  have hBudget :=
    two_children_add_eight_le_of_lt hLeftFuel hRightFuel
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
    {childFuel sourceFuel : Nat}
    (left :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program leftLower initial middle entryLayout
        sourceFinal target ctx (sourceControl := sourceControl))
    (hNonregular : left.outcome.mode ≠ .regular)
    (hSuffixFresh : Fresh.Extends middle final)
    (hLeft : ScopedOpenResult.Bounded childFuel left)
    (hFuel : childFuel < sourceFuel) :
    ScopedOpenResult.Bounded sourceFuel
      (FunctionsObserverOutcome.ScopedOpenResult.appendNonregular
        (rightLower := rightLower) left hNonregular hSuffixFresh) := by
  have hCompose :=
    FunctionsObserverOutcome.ScopedOpenResult.requiredFuel_appendNonregular_le
      (rightLower := rightLower) left hNonregular hSuffixFresh
  have hMono := targetBudget_mono (Nat.le_of_lt hFuel)
  dsimp [ScopedOpenResult.Bounded] at hLeft ⊢
  omega

end FunctionsObserverFuel
end Yul
end EvmCompiler
