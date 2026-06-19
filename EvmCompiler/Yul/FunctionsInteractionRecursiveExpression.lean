import EvmCompiler.Yul.FunctionsInteractionPreparedCondition
import EvmCompiler.Yul.FunctionsInteractionPreparedPrimitive
import EvmCompiler.Yul.FunctionsInteractionSelectedCall

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveExpression

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation

/-- Compiler-selected condition preservation at one source/target fuel pair.
The interface owns only expression lowering; statement control remains in the
adjacent statement module. -/
def ConditionForwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (sourceFuel targetFuel : Nat) (layout : List Functions.Name) : Prop :=
  ∀ {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {before after : Fresh.State}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx},
    SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr = true →
    Expr.lower1Unchecked? before expr = some (pre, lower, after) →
    FunctionsInteractionStaticCost.programBudget sourceProgram sourceFuel +
        pre.length + 2 ≤ targetFuel →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ScopedStateRel layout source target →
    TargetDomainWithin before.used target.vars →
    FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx →
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedCondition.DoneRel layout after.used ctx)
      (Yul.InteractionSemantics.evalValues sourceFuel expr
        (some sourceProgram.contract) source)
      (FunctionsInteractionPreparedCondition.run targetProgram.toFunctions ctx
        targetFuel pre lower target)

/-- Construct the validated recursive bounded-head capability by strong
induction on canonical source fuel. Primitive operands and internal-call
arguments recurse at `fuel - 2`; selected function bodies recurse at
`fuel - 3`. -/
theorem recursiveBoundHeads
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true) :
    ∀ (fuel targetFuel : Nat) (layout : List Functions.Name),
      (∀ {bodyFuel bodyTargetFuel : Nat},
        bodyFuel < fuel →
          FunctionsInteractionSelectedCall.BodyForwardAt
            profile sourceProgram targetProgram bodyFuel bodyTargetFuel) →
      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
        profile sourceProgram fuel targetFuel
        (some sourceProgram.contract) targetProgram.toFunctions layout := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro targetFuel layout hBodies
      intro expr rest preRest preHead lowerHead stateRest stateHead
        stateFresh tmp hExprOk hLower hFresh hTargetFuel
        hLayoutRest hLayoutHead hHeadBudget
      let headFuel := fuel - 2 * rest.reverse.length
      have hHeadFuelLe : headFuel ≤ fuel := by
        simp [headFuel]
      cases expr with
      | Lit value =>
          exact FunctionsInteractionPreparedArgs.boundDeferred
            (by simp [Expr.deferredBoundArgSafe?])
            hLayoutHead hTargetFuel
      | Var name =>
          exact FunctionsInteractionPreparedArgs.boundDeferred
            (by simp [Expr.deferredBoundArgSafe?])
            hLayoutHead hTargetFuel
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hPrimitiveLower :
                  Expr.UncheckedPrimitiveLowering 1 stateRest prim args
                    preHead lowerHead stateHead :=
                Expr.uncheckedPrimitiveLowering_of_lowerUnchecked?
                  (by simpa [Expr.lower1Unchecked?] using hLower)
              apply FunctionsInteractionPreparedPrimitive.boundPrimitive
                FunctionsInteractionClosedPrimitive.compilerSelected
                hPrimitiveLower hExprOk hFresh
              · intro argsFuel hFuelEq
                have hArgsLt : argsFuel < fuel := by
                  omega
                apply ih argsFuel hArgsLt
                  (targetFuel - preRest.length) layout
                intro bodyFuel bodyTargetFuel hBodyLt
                exact hBodies (lt_trans hBodyLt hArgsLt)
              · omega
              · exact hLayoutRest
              · exact hLayoutHead
              · exact hTargetFuel
          | inr functionName =>
              have hCallLower :
                  Expr.UncheckedFunctionCallLowering stateRest functionName
                    args preHead lowerHead stateHead :=
                Expr.uncheckedFunctionCallLowering_of_lower1Unchecked? hLower
              apply FunctionsInteractionSelectedCall.boundCallAtFuel
                hDecomposition hProgramOk hExprOk hCallLower
              · intro argsFuel hFuelEq
                have hArgsLt : argsFuel < fuel := by
                  omega
                apply ih argsFuel hArgsLt
                  (targetFuel - preRest.length) layout
                intro bodyFuel bodyTargetFuel hBodyLt
                exact hBodies (lt_trans hBodyLt hArgsLt)
              · intro bodyFuel hFuelEq
                have hBodyLt : bodyFuel < fuel := by
                  omega
                unfold FunctionsInteractionSelectedCall.BodyForwardAt
                intro body before after fn source target hLowerBody hBodyOk
                  hReserved hBodyBudget hRel
                exact hBodies
                    (bodyFuel := bodyFuel)
                    (bodyTargetFuel :=
                      targetFuel - preRest.length - preHead.length - 2)
                    hBodyLt
                  hLowerBody hBodyOk hReserved hBodyBudget hRel
              · intro bodyFuel hFuelEq
                have hChildFuelLe : bodyFuel + 1 ≤ headFuel := by
                  omega
                have hProgramLe :
                    FunctionsInteractionStaticCost.programBudget sourceProgram
                        (bodyFuel + 1) ≤
                      FunctionsInteractionStaticCost.programBudget sourceProgram
                        headFuel := by
                  unfold FunctionsInteractionStaticCost.programBudget
                  exact FunctionsInteractionFuel.executionBudgetFor_mono
                    _ _ hChildFuelLe
                dsimp [headFuel] at hProgramLe
                omega
              · exact hLayoutRest
              · exact hLayoutHead
              · exact hTargetFuel

/-- Exhaustive condition dispatcher for the ordinary compiler. Recursive
primitive operands and selected internal-call bodies use only strictly smaller
source fuel and the existing adjacent expression/call capabilities. -/
theorem recursiveCondition
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true) :
    ∀ (fuel targetFuel : Nat) (layout : List Functions.Name),
      (∀ {bodyFuel bodyTargetFuel : Nat},
        bodyFuel < fuel →
          FunctionsInteractionSelectedCall.BodyForwardAt
            profile sourceProgram targetProgram bodyFuel bodyTargetFuel) →
      ConditionForwardAt profile sourceProgram targetProgram
        fuel targetFuel layout := by
  intro fuel targetFuel layout hBodies
  intro expr pre lower before after source target ctx hExprOk hLower
    hBudget hLayout hScoped hDomain hTargetScope
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.evalValues,
        Yul.Source.Canonical.evalValues,
        Yul.Source.Effectful.evalValues,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.Source.Effectful.Control.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := FunctionsInteractionPreparedCondition.DoneRel
            layout after.used ctx)
          (right := FunctionsInteractionPreparedCondition.run
            targetProgram.toFunctions ctx targetFuel pre lower target)
          hTruncated)
  | succ previous =>
      have hTargetPositive : 0 < targetFuel := by omega
      cases expr with
      | Lit value =>
          obtain ⟨remaining, rfl⟩ : ∃ remaining, targetFuel = remaining + 1 :=
            ⟨targetFuel - 1, by omega⟩
          have hPrepared := FunctionsInteractionPreparedArgs.deferred
            (fuel := previous + 1)
            (targetFuel := remaining)
            (codeOverride := some sourceProgram.contract)
            (program := targetProgram.toFunctions) (ctx := ctx)
            (by simp [Expr.deferredBoundArgSafe?]) hLower hScoped hDomain
            hTargetScope
          exact FunctionsInteractionPreparedCondition.ofStablePrepared hPrepared
      | Var name =>
          obtain ⟨remaining, rfl⟩ : ∃ remaining, targetFuel = remaining + 1 :=
            ⟨targetFuel - 1, by omega⟩
          have hPrepared := FunctionsInteractionPreparedArgs.deferred
            (fuel := previous + 1)
            (targetFuel := remaining)
            (codeOverride := some sourceProgram.contract)
            (program := targetProgram.toFunctions) (ctx := ctx)
            (by simp [Expr.deferredBoundArgSafe?]) hLower hScoped hDomain
            hTargetScope
          exact FunctionsInteractionPreparedCondition.ofStablePrepared hPrepared
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hPrimitiveLower :
                  Expr.UncheckedPrimitiveLowering 1 before prim args
                    pre lower after :=
                Expr.uncheckedPrimitiveLowering_of_lowerUnchecked?
                  (by simpa [Expr.lower1Unchecked?] using hLower)
              cases hPrimitiveLower with
              | direct hDirect hOp hArgs hSeq hOutputs =>
                  exact
                    FunctionsInteractionPreparedCondition.ofDirectPrimitiveLowering
                      FunctionsInteractionClosedPrimitive.compilerSelected
                      (argsFuel := previous)
                      (Expr.UncheckedDirectPrimitiveLowering.primitive
                        hOp hArgs hSeq hOutputs)
                      hTargetPositive hScoped hDomain hTargetScope
              | bound hBound hOp hArgs hSeq hOutputs =>
                  have hArgsOk :=
                    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
                  have hNested :
                      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
                        profile sourceProgram previous targetFuel
                        (some sourceProgram.contract)
                        targetProgram.toFunctions layout := by
                    apply recursiveBoundHeads hDecomposition hProgramOk
                      previous targetFuel layout
                    intro bodyFuel bodyTargetFuel hBodyLt
                    exact hBodies
                      (lt_trans hBodyLt (Nat.lt_succ_self previous))
                  have hPreviousLe : previous ≤ previous + 1 := by omega
                  have hProgramLe :
                      FunctionsInteractionStaticCost.programBudget sourceProgram
                          previous ≤
                        FunctionsInteractionStaticCost.programBudget sourceProgram
                          (previous + 1) := by
                    unfold FunctionsInteractionStaticCost.programBudget
                    exact FunctionsInteractionFuel.executionBudgetFor_mono
                      _ _ hPreviousLe
                  have hArgsBudget :
                      FunctionsInteractionStaticCost.programBudget sourceProgram
                          previous + pre.length + 2 ≤ targetFuel := by
                    omega
                  have hPrepared :=
                    FunctionsInteractionPreparedArgs.ofUncheckedLowering
                      (fuel := previous) (targetFuel := targetFuel)
                      (ctx := ctx) hArgsOk hArgs hNested hArgsBudget
                      hScoped hDomain hTargetScope hLayout (by omega)
                  exact
                    FunctionsInteractionPreparedCondition.ofPreparedPrimitive
                      FunctionsInteractionClosedPrimitive.compilerSelected
                      hOp hSeq hOutputs hPrepared
          | inr functionName =>
              cases previous with
              | zero =>
                  rw [Yul.InteractionSemantics.EvalValues.internal_succ]
                  have hArgsZero :
                      Yul.InteractionSemantics.evalArgs 0 args.reverse
                          (some sourceProgram.contract) source =
                        Yul.InteractionSemantics.Primitive.fail
                          source .OutOfFuel := by
                    unfold Yul.InteractionSemantics.evalArgs
                      Yul.Source.Canonical.evalArgs
                      Yul.Source.Effectful.evalArgs
                    rfl
                  rw [hArgsZero]
                  have hTruncated :
                      Truncated
                        ({ exception := .OutOfFuel, state := source } :
                          Yul.InteractionSemantics.Failure) := by
                    trivial
                  simpa [Yul.InteractionSemantics.Primitive.fail] using
                    (Simulation.Interaction.ForwardRel.truncated
                      (doneRel :=
                        FunctionsInteractionPreparedCondition.DoneRel
                          layout after.used ctx)
                      (right := FunctionsInteractionPreparedCondition.run
                        targetProgram.toFunctions ctx targetFuel pre lower target)
                      hTruncated)
              | succ bodyFuel =>
                  have hCallLower :
                      Expr.UncheckedFunctionCallLowering before functionName
                        args pre lower after :=
                    Expr.uncheckedFunctionCallLowering_of_lower1Unchecked? hLower
                  let targetBodyFuel := targetFuel - pre.length - 2
                  have hFuelEq :
                      pre.length + targetBodyFuel + 2 = targetFuel := by
                    dsimp [targetBodyFuel]
                    omega
                  have hNested :
                      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
                        profile sourceProgram (bodyFuel + 1) targetFuel
                        (some sourceProgram.contract)
                        targetProgram.toFunctions layout := by
                    apply recursiveBoundHeads hDecomposition hProgramOk
                      (bodyFuel + 1) targetFuel layout
                    intro nestedBodyFuel nestedTargetFuel hBodyLt
                    exact hBodies (lt_trans hBodyLt (by omega))
                  have hNestedTarget :
                      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
                        profile sourceProgram (bodyFuel + 1)
                        (pre.length + targetBodyFuel + 2)
                        (some sourceProgram.contract)
                        targetProgram.toFunctions layout := by
                    rw [hFuelEq]
                    exact hNested
                  have hBodyForward :
                      FunctionsInteractionSelectedCall.BodyForwardAt
                        profile sourceProgram targetProgram bodyFuel
                          targetBodyFuel :=
                    hBodies (by omega)
                  have hChildLe : bodyFuel + 1 ≤ bodyFuel + 2 := by omega
                  have hChildBudgetLe :
                      FunctionsInteractionStaticCost.programBudget sourceProgram
                          (bodyFuel + 1) ≤
                        FunctionsInteractionStaticCost.programBudget sourceProgram
                          (bodyFuel + 2) := by
                    unfold FunctionsInteractionStaticCost.programBudget
                    exact FunctionsInteractionFuel.executionBudgetFor_mono
                      _ _ hChildLe
                  have hTargetBodyBudget :
                      FunctionsInteractionStaticCost.programBudget sourceProgram
                          (bodyFuel + 1) ≤ targetBodyFuel := by
                    have hBudget' := hBudget
                    have hParentFuel : bodyFuel + 1 + 1 = bodyFuel + 2 := by
                      omega
                    rw [hParentFuel] at hBudget'
                    rw [← hFuelEq] at hBudget'
                    omega
                  have hSelected :=
                    FunctionsInteractionSelectedCall.ofUncheckedFunctionCallLowering
                      (sourceFuel := bodyFuel)
                      (targetBodyFuel := targetBodyFuel)
                      (ctx := ctx) hDecomposition hProgramOk hExprOk hCallLower
                      hNestedTarget hBodyForward hTargetBodyBudget hScoped hDomain
                      hTargetScope hLayout
                  have hSelected' :
                      Simulation.Interaction.ForwardRel Truncated
                        (FunctionsInteractionPreparedArgs.DoneRel
                          layout after [lower] target ctx)
                        (Yul.InteractionSemantics.evalValues (bodyFuel + 2)
                          (.Call (.inr functionName) args)
                          (some sourceProgram.contract) source)
                        (Functions.InteractionSemantics.Block.openRun
                          targetProgram.toFunctions ctx targetFuel
                          { stmts := pre } target) := by
                    rw [← hFuelEq]
                    exact hSelected
                  exact
                    FunctionsInteractionPreparedCondition.ofStablePrepared
                      hSelected'

end FunctionsInteractionRecursiveExpression
end Yul
end EvmCompiler
