import EvmCompiler.Yul.FunctionsInteractionSelectedCall

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveExpression

open FunctionsInteractionPrimitive

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

end FunctionsInteractionRecursiveExpression
end Yul
end EvmCompiler
