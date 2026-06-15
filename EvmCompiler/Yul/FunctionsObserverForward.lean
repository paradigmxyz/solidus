import EvmCompiler.Yul.FunctionsObserverStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverForward

/-!
Fuel-bounded composition for the adjacent Yul-to-Functions observer proof.

This module assembles the expression, call, and statement-owned constructors.
It does not define a compiler or interpreter. Recursive premises are strictly
smaller source-fuel interfaces and remain private to this pass boundary.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

namespace RecursiveScopedValueForward

theorem ofBody
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram bound) :
    FunctionsObserverCall.RecursiveScopedValueForward
      contract transcript codeRel sourceProgram targetProgram profile
      bound := by
  intro exprFuel
  induction exprFuel using Nat.strong_induction_on with
  | h exprFuel ih =>
      intro before after layout expr pre lower source source'
        target ctx values hFuel hOk hLower hRel hDomain hScope hRun
      have hSmallerValue :
          FunctionsObserverCall.RecursiveScopedValueForward
            contract transcript codeRel sourceProgram targetProgram
            profile exprFuel := by
        intro smallerFuel smallerBefore smallerAfter smallerLayout
          smallerExpr smallerPre smallerLower smallerSource
          smallerSource' smallerTarget smallerCtx smallerValues
          hSmaller hSmallerOk hSmallerLower hSmallerRel
          hSmallerDomain hSmallerScope hSmallerRun
        exact
          ih smallerFuel hSmaller
            (by omega) hSmallerOk hSmallerLower hSmallerRel
            hSmallerDomain hSmallerScope hSmallerRun
      have hSmallerExpr :
          FunctionsObserverCall.RecursiveScopedExpressionForward
            contract transcript codeRel sourceProgram targetProgram
            profile exprFuel :=
        FunctionsObserverCall.RecursiveScopedValueForward.expression
          hSmallerValue
      have hSmallerBody :
          FunctionsObserverCall.RecursiveBodyForward
            contract transcript codeRel sourceProgram targetProgram
            exprFuel := by
        intro sourceFuel bodyBefore bodyAfter params returns body fn
          args paramStore sourceCaller sourceAfterBody targetCaller
          hSourceFuel hBodyLower hParams hReturns hParamStore
          hEntry hBodyRun
        exact
          hBody (by omega) hBodyLower hParams hReturns hParamStore
            hEntry hBodyRun
      cases expr with
      | Lit value =>
          exact
            FunctionsObserverExpression.ScopedPreparedValue.ofLiteral
              hLower hRel hDomain hScope hRun
      | Var name =>
          exact
            FunctionsObserverExpression.ScopedPreparedValue.ofVariable
              hLower hRel hDomain hScope hRun
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hArgsOk :
                  SolcValidation.ExprsOk? profile
                      sourceProgram.contract layout args =
                    true :=
                SolcValidation.exprsOk_of_exprOk_primitive hOk
              exact
                FunctionsObserverExpression.ScopedPreparedValue.ofPrimitive
                  hLower
                  (fun candidate hMem =>
                    SolcValidation.exprOk_of_exprsOk_of_mem
                      hArgsOk hMem)
                  (fun hArgFuel hArgOk hArgLower hArgRel
                      hArgDomain hArgScope hArgRun =>
                    hSmallerExpr hArgFuel hArgOk hArgLower hArgRel
                      hArgDomain hArgScope hArgRun)
                  hRel hDomain hScope hRun
          | inr functionName =>
              cases hLookup :
                  sourceProgram.contract.functions.lookup functionName with
              | none =>
                  simp [SolcValidation.ExprOk?,
                    SolcValidation.lookupFunction?, hLookup] at hOk
              | some fnDef =>
                  cases fnDef with
                  | Def params returns body =>
                      obtain ⟨returnName, hReturns⟩ :=
                        SolcValidation.returns_singleton_of_exprOk_functionCall
                          hOk hLookup
                      have hLength :=
                        Yul.Source.Effectful.evalValues_function_ok_length
                          (ObserverSemantics.SourceReplay.stateModel transcript)
                          (ObserverSafety.SafeSemantics.primitiveSemantics
                            contract transcript)
                          hLookup hRun
                      rw [hReturns] at hLength
                      cases values with
                      | nil =>
                          simp at hLength
                      | cons value rest =>
                          cases rest with
                          | nil =>
                              have hEval :
                                  Yul.Source.Effectful.eval
                                      (ObserverSemantics.SourceReplay.stateModel
                                        transcript)
                                      (ObserverSafety.SafeSemantics.primitiveSemantics
                                        contract transcript)
                                      exprFuel
                                      (.Call (.inr functionName) args)
                                      (some sourceProgram.contract) source =
                                    .ok (source', value) :=
                                Yul.Source.Effectful.eval_of_evalValues_singleton
                                  (ObserverSemantics.SourceReplay.stateModel
                                    transcript)
                                  (ObserverSafety.SafeSemantics.primitiveSemantics
                                    contract transcript)
                                  hRun
                              exact
                                ⟨value, rfl,
                                  FunctionsObserverCall.ScopedPreparedValue.ofFunctionCall
                                      hDecomposition hLower hProgramOk hOk
                                      hSmallerExpr hSmallerBody hRel
                                      hDomain hScope hEval⟩
                          | cons next tail =>
                              simp at hLength

end RecursiveScopedValueForward

end FunctionsObserverForward
end Yul
end EvmCompiler
