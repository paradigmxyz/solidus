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

namespace RecursiveBodyForward

theorem entryTargetDomain
    {before : Fresh.State} {fn : Functions.FunDef}
    {args : List Word} {paramStore : Locals.Source.Store}
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params)) :
    StateRelation.Vars.TargetDomainWithin before.used
      (Functions.Source.Store.initReturns fn.returns paramStore) := by
  intro name value hLookup
  exact
    hReserved name
      (Functions.Source.Store.initReturns_insertMany_empty_apply_mem
        hParamStore hLookup)

theorem bodyScope
    {before : Fresh.State} {fn : Functions.FunDef}
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params)) :
    StateRelation.Vars.NamesWithin before.used
      (Functions.Source.Effectful.FunDef.bodyCtx fn).scope := by
  simpa [Functions.Source.Effectful.FunDef.bodyCtx] using hReserved

theorem ofLetOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Let [name] (some expr)] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Let [name] (some expr)]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Let [name] (some expr)] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Let [name] (some expr)])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  apply
    FunctionsObserverStatement.ReturnedBody.of_let_one
      hNotFunctionCall hExprOk hLower hParams hReturns hParamStore
      hEntry
  · simpa using entryTargetDomain hParamStore hReserved
  · exact bodyScope hReserved
  · exact hValue
  · exact hRun

theorem ofAssignOne
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {name : EvmYul.Identifier}
    {expr : AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before [.Assign [name] expr] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names [.Assign [name] expr]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Assign [name] expr] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block [.Assign [name] expr])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) 1 expr =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  apply
    FunctionsObserverStatement.ReturnedBody.of_assign_one
      hNotFunctionCall hExprOk hLower hParams hReturns hParamStore
      hEntry
  · simpa using entryTargetDomain hParamStore hReserved
  · exact bodyScope hReserved
  · exact hValue
  · exact hRun

theorem ofAssignCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before
          [.Assign names (.Call (.inr functionName) callArgs)] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (_hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names
          [.Assign names (.Call (.inr functionName) callArgs)]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Assign names (.Call (.inr functionName) callArgs)] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block
            [.Assign names
              (.Call (.inr functionName) callArgs)])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_assign_call_parts hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  exact
    FunctionsObserverStatement.ReturnedBody.of_assign_call
      hDecomposition hArgsLowering hFnBody hExprOk hProgramOk
      hParams hReturns hParamStore hEntry
      (by simpa using entryTargetDomain hParamStore hReserved)
      (bodyScope hReserved)
      (FunctionsObserverCall.RecursiveScopedValueForward.expression hValue)
      hBody hRun

theorem ofLetCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {before after : Fresh.State}
    {params returns names : List EvmYul.Identifier}
    {functionName : Name}
    {callArgs : List AstExpr}
    {fn : Functions.FunDef}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hLower :
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before
          [.Let names (some (.Call (.inr functionName) callArgs))] =
        some (fn.body, after))
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hReserved :
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params))
    (hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names
          [.Let names (some (.Call (.inr functionName) callArgs))]))
    (hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true
          [.Let names (some (.Call (.inr functionName) callArgs))] =
        true)
    (hEntry :
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }))
    (hValue :
      FunctionsObserverCall.RecursiveScopedValueForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hBody :
      FunctionsObserverCall.RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile
        sourceFuel)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block
            [.Let names
              (some (.Call (.inr functionName) callArgs))])
          (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody) :
    ∃ targetFuel,
      Nonempty
        (FunctionsObserverCall.ReturnedBody
          contract transcript codeRel targetProgram.toFunctions
          fn args targetFuel sourceAfterBody targetCaller) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_singleton_let_call_parts hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          (fn.returns ++ fn.params) names.length
          (.Call (.inr functionName) callArgs) =
        true := by
    simp [SolcValidation.StmtsOk?, SolcValidation.StmtOk?] at hBodyOk
    exact hBodyOk.2
  exact
    FunctionsObserverStatement.ReturnedBody.of_let_call
      hDecomposition hArgsLowering hFnBody hExprOk hProgramOk
      hParams hReturns hParamStore hEntry
      (by simpa using entryTargetDomain hParamStore hReserved)
      (bodyScope hReserved) hBodyNames
      (FunctionsObserverCall.RecursiveScopedValueForward.expression hValue)
      hBody hRun

end RecursiveBodyForward

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
        contract transcript codeRel sourceProgram targetProgram profile
        bound) :
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
            contract transcript codeRel sourceProgram targetProgram profile
            exprFuel := by
        intro sourceFuel bodyBefore bodyAfter params returns body fn
          args paramStore sourceCaller sourceAfterBody targetCaller
          hSourceFuel hBodyLower hParams hReturns hParamStore
          hReserved hBodyNames hBodyOk hEntry hBodyRun
        exact
          hBody (by omega) hBodyLower hParams hReturns hParamStore
            hReserved hBodyNames hBodyOk hEntry hBodyRun
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
