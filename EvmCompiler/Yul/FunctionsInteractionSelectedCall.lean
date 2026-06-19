import EvmCompiler.Yul.FunctionsInteractionCall
import EvmCompiler.Yul.FunctionsCompilerArtifact
import EvmCompiler.Yul.FunctionsInteractionStaticCost
import EvmCompiler.Yul.SolcValidation

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionSelectedCall

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation

/-- Fuel-indexed recursive body interface for one ordinary compiler-selected
function. The whole-program source-fuel induction constructs this capability;
it is not a public call oracle. -/
def BodyForwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (sourceFuel targetFuel : Nat) : Prop :=
  ∀ {body : List AstStmt} {before after : Fresh.State}
    {fn : Functions.FunDef}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State},
    Stmt.List.toBlockUncheckedFuel?
        (FunctionList.fuel
          (Contract.functionEntries sourceProgram.contract))
        before body = some (fn.body, after) →
    SolcValidation.StmtsOk? profile sourceProgram.contract
        ((Contract.functionEntries
          sourceProgram.contract).map Prod.fst)
        (fn.returns ++ fn.params) false false true body = true →
    (∀ name, name ∈ fn.returns ++ fn.params → name ∈ before.used) →
    (∀ name, name ∈ Stmt.List.names body → name ∈ before.used) →
    FunctionsInteractionStaticCost.bodyBudget
        sourceProgram body sourceFuel ≤ targetFuel →
    ScopedStateRel (fn.returns ++ fn.params) source target →
    TargetDomainWithin before.used target.vars →
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionCall.FunctionBodyDoneRel
        (fn.returns ++ fn.params))
      (Yul.InteractionSemantics.exec sourceFuel (.Block body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions
        (Functions.Source.Effectful.FunDef.bodyCtx fn)
        targetFuel fn.body target)

/-- The exact compiler-selected callee frame contains only initialized returns
and parameters, all of which are reserved by the body compiler artifact. -/
theorem entryTargetDomain
    {before : Fresh.State} {fn : Functions.FunDef}
    {args : List Word} {paramStore : Locals.Source.Store}
    (hParamStore :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hReserved : ∀ name, name ∈ fn.returns ++ fn.params →
      name ∈ before.used) :
    TargetDomainWithin before.used
      (Functions.Source.Store.initReturns fn.returns paramStore) := by
  intro name value hLookup
  exact hReserved name
    (Functions.Source.Store.initReturns_insertMany_empty_apply_mem
      hParamStore hLookup)

/-- Preserve the exact ordinary compiler output for a validated one-result
internal-call expression, assuming only the smaller-fuel selected body theorem.
Argument preparation, call-frame setup, body execution, caller restoration,
fresh result writeback, and terminal propagation are all composed here. -/
theorem ofUncheckedFunctionCallLowering
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetBodyFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {initial final : Fresh.State} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1
          (.Call (.inr functionName) args) = true)
    (hLowering : Expr.UncheckedFunctionCallLowering
      initial functionName args pre lower final)
    (hBound : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram
      (sourceFuel + 1) (pre.length + targetBodyFuel + 2)
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodyForward : BodyForwardAt profile sourceProgram targetProgram
      sourceFuel targetBodyFuel)
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1) ≤ targetBodyFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hTargetScope : FunctionsInteractionControlRelation.TargetScopeWithin
      initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedArgs.DoneRel
        layout final [lower] target ctx)
      (Yul.InteractionSemantics.evalValues (sourceFuel + 2)
        (.Call (.inr functionName) args)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx
        (pre.length + targetBodyFuel + 2) { stmts := pre } target) := by
  cases hLowering with
  | @call argsState finalState functionName tmp args preArgs lowerArgs
      hSupported hArgs hFresh =>
      obtain ⟨params, returns, body, hLookup⟩ :=
        SolcValidation.exprOk_functionCall_lookup_exists hExprOk
      obtain ⟨before, after, fn, hPrefix, hFind, hFnName,
          hFnParams, hFnReturns, hLowerBody, hReserved⟩ :=
        hDecomposition.findFunction_parts hLookup
      obtain ⟨hArgCount, hSignature, returnName, hReturnSingleton⟩ :=
        SolcValidation.programOkWith_functionCall_parts
          hProgramOk hExprOk hLookup
      have hArgsOk :
          SolcValidation.ExprsOk? profile sourceProgram.contract
            layout args = true :=
        SolcValidation.exprsOk_of_exprOk_functionCall hExprOk hLookup
      have hBodyOk :
          SolcValidation.StmtsOk? profile sourceProgram.contract
              ((Contract.functionEntries
                sourceProgram.contract).map Prod.fst)
              (fn.returns ++ fn.params) false false true body = true := by
        rw [hFnReturns, hFnParams]
        exact SolcValidation.programOkWith_function_bodyOk
          hProgramOk hLookup
      have hBodyNames : ∀ candidate,
          candidate ∈ Stmt.List.names body → candidate ∈ before.used := by
        intro candidate hCandidate
        apply hPrefix candidate
        change candidate ∈ Contract.names sourceProgram.contract
        exact (Contract.function_names_mem_names_of_lookup hLookup).2
          candidate (by simp [FunctionDefinition.names, hCandidate])
      have hArgsExtends : Fresh.Extends initial argsState :=
        hArgs.stateExtends
      have hLayoutArgs :
          ∀ name, name ∈ layout → name ∈ argsState.used := by
        intro name hName
        exact hArgsExtends name (hLayout name hName)
      have hPrepared :=
        FunctionsInteractionPreparedCall.ofUncheckedCallArgsLowering
          (fuel := sourceFuel + 1)
          (ctx := ctx)
          (targetFuel :=
            (preArgs ++
              [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                Functions.Stmt.call [tmp] functionName lowerArgs]).length +
              targetBodyFuel + 2)
          hArgs hArgsOk hBound
          (by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega)
          hRel hDomain hTargetScope hLayout
          (by simp; omega)
      rw [show sourceFuel + 2 = (sourceFuel + 1) + 1 by omega,
        Yul.InteractionSemantics.EvalValues.internal_succ]
      change
        Simulation.Interaction.ForwardRel Truncated
          (FunctionsInteractionPreparedArgs.DoneRel
            layout final [.var tmp] target ctx)
          (Simulation.Interaction.bind
            (Yul.InteractionSemantics.evalArgs (sourceFuel + 1)
              args.reverse (some sourceProgram.contract) source)
            (fun result =>
              Yul.InteractionSemantics.call (sourceFuel + 1)
                result.2.reverse (some functionName)
                (some sourceProgram.contract) result.1))
          (Functions.InteractionSemantics.Block.openRun
            targetProgram.toFunctions ctx
            ((preArgs ++
              [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                Functions.Stmt.call [tmp] functionName lowerArgs]).length +
              targetBodyFuel + 2)
            { stmts :=
                preArgs ++
                  [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                    Functions.Stmt.call [tmp] functionName lowerArgs] }
            target)
      rw [Functions.InteractionSemantics.Block.openRun_append]
      apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
      intro sourceDone targetDone hDone
      cases hDone with
      | error hError =>
          exact Simulation.Interaction.ForwardRel.done (.error hError)
      | terminal hTerminal =>
          cases hTerminal with
          | stop hState =>
              exact Simulation.Interaction.ForwardRel.done
                (.terminal (.stop hState))
          | return_ hState =>
              exact Simulation.Interaction.ForwardRel.done
                (.terminal (.return_ hState))
          | selfdestruct hState =>
              exact Simulation.Interaction.ForwardRel.done
                (.terminal (.selfdestruct hState))
          | revert hState =>
              exact Simulation.Interaction.ForwardRel.done
                (.terminal (.revert hState))
      | @regular sourceAfter reversedValues targetAfter ctxAfter
          hStable hScoped hDomainAfter hExtendsAfter
          hScopeAfter hControlAfter hTargetScopeAfter =>
          have hTmpFresh : tmp ∉ argsState.used :=
            Fresh.not_mem_of_fresh? hFresh
          have hTmpLayout : tmp ∉ layout := by
            intro hName
            exact hTmpFresh (hLayoutArgs tmp hName)
          have hTmpNone : targetAfter.vars tmp = none :=
            hDomainAfter.lookup_none hTmpFresh
          have hInsertExtends :
              TargetExtends targetAfter.vars
                (Locals.Source.Store.insert targetAfter.vars tmp
                  Functions.Source.zero) :=
            TargetExtends.insert_fresh hTmpNone
          have hCallStable :
              FunctionsInteractionExpression.StableArgs lowerArgs
                (targetAfter.insert tmp Functions.Source.zero)
                reversedValues.reverse :=
            by
              simpa using hStable.reverse.mono
                (candidate :=
                  targetAfter.insert tmp Functions.Source.zero)
                hInsertExtends
          have hCallerRel :
              ScopedStateRel layout sourceAfter
                (targetAfter.insert tmp Functions.Source.zero) :=
            hScoped.insert_private hTmpLayout Functions.Source.zero
          have hValueLength :
              reversedValues.reverse.length = fn.params.length := by
            calc
              reversedValues.reverse.length = reversedValues.length := by simp
              _ = (lowerArgs.reverse).length := hStable.length
              _ = lowerArgs.length := by simp
              _ = args.length := hArgs.length_lowerArgs_eq
              _ = params.length := hArgCount
              _ = (identNames params).length := by
                simp [identNames_eq_self]
              _ = fn.params.length := by rw [hFnParams]
          obtain ⟨paramStore, hParamStore⟩ :=
            Functions.Source.Store.insertMany_exists_of_length
              (names := fn.params) (values := reversedValues.reverse)
              (store := Locals.Source.Store.empty) hValueLength
          have hFnSignature : (fn.returns ++ fn.params).Nodup := by
            simpa [hFnReturns, hFnParams, identNames_eq_self]
              using hSignature
          have hResultCount : fn.returns.length = 1 := by
            subst returns
            simp [hFnReturns, identNames_eq_self]
          have hEntry := ScopedStateRel.initcall hCallerRel.state
            hFnSignature hParamStore
          have hBodyRel := hBodyForward hLowerBody hBodyOk hReserved hBodyNames
            (by
              unfold FunctionsInteractionStaticCost.bodyBudget
              exact
                (FunctionsInteractionFuel.executionBudgetFor_le_global_at
                  (FunctionsInteractionStaticCost.program sourceProgram)
                  (FunctionsInteractionStaticCost.function_body_le_program_of_lookup
                    hLookup) (by omega)).trans hTargetBodyFuel)
            (by
              simpa [hFnParams, hFnReturns, identNames_eq_self,
                Functions.InteractionSemantics.stateModel,
                Locals.InteractionSemantics.stateModel,
                Locals.Source.Effectful.Ordinary.stateModel,
                Locals.Source.Effectful.StateModel.source,
                Locals.Source.Effectful.StateModel.withSource]
                using hEntry)
            (by
              simpa [hFnParams, hFnReturns, identNames_eq_self,
                Functions.InteractionSemantics.stateModel,
                Locals.InteractionSemantics.stateModel,
                Locals.Source.Effectful.Ordinary.stateModel,
                Locals.Source.Effectful.StateModel.source,
                Locals.Source.Effectful.StateModel.withSource] using
                (entryTargetDomain hParamStore hReserved))
          have hRunBody := FunctionsInteractionCall.runBodyForward
            (program := targetProgram.toFunctions)
            (targetBodyFuel := targetBodyFuel)
            (targetCaller :=
              targetAfter.insert tmp Functions.Source.zero)
            hParamStore hCallerRel hResultCount hBodyRel
            (by
              simp [hFnReturns, identNames_eq_self,
                Functions.InteractionSemantics.stateModel,
                Locals.InteractionSemantics.stateModel,
                Locals.Source.Effectful.Ordinary.stateModel,
                Locals.Source.Effectful.StateModel.source,
                Locals.Source.Effectful.StateModel.withSource])
          have hCallRun :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionCall.RunBodyDoneRel layout sourceAfter
                  (targetAfter.insert tmp Functions.Source.zero) 1)
                (Yul.InteractionSemantics.call (sourceFuel + 1)
                  reversedValues.reverse (some functionName)
                  (some sourceProgram.contract) sourceAfter)
                (Functions.InteractionSemantics.FunDef.openRunBody
                  targetProgram.toFunctions fn reversedValues.reverse
                  (targetBodyFuel + 1)
                  (targetAfter.insert tmp Functions.Source.zero)) := by
            rw [Yul.InteractionSemantics.Call.explicit_succ
              sourceFuel reversedValues.reverse functionName
              sourceProgram.contract params returns body sourceAfter hLookup]
            simpa [hFnParams, hFnReturns, identNames_eq_self] using hRunBody
          obtain ⟨hFinalUsed, _hTmpFresh⟩ :=
            Fresh.fresh?_components hFresh
          have hTargetCallScope :
              FunctionsInteractionControlRelation.TargetScopeWithin
                final.used
                { ctxAfter with scope := tmp :: ctxAfter.scope } := by
            intro name hName
            change name ∈ tmp :: ctxAfter.scope at hName
            rw [hFinalUsed]
            rcases List.mem_cons.mp hName with rfl | hName
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem tmp
                (hTargetScopeAfter name hName)
          have hCallStmt := FunctionsInteractionCall.callStmtForward
            (ctx := { ctxAfter with scope := tmp :: ctxAfter.scope })
            hFind hCallStable hFresh hLayoutArgs rfl hDomainAfter
            hExtendsAfter
            (Functions.Source.Ctx.ScopeExtends.cons ctxAfter tmp)
            (Functions.Source.Ctx.SameControl.scopeUpdate
              ctxAfter (tmp :: ctxAfter.scope))
            hTargetCallScope
            hCallRun (by rfl)
          have hSuffix := FunctionsInteractionCall.letCallBlockForward
            (ctx := ctxAfter) rfl hCallStmt
          have hSuffix' :=
            Simulation.Interaction.ForwardRel.mono hSuffix
              (fun _sourceDone _targetDone hDone =>
                FunctionsInteractionPreparedArgs.DoneRel.transport_entry
                  hScopeAfter hControlAfter hDone)
          have hResidual :
              preArgs.length + 2 + targetBodyFuel + 2 - preArgs.length =
              targetBodyFuel + 4 := by
            omega
          simp only
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.zero_add]
          rw [hResidual]
          simpa using hSuffix'

/-- Lift one compiler-selected internal call into the generic recursively
prepared expression-head interface. The body uses strictly smaller source
fuel; argument heads use the immediately smaller list fuel. -/
theorem headValueOfUncheckedFunctionCallLowering
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {bodyFuel targetFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {before after : Fresh.State} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {layout : List Functions.Name}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1
          (.Call (.inr functionName) args) = true)
    (hLowering : Expr.UncheckedFunctionCallLowering
      before functionName args pre lower after)
    (hNested : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (bodyFuel + 1) targetFuel
      (some sourceProgram.contract)
      targetProgram.toFunctions layout)
    (hBodyForward : BodyForwardAt profile sourceProgram targetProgram
      bodyFuel (targetFuel - pre.length - 2))
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (bodyFuel + 1) ≤ targetFuel - pre.length - 2)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    FunctionsInteractionPreparedArgs.HeadValueForward
      (bodyFuel + 3) targetFuel
      (.Call (.inr functionName) args) pre lower before after
      (some sourceProgram.contract) targetProgram.toFunctions layout := by
  intro _hLower source target ctx hRel hDomain hTargetScope
  have hFuelEq :
      pre.length + (targetFuel - pre.length - 2) + 2 = targetFuel := by
    omega
  have hNested' : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (bodyFuel + 1)
      (pre.length + (targetFuel - pre.length - 2) + 2)
      (some sourceProgram.contract) targetProgram.toFunctions layout := by
    rw [hFuelEq]
    exact hNested
  have hSelected := ofUncheckedFunctionCallLowering
    (sourceFuel := bodyFuel)
    (targetBodyFuel := targetFuel - pre.length - 2)
    (ctx := ctx) hDecomposition hProgramOk hExprOk hLowering
    hNested' hBodyForward hTargetBodyFuel hRel hDomain hTargetScope hLayout
  have hSingleton :=
    FunctionsInteractionPreparedArgs.singletonOfValues hSelected
  simpa [hFuelEq] using hSingleton

/-- A compiler-selected call head followed by the bounded-argument owner's
fresh spill binding. This is the call-family sibling of
`FunctionsInteractionPreparedPrimitive.boundPrimitive`. -/
theorem boundCall
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {bodyFuel targetFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {before after final : Fresh.State} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {tmp : Functions.Name}
    {layout : List Functions.Name}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1
          (.Call (.inr functionName) args) = true)
    (hLowering : Expr.UncheckedFunctionCallLowering
      before functionName args pre lower after)
    (hNested : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (bodyFuel + 1) targetFuel
      (some sourceProgram.contract)
      targetProgram.toFunctions layout)
    (hBodyForward : BodyForwardAt profile sourceProgram targetProgram
      bodyFuel (targetFuel - pre.length - 2))
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (bodyFuel + 1) ≤ targetFuel - pre.length - 2)
    (hLayoutBefore : ∀ name, name ∈ layout → name ∈ before.used)
    (hLayoutAfter : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    FunctionsInteractionPreparedArgs.BoundHeadForward
      (bodyFuel + 3) targetFuel
      (.Call (.inr functionName) args) pre lower before after final tmp
      (some sourceProgram.contract) targetProgram.toFunctions layout :=
  FunctionsInteractionPreparedArgs.bindHeadValue hLayoutAfter hTargetFuel
    (headValueOfUncheckedFunctionCallLowering
      hDecomposition hProgramOk hExprOk hLowering hNested hBodyForward
      hTargetBodyFuel hLayoutBefore hTargetFuel)

/-- Internal-call singleton evaluation is source-truncated below three list
fuel units. The `fuel = 2` case enters the expression but exhausts fuel before
evaluating its argument list. -/
theorem boundCall_lowFuel
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {before after final : Fresh.State} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {tmp : Functions.Name}
    {layout : List Functions.Name}
    (hFuel : fuel < 3) :
    FunctionsInteractionPreparedArgs.BoundHeadForward
      fuel targetFuel (.Call (.inr functionName) args)
      pre lower before after final tmp
      (some sourceProgram.contract) targetProgram.toFunctions layout := by
  by_cases hVeryLow : fuel < 2
  · exact FunctionsInteractionPreparedArgs.boundHead_lowFuel hVeryLow
  · have hFuelEq : fuel = 2 := by omega
    subst fuel
    intro _hLower _hFresh source target ctx _hRel _hDomain _hTargetScope
    rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
    rw [Yul.InteractionSemantics.EvalValues.internal_succ]
    have hArgsZero :
        Yul.InteractionSemantics.evalArgs 0 args.reverse
            (some sourceProgram.contract) source =
          Yul.InteractionSemantics.Primitive.fail source .OutOfFuel := by
      unfold Yul.InteractionSemantics.evalArgs
        Yul.Source.Canonical.evalArgs Yul.Source.Effectful.evalArgs
      rfl
    rw [hArgsZero]
    have hTruncated :
        Truncated
          ({ exception := .OutOfFuel, state := source } :
            Yul.InteractionSemantics.Failure) := by
      trivial
    simpa [Yul.InteractionSemantics.Primitive.fail] using
      (Simulation.Interaction.ForwardRel.truncated
        (doneRel := FunctionsInteractionPreparedArgs.DoneRel
          layout final [.var tmp] target ctx)
        (right := Functions.InteractionSemantics.Block.openRun
          targetProgram.toFunctions ctx targetFuel
          { stmts := pre ++ [.let_ tmp lower] } target)
        hTruncated)

/-- Exhaustive arbitrary-fuel dispatcher for a generated internal-call head.
Recursive argument and body premises are requested only at the exact smaller
source fuels exposed by the canonical evaluator. -/
theorem boundCallAtFuel
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {before after final : Fresh.State} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {tmp : Functions.Name}
    {layout : List Functions.Name}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1
          (.Call (.inr functionName) args) = true)
    (hLowering : Expr.UncheckedFunctionCallLowering
      before functionName args pre lower after)
    (hNested :
      ∀ argsFuel,
        fuel = argsFuel + 2 →
          FunctionsInteractionPreparedArgs.RecursiveBoundHeads
            profile sourceProgram argsFuel targetFuel
            (some sourceProgram.contract)
            targetProgram.toFunctions layout)
    (hBodies :
      ∀ bodyFuel,
        fuel = bodyFuel + 3 →
          BodyForwardAt profile sourceProgram targetProgram bodyFuel
            (targetFuel - pre.length - 2))
    (hBodyFuel :
      ∀ bodyFuel,
        fuel = bodyFuel + 3 →
          FunctionsInteractionStaticCost.programBudget
            sourceProgram (bodyFuel + 1) ≤ targetFuel - pre.length - 2)
    (hLayoutBefore : ∀ name, name ∈ layout → name ∈ before.used)
    (hLayoutAfter : ∀ name, name ∈ layout → name ∈ after.used)
    (hTargetFuel : pre.length + 1 < targetFuel) :
    FunctionsInteractionPreparedArgs.BoundHeadForward
      fuel targetFuel (.Call (.inr functionName) args)
      pre lower before after final tmp
      (some sourceProgram.contract) targetProgram.toFunctions layout := by
  by_cases hLow : fuel < 3
  · exact boundCall_lowFuel hLow
  · obtain ⟨bodyFuel, hFuel⟩ : ∃ bodyFuel, fuel = bodyFuel + 3 := by
      refine ⟨fuel - 3, ?_⟩
      omega
    subst fuel
    exact boundCall hDecomposition hProgramOk hExprOk hLowering
      (hNested (bodyFuel + 1) (by omega))
      (hBodies bodyFuel rfl) (hBodyFuel bodyFuel rfl)
      hLayoutBefore hLayoutAfter hTargetFuel

end FunctionsInteractionSelectedCall
end Yul
end EvmCompiler
