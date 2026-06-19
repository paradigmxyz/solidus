import EvmCompiler.Yul.FunctionsInteractionCall
import EvmCompiler.Yul.FunctionsCompilerArtifact
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
    ScopedStateRel (fn.returns ++ fn.params) source target →
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionCall.FunctionBodyDoneRel
        (fn.returns ++ fn.params))
      (Yul.InteractionSemantics.exec sourceFuel (.Block body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions
        (Functions.Source.Effectful.FunDef.bodyCtx fn)
        targetFuel fn.body target)

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
      (sourceFuel + 1) (pre.length + targetBodyFuel + 2)
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodyForward : BodyForwardAt profile sourceProgram targetProgram
      sourceFuel targetBodyFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedArgs.DoneRel
        layout final [lower] target)
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
      have hBodyOk :
          SolcValidation.StmtsOk? profile sourceProgram.contract
              ((Contract.functionEntries
                sourceProgram.contract).map Prod.fst)
              (fn.returns ++ fn.params) false false true body = true := by
        rw [hFnReturns, hFnParams]
        exact SolcValidation.programOkWith_function_bodyOk
          hProgramOk hLookup
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
          hArgs hBound hRel hDomain hLayout
          (by simp; omega)
      rw [show sourceFuel + 2 = (sourceFuel + 1) + 1 by omega,
        Yul.InteractionSemantics.EvalValues.internal_succ]
      change
        Simulation.Interaction.ForwardRel Truncated
          (FunctionsInteractionPreparedArgs.DoneRel
            layout final [.var tmp] target)
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
          hStable hScoped hDomainAfter hExtendsAfter =>
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
          have hBodyRel := hBodyForward hLowerBody hBodyOk hReserved
            (by
              simpa [hFnParams, hFnReturns, identNames_eq_self,
                Functions.InteractionSemantics.stateModel,
                Locals.InteractionSemantics.stateModel,
                Locals.Source.Effectful.Ordinary.stateModel,
                Locals.Source.Effectful.StateModel.source,
                Locals.Source.Effectful.StateModel.withSource]
                using hEntry)
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
          have hCallStmt := FunctionsInteractionCall.callStmtForward
            (ctx := { ctxAfter with scope := tmp :: ctxAfter.scope })
            hFind hCallStable hFresh hLayoutArgs rfl hDomainAfter
            hExtendsAfter hCallRun (by rfl)
          have hSuffix := FunctionsInteractionCall.letCallBlockForward
            (ctx := ctxAfter) rfl hCallStmt
          have hResidual :
              preArgs.length + 2 + targetBodyFuel + 2 - preArgs.length =
              targetBodyFuel + 4 := by
            omega
          simp only
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.zero_add]
          rw [hResidual]
          simpa using hSuffix

end FunctionsInteractionSelectedCall
end Yul
end EvmCompiler
