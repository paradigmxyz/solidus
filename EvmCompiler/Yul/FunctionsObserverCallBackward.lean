import EvmCompiler.Yul.FunctionsObserverCall
import EvmCompiler.Yul.FunctionsObserverExpressionBackward

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCallBackward

/-!
Backward adequacy for internal calls at the adjacent Yul-to-Functions pass.

The body artifact is indexed by the actual compiler-selected function and
target execution. Recursive construction is kept behind a target-fuel bound;
no public all-callee premise or alternative call interpreter is introduced.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

structure ReturnedBodyBackward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Functions.Program)
    (params returns : List EvmYul.Identifier)
    (body : List AstStmt)
    (fn : Functions.FunDef)
    (args : List Word)
    (bodyFuel : Nat)
    (sourceCaller : ObserverSemantics.SourceReplay.State transcript)
    (targetCaller : Functions.ObserverSemantics.State transcript) where
  paramStore : Locals.Source.Store
  bodyOutcome :
    Functions.Source.Effectful.Outcome
      (Functions.ObserverSemantics.State transcript)
  finalCtx : Functions.Source.Ctx
  paramsInserted :
    Functions.Source.Store.insertMany fn.params args
        Locals.Source.Store.empty =
      some paramStore
  targetRun :
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram (Functions.Source.Effectful.FunDef.bodyCtx fn)
        bodyFuel fn.body
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }) =
      .ok (bodyOutcome, finalCtx)
  mode :
    bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave
  sourceAfterBody : ObserverSemantics.SourceReplay.State transcript
  sourceFuel : Nat
  sourceRun :
    Yul.Source.Effectful.exec
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        sourceFuel (.Block body) (some sourceProgram.contract)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args))) =
      .ok sourceAfterBody
  relation :
    StateRelation.Replay.ScopedExactRel codeRel
      (fn.returns ++ fn.params)
      (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
      bodyOutcome.state

def RecursiveBodyBackward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {targetFuel : Nat} {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt} {fn : Functions.FunDef}
    {args : List Word} {paramStore : Locals.Source.Store}
    {sourceCaller : ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    {bodyOutcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {finalCtx : Functions.Source.Ctx},
    targetFuel < bound →
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries sourceProgram.contract))
          before body =
        some (fn.body, after) →
      fn.params = identNames params →
      fn.returns = identNames returns →
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore →
      StateRelation.Vars.NamesWithin before.used
        (fn.returns ++ fn.params) →
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true body =
        true →
      StateRelation.Replay.ScopedExactRel codeRel
        (fn.returns ++ fn.params)
        (sourceCaller.withSource
          (EvmYul.Yul.State.mkOk
            (sourceCaller.source.initcall params returns args)))
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }) →
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          targetFuel fn.body
          (targetCaller.withSource
            { shared := targetCaller.source.shared,
              vars :=
                Functions.Source.Store.initReturns fn.returns paramStore }) =
        .ok (bodyOutcome, finalCtx) →
      (bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave) →
      Nonempty
        (ReturnedBodyBackward contract transcript codeRel sourceProgram
          targetProgram.toFunctions params returns body fn args targetFuel
          sourceCaller targetCaller)

namespace ReturnedBodyBackward

theorem compose
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Functions.Program}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    {fn : Functions.FunDef}
    {args : List Word}
    {bodyFuel : Nat}
    {sourceCaller : ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    {account : EvmYul.Account .Yul}
    (returned :
      ReturnedBodyBackward contract transcript codeRel sourceProgram
        targetProgram params returns body fn args bodyFuel
        sourceCaller targetCaller)
    (hParams : fn.params = identNames params)
    (hReturns : fn.returns = identNames returns)
    (hAccount :
      sourceCaller.source.sharedState.accountMap.find?
          sourceCaller.source.executionEnv.codeOwner =
        some account)
    (hLookup :
      sourceProgram.contract.functions.lookup fn.name =
        some (.Def params returns body))
    (hCaller :
      StateRelation.Replay.Rel codeRel sourceCaller targetCaller) :
    ∃ returnValues,
      Yul.Source.Effectful.call
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (returned.sourceFuel + 1) args (some fn.name)
          (some sourceProgram.contract) sourceCaller =
        .ok
          (returned.sourceAfterBody.withSource
              ((returned.sourceAfterBody.source.reviveJump.overwrite?
                sourceCaller.source).setStore sourceCaller.source),
            returnValues) ∧
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram fn args (bodyFuel + 1) targetCaller =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            returned.bodyOutcome.state returnValues) ∧
      StateRelation.Replay.Rel codeRel
        (returned.sourceAfterBody.withSource
          ((returned.sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
        (returned.bodyOutcome.state.withSource
          { shared := returned.bodyOutcome.state.source.shared,
            vars := targetCaller.source.vars }) := by
  have hSourceLookup :
      ((some sourceProgram.contract).getD account.code).functions.lookup
          fn.name =
        some (.Def params returns body) := by
    simpa using hLookup
  have hSourceCall :=
    Yul.Source.Effectful.call_succ_of_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hAccount hSourceLookup returned.sourceRun
  have hReturnNames : fn.returns = returns := by
    simpa [identNames_eq_self] using hReturns
  have hTargetReturns :
      Functions.Source.Store.lookupMany fn.returns
          returned.bodyOutcome.state.source.vars =
        some
          (List.map returned.sourceAfterBody.source.lookup! returns) := by
    calc
      Functions.Source.Store.lookupMany fn.returns
            returned.bodyOutcome.state.source.vars =
          some
            (List.map returned.sourceAfterBody.source.lookup!
              fn.returns) :=
        StateRelation.Replay.lookupMany_of_scopedExact returned.relation
          (by
            intro name hMem
            exact List.mem_append_left fn.params hMem)
      _ =
          some
            (List.map returned.sourceAfterBody.source.lookup!
              returns) := by
        rw [hReturnNames]
  let returnValues :=
    List.map returned.sourceAfterBody.source.lookup! returns
  have hTargetBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram fn args (bodyFuel + 1) targetCaller =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            returned.bodyOutcome.state returnValues) := by
    exact
      Functions.Source.Effectful.FunDef.runBody_returned_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram returned.paramsInserted returned.targetRun
        returned.mode (by simpa [returnValues] using hTargetReturns) rfl
  refine ⟨returnValues, ?_, hTargetBody, ?_⟩
  · simpa [returnValues] using hSourceCall
  · exact
      StateRelation.Replay.restore_call hCaller returned.relation

end ReturnedBodyBackward

end FunctionsObserverCallBackward
end Yul
end EvmCompiler
