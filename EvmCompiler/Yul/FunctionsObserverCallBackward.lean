import EvmCompiler.Yul.FunctionsObserverCall
import EvmCompiler.Yul.FunctionsObserverExpressionBackward
import EvmCompiler.Yul.FunctionsObserverOutcome

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

structure HaltedBodyBackward
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
    (targetCaller finalTarget :
      Functions.ObserverSemantics.State transcript)
    (kind : Assembly.HaltKind) where
  paramStore : Locals.Source.Store
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
      .ok
        (Functions.Source.Effectful.Outcome.halt kind finalTarget,
          finalCtx)
  failure :
    Yul.Source.Effectful.Failure
      (ObserverSemantics.SourceReplay.State transcript)
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
      .error failure
  relation :
    FunctionsObserverOutcome.TerminalFailureRel codeRel failure
      (Functions.Source.Effectful.Outcome.halt kind finalTarget)

def RecursiveHaltedBodyBackward
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
    {targetCaller finalTarget :
      Functions.ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
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
        .ok
          (Functions.Source.Effectful.Outcome.halt kind finalTarget,
            finalCtx) →
      Nonempty
        (HaltedBodyBackward contract transcript codeRel sourceProgram
          targetProgram.toFunctions params returns body fn args targetFuel
          sourceCaller targetCaller finalTarget kind)

theorem callArgsBackwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {initial final : Fresh.State}
    {layout : List Name} {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : List (Locals.Expr 1)}
    {targetFuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal : Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    (hLowering :
      Expr.UncheckedCallArgsLowering initial args pre lower final)
    (hEligible :
      ∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr = true)
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardAt
        profile sourceContract contract transcript codeRel program
        codeOverride layout)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            finalCtx)) :
    ∃ sourceFuel,
      Nonempty
        (FunctionsObserverExpressionBackward.AlignedArgsBackward
          contract transcript codeRel program codeOverride sourceFuel
          initial final layout args pre lower source target targetFinal
          ctx finalCtx) := by
  cases hLowering with
  | empty =>
      obtain ⟨hOutcome, hCtx⟩ :=
        Functions.Source.Effectful.Block.runOpen_nil_ok
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hRun
      injection hOutcome with hTarget
      subst targetFinal
      subst finalCtx
      have hSource :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              1 [] codeOverride source =
            .ok (source, []) := by
        simp [Yul.Source.Effectful.evalArgs]
      let prepared :=
        FunctionsObserverExpression.PreparedArgs.empty
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) (program := program)
          (StateRelation.Replay.rel_of_scopedExact hRel)
          hDomain hScope
      exact
        ⟨1,
          ⟨source, [], hSource, ⟨prepared, hRel⟩, rfl, rfl⟩⟩
  | bound hNonempty hBound =>
      refine
        ⟨FunctionsObserverExpressionBackward.directArgsFuel args, ?_⟩
      exact
        FunctionsObserverExpressionBackward.boundArgsBackwardAt
          profile sourceContract contract transcript codeRel program
          codeOverride (by rfl) hBound hEligible hExpr hRel hDomain hScope
          hRun

theorem callArgsBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {initial final : Fresh.State}
    {layout : List Name} {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : List (Locals.Expr 1)}
    {targetFuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal : Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hLowering :
      Expr.UncheckedCallArgsLowering initial args pre lower final)
    (hEligible :
      ∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr = true)
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceContract contract transcript codeRel program
        codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            finalCtx)) :
    Nonempty
      (FunctionsObserverExpressionBackward.SomeAlignedArgsBackward
        contract transcript codeRel program codeOverride initial final
        layout args pre lower source target targetFinal ctx finalCtx) := by
  cases hLowering with
  | empty =>
      obtain ⟨hOutcome, hCtx⟩ :=
        Functions.Source.Effectful.Block.runOpen_nil_ok
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hRun
      injection hOutcome with hTarget
      subst targetFinal
      subst finalCtx
      have hSource :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              1 [] codeOverride source =
            .ok (source, []) := by
        simp [Yul.Source.Effectful.evalArgs]
      let prepared :=
        FunctionsObserverExpression.PreparedArgs.empty
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) (program := program)
          (StateRelation.Replay.rel_of_scopedExact hRel)
          hDomain hScope
      exact
        ⟨⟨1,
          ⟨source, [], hSource, ⟨prepared, hRel⟩, rfl, rfl⟩⟩⟩
  | bound hNonempty hBound =>
      exact
        FunctionsObserverExpressionBackward.boundArgsBackwardBelow
          profile sourceContract contract transcript codeRel program
          codeOverride bound hTargetFuel hBound hEligible hExpr hRel
          hDomain hScope hRun

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
      returnValues =
        List.map returned.sourceAfterBody.source.lookup! fn.returns ∧
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
  refine
    ⟨returnValues, ?_, hTargetBody,
      by simp [returnValues, hReturnNames], ?_⟩
  · simpa [returnValues] using hSourceCall
  · exact
      StateRelation.Replay.restore_call hCaller returned.relation

end ReturnedBodyBackward

private structure ReturnedCallCoreBackward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Functions.Program)
    (functionName : Name)
    (targets : List Name)
    (args : List AstExpr)
    (preArgs : List Functions.Stmt)
    (lowerArgs : List (Locals.Expr 1))
    (fresh : Fresh.State)
    (layout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) where
  sourceAfterArgs : ObserverSemantics.SourceReplay.State transcript
  argValues : List Word
  argsPrepared :
    FunctionsObserverExpression.ScopedPreparedArgs
      contract transcript codeRel targetProgram preArgs lowerArgs fresh
      layout sourceAfterArgs target ctx argValues
  fn : Functions.FunDef
  bodyFuel : Nat
  sourceAfterBody : ObserverSemantics.SourceReplay.State transcript
  body :
    FunctionsObserverCall.ReturnedBody contract transcript codeRel
      targetProgram fn argValues bodyFuel sourceAfterBody
      argsPrepared.prepared.prepared.finalTarget
  find :
    Functions.Source.FunList.find? functionName targetProgram.functions =
      some fn
  sourceAfterCall : ObserverSemantics.SourceReplay.State transcript
  sourceAfterCall_eq :
    sourceAfterCall =
      sourceAfterBody.withSource
        ((sourceAfterBody.source.reviveJump.overwrite?
          sourceAfterArgs.source).setStore sourceAfterArgs.source)
  returnValues : List Word
  sourceFuel : Nat
  sourceValuesRun :
    Yul.Source.Effectful.evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        sourceFuel (.Call (.inr functionName) args)
        (some sourceProgram.contract) source =
      .ok (sourceAfterCall, returnValues)
  sourceExprStmtRun :
    Yul.Source.Effectful.exec
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        (sourceFuel + 1)
        (.ExprStmtCall (.Call (.inr functionName) args))
        (some sourceProgram.contract) source =
      .ok
        (sourceAfterCall.withSource
          (sourceAfterCall.source.multifill [] returnValues))
  mappedReturnValues :
    List.map sourceAfterBody.source.lookup! fn.returns = returnValues
  returnLength : returnValues.length = targets.length

structure ReturnedCallBackward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Functions.Program)
    (functionName : Name)
    (targets : List Name)
    (args : List AstExpr)
    (preArgs : List Functions.Stmt)
    (lowerArgs : List (Locals.Expr 1))
    (fresh : Fresh.State)
    (layout finalLayout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target targetFinal : Functions.ObserverSemantics.State transcript)
    (ctx targetFinalCtx : Functions.Source.Ctx) where
  sourceFuel : Nat
  sourceAfterCall : ObserverSemantics.SourceReplay.State transcript
  returnValues : List Word
  sourceValuesRun :
    Yul.Source.Effectful.evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        sourceFuel (.Call (.inr functionName) args)
        (some sourceProgram.contract) source =
      .ok (sourceAfterCall, returnValues)
  sourceExprStmtRun :
    Yul.Source.Effectful.exec
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        (sourceFuel + 1)
        (.ExprStmtCall (.Call (.inr functionName) args))
        (some sourceProgram.contract) source =
      .ok
        (sourceAfterCall.withSource
          (sourceAfterCall.source.multifill [] returnValues))
  returned :
    FunctionsObserverCall.ScopedReturnedCall contract transcript codeRel
      targetProgram functionName targets preArgs lowerArgs fresh finalLayout
      (sourceAfterCall.withSource
        (sourceAfterCall.source.multifill targets returnValues))
      target ctx
  finalTarget_eq : returned.finalTarget = targetFinal
  finalCtx_eq : returned.finalCtx = targetFinalCtx

private theorem returnedCallCoreBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (bound : Nat)
    {targetFuel : Nat}
    {initial final : Fresh.State}
    {layout targets : List Name}
    {functionName : Name} {args : List AstExpr}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal :
      Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          targets.length (.Call (.inr functionName) args) =
        true)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering initial args
        preArgs lowerArgs final)
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceProgram.contract contract transcript codeRel
        targetProgram.toFunctions (some sourceProgram.contract) layout bound)
    (hBody :
      RecursiveBodyBackward contract transcript codeRel sourceProgram
        targetProgram profile bound)
    (hOwner :
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel
          { stmts :=
              preArgs ++
                [Functions.Stmt.call targets functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            targetFinalCtx)) :
    Nonempty
      (ReturnedCallCoreBackward contract transcript codeRel sourceProgram
        targetProgram.toFunctions functionName targets args preArgs lowerArgs
        final layout source target ctx) := by
  obtain ⟨params, returns, body, hLookup⟩ :=
    SolcValidation.exprOk_functionCall_lookup_exists hOk
  obtain
      ⟨targetAfterArgs, ctxAfterArgs, callBlockFuel,
        hArgsPre, hCallBlock, hCallBlockFuel⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_bounded_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hTarget
  obtain
      ⟨callFuel, hCallBlockEq, hCall⟩ :=
    Functions.Source.Effectful.Block.runOpen_singleton_regular_bounded_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hCallBlock
  obtain ⟨argsBackward⟩ :=
    callArgsBackwardBelow profile sourceProgram.contract contract transcript
      codeRel targetProgram.toFunctions (some sourceProgram.contract) bound
      hTargetFuel hArgsLowering
      (fun expr hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem
          (SolcValidation.exprsOk_of_exprOk_functionCall hOk hLookup)
          hMem)
      hExpr hRel hDomain hScope hArgsPre
  let argsExact := argsBackward.result
  have hArgsTarget :
      argsExact.prepared.prepared.prepared.finalTarget =
        targetAfterArgs :=
    argsExact.finalTarget_eq
  rw [← hArgsTarget] at hCall
  have hStableArgs :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs argsExact.prepared.prepared.prepared.finalTarget =
        .ok
          (argsExact.prepared.prepared.prepared.finalTarget,
            argsExact.values) :=
    argsExact.prepared.prepared.stable
      argsExact.prepared.prepared.prepared.finalTarget
      (StateRelation.Vars.TargetExtends.refl _)
  cases callFuel with
  | zero =>
      simp [Functions.Source.Effectful.Stmt.run,
        Functions.Source.invalid, Structured.invalid] at hCall
  | succ callPrevious =>
      have hFinalCtx : targetFinalCtx = ctxAfterArgs := by
        rcases
            Functions.Source.Effectful.Stmt.run_call_cases
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hCall with
          hRegular | hHalt
        · rcases hRegular with ⟨sourceFinal, hOutcome, hCtx⟩
          exact hCtx
        · rcases hHalt with ⟨kind, sourceFinal, hOutcome, hCtx⟩
          cases hOutcome
      rw [hFinalCtx] at hCall
      cases callPrevious with
      | zero =>
          obtain
              ⟨stateAfterArgs, argValues, targetFn, stateAfterCall,
                returnValues, returnStore, hTargets, hTargetArgs, hFind,
                hBodyZero, hAssign, hCallFinal⟩ :=
            Functions.Source.Effectful.Stmt.call_regular_parts
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (ctx := ctxAfterArgs)
              (fuel := 0) (targets := targets)
              (functionName := functionName) (args := lowerArgs)
              (source :=
                argsExact.prepared.prepared.prepared.finalTarget)
              (sourceAfter := targetFinal)
              (by simpa using hCall)
          simp [Functions.Source.Effectful.Control.FunDef.runBody,
            Functions.Source.invalid, Structured.invalid] at hBodyZero
      | succ bodyFuel =>
          obtain
              ⟨stateAfterArgs, argValues, targetFn, stateAfterCall,
                returnValues, returnStore, paramStore, bodyOutcome,
                bodyCtx, hTargets, hTargetArgs, hFind, hParamsInserted,
                hBodyRun, hMode, hTargetReturns, hBodyState,
                hAssign, hCallFinal⟩ :=
            Functions.Source.Effectful.Stmt.call_regular_body_parts
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (ctx := ctxAfterArgs)
              (fuel := bodyFuel) (targets := targets)
              (functionName := functionName) (args := lowerArgs)
              (source :=
                argsExact.prepared.prepared.prepared.finalTarget)
              (sourceAfter := targetFinal)
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using hCall)
          change
            Functions.Source.Effectful.ArgList.Control.eval
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                lowerArgs argsExact.prepared.prepared.prepared.finalTarget =
              .ok
                (argsExact.prepared.prepared.prepared.finalTarget,
                  argsExact.values) at hStableArgs
          rw [hStableArgs] at hTargetArgs
          have hArgsPair := Except.ok.inj hTargetArgs
          injection hArgsPair with hStateAfterArgs hArgValues
          subst stateAfterArgs
          subst argValues
          obtain
              ⟨fnBefore, fnAfter, compiledFn, hPrefix, hCompiledFind,
                hFnName, hFnParams, hFnReturns, hLowerBody, hReserved⟩ :=
            hDecomposition.findFunction_parts hLookup
          rw [hFind] at hCompiledFind
          injection hCompiledFind with hFnEq
          subst compiledFn
          have hBodyFuelLt : bodyFuel < bound := by
            omega
          obtain ⟨hReturnCount, hArgCount, hSignature⟩ :=
            SolcValidation.programOkWith_functionCall_partsN
              hProgramOk hOk hLookup
          have hArgsLength :
              argsExact.values.length = targetFn.params.length := by
            have hEvaluatedLength :=
              Yul.Source.Effectful.evalArgs_ok_length
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                argsExact.sourceRun
            rw [hFnParams]
            simpa [identNames, hArgCount] using hEvaluatedLength
          have hEntry :
              StateRelation.Replay.ScopedExactRel codeRel
                (targetFn.returns ++ targetFn.params)
                (argsExact.sourceFinal.withSource
                  (EvmYul.Yul.State.mkOk
                    (argsExact.sourceFinal.source.initcall
                      params returns argsExact.values)))
                (argsExact.prepared.prepared.prepared.finalTarget.withSource
                  { shared :=
                      argsExact.prepared.prepared.prepared.finalTarget.source.shared,
                    vars :=
                      Functions.Source.Store.initReturns
                        targetFn.returns paramStore }) := by
            have hSignature' : (returns ++ params).Nodup := by
              simpa [identNames_eq_self] using hSignature
            have hParamStore' :
                Functions.Source.Store.insertMany params argsExact.values
                    Locals.Source.Store.empty =
                  some paramStore := by
              simpa [hFnParams, identNames_eq_self] using hParamsInserted
            have hEntryBase :=
              StateRelation.Replay.scopedExact_initcall
                (params := params) (returns := returns)
                (args := argsExact.values) (paramStore := paramStore)
                (StateRelation.Replay.rel_of_scopedExact
                  argsExact.prepared.relation)
                hSignature' hParamStore'
            simpa [hFnParams, hFnReturns, identNames_eq_self] using
              hEntryBase
          have hBodyOk :
              SolcValidation.StmtsOk? profile sourceProgram.contract
                  ((Contract.functionEntries
                    sourceProgram.contract).map Prod.fst)
                  (targetFn.returns ++ targetFn.params)
                  false false true body =
                true := by
            rw [hFnReturns, hFnParams]
            exact
              SolcValidation.programOkWith_function_bodyOk
                hProgramOk hLookup
          have hBodyNames :
              StateRelation.Vars.NamesWithin fnBefore.used
                (Stmt.List.names body) := by
            intro candidate hMem
            apply hPrefix candidate
            change candidate ∈ Contract.names sourceProgram.contract
            exact
              (Contract.function_names_mem_names_of_lookup hLookup).2
                candidate
                (by simp [FunctionDefinition.names, hMem])
          obtain ⟨returned⟩ :=
            hBody hBodyFuelLt hLowerBody hFnParams hFnReturns
              hParamsInserted hReserved hBodyNames hBodyOk hEntry
              hBodyRun hMode
          have hAfterArgsOwner :=
            ObserverSafety.SafeSemantics.evalArgs_preservesOwner
              contract transcript hOwner argsExact.sourceRun
          unfold Yul.Source.Effectful.OwnerAvailable at hAfterArgsOwner
          rcases argsExact.prepared.relation.2 with
            ⟨sourceShared, sourceVars, hSourceOk, _hShared,
              _hVars, _hDomain⟩
          have hSharedOwner :
              ∃ account,
                sourceShared.accountMap.find?
                    sourceShared.executionEnv.codeOwner =
                  some account := by
            change
              Yul.Source.Effectful.ActiveOwnerAvailable
                argsExact.sourceFinal.source at hAfterArgsOwner
            rw [hSourceOk] at hAfterArgsOwner
            simpa [Yul.Source.Effectful.ActiveOwnerAvailable,
              Yul.Source.Effectful.activeShared?] using hAfterArgsOwner
          obtain ⟨account, hSharedAccount⟩ := hSharedOwner
          have hAccount :
              argsExact.sourceFinal.source.sharedState.accountMap.find?
                  argsExact.sourceFinal.source.executionEnv.codeOwner =
                some account := by
            rw [hSourceOk]
            exact hSharedAccount
          have hCallerRel :
              StateRelation.Replay.Rel codeRel argsExact.sourceFinal
                argsExact.prepared.prepared.prepared.finalTarget :=
            StateRelation.Replay.rel_of_scopedExact
              argsExact.prepared.relation
          obtain
              ⟨sourceReturnValues, hSourceCall, hTargetBody,
                hMappedReturnValues, hRestoredRel⟩ :=
            returned.compose hFnReturns hAccount
              (by
                rw [hFnName]
                exact hLookup)
              hCallerRel
          have hActualTargetBody :
              Functions.Source.Effectful.FunDef.runBody
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions targetFn argsExact.values
                  (bodyFuel + 1)
                  argsExact.prepared.prepared.prepared.finalTarget =
                .ok
                  (Functions.Source.Effectful.CallResult.returned
                    stateAfterCall returnValues) := by
            exact
              Functions.Source.Effectful.FunDef.runBody_returned_of_parts
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions hParamsInserted hBodyRun hMode
                hTargetReturns hBodyState
          have hTargetBodyEq :
              sourceReturnValues = returnValues := by
            rw [hActualTargetBody] at hTargetBody
            have hCallResult := Except.ok.inj hTargetBody
            injection hCallResult with hStateEq hValuesEq
            exact hValuesEq.symm
          let bodyForward :
              FunctionsObserverCall.ReturnedBody contract transcript codeRel
                targetProgram.toFunctions targetFn argsExact.values bodyFuel
                returned.sourceAfterBody
                argsExact.prepared.prepared.prepared.finalTarget :=
            { paramStore := returned.paramStore
              bodyOutcome := returned.bodyOutcome
              finalCtx := returned.finalCtx
              params := returned.paramsInserted
              run := returned.targetRun
              mode := returned.mode
              relation := returned.relation }
          let restoredSource :=
            returned.sourceAfterBody.withSource
              ((returned.sourceAfterBody.source.reviveJump.overwrite?
                argsExact.sourceFinal.source).setStore
                  argsExact.sourceFinal.source)
          let commonFuel :=
            max argsBackward.sourceFuel (returned.sourceFuel + 1)
          have hArgsSource :
              Yul.Source.Effectful.evalArgs
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  commonFuel args.reverse (some sourceProgram.contract)
                  source =
                .ok
                  (argsExact.sourceFinal, argsExact.values.reverse) :=
            Yul.Source.Effectful.evalArgs_mono
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
                contract transcript)
              (Nat.le_max_left _ _) argsExact.sourceRun
          have hCallSource :
              Yul.Source.Effectful.call
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  commonFuel argsExact.values (some functionName)
                  (some sourceProgram.contract) argsExact.sourceFinal =
                .ok (restoredSource, returnValues) := by
            rw [hTargetBodyEq] at hSourceCall
            exact
              Yul.Source.Effectful.call_mono
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
                  contract transcript)
                (Nat.le_max_right _ _)
                (by simpa [hFnName, restoredSource] using hSourceCall)
          have hSourceValues :
              Yul.Source.Effectful.evalValues
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (commonFuel + 1)
                  (.Call (.inr functionName) args)
                  (some sourceProgram.contract) source =
                .ok (restoredSource, returnValues) := by
            simp only [Yul.Source.Effectful.evalValues, hArgsSource]
            simpa using hCallSource
          have hArgsExec :
              Yul.Source.Effectful.evalArgs
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (commonFuel + 1) args.reverse
                  (some sourceProgram.contract) source =
                .ok
                  (argsExact.sourceFinal, argsExact.values.reverse) :=
            Yul.Source.Effectful.evalArgs_mono
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
                contract transcript)
              (Nat.le_succ commonFuel) hArgsSource
          have hSourceExprStmt :
              Yul.Source.Effectful.exec
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (commonFuel + 2)
                  (.ExprStmtCall (.Call (.inr functionName) args))
                  (some sourceProgram.contract) source =
                .ok
                  (restoredSource.withSource
                    (restoredSource.source.multifill [] returnValues)) :=
            Yul.Source.Effectful.exec_expr_function_of_parts
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hArgsExec (by simpa using hCallSource)
          have hMapped :
              List.map returned.sourceAfterBody.source.lookup!
                  targetFn.returns =
                returnValues := by
            rw [← hMappedReturnValues, hTargetBodyEq]
          have hReturnLength :
              returnValues.length = targets.length := by
            calc
              returnValues.length =
                  sourceReturnValues.length := by
                    rw [hTargetBodyEq]
              _ = targetFn.returns.length := by
                    rw [hMappedReturnValues]
                    simp
              _ = returns.length := by
                    rw [hFnReturns, identNames_eq_self]
              _ = targets.length := hReturnCount.symm
          exact
            ⟨{ sourceAfterArgs := argsExact.sourceFinal
               argValues := argsExact.values
               argsPrepared := argsExact.prepared
               fn := targetFn
               bodyFuel := bodyFuel
               sourceAfterBody := returned.sourceAfterBody
               body := bodyForward
               find := hFind
               sourceAfterCall := restoredSource
               sourceAfterCall_eq := rfl
               returnValues := returnValues
               sourceFuel := commonFuel + 1
               sourceValuesRun := hSourceValues
               sourceExprStmtRun := by
                 simpa [Nat.add_assoc] using hSourceExprStmt
               mappedReturnValues := hMapped
               returnLength := hReturnLength }⟩

theorem returnedCallBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (bound : Nat)
    {targetFuel : Nat}
    {initial final : Fresh.State}
    {layout targets : List Name}
    {functionName : Name} {args : List AstExpr}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal :
      Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          targets.length (.Call (.inr functionName) args) =
        true)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering initial args
        preArgs lowerArgs final)
    (hTargetsNodup : targets.Nodup)
    (hTargetsVisible : ∀ name, name ∈ targets → name ∈ layout)
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceProgram.contract contract transcript codeRel
        targetProgram.toFunctions (some sourceProgram.contract) layout bound)
    (hBody :
      RecursiveBodyBackward contract transcript codeRel sourceProgram
        targetProgram profile bound)
    (hOwner :
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel
          { stmts :=
              preArgs ++
                [Functions.Stmt.call targets functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            targetFinalCtx)) :
    Nonempty
      (ReturnedCallBackward contract transcript codeRel sourceProgram
        targetProgram.toFunctions functionName targets args preArgs lowerArgs
        final layout layout source target targetFinal ctx targetFinalCtx) := by
  obtain ⟨core⟩ :=
    returnedCallCoreBackwardBelow profile sourceProgram targetProgram
      hDecomposition contract transcript codeRel bound hTargetFuel hProgramOk
      hOk hArgsLowering hExpr hBody hOwner hRel hDomain hScope hTarget
  obtain ⟨returned⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofReturnedBody
      core.argsPrepared hTargetsNodup hTargetsVisible core.find core.body
      core.mappedReturnValues core.returnLength rfl
  have returned' :
      FunctionsObserverCall.ScopedReturnedCall contract transcript codeRel
        targetProgram.toFunctions functionName targets preArgs lowerArgs
        final layout
        (core.sourceAfterCall.withSource
          (core.sourceAfterCall.source.multifill
            targets core.returnValues))
        target ctx := by
    simpa [core.sourceAfterCall_eq] using returned
  obtain ⟨returnedFuel, hReturnedRun⟩ := returned'.run
  have hAligned :=
    Functions.Source.Effectful.Block.runOpen_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hReturnedRun hTarget
  have hFinalTarget : returned'.finalTarget = targetFinal := by
    have hOutcome := congrArg Prod.fst hAligned
    injection hOutcome
  exact
    ⟨{ sourceFuel := core.sourceFuel
       sourceAfterCall := core.sourceAfterCall
       returnValues := core.returnValues
       sourceValuesRun := core.sourceValuesRun
       sourceExprStmtRun := core.sourceExprStmtRun
       returned := returned'
       finalTarget_eq := hFinalTarget
       finalCtx_eq := congrArg Prod.snd hAligned }⟩

theorem returnedCallFreshBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (bound : Nat)
    {targetFuel : Nat}
    {initial final : Fresh.State}
    {layout targets : List Name}
    {functionName : Name} {args : List AstExpr}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal :
      Functions.ObserverSemantics.State transcript}
    {ctx targetFinalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          targets.length (.Call (.inr functionName) args) =
        true)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering initial args
        preArgs lowerArgs final)
    (hTargetsNodup : targets.Nodup)
    (hTargetsFresh : ∀ name, name ∈ targets → name ∉ layout)
    (hTargetsContain :
      ∀ name, name ∈ targets →
        target.source.vars.contains name = true)
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceProgram.contract contract transcript codeRel
        targetProgram.toFunctions (some sourceProgram.contract) layout bound)
    (hBody :
      RecursiveBodyBackward contract transcript codeRel sourceProgram
        targetProgram profile bound)
    (hOwner :
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hTarget :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel
          { stmts :=
              preArgs ++
                [Functions.Stmt.call targets functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            targetFinalCtx)) :
    Nonempty
      (ReturnedCallBackward contract transcript codeRel sourceProgram
        targetProgram.toFunctions functionName targets args preArgs lowerArgs
        final layout (targets ++ layout) source target targetFinal ctx
        targetFinalCtx) := by
  obtain ⟨core⟩ :=
    returnedCallCoreBackwardBelow profile sourceProgram targetProgram
      hDecomposition contract transcript codeRel bound hTargetFuel hProgramOk
      hOk hArgsLowering hExpr hBody hOwner hRel hDomain hScope hTarget
  have hTargetsContainAfter :
      ∀ name, name ∈ targets →
        core.argsPrepared.prepared.prepared.finalTarget.source.vars.contains
            name =
          true := by
    intro name hMem
    cases hLookup : target.source.vars name with
    | none =>
        have hContains := hTargetsContain name hMem
        simp [Locals.Source.Store.contains, hLookup] at hContains
    | some value =>
        have hFinalLookup :
            core.argsPrepared.prepared.prepared.finalTarget.source.vars name =
              some value :=
          core.argsPrepared.prepared.prepared.varsExtends
            name value hLookup
        simp [Locals.Source.Store.contains, hFinalLookup]
  obtain ⟨returned⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofReturnedBodyFresh
      core.argsPrepared hTargetsNodup hTargetsFresh hTargetsContainAfter
      core.find core.body core.mappedReturnValues core.returnLength rfl
  have returned' :
      FunctionsObserverCall.ScopedReturnedCall contract transcript codeRel
        targetProgram.toFunctions functionName targets preArgs lowerArgs
        final (targets ++ layout)
        (core.sourceAfterCall.withSource
          (core.sourceAfterCall.source.multifill
            targets core.returnValues))
        target ctx := by
    simpa [core.sourceAfterCall_eq] using returned
  obtain ⟨returnedFuel, hReturnedRun⟩ := returned'.run
  have hAligned :=
    Functions.Source.Effectful.Block.runOpen_success_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hReturnedRun hTarget
  have hFinalTarget : returned'.finalTarget = targetFinal := by
    have hOutcome := congrArg Prod.fst hAligned
    injection hOutcome
  exact
    ⟨{ sourceFuel := core.sourceFuel
       sourceAfterCall := core.sourceAfterCall
       returnValues := core.returnValues
       sourceValuesRun := core.sourceValuesRun
       sourceExprStmtRun := core.sourceExprStmtRun
       returned := returned'
       finalTarget_eq := hFinalTarget
       finalCtx_eq := congrArg Prod.snd hAligned }⟩

theorem boundFunctionBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (bound : Nat)
    {targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {functionName : Name} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    {value : Word}
    (hTargetFuel : targetFuel < bound)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1
          (.Call (.inr functionName) args) =
        true)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before
          (.Call (.inr functionName) args) =
        some (pre, lower, after))
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceProgram.contract contract transcript codeRel
        targetProgram.toFunctions (some sourceProgram.contract) layout bound)
    (hBody :
      RecursiveBodyBackward contract transcript codeRel sourceProgram
        targetProgram profile bound)
    (hOwner :
      Yul.Source.Effectful.OwnerAvailable
        (ObserverSemantics.SourceReplay.stateModel transcript) source)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hPre :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular preTarget,
            finalCtx))
    (hTarget :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower preTarget =
        .ok (evalTarget, [value])) :
    Nonempty
      (FunctionsObserverExpressionBackward.SomeAlignedValueBackward
        contract transcript codeRel targetProgram.toFunctions
        (some sourceProgram.contract) before after layout
        (.Call (.inr functionName) args) pre lower source target preTarget
        evalTarget ctx finalCtx value) := by
  obtain ⟨params, returns, body, hLookup⟩ :=
    SolcValidation.exprOk_functionCall_lookup_exists hOk
  obtain
      ⟨argsFresh, tmp, preArgs, lowerArgs,
        hArgsLowering, hFresh, rfl, rfl⟩ :=
    (Expr.uncheckedFunctionCallLowering_of_lower1Unchecked? hLower).parts
  obtain
      ⟨targetAfterArgs, ctxAfterArgs, suffixFuel,
        hArgsPre, hSuffix, hSuffixFuel⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_regular_bounded_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions
      (left := preArgs)
      (right :=
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
          Functions.Stmt.call [tmp] functionName lowerArgs])
      hPre
  obtain
      ⟨emptyFinal, emptyCtx, targetWithZero, zeroCtx,
        emptyFuel, zeroFuel, callFuel,
        hEmpty, hZero, hCall, hCallFuel⟩ :=
    Functions.Source.Effectful.Block.runOpen_append_two_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions
      (prefixStmts := [])
      hSuffix
  obtain ⟨hEmptyOutcome, hEmptyCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_nil_ok
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hEmpty
  injection hEmptyOutcome with hEmptyFinal
  subst emptyFinal
  subst emptyCtx
  obtain
      ⟨targetAfterZeroEval, zeroValue, hZeroEval,
        hTargetWithZero, hZeroCtx⟩ :=
    Functions.Source.Effectful.Stmt.run_let_regular_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      targetProgram.toFunctions hZero
  obtain ⟨hAfterZero, hZeroValues⟩ :=
    Functions.Source.Effectful.Expr.eval_lit_ok_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hZeroEval
  subst targetAfterZeroEval
  injection hZeroValues with hZeroValue
  subst zeroValue
  subst targetWithZero
  subst zeroCtx
  obtain ⟨argsBackward⟩ :=
    callArgsBackwardBelow profile sourceProgram.contract contract transcript
      codeRel targetProgram.toFunctions (some sourceProgram.contract) bound
      hTargetFuel hArgsLowering
      (fun expr hMem =>
        SolcValidation.exprOk_of_exprsOk_of_mem
          (SolcValidation.exprsOk_of_exprOk_functionCall hOk hLookup)
          hMem)
      hExpr hRel hDomain hScope hArgsPre
  let argsExact := argsBackward.result
  have hArgsTarget :
      argsExact.prepared.prepared.prepared.finalTarget =
        targetAfterArgs :=
    argsExact.finalTarget_eq
  have hArgsCtx :
      argsExact.prepared.prepared.prepared.finalCtx =
        ctxAfterArgs :=
    argsExact.finalCtx_eq
  have hNotMem : tmp ∉ argsFresh.used :=
    Fresh.not_mem_of_fresh? hFresh
  have hTargetHidden :
      argsExact.prepared.prepared.prepared.finalTarget.source.vars tmp =
        none :=
    argsExact.prepared.prepared.prepared.domain.lookup_none hNotMem
  let expectedTargetCaller :=
    argsExact.prepared.prepared.prepared.finalTarget.withSource
      (argsExact.prepared.prepared.prepared.finalTarget.source.insert
        tmp Functions.Source.zero)
  have hActualCaller : expectedTargetCaller =
      targetAfterArgs.withSource
        (targetAfterArgs.source.insert tmp Functions.Source.zero) := by
    simp [expectedTargetCaller, hArgsTarget]
  have hZeroExtends :
      StateRelation.Vars.TargetExtends
        argsExact.prepared.prepared.prepared.finalTarget.source.vars
        expectedTargetCaller.source.vars := by
    dsimp [expectedTargetCaller]
    exact StateRelation.Vars.TargetExtends.insert_fresh hTargetHidden
  have hStableArgs :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs expectedTargetCaller =
        .ok (expectedTargetCaller, argsExact.values) :=
    argsExact.prepared.prepared.stable expectedTargetCaller hZeroExtends
  let callCtx : Functions.Source.Ctx :=
    { ctxAfterArgs with scope := tmp :: ctxAfterArgs.scope }
  have hCall' :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetProgram.toFunctions callCtx callFuel
          (Functions.Stmt.call [tmp] functionName lowerArgs)
          expectedTargetCaller =
        .ok
          (Functions.Source.Effectful.Outcome.regular preTarget,
            finalCtx) := by
    simpa [callCtx, expectedTargetCaller, hArgsTarget] using hCall
  cases callFuel with
  | zero =>
      simp [Functions.Source.Effectful.Stmt.run,
        Functions.Source.invalid, Structured.invalid] at hCall'
  | succ callPrevious =>
      have hFinalCtx : finalCtx = callCtx := by
        rcases
            Functions.Source.Effectful.Stmt.run_call_cases
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hCall' with
          hRegular | hHalt
        · rcases hRegular with ⟨sourceFinal, hOutcome, hCtx⟩
          exact hCtx
        · rcases hHalt with ⟨kind, sourceFinal, hOutcome, hCtx⟩
          cases hOutcome
      subst finalCtx
      cases callPrevious with
      | zero =>
          obtain
              ⟨stateAfterArgs, argValues, targetFn, stateAfterCall,
                returnValues, returnStore, hTargets, hTargetArgs, hFind,
                hBodyZero, hAssign, hCallFinal⟩ :=
            Functions.Source.Effectful.Stmt.call_regular_parts
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (ctx := callCtx) (fuel := 0)
              (targets := [tmp]) (functionName := functionName)
              (args := lowerArgs) (source := expectedTargetCaller)
              (sourceAfter := preTarget)
              (by simpa using hCall')
          simp [Functions.Source.Effectful.Control.FunDef.runBody,
            Functions.Source.invalid, Structured.invalid] at hBodyZero
      | succ bodyFuel =>
          obtain
              ⟨stateAfterArgs, argValues, targetFn, stateAfterCall,
                returnValues, returnStore, paramStore, bodyOutcome,
                bodyCtx, hTargets, hTargetArgs, hFind, hParamsInserted,
                hBodyRun, hMode, hTargetReturns, hBodyState,
                hAssign, hCallFinal⟩ :=
            Functions.Source.Effectful.Stmt.call_regular_body_parts
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (ctx := callCtx) (fuel := bodyFuel)
              (targets := [tmp]) (functionName := functionName)
              (args := lowerArgs) (source := expectedTargetCaller)
              (sourceAfter := preTarget)
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using hCall')
          change
            Functions.Source.Effectful.ArgList.Control.eval
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                lowerArgs expectedTargetCaller =
              .ok (expectedTargetCaller, argsExact.values) at hStableArgs
          rw [hStableArgs] at hTargetArgs
          have hArgsPair := Except.ok.inj hTargetArgs
          injection hArgsPair with hStateAfterArgs hArgValues
          subst stateAfterArgs
          subst argValues
          obtain
              ⟨fnBefore, fnAfter, compiledFn, hPrefix, hCompiledFind,
                hFnName, hFnParams, hFnReturns, hLowerBody, hReserved⟩ :=
            hDecomposition.findFunction_parts hLookup
          rw [hFind] at hCompiledFind
          injection hCompiledFind with hFnEq
          subst compiledFn
          have hBodyFuelLt : bodyFuel < bound := by
            have hCallFuelLe :
                bodyFuel + 2 + 2 ≤ targetFuel := by
              exact
                le_trans
                  (by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hCallFuel)
                  hSuffixFuel
            omega
          obtain ⟨hArgCount, hSignature, returnName, hReturns⟩ :=
            SolcValidation.programOkWith_functionCall_parts
              hProgramOk hOk hLookup
          subst returns
          have hArgsLength :
              argsExact.values.length = targetFn.params.length := by
            have hEvaluatedLength :=
              Yul.Source.Effectful.evalArgs_ok_length
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                argsExact.sourceRun
            rw [hFnParams]
            simpa [identNames, hArgCount] using hEvaluatedLength
          have hSourceHidden :
              argsExact.sourceFinal.source.lookup? tmp = none :=
            StateRelation.Replay.source_lookup_none_of_targetDomainWithin
              argsExact.prepared.prepared.prepared.rel
              argsExact.prepared.prepared.prepared.domain hNotMem
          have hCallerRel :
              StateRelation.Replay.Rel codeRel argsExact.sourceFinal
                expectedTargetCaller := by
            dsimp [expectedTargetCaller]
            exact
              StateRelation.Replay.insert_target_hidden
                argsExact.prepared.prepared.prepared.rel hSourceHidden
          have hEntry :
              StateRelation.Replay.ScopedExactRel codeRel
                (targetFn.returns ++ targetFn.params)
                (argsExact.sourceFinal.withSource
                  (EvmYul.Yul.State.mkOk
                    (argsExact.sourceFinal.source.initcall
                      params [returnName] argsExact.values)))
                (expectedTargetCaller.withSource
                  { shared := expectedTargetCaller.source.shared,
                    vars :=
                      Functions.Source.Store.initReturns
                        targetFn.returns paramStore }) := by
            have hSignature' : ([returnName] ++ params).Nodup := by
              simpa [identNames_eq_self] using hSignature
            have hParamStore' :
                Functions.Source.Store.insertMany params argsExact.values
                    Locals.Source.Store.empty =
                  some paramStore := by
              simpa [hFnParams, identNames_eq_self] using hParamsInserted
            have hEntryBase :=
              StateRelation.Replay.scopedExact_initcall
                (params := params)
                (returns := [returnName])
                (args := argsExact.values)
                (paramStore := paramStore)
                hCallerRel hSignature' hParamStore'
            simpa [hFnParams, hFnReturns, identNames_eq_self] using
              hEntryBase
          have hBodyOk :
              SolcValidation.StmtsOk? profile sourceProgram.contract
                  ((Contract.functionEntries
                    sourceProgram.contract).map Prod.fst)
                  (targetFn.returns ++ targetFn.params)
                  false false true body =
                true := by
            rw [hFnReturns, hFnParams]
            exact
              SolcValidation.programOkWith_function_bodyOk
                hProgramOk hLookup
          have hBodyNames :
              StateRelation.Vars.NamesWithin fnBefore.used
                (Stmt.List.names body) := by
            intro candidate hMem
            apply hPrefix candidate
            change candidate ∈ Contract.names sourceProgram.contract
            exact
              (Contract.function_names_mem_names_of_lookup hLookup).2
                candidate
                (by simp [FunctionDefinition.names, hMem])
          obtain ⟨returned⟩ :=
            hBody hBodyFuelLt hLowerBody hFnParams hFnReturns
              hParamsInserted hReserved hBodyNames hBodyOk hEntry
              hBodyRun hMode
          have hAfterArgsOwner :=
            ObserverSafety.SafeSemantics.evalArgs_preservesOwner
              contract transcript hOwner argsExact.sourceRun
          unfold Yul.Source.Effectful.OwnerAvailable at hAfterArgsOwner
          rcases argsExact.prepared.relation.2 with
            ⟨sourceShared, sourceVars, hSourceOk, _hShared,
              _hVars, _hDomain⟩
          have hSharedOwner :
              ∃ account,
                sourceShared.accountMap.find?
                    sourceShared.executionEnv.codeOwner =
                  some account := by
            change
              Yul.Source.Effectful.ActiveOwnerAvailable
                argsExact.sourceFinal.source at hAfterArgsOwner
            rw [hSourceOk] at hAfterArgsOwner
            simpa [Yul.Source.Effectful.ActiveOwnerAvailable,
              Yul.Source.Effectful.activeShared?] using hAfterArgsOwner
          obtain ⟨account, hSharedAccount⟩ := hSharedOwner
          have hAccount :
              argsExact.sourceFinal.source.sharedState.accountMap.find?
                  argsExact.sourceFinal.source.executionEnv.codeOwner =
                some account := by
            rw [hSourceOk]
            exact hSharedAccount
          obtain
              ⟨sourceReturnValues, hSourceCall, hTargetBody,
                hMappedReturnValues, hRestoredRel⟩ :=
            returned.compose hFnReturns hAccount
              (by
                rw [hFnName]
                exact hLookup)
              hCallerRel
          have hActualTargetBody :
              Functions.Source.Effectful.FunDef.runBody
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions targetFn argsExact.values
                  (bodyFuel + 1) expectedTargetCaller =
                .ok
                  (Functions.Source.Effectful.CallResult.returned
                    stateAfterCall returnValues) := by
            exact
              Functions.Source.Effectful.FunDef.runBody_returned_of_parts
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions hParamsInserted hBodyRun hMode
                hTargetReturns hBodyState
          have hTargetBodyEq :
              sourceReturnValues = returnValues := by
            rw [hActualTargetBody] at hTargetBody
            have hCallResult := Except.ok.inj hTargetBody
            injection hCallResult with hStateEq hValuesEq
            exact hValuesEq.symm
          have hActualFinal :
              preTarget =
                bodyOutcome.state.withSource
                  { shared := bodyOutcome.state.source.shared,
                    vars := returnStore } := by
            simpa [hBodyState] using hCallFinal
          have hTargetVar :
              preTarget.source.vars tmp = some value := by
            obtain ⟨targetValue, hLookupTarget, hEvalFinal, hEvalValues⟩ :=
              Functions.Source.Effectful.Expr.eval_var_ok_parts
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                hTarget
            injection hEvalValues with hTargetValue
            subst targetValue
            exact hLookupTarget
          have hReturnSingleton : returnValues = [value] := by
            cases returnValues with
            | nil =>
                simp [Functions.Source.Store.assignMany] at hAssign
            | cons returnValue rest =>
                cases rest with
                | nil =>
                    have hAssigned :
                        returnStore =
                          Locals.Source.Store.insert
                            expectedTargetCaller.source.vars tmp returnValue := by
                      simp [Functions.Source.Store.assignMany] at hAssign
                      exact hAssign.2.symm
                    have hLookupReturn :
                        preTarget.source.vars tmp = some returnValue := by
                      rw [hActualFinal, hAssigned]
                      simp [Locals.Source.Store.insert]
                    rw [hLookupReturn] at hTargetVar
                    injection hTargetVar with hValueEq
                    subst returnValue
                    rfl
                | cons next more =>
                    simp [Functions.Source.Store.assignMany] at hAssign
          have hMappedReturns :
              List.map returned.sourceAfterBody.source.lookup!
                  targetFn.returns =
                [value] := by
            rw [← hMappedReturnValues, hTargetBodyEq, hReturnSingleton]
          let bodyForward :
              FunctionsObserverCall.ReturnedBody contract transcript codeRel
                targetProgram.toFunctions targetFn argsExact.values bodyFuel
                returned.sourceAfterBody expectedTargetCaller :=
            { paramStore := returned.paramStore
              bodyOutcome := returned.bodyOutcome
              finalCtx := returned.finalCtx
              params := returned.paramsInserted
              run := returned.targetRun
              mode := returned.mode
              relation := returned.relation }
          let restoredSource :=
            returned.sourceAfterBody.withSource
              ((returned.sourceAfterBody.source.reviveJump.overwrite?
                argsExact.sourceFinal.source).setStore
                  argsExact.sourceFinal.source)
          let prepared :=
            FunctionsObserverCall.PreparedValue.ofReturnedCall
              argsExact.prepared.prepared hFresh hFind bodyForward
              (sourceFinal := restoredSource) rfl hMappedReturns
          have hRestoredStore :
              restoredSource.source.store =
                argsExact.sourceFinal.source.store := by
            dsimp [restoredSource]
            obtain
                ⟨sourceShared, sourceVars, hSourceArgs,
                  _hShared, _hVars, _hDomain⟩ :=
              argsExact.prepared.relation.2
            obtain
                ⟨bodyShared, bodyVars, hBodySource,
                  _hBodyShared, _hBodyVars, _hBodyDomain⟩ :=
              returned.relation.2
            change
              returned.sourceAfterBody.source.reviveJump =
                .Ok bodyShared bodyVars at hBodySource
            rw [hSourceArgs, hBodySource]
            rfl
          let scopedPrepared :
              FunctionsObserverExpression.ScopedPreparedValue
                contract transcript codeRel targetProgram.toFunctions
                (preArgs ++
                  [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                    Functions.Stmt.call [tmp] functionName lowerArgs])
                (.var tmp) after layout restoredSource target ctx value :=
            { prepared := prepared
              relation :=
                StateRelation.Replay.scopedExact_of_rel_store
                  prepared.rel (by
                    rw [hRestoredStore]
                    exact
                      StateRelation.Replay.sourceStoreDomain_of_scopedExact
                        argsExact.prepared.relation) }
          obtain ⟨preparedFuel, hPreparedRun⟩ := prepared.run
          obtain ⟨hPreparedTarget, hPreparedCtx⟩ :=
            Functions.Source.Effectful.Block.runOpen_regular_unique
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions hPreparedRun hPre
          have hPreparedEval := prepared.eval
          rw [hPreparedTarget] at hPreparedEval
          rw [hPreparedEval] at hTarget
          have hEvalPair := Except.ok.inj hTarget
          have hEvalTarget := congrArg Prod.fst hEvalPair
          let commonFuel :=
            max argsBackward.sourceFuel (returned.sourceFuel + 1)
          have hArgsSource :
              Yul.Source.Effectful.evalArgs
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  commonFuel args.reverse (some sourceProgram.contract)
                  source =
                .ok
                  (argsExact.sourceFinal, argsExact.values.reverse) :=
            Yul.Source.Effectful.evalArgs_mono
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
                contract transcript)
              (Nat.le_max_left _ _) argsExact.sourceRun
          have hCallSource :
              Yul.Source.Effectful.call
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  commonFuel argsExact.values (some functionName)
                  (some sourceProgram.contract) argsExact.sourceFinal =
                .ok (restoredSource, returnValues) :=
            Yul.Source.Effectful.call_mono
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
                contract transcript)
              (Nat.le_max_right _ _) (by
                rw [hTargetBodyEq] at hSourceCall
                simpa [hFnName, restoredSource] using hSourceCall)
          rw [hReturnSingleton] at hCallSource
          have hCallSource' :
              Yul.Source.Effectful.call
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  commonFuel argsExact.values.reverse.reverse
                  (some functionName) (some sourceProgram.contract)
                  argsExact.sourceFinal =
                .ok (restoredSource, [value]) := by
            simpa using hCallSource
          have hSourceValues :
              Yul.Source.Effectful.evalValues
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (commonFuel + 1)
                  (.Call (.inr functionName) args)
                  (some sourceProgram.contract) source =
                .ok (restoredSource, [value]) := by
            simp only [Yul.Source.Effectful.evalValues, hArgsSource]
            simpa using hCallSource'
          have hSource :
              Yul.Source.Effectful.eval
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (commonFuel + 1)
                  (.Call (.inr functionName) args)
                  (some sourceProgram.contract) source =
                .ok (restoredSource, value) := by
            simp [Yul.Source.Effectful.eval, hSourceValues]
          exact
            ⟨⟨commonFuel + 1,
              ⟨restoredSource, hSourceValues, hSource, scopedPrepared,
                hPreparedTarget, hEvalTarget, hPreparedCtx⟩⟩⟩

end FunctionsObserverCallBackward
end Yul
end EvmCompiler
