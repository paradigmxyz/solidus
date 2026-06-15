import EvmCompiler.Yul.FunctionsObserverCompiler
import EvmCompiler.Yul.FunctionsObserverExpression
import EvmCompiler.Yul.SolcValidation

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCall

/-!
Function-call preservation owned by the adjacent Yul-to-Functions pass.

This module composes the ordinary selected `FunDef`, canonical call-frame
semantics, and the recursive body theorem. It does not define a call
interpreter, compiler, replay certificate, or callee oracle.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

structure ReturnedBody
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (fn : Functions.FunDef)
    (args : List Word)
    (bodyFuel : Nat)
    (sourceAfterBody : ObserverSemantics.SourceReplay.State transcript)
    (targetCaller : Functions.ObserverSemantics.State transcript) where
  paramStore : Locals.Source.Store
  bodyOutcome :
    Functions.Source.Effectful.Outcome
      (Functions.ObserverSemantics.State transcript)
  finalCtx : Functions.Source.Ctx
  params :
    Functions.Source.Store.insertMany fn.params args
        Locals.Source.Store.empty =
      some paramStore
  run :
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program (Functions.Source.Effectful.FunDef.bodyCtx fn)
        bodyFuel fn.body
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }) =
      .ok
        (bodyOutcome, finalCtx)
  mode :
    bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave
  relation :
    StateRelation.Replay.ScopedExactRel codeRel
      (fn.returns ++ fn.params)
      (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
      bodyOutcome.state

namespace ReturnedBody

theorem compose
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {fn : Functions.FunDef}
    {args : List Word}
    {bodyFuel : Nat}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (body :
      ReturnedBody contract transcript codeRel program fn args bodyFuel
        sourceAfterBody targetCaller)
    (hCaller :
      StateRelation.Replay.Rel codeRel sourceCaller targetCaller) :
    ∃ returnValues,
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn args (bodyFuel + 1) targetCaller =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            body.bodyOutcome.state returnValues) ∧
      returnValues =
        List.map sourceAfterBody.source.lookup! fn.returns ∧
      StateRelation.Replay.Rel codeRel
        (sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
        (body.bodyOutcome.state.withSource
          { shared := body.bodyOutcome.state.source.shared,
            vars := targetCaller.source.vars }) := by
  have hReturns :
      Functions.Source.Store.lookupMany fn.returns
          body.bodyOutcome.state.source.vars =
        some (List.map sourceAfterBody.source.lookup! fn.returns) :=
    StateRelation.Replay.lookupMany_of_scopedExact body.relation
      (by
        intro name hMem
        exact List.mem_append_left fn.params hMem)
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn args (bodyFuel + 1) targetCaller =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            body.bodyOutcome.state
            (List.map sourceAfterBody.source.lookup! fn.returns)) :=
    Functions.Source.Effectful.FunDef.runBody_returned_of_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program body.params body.run body.mode hReturns rfl
  exact
    ⟨List.map sourceAfterBody.source.lookup! fn.returns,
      hRunBody, rfl,
      StateRelation.Replay.restore_call hCaller body.relation⟩

end ReturnedBody

structure ScopedReturnedCall
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (functionName : Name)
    (targets : List Name)
    (preArgs : List Functions.Stmt)
    (lowerArgs : List (Locals.Expr 1))
    (fresh : Fresh.State)
    (layout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) where
  finalTarget : Functions.ObserverSemantics.State transcript
  finalCtx : Functions.Source.Ctx
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel
          { stmts :=
              preArgs ++
                [Functions.Stmt.call targets functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            finalCtx)
  relation :
    StateRelation.Replay.ScopedExactRel codeRel layout
      sourceFinal finalTarget
  domain :
    StateRelation.Vars.TargetDomainWithin
      fresh.used finalTarget.source.vars
  scope :
    StateRelation.Vars.NamesWithin fresh.used finalCtx.scope
  control : Functions.Source.Ctx.SameControl ctx finalCtx

namespace ScopedReturnedCall

private theorem ofReturnedBodyWithWriteback
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout finalLayout : List Name}
    {argValues returnValues : List Word}
    {bodyFuel : Nat}
    {sourceAfterArgs sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh layout
        sourceAfterArgs target ctx argValues)
    (hTargetsNodup : targets.Nodup)
    (hTargetsContain :
      ∀ name, name ∈ targets →
        argsPrepared.prepared.prepared.finalTarget.source.vars.contains name =
          true)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      ReturnedBody contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hReturnValues :
      List.map sourceAfterBody.source.lookup! fn.returns = returnValues)
    (hLength : returnValues.length = targets.length)
    (hWriteback :
      ∀ {finalVars : Locals.Source.Store},
        Functions.Source.Store.assignMany targets returnValues
            argsPrepared.prepared.prepared.finalTarget.source.vars =
          some finalVars →
        StateRelation.Replay.ScopedExactRel codeRel layout
            (sourceAfterBody.withSource
              ((sourceAfterBody.source.reviveJump.overwrite?
                sourceAfterArgs.source).setStore sourceAfterArgs.source))
            (body.bodyOutcome.state.withSource
              { shared := body.bodyOutcome.state.source.shared,
                vars :=
                  argsPrepared.prepared.prepared.finalTarget.source.vars }) →
        StateRelation.Replay.ScopedExactRel codeRel finalLayout
          sourceFinal
          (body.bodyOutcome.state.withSource
            { shared := body.bodyOutcome.state.source.shared,
              vars := finalVars })) :
    Nonempty
      (ScopedReturnedCall contract transcript codeRel program functionName
        targets preArgs lowerArgs fresh finalLayout sourceFinal target ctx) := by
  let targetAfterArgs := argsPrepared.prepared.prepared.finalTarget
  have hArgsEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs targetAfterArgs =
        .ok (targetAfterArgs, argValues) :=
    argsPrepared.prepared.stable targetAfterArgs
      (StateRelation.Vars.TargetExtends.refl _)
  have hReturns :
      Functions.Source.Store.lookupMany fn.returns
          body.bodyOutcome.state.source.vars =
        some (List.map sourceAfterBody.source.lookup! fn.returns) :=
    StateRelation.Replay.lookupMany_of_scopedExact body.relation
      (by
        intro name hMem
        exact List.mem_append_left fn.params hMem)
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn argValues (bodyFuel + 1) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            body.bodyOutcome.state returnValues) := by
    rw [← hReturnValues]
    exact
      Functions.Source.Effectful.FunDef.runBody_returned_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program body.params body.run body.mode hReturns rfl
  obtain ⟨finalVars, hAssign⟩ :=
    Functions.Source.Store.assignMany_exists_of_length_of_contains
      hLength hTargetsContain
  let finalTarget :=
    body.bodyOutcome.state.withSource
      { shared := body.bodyOutcome.state.source.shared,
        vars := finalVars }
  have hCallRun :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx (bodyFuel + 2)
          (.call targets functionName lowerArgs) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            argsPrepared.prepared.prepared.finalCtx) := by
    apply
      Functions.Source.Effectful.Stmt.call_regular_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program
    · exact hTargetsNodup
    · exact hArgsEval
    · exact hFind
    · simpa [Nat.add_assoc] using hRunBody
    · exact hAssign
    · rfl
  have hCallEmpty :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx 1
          { stmts := [] } finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            argsPrepared.prepared.prepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_nil
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program argsPrepared.prepared.prepared.finalCtx 0 finalTarget
  obtain ⟨callFuel, hCallBlock⟩ :=
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hCallRun hCallEmpty
  have hFullRun :
      ∃ fuel,
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx fuel
            { stmts :=
                preArgs ++
                  [Functions.Stmt.call targets functionName lowerArgs] }
            target =
          .ok
            (Functions.Source.Effectful.Outcome.regular finalTarget,
              argsPrepared.prepared.prepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program preArgs
      [Functions.Stmt.call targets functionName lowerArgs]
      ctx argsPrepared.prepared.prepared.finalCtx target targetAfterArgs
      (Functions.Source.Effectful.Outcome.regular finalTarget)
      argsPrepared.prepared.prepared.finalCtx
      argsPrepared.prepared.prepared.run
      ⟨callFuel, hCallBlock⟩
  have hRestored :
      StateRelation.Replay.ScopedExactRel codeRel layout
        (sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceAfterArgs.source).setStore sourceAfterArgs.source))
        (body.bodyOutcome.state.withSource
          { shared := body.bodyOutcome.state.source.shared,
            vars := targetAfterArgs.source.vars }) :=
    StateRelation.Replay.scopedExact_restore_call
      argsPrepared.relation body.relation
  have hFinalRel :
      StateRelation.Replay.ScopedExactRel codeRel finalLayout
        sourceFinal finalTarget :=
    hWriteback hAssign hRestored
  have hTargetsUsed :
      ∀ name, name ∈ targets → name ∈ fresh.used := by
    intro name hMem
    cases hLookup : targetAfterArgs.source.vars name with
    | none =>
        have hContains := hTargetsContain name hMem
        have hLookup' :
            argsPrepared.prepared.prepared.finalTarget.source.vars name =
              none := by
          simpa [targetAfterArgs] using hLookup
        simp [Locals.Source.Store.contains, hLookup'] at hContains
    | some value =>
        exact
          argsPrepared.prepared.prepared.domain name value hLookup
  exact
    ⟨{ finalTarget := finalTarget
       finalCtx := argsPrepared.prepared.prepared.finalCtx
       run := hFullRun
       relation := hFinalRel
       domain :=
         argsPrepared.prepared.prepared.domain.assignMany
           hTargetsUsed hAssign
       scope := argsPrepared.prepared.prepared.scope
       control := argsPrepared.prepared.prepared.control }⟩

theorem ofReturnedBody
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout : List Name}
    {argValues returnValues : List Word}
    {bodyFuel : Nat}
    {sourceAfterArgs sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh layout
        sourceAfterArgs target ctx argValues)
    (hTargetsNodup : targets.Nodup)
    (hTargetsVisible :
      ∀ name, name ∈ targets → name ∈ layout)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      ReturnedBody contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hReturnValues :
      List.map sourceAfterBody.source.lookup! fn.returns = returnValues)
    (hLength : returnValues.length = targets.length)
    (hSourceFinal :
      sourceFinal =
        sourceAfterBody.withSource
          (((sourceAfterBody.source.reviveJump.overwrite?
            sourceAfterArgs.source).setStore sourceAfterArgs.source).multifill
              targets returnValues)) :
    Nonempty
      (ScopedReturnedCall contract transcript codeRel program functionName
        targets preArgs lowerArgs fresh layout sourceFinal target ctx) := by
  obtain
      ⟨_sourceShared, _sourceVars, _hSource, _hShared,
        hScoped, hSourceDomain⟩ :=
    argsPrepared.relation.2
  have hTargetsContain :
      ∀ name, name ∈ targets →
        argsPrepared.prepared.prepared.finalTarget.source.vars.contains name =
          true := by
    intro name hMem
    exact
      StateRelation.Vars.target_contains_of_scopedExact
        hScoped hSourceDomain (hTargetsVisible name hMem)
  apply
    ofReturnedBodyWithWriteback argsPrepared hTargetsNodup
      hTargetsContain hFind body hReturnValues hLength
  intro finalVars hAssign hRestored
  rw [hSourceFinal]
  exact
    StateRelation.Replay.scopedExact_multifill_assignMany
      hRestored hTargetsNodup hTargetsVisible hAssign

theorem ofReturnedBodyFresh
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout : List Name}
    {argValues returnValues : List Word}
    {bodyFuel : Nat}
    {sourceAfterArgs sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh layout
        sourceAfterArgs target ctx argValues)
    (hTargetsNodup : targets.Nodup)
    (hTargetsFresh :
      ∀ name, name ∈ targets → name ∉ layout)
    (hTargetsContain :
      ∀ name, name ∈ targets →
        argsPrepared.prepared.prepared.finalTarget.source.vars.contains name =
          true)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      ReturnedBody contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hReturnValues :
      List.map sourceAfterBody.source.lookup! fn.returns = returnValues)
    (hLength : returnValues.length = targets.length)
    (hSourceFinal :
      sourceFinal =
        sourceAfterBody.withSource
          (((sourceAfterBody.source.reviveJump.overwrite?
            sourceAfterArgs.source).setStore sourceAfterArgs.source).multifill
              targets returnValues)) :
    Nonempty
      (ScopedReturnedCall contract transcript codeRel program functionName
        targets preArgs lowerArgs fresh (targets ++ layout)
        sourceFinal target ctx) := by
  apply
    ofReturnedBodyWithWriteback argsPrepared hTargetsNodup
      hTargetsContain hFind body hReturnValues hLength
  intro finalVars hAssign hRestored
  rw [hSourceFinal]
  exact
    StateRelation.Replay.scopedExact_multifill_assignMany_fresh
      hRestored hTargetsNodup hTargetsFresh hAssign

end ScopedReturnedCall

def RecursiveScopedExpressionForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {exprFuel : Nat} {before after : Fresh.State}
    {layout : List Name}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {value : Word},
    exprFuel < bound →
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
        true →
      Expr.lower1Unchecked? before expr = some (pre, lower, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      Yul.Source.Effectful.eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          exprFuel expr (some sourceProgram.contract) source =
        .ok (source', value) →
      Nonempty
        (FunctionsObserverExpression.ScopedPreparedValue
          contract transcript codeRel targetProgram.toFunctions
          pre lower after layout source' target ctx value)

def RecursiveScopedValueForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {exprFuel : Nat} {before after : Fresh.State}
    {layout : List Name}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word},
    exprFuel < bound →
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr =
        true →
      Expr.lower1Unchecked? before expr = some (pre, lower, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          exprFuel expr (some sourceProgram.contract) source =
        .ok (source', values) →
      ∃ value,
        values = [value] ∧
          Nonempty
            (FunctionsObserverExpression.ScopedPreparedValue
              contract transcript codeRel targetProgram.toFunctions
              pre lower after layout source' target ctx value)

namespace RecursiveScopedValueForward

theorem expression
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hValue :
      RecursiveScopedValueForward contract transcript codeRel
        sourceProgram targetProgram profile bound) :
    RecursiveScopedExpressionForward contract transcript codeRel
      sourceProgram targetProgram profile bound := by
  intro exprFuel before after layout expr pre lower source source'
    target ctx value hFuel hOk hLower hRel hDomain hScope hRun
  obtain ⟨values, hValues, hHead⟩ :=
    Yul.Source.Effectful.eval_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨result, hSingleton, hPrepared⟩ :=
    hValue hFuel hOk hLower hRel hDomain hScope hValues
  rw [hSingleton] at hHead
  simp at hHead
  subst value
  exact hPrepared

end RecursiveScopedValueForward

def RecursiveBodyForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel : Nat} {before after : Fresh.State}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt} {fn : Functions.FunDef}
    {args : List Word} {paramStore : Locals.Source.Store}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript},
    sourceFuel < bound →
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
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.Block body) (some sourceProgram.contract)
          (sourceCaller.withSource
            (EvmYul.Yul.State.mkOk
              (sourceCaller.source.initcall params returns args))) =
        .ok sourceAfterBody →
      ∃ targetFuel,
        Nonempty
          (ReturnedBody contract transcript codeRel
            targetProgram.toFunctions fn args targetFuel
            sourceAfterBody targetCaller)

namespace ScopedReturnedCall

private structure WritebackPolicy
    {transcript : Trace}
    (codeRel : StateRelation.CodeRel)
    (layout targets : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript) where
  finalLayout : List Name
  contains :
    ∀ name, name ∈ targets →
      target.source.vars.contains name = true
  relation :
    ∀ {sourceAfterArgs sourceAfterBody :
        ObserverSemantics.SourceReplay.State transcript}
      {targetAfterArgs bodyTarget :
        Functions.ObserverSemantics.State transcript}
      {returnValues : List Word}
      {finalVars : Locals.Source.Store},
      sourceFinal =
          sourceAfterBody.withSource
            (((sourceAfterBody.source.reviveJump.overwrite?
              sourceAfterArgs.source).setStore
                sourceAfterArgs.source).multifill targets returnValues) →
      StateRelation.Replay.ScopedExactRel codeRel layout
          (sourceAfterBody.withSource
            ((sourceAfterBody.source.reviveJump.overwrite?
              sourceAfterArgs.source).setStore sourceAfterArgs.source))
          (bodyTarget.withSource
            { shared := bodyTarget.source.shared,
              vars := targetAfterArgs.source.vars }) →
      Functions.Source.Store.assignMany targets returnValues
          targetAfterArgs.source.vars =
        some finalVars →
      StateRelation.Replay.ScopedExactRel codeRel finalLayout
        sourceFinal
        (bodyTarget.withSource
          { shared := bodyTarget.source.shared, vars := finalVars })

private theorem ofFunctionCallWithPolicy
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {layout targets : List Name}
    {functionName : Name}
    {args : List AstExpr}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel : Nat}
    {source sourceAfterCall sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {returnValues : List Word}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering initial args
        preArgs lowerArgs final)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout targets.length
          (.Call (.inr functionName) args) =
        true)
    (hTargetsNodup : targets.Nodup)
    (policy :
      WritebackPolicy codeRel layout targets sourceFinal target)
    (hExpr :
      RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hBody :
      RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inr functionName) args)
          (some sourceProgram.contract) source =
        .ok (sourceAfterCall, returnValues))
    (hSourceFinal :
      sourceFinal =
        sourceAfterCall.withSource
          (sourceAfterCall.source.multifill targets returnValues)) :
    Nonempty
      (ScopedReturnedCall contract transcript codeRel
        targetProgram.toFunctions functionName targets preArgs lowerArgs
        final policy.finalLayout sourceFinal target ctx) := by
  obtain
      ⟨callFuel, sourceAfterArgs, reversedValues,
        hFuel, hArgsRun, hCallRun⟩ :=
    Yul.Source.Effectful.evalValues_function_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  cases callFuel with
  | zero =>
      simp [Yul.Source.Effectful.call,
        Yul.Source.Effectful.fail] at hCallRun
  | succ bodyFuel =>
      obtain
          ⟨_accountContract, params, returns, body, sourceAfterBody,
            _hAccount, hFunction, hBodyRun, hSourceAfterCall,
            hSourceReturns⟩ :=
        Yul.Source.Effectful.call_succ_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (by simpa [Nat.succ_eq_add_one] using hCallRun)
      have hLookup :
          sourceProgram.contract.functions.lookup functionName =
            some (.Def params returns body) := by
        simpa using hFunction
      have hArgsOk :
          SolcValidation.ExprsOk? profile sourceProgram.contract
              layout args =
            true :=
        SolcValidation.exprsOk_of_exprOk_functionCall hExprOk hLookup
      obtain ⟨hReturnCount, hArgCount, hSignature⟩ :=
        SolcValidation.programOkWith_functionCall_partsN
          hProgramOk hExprOk hLookup
      have hPreparedArgs :
          Nonempty
            (FunctionsObserverExpression.ScopedPreparedArgs
              contract transcript codeRel targetProgram.toFunctions
              preArgs lowerArgs final layout sourceAfterArgs target ctx
              reversedValues.reverse) := by
        cases hArgsLowering with
        | empty =>
            simp [Yul.Source.Effectful.evalArgs] at hArgsRun
            rcases hArgsRun with ⟨rfl, rfl⟩
            exact
              ⟨FunctionsObserverExpression.PreparedArgs.empty
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope,
                hRel⟩
        | bound hNonempty hArgsLowering =>
            exact
              FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
                hArgsLowering
                (fun expr hMem =>
                  SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
                (fun hLt hArgOk hExprLower hExprRel hExprDomain
                    hExprScope hExprRun =>
                  hExpr (by omega) hArgOk hExprLower hExprRel
                    hExprDomain hExprScope hExprRun)
                hRel hDomain hScope hArgsRun
      obtain ⟨preparedArgs⟩ := hPreparedArgs
      have hTargetsContain :
          ∀ name, name ∈ targets →
            preparedArgs.prepared.prepared.finalTarget.source.vars.contains
                name =
              true := by
        intro name hMem
        cases hLookupTarget : target.source.vars name with
        | none =>
            have hContains := policy.contains name hMem
            simp [Locals.Source.Store.contains, hLookupTarget] at hContains
        | some value =>
            have hFinalLookup :
                preparedArgs.prepared.prepared.finalTarget.source.vars name =
                  some value :=
              preparedArgs.prepared.prepared.varsExtends
                name value hLookupTarget
            simp [Locals.Source.Store.contains, hFinalLookup]
      obtain
          ⟨before, after, fn, hPrefix, hFind, _hName, hParams,
            hFnReturns, hLowerBody, hReserved⟩ :=
        hDecomposition.findFunction_parts hLookup
      have hArgsLength :
          reversedValues.reverse.length = (identNames params).length := by
        have hEvaluatedLength :=
          Yul.Source.Effectful.evalArgs_ok_length
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hArgsRun
        simpa [identNames, hArgCount] using hEvaluatedLength
      obtain ⟨paramStore, hParamStore⟩ :=
        Functions.Source.Store.insertMany_exists_of_length
          (names := identNames params)
          (values := reversedValues.reverse)
          (store := Locals.Source.Store.empty)
          hArgsLength
      have hEntry :
          StateRelation.Replay.ScopedExactRel codeRel
            (fn.returns ++ fn.params)
            (sourceAfterArgs.withSource
              (EvmYul.Yul.State.mkOk
                (sourceAfterArgs.source.initcall
                  params returns reversedValues.reverse)))
            (preparedArgs.prepared.prepared.finalTarget.withSource
              { shared :=
                  preparedArgs.prepared.prepared.finalTarget.source.shared,
                vars :=
                  Functions.Source.Store.initReturns
                    fn.returns paramStore }) := by
        have hIdentParams : identNames params = params :=
          identNames_eq_self params
        have hIdentReturns : identNames returns = returns :=
          identNames_eq_self returns
        have hSignature' : (returns ++ params).Nodup := by
          rw [hIdentReturns, hIdentParams] at hSignature
          exact hSignature
        have hParamStore' :
            Functions.Source.Store.insertMany params reversedValues.reverse
                Locals.Source.Store.empty =
              some paramStore := by
          rw [hIdentParams] at hParamStore
          exact hParamStore
        have hParams' : fn.params = params :=
          hParams.trans hIdentParams
        have hFnReturns' : fn.returns = returns :=
          hFnReturns.trans hIdentReturns
        have hEntryBase :=
          StateRelation.Replay.scopedExact_initcall
            (params := params)
            (returns := returns)
            (args := reversedValues.reverse)
            (paramStore := paramStore)
            (StateRelation.Replay.rel_of_scopedExact
              preparedArgs.relation)
            hSignature' hParamStore'
        simpa [hParams', hFnReturns'] using hEntryBase
      have hBodyOk :
          SolcValidation.StmtsOk? profile sourceProgram.contract
              ((Contract.functionEntries
                sourceProgram.contract).map Prod.fst)
              (fn.returns ++ fn.params) false false true body =
            true := by
        rw [hFnReturns, hParams]
        exact
          SolcValidation.programOkWith_function_bodyOk
            hProgramOk hLookup
      have hBodyNames :
          StateRelation.Vars.NamesWithin before.used
            (Stmt.List.names body) := by
        intro candidate hMem
        apply hPrefix candidate
        change candidate ∈ Contract.names sourceProgram.contract
        exact
          (Contract.function_names_mem_names_of_lookup hLookup).2 candidate
            (by
              simp [FunctionDefinition.names, hMem])
      obtain ⟨targetBodyFuel, returnedBodyNonempty⟩ :=
        hBody (by omega) hLowerBody hParams hFnReturns
          (by simpa [hParams] using hParamStore)
          hReserved hBodyNames hBodyOk hEntry hBodyRun
      obtain ⟨returnedBody⟩ := returnedBodyNonempty
      have hReturnedValues :
          List.map sourceAfterBody.source.lookup! fn.returns =
            returnValues := by
        rw [hFnReturns, identNames_eq_self]
        exact hSourceReturns.symm
      have hReturnLength :
          returnValues.length = targets.length := by
        calc
          returnValues.length =
              (List.map sourceAfterBody.source.lookup! fn.returns).length := by
                rw [hReturnedValues]
          _ = fn.returns.length := by simp
          _ = returns.length := by
            rw [hFnReturns, identNames_eq_self]
          _ = targets.length := hReturnCount.symm
      have hSourceFinal' :
          sourceFinal =
            sourceAfterBody.withSource
              (((sourceAfterBody.source.reviveJump.overwrite?
                sourceAfterArgs.source).setStore
                  sourceAfterArgs.source).multifill targets returnValues) := by
        rw [hSourceFinal, hSourceAfterCall]
        rfl
      exact
        ofReturnedBodyWithWriteback preparedArgs hTargetsNodup
          hTargetsContain hFind returnedBody hReturnedValues hReturnLength
          (fun hAssign hRestored =>
            policy.relation hSourceFinal' hRestored hAssign)

theorem ofFunctionCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {layout targets : List Name}
    {functionName : Name}
    {args : List AstExpr}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel : Nat}
    {source sourceAfterCall sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {returnValues : List Word}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering initial args
        preArgs lowerArgs final)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout targets.length
          (.Call (.inr functionName) args) =
        true)
    (hTargetsNodup : targets.Nodup)
    (hTargetsVisible :
      ∀ name, name ∈ targets → name ∈ layout)
    (hExpr :
      RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hBody :
      RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inr functionName) args)
          (some sourceProgram.contract) source =
        .ok (sourceAfterCall, returnValues))
    (hSourceFinal :
      sourceFinal =
        sourceAfterCall.withSource
          (sourceAfterCall.source.multifill targets returnValues)) :
    Nonempty
      (ScopedReturnedCall contract transcript codeRel
        targetProgram.toFunctions functionName targets preArgs lowerArgs
        final layout sourceFinal target ctx) := by
  obtain
      ⟨_sourceShared, _sourceVars, _hSource, _hShared,
        hScoped, hSourceDomain⟩ :=
    hRel.2
  let policy :
      WritebackPolicy codeRel layout targets sourceFinal target :=
    { finalLayout := layout
      contains := fun name hMem =>
        StateRelation.Vars.target_contains_of_scopedExact
          hScoped hSourceDomain (hTargetsVisible name hMem)
      relation := by
        intro sourceAfterArgs sourceAfterBody targetAfterArgs bodyTarget
          callReturnValues finalVars hFinal hRestored hAssign
        rw [hFinal]
        exact
          StateRelation.Replay.scopedExact_multifill_assignMany
            hRestored hTargetsNodup hTargetsVisible hAssign }
  exact
    ofFunctionCallWithPolicy hDecomposition hArgsLowering hProgramOk
      hExprOk hTargetsNodup policy hExpr hBody hRel hDomain hScope
      hRun hSourceFinal

theorem ofFunctionCallFresh
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {layout targets : List Name}
    {functionName : Name}
    {args : List AstExpr}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel : Nat}
    {source sourceAfterCall sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {returnValues : List Word}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hArgsLowering :
      Expr.UncheckedCallArgsLowering initial args
        preArgs lowerArgs final)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout targets.length
          (.Call (.inr functionName) args) =
        true)
    (hTargetsNodup : targets.Nodup)
    (hTargetsFresh :
      ∀ name, name ∈ targets → name ∉ layout)
    (hTargetsContain :
      ∀ name, name ∈ targets →
        target.source.vars.contains name = true)
    (hExpr :
      RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hBody :
      RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inr functionName) args)
          (some sourceProgram.contract) source =
        .ok (sourceAfterCall, returnValues))
    (hSourceFinal :
      sourceFinal =
        sourceAfterCall.withSource
          (sourceAfterCall.source.multifill targets returnValues)) :
    Nonempty
      (ScopedReturnedCall contract transcript codeRel
        targetProgram.toFunctions functionName targets preArgs lowerArgs
        final (targets ++ layout) sourceFinal target ctx) := by
  let policy :
      WritebackPolicy codeRel layout targets sourceFinal target :=
    { finalLayout := targets ++ layout
      contains := hTargetsContain
      relation := by
        intro sourceAfterArgs sourceAfterBody targetAfterArgs bodyTarget
          callReturnValues finalVars hFinal hRestored hAssign
        rw [hFinal]
        exact
          StateRelation.Replay.scopedExact_multifill_assignMany_fresh
            hRestored hTargetsNodup hTargetsFresh hAssign }
  exact
    ofFunctionCallWithPolicy hDecomposition hArgsLowering hProgramOk
      hExprOk hTargetsNodup policy hExpr hBody hRel hDomain hScope
      hRun hSourceFinal

end ScopedReturnedCall

namespace PreparedValue

def ofReturnedCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName tmp : Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {argsFresh finalFresh : Fresh.State}
    {argValues : List Word}
    {bodyFuel : Nat}
    {sourceCaller sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Word}
    (argsPrepared :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program preArgs lowerArgs argsFresh
        sourceCaller target ctx argValues)
    (hFresh : Fresh.fresh? argsFresh = some (tmp, finalFresh))
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      ReturnedBody contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody
        (argsPrepared.prepared.finalTarget.withSource
          (argsPrepared.prepared.finalTarget.source.insert
            tmp Functions.Source.zero)))
    (hSourceFinal :
      sourceFinal =
        sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
    (hReturnValues :
      List.map sourceAfterBody.source.lookup! fn.returns = [value]) :
    FunctionsObserverExpression.PreparedValue
      contract transcript codeRel program
      (preArgs ++
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
          Functions.Stmt.call [tmp] functionName lowerArgs])
      (.var tmp) finalFresh sourceFinal target ctx value := by
  let targetAfterArgs := argsPrepared.prepared.finalTarget
  let targetWithZero :=
    targetAfterArgs.withSource
      (targetAfterArgs.source.insert tmp Functions.Source.zero)
  have hNotMem : tmp ∉ argsFresh.used :=
    Fresh.not_mem_of_fresh? hFresh
  have hTargetHidden : targetAfterArgs.source.vars tmp = none :=
    argsPrepared.prepared.domain.lookup_none hNotMem
  have hSourceHidden : sourceCaller.source.lookup? tmp = none :=
    StateRelation.Replay.source_lookup_none_of_targetDomainWithin
      argsPrepared.prepared.rel argsPrepared.prepared.domain hNotMem
  have hZeroExtends :
      StateRelation.Vars.TargetExtends
        targetAfterArgs.source.vars targetWithZero.source.vars := by
    dsimp [targetWithZero]
    exact StateRelation.Vars.TargetExtends.insert_fresh hTargetHidden
  have hArgsEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs targetWithZero =
        .ok (targetWithZero, argValues) :=
    argsPrepared.stable targetWithZero hZeroExtends
  have hZeroRel :
      StateRelation.Replay.Rel codeRel sourceCaller targetWithZero := by
    dsimp [targetWithZero]
    exact
      StateRelation.Replay.insert_target_hidden
        argsPrepared.prepared.rel hSourceHidden
  have hZeroEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.lit Functions.Source.zero : Locals.Expr 1) targetAfterArgs =
        .ok (targetAfterArgs, [Functions.Source.zero]) := by
    rfl
  let zeroPrepared :=
    FunctionsObserverExpression.Prepared.generated
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (program := program)
      (ctx := argsPrepared.prepared.finalCtx)
      hFresh hZeroEval argsPrepared.prepared.rel
      argsPrepared.prepared.domain argsPrepared.prepared.scope
  have hZeroTarget : zeroPrepared.finalTarget = targetWithZero := by
    rfl
  have hBodyCaller :
      StateRelation.Replay.Rel codeRel sourceCaller
        zeroPrepared.finalTarget := by
    rw [hZeroTarget]
    exact hZeroRel
  have hBody' :
      ReturnedBody contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody zeroPrepared.finalTarget := by
    simpa [hZeroTarget] using body
  have hReturns :
      Functions.Source.Store.lookupMany fn.returns
          hBody'.bodyOutcome.state.source.vars =
        some (List.map sourceAfterBody.source.lookup! fn.returns) :=
    StateRelation.Replay.lookupMany_of_scopedExact hBody'.relation
      (by
        intro name hMem
        exact List.mem_append_left fn.params hMem)
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn argValues (bodyFuel + 1) zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            hBody'.bodyOutcome.state [value]) := by
    rw [← hReturnValues]
    exact
      Functions.Source.Effectful.FunDef.runBody_returned_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hBody'.params hBody'.run hBody'.mode hReturns rfl
  have hRestoredRel :
      StateRelation.Replay.Rel codeRel
        (sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
        (hBody'.bodyOutcome.state.withSource
          { shared := hBody'.bodyOutcome.state.source.shared,
            vars := zeroPrepared.finalTarget.source.vars }) :=
    StateRelation.Replay.restore_call hBodyCaller hBody'.relation
  let targetAfterCall :=
    hBody'.bodyOutcome.state.withSource
      { shared := hBody'.bodyOutcome.state.source.shared,
        vars :=
          Locals.Source.Store.insert zeroPrepared.finalTarget.source.vars
            tmp value }
  have hTmpContains :
      zeroPrepared.finalTarget.source.vars.contains tmp = true := by
    rw [hZeroTarget]
    simp [targetWithZero, Locals.Source.State.insert,
      Locals.Source.Store.contains, Locals.Source.Store.insert]
  have hAssign :
      Functions.Source.Store.assignMany [tmp] [value]
          zeroPrepared.finalTarget.source.vars =
        some
          (Locals.Source.Store.insert zeroPrepared.finalTarget.source.vars
            tmp value) := by
    simp [Functions.Source.Store.assignMany, hTmpContains]
  have hCallRun :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program zeroPrepared.finalCtx (bodyFuel + 2)
          (.call [tmp] functionName lowerArgs) zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfterCall,
            zeroPrepared.finalCtx) := by
    apply
      Functions.Source.Effectful.Stmt.call_regular_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program
    · simp
    · simpa [hZeroTarget] using hArgsEval
    · exact hFind
    · simpa [Nat.add_assoc] using hRunBody
    · exact hAssign
    · rfl
  have hRestoredHidden :
      ((sourceAfterBody.source.reviveJump.overwrite?
          sourceCaller.source).setStore sourceCaller.source).lookup? tmp =
        none := by
    rw [StateRelation.Replay.restore_call_lookup
      argsPrepared.prepared.rel body.relation tmp]
    exact hSourceHidden
  have hAfterCallRel :
      StateRelation.Replay.Rel codeRel
        (sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
        targetAfterCall := by
    dsimp [targetAfterCall]
    exact
      StateRelation.Replay.insert_target_hidden
        (by simpa [hZeroTarget] using hRestoredRel)
        hRestoredHidden
  have hCallEmpty :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program zeroPrepared.finalCtx 1 { stmts := [] } targetAfterCall =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfterCall,
            zeroPrepared.finalCtx) := by
    exact
      Functions.Source.Effectful.Block.runOpen_nil
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program zeroPrepared.finalCtx 0 targetAfterCall
  have hCallBlock :
      ∃ fuel,
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program zeroPrepared.finalCtx fuel
            { stmts := [Functions.Stmt.call [tmp] functionName lowerArgs] }
            zeroPrepared.finalTarget =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetAfterCall,
              zeroPrepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hCallRun hCallEmpty
  have hUsed : finalFresh.used = tmp :: argsFresh.used :=
    (Fresh.fresh?_components hFresh).1
  have hFinalDomain :
      StateRelation.Vars.TargetDomainWithin
        finalFresh.used targetAfterCall.source.vars := by
    rw [hUsed]
    dsimp [targetAfterCall]
    exact
      (argsPrepared.prepared.domain.insert hNotMem).insert_visible
        (by simp)
  have hFinalScope :
      StateRelation.Vars.NamesWithin
        finalFresh.used zeroPrepared.finalCtx.scope :=
    zeroPrepared.scope
  have hVarsExtends :
      StateRelation.Vars.TargetExtends
        target.source.vars targetAfterCall.source.vars := by
    intro name result hLookup
    have hAfterArgs :
        targetAfterArgs.source.vars name = some result :=
      argsPrepared.prepared.varsExtends name result hLookup
    have hNe : name ≠ tmp := by
      intro hEq
      subst name
      rw [hTargetHidden] at hAfterArgs
      contradiction
    dsimp [targetAfterCall]
    rw [Locals.Source.Store.insert_of_ne hNe]
    rw [hZeroTarget]
    change
      (Locals.Source.Store.insert targetAfterArgs.source.vars
        tmp Functions.Source.zero) name = some result
    rw [Locals.Source.Store.insert_of_ne hNe]
    exact hAfterArgs
  have hSuffixRun :
      ∃ fuel,
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program argsPrepared.prepared.finalCtx fuel
            { stmts :=
                [Functions.Stmt.let_ tmp (.lit Functions.Source.zero)] ++
                  [Functions.Stmt.call [tmp] functionName lowerArgs] }
            targetAfterArgs =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetAfterCall,
              zeroPrepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program
      [Functions.Stmt.let_ tmp (.lit Functions.Source.zero)]
      [Functions.Stmt.call [tmp] functionName lowerArgs]
      argsPrepared.prepared.finalCtx zeroPrepared.finalCtx
      targetAfterArgs zeroPrepared.finalTarget
      (Functions.Source.Effectful.Outcome.regular targetAfterCall)
      zeroPrepared.finalCtx zeroPrepared.run hCallBlock
  have hFullRun :
      ∃ fuel,
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx fuel
            { stmts :=
                preArgs ++
                  ([Functions.Stmt.let_ tmp (.lit Functions.Source.zero)] ++
                    [Functions.Stmt.call [tmp] functionName lowerArgs]) }
            target =
          .ok
            (Functions.Source.Effectful.Outcome.regular targetAfterCall,
              zeroPrepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program preArgs
      ([Functions.Stmt.let_ tmp (.lit Functions.Source.zero)] ++
        [Functions.Stmt.call [tmp] functionName lowerArgs])
      ctx argsPrepared.prepared.finalCtx target targetAfterArgs
      (Functions.Source.Effectful.Outcome.regular targetAfterCall)
      zeroPrepared.finalCtx argsPrepared.prepared.run hSuffixRun
  let fullPrepared :=
    { finalTarget := targetAfterCall
      finalCtx := zeroPrepared.finalCtx
      run := hFullRun
      rel := by simpa [hSourceFinal] using hAfterCallRel
      domain := hFinalDomain
      scope := hFinalScope
      control :=
        Functions.Source.Ctx.SameControl.trans
          argsPrepared.prepared.control zeroPrepared.control
      varsExtends := hVarsExtends :
      FunctionsObserverExpression.Prepared
        contract transcript codeRel program
        (preArgs ++
          ([Functions.Stmt.let_ tmp (.lit Functions.Source.zero)] ++
            [Functions.Stmt.call [tmp] functionName lowerArgs]))
        finalFresh sourceFinal target ctx }
  have hTmpLookup :
      fullPrepared.finalTarget.source.vars tmp = some value := by
    dsimp [fullPrepared, targetAfterCall]
    simp [Locals.Source.Store.insert]
  have hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.var tmp : Locals.Expr 1) fullPrepared.finalTarget =
        .ok (fullPrepared.finalTarget, [value]) := by
    apply Functions.Source.Effectful.Expr.eval_var
    exact hTmpLookup
  refine
    { preTarget := fullPrepared.finalTarget
      evalTarget := fullPrepared.finalTarget
      finalCtx := fullPrepared.finalCtx
      run := ?_
      eval := hEval
      rel := fullPrepared.rel
      domain := fullPrepared.domain
      scope := fullPrepared.scope
      control := fullPrepared.control
      varsExtends := ?_ }
  · simpa [List.append_assoc] using fullPrepared.run
  · exact hVarsExtends

end PreparedValue

namespace ScopedPreparedValue

theorem ofFunctionCall
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {vars : List Name}
    {functionName : Name}
    {args : List AstExpr}
    {initial final : Fresh.State}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {fuel : Nat}
    {source sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Word}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition
        sourceProgram targetProgram)
    (hLower :
      Expr.lower1Unchecked? initial (.Call (.inr functionName) args) =
        some (pre, lower, final))
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract vars 1
          (.Call (.inr functionName) args) =
        true)
    (hExpr :
      RecursiveScopedExpressionForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hBody :
      RecursiveBodyForward
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel vars source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        initial.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inr functionName) args)
          (some sourceProgram.contract) source =
        .ok (sourceFinal, value)) :
    Nonempty
      (FunctionsObserverExpression.ScopedPreparedValue
        contract transcript codeRel targetProgram.toFunctions
        pre lower final vars sourceFinal target ctx value) := by
  obtain
      ⟨callFuel, sourceAfterArgs, reversedValues, returnValues,
        _hFuel, hArgsRun, hCallRun, hValue⟩ :=
    Yul.Source.Effectful.eval_function_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  cases callFuel with
  | zero =>
      simp [Yul.Source.Effectful.call,
        Yul.Source.Effectful.fail] at hCallRun
  | succ bodyFuel =>
      obtain
          ⟨_accountContract, params, returns, body, sourceAfterBody,
            _hAccount, hFunction, hBodyRun, hSourceFinal,
            hSourceReturns⟩ :=
        Yul.Source.Effectful.call_succ_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (by simpa [Nat.succ_eq_add_one] using hCallRun)
      have hLookup :
          sourceProgram.contract.functions.lookup functionName =
            some (.Def params returns body) := by
        simpa using hFunction
      have hArgsOk :
          SolcValidation.ExprsOk? profile sourceProgram.contract vars args =
            true :=
        SolcValidation.exprsOk_of_exprOk_functionCall hExprOk hLookup
      obtain ⟨hArgCount, hSignature, returnName, hReturns⟩ :=
        SolcValidation.programOkWith_functionCall_parts
          hProgramOk hExprOk hLookup
      subst returns
      obtain
          ⟨argsFresh, tmp, preArgs, lowerArgs,
            hArgsLowering, hFresh, rfl, rfl⟩ :=
        (Expr.uncheckedFunctionCallLowering_of_lower1Unchecked?
          hLower).parts
      have hPreparedArgs :
          Nonempty
            (FunctionsObserverExpression.ScopedPreparedArgs
              contract transcript codeRel targetProgram.toFunctions
              preArgs lowerArgs argsFresh vars sourceAfterArgs target ctx
              reversedValues.reverse) := by
        cases hArgsLowering with
        | empty =>
            simp [Yul.Source.Effectful.evalArgs] at hArgsRun
            rcases hArgsRun with ⟨rfl, rfl⟩
            exact
              ⟨FunctionsObserverExpression.PreparedArgs.empty
                  (StateRelation.Replay.rel_of_scopedExact hRel)
                  hDomain hScope,
                hRel⟩
        | bound hNonempty hArgsLowering =>
            exact
              FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
                hArgsLowering
                (fun expr hMem =>
                  SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
                (fun hLt hArgOk hExprLower hExprRel hExprDomain
                    hExprScope hExprRun =>
                  hExpr (by omega) hArgOk hExprLower hExprRel
                    hExprDomain hExprScope hExprRun)
                hRel hDomain hScope hArgsRun
      obtain ⟨preparedArgs⟩ := hPreparedArgs
      obtain
          ⟨before, after, fn, hPrefix, hFind, _hName, hParams,
            hFnReturns, hLowerBody, hReserved⟩ :=
        hDecomposition.findFunction_parts hLookup
      have hArgsLength :
          reversedValues.reverse.length = (identNames params).length := by
        have hEvaluatedLength :=
          Yul.Source.Effectful.evalArgs_ok_length
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hArgsRun
        simpa [identNames, hArgCount] using hEvaluatedLength
      obtain ⟨paramStore, hParamStore⟩ :=
        Functions.Source.Store.insertMany_exists_of_length
          (names := identNames params)
          (values := reversedValues.reverse)
          (store := Locals.Source.Store.empty)
          hArgsLength
      have hNotMem : tmp ∉ argsFresh.used :=
        Fresh.not_mem_of_fresh? hFresh
      have hTargetHidden :
          preparedArgs.prepared.prepared.finalTarget.source.vars tmp = none :=
        preparedArgs.prepared.prepared.domain.lookup_none hNotMem
      have hSourceHidden :
          sourceAfterArgs.source.lookup? tmp = none :=
        StateRelation.Replay.source_lookup_none_of_targetDomainWithin
          preparedArgs.prepared.prepared.rel
          preparedArgs.prepared.prepared.domain hNotMem
      let targetCaller :=
        preparedArgs.prepared.prepared.finalTarget.withSource
          (preparedArgs.prepared.prepared.finalTarget.source.insert
            tmp Functions.Source.zero)
      have hCallerRel :
          StateRelation.Replay.Rel codeRel sourceAfterArgs targetCaller := by
        dsimp [targetCaller]
        exact
          StateRelation.Replay.insert_target_hidden
            preparedArgs.prepared.prepared.rel hSourceHidden
      have hEntry :
          StateRelation.Replay.ScopedExactRel codeRel
            (fn.returns ++ fn.params)
            (sourceAfterArgs.withSource
              (EvmYul.Yul.State.mkOk
                (sourceAfterArgs.source.initcall
                  params [returnName] reversedValues.reverse)))
            (targetCaller.withSource
              { shared := targetCaller.source.shared,
                vars :=
                  Functions.Source.Store.initReturns
                    fn.returns paramStore }) := by
        have hIdentParams : identNames params = params :=
          identNames_eq_self params
        have hIdentReturns :
            identNames [returnName] = [returnName] :=
          identNames_eq_self [returnName]
        have hSignature' : ([returnName] ++ params).Nodup := by
          rw [hIdentReturns, hIdentParams] at hSignature
          exact hSignature
        have hParamStore' :
            Functions.Source.Store.insertMany params reversedValues.reverse
                Locals.Source.Store.empty =
              some paramStore := by
          rw [hIdentParams] at hParamStore
          exact hParamStore
        have hParams' : fn.params = params :=
          hParams.trans hIdentParams
        have hFnReturns' : fn.returns = [returnName] := by
          rw [hIdentReturns] at hFnReturns
          exact hFnReturns
        have hEntryBase :=
          StateRelation.Replay.scopedExact_initcall
            (params := params)
            (returns := [returnName])
            (args := reversedValues.reverse)
            (paramStore := paramStore)
            hCallerRel hSignature' hParamStore'
        simpa [hParams', hFnReturns'] using hEntryBase
      obtain ⟨targetBodyFuel, returnedBodyNonempty⟩ :=
        have hBodyOk :
            SolcValidation.StmtsOk? profile sourceProgram.contract
                ((Contract.functionEntries
                  sourceProgram.contract).map Prod.fst)
                (fn.returns ++ fn.params) false false true body =
              true := by
          rw [hFnReturns, hParams]
          exact
            SolcValidation.programOkWith_function_bodyOk
              hProgramOk hLookup
        have hBodyNames :
            StateRelation.Vars.NamesWithin before.used
              (Stmt.List.names body) := by
          intro candidate hMem
          apply hPrefix candidate
          change candidate ∈ Contract.names sourceProgram.contract
          exact
            (Contract.function_names_mem_names_of_lookup hLookup).2 candidate
              (by
                simp [FunctionDefinition.names, hMem])
        hBody (by omega) hLowerBody hParams hFnReturns
          (by simpa [hParams] using hParamStore)
          hReserved hBodyNames hBodyOk
          hEntry hBodyRun
      obtain ⟨returnedBody⟩ := returnedBodyNonempty
      have hReturnedValues :
          List.map sourceAfterBody.source.lookup! fn.returns = [value] := by
        have hReturnValue :
            value = sourceAfterBody.source.lookup! returnName := by
          rw [hSourceReturns] at hValue
          simpa using hValue
        rw [hFnReturns]
        simp [identNames, identName, ← hReturnValue]
      let prepared :=
        PreparedValue.ofReturnedCall preparedArgs.prepared
          hFresh hFind returnedBody hSourceFinal hReturnedValues
      refine ⟨prepared, ?_⟩
      apply StateRelation.Replay.scopedExact_of_rel_store prepared.rel
      rw [hSourceFinal]
      change
        StateRelation.Vars.DomainExact vars
          (((sourceAfterBody.source.reviveJump.overwrite?
            sourceAfterArgs.source).setStore sourceAfterArgs.source).store)
      have hRestoredStore :
          ((sourceAfterBody.source.reviveJump.overwrite?
              sourceAfterArgs.source).setStore sourceAfterArgs.source).store =
            sourceAfterArgs.source.store := by
        obtain
            ⟨sourceShared, sourceVars, hSourceArgs,
              _hShared, _hVars, _hDomain⟩ :=
          preparedArgs.relation.2
        obtain
            ⟨bodyShared, bodyVars, hBodySource,
              _hBodyShared, _hBodyVars, _hBodyDomain⟩ :=
          returnedBody.relation.2
        change
          sourceAfterBody.source.reviveJump =
            .Ok bodyShared bodyVars at hBodySource
        rw [hSourceArgs, hBodySource]
        rfl
      rw [hRestoredStore]
      exact
        StateRelation.Replay.sourceStoreDomain_of_scopedExact
          preparedArgs.relation

end ScopedPreparedValue

end FunctionsObserverCall
end Yul
end EvmCompiler
