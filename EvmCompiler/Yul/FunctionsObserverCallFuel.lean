import EvmCompiler.Functions.EffectSemanticsInversion
import EvmCompiler.Yul.FunctionsObserverCall
import EvmCompiler.Yul.FunctionsObserverExpressionFuel

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCallFuel

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

def RecursiveScopedExpressionForwardBounded
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
        { result :
            FunctionsObserverExpression.ScopedPreparedValue
              contract transcript codeRel targetProgram.toFunctions
              pre lower after layout source' target ctx value //
          FunctionsObserverFuel.PreparedValue.Bounded
            (FunctionsObserverStaticCost.runtimeExpr sourceProgram expr)
            exprFuel result.prepared }

def RecursiveScopedValueForwardBounded
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
            { result :
                FunctionsObserverExpression.ScopedPreparedValue
                  contract transcript codeRel targetProgram.toFunctions
                  pre lower after layout source' target ctx value //
              FunctionsObserverFuel.PreparedValue.Bounded
                (FunctionsObserverStaticCost.runtimeExpr sourceProgram expr)
                exprFuel result.prepared }

namespace RecursiveScopedValueForwardBounded

theorem mono
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {smaller bound : Nat}
    (hForward :
      RecursiveScopedValueForwardBounded
        contract transcript codeRel sourceProgram targetProgram profile
        bound)
    (hBound : smaller ≤ bound) :
    RecursiveScopedValueForwardBounded
      contract transcript codeRel sourceProgram targetProgram profile
      smaller := by
  intro exprFuel before after layout expr pre lower source source'
    target ctx values hFuel
  exact hForward (lt_of_lt_of_le hFuel hBound)

theorem expression
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hValue :
      RecursiveScopedValueForwardBounded
        contract transcript codeRel sourceProgram targetProgram profile
        bound) :
    RecursiveScopedExpressionForwardBounded
      contract transcript codeRel sourceProgram targetProgram profile
      bound := by
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

end RecursiveScopedValueForwardBounded

def RecursiveBodyForwardBounded
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
          { shared := targetCaller.source.shared
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
          { result :
              FunctionsObserverCall.ReturnedBody
                contract transcript codeRel targetProgram.toFunctions
                fn args targetFuel sourceAfterBody targetCaller //
            targetFuel ≤
              FunctionsObserverFuel.executionBudget
                (FunctionsObserverStaticCost.stmtList body)
                sourceFuel }

namespace RecursiveBodyForwardBounded

theorem mono
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {smaller bound : Nat}
    (hForward :
      RecursiveBodyForwardBounded
        contract transcript codeRel sourceProgram targetProgram profile
        bound)
    (hBound : smaller ≤ bound) :
    RecursiveBodyForwardBounded
      contract transcript codeRel sourceProgram targetProgram profile
      smaller := by
  intro sourceFuel before after params returns body fn args
    paramStore sourceCaller sourceAfterBody targetCaller hFuel
  exact hForward (lt_of_lt_of_le hFuel hBound)

end RecursiveBodyForwardBounded

namespace ScopedReturnedCall

noncomputable def requiredFuel
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (result :
      FunctionsObserverCall.ScopedReturnedCall
        contract transcript codeRel program functionName targets
        preArgs lowerArgs fresh layout sourceFinal target ctx) : Nat := by
  classical
  exact Nat.find result.run

theorem run_requiredFuel
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (result :
      FunctionsObserverCall.ScopedReturnedCall
        contract transcript codeRel program functionName targets
        preArgs lowerArgs fresh layout sourceFinal target ctx) :
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program ctx (requiredFuel result)
        { stmts :=
            preArgs ++
              [Functions.Stmt.call targets functionName lowerArgs] }
        target =
      .ok
        (Functions.Source.Effectful.Outcome.regular result.finalTarget,
          result.finalCtx) := by
  classical
  simpa [requiredFuel] using Nat.find_spec result.run

theorem requiredFuel_le_of_run
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout : List Name}
    {sourceFinal : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (result :
      FunctionsObserverCall.ScopedReturnedCall
        contract transcript codeRel program functionName targets
        preArgs lowerArgs fresh layout sourceFinal target ctx)
    {fuel : Nat}
    (hRun :
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
          (Functions.Source.Effectful.Outcome.regular result.finalTarget,
            result.finalCtx)) :
    requiredFuel result ≤ fuel := by
  classical
  simpa [requiredFuel] using Nat.find_min' result.run hRun

/--
The shared returned-call execution admits an explicit bound independent of
whether writeback targets are existing source variables or fresh declarations.
-/
private theorem requiredFuel_le_of_parts
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
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hReturnValues :
      List.map sourceAfterBody.source.lookup! fn.returns = returnValues)
    (hLength : returnValues.length = targets.length)
    (result :
      FunctionsObserverCall.ScopedReturnedCall
        contract transcript codeRel program functionName targets
        preArgs lowerArgs fresh finalLayout sourceFinal target ctx) :
    requiredFuel result ≤
      argsPrepared.prepared.prepared.requiredFuel + bodyFuel + 3 := by
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
      { shared := body.bodyOutcome.state.source.shared
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
  have hCallBlock :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx (bodyFuel + 3)
          { stmts :=
              [Functions.Stmt.call targets functionName lowerArgs] }
          targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            argsPrepared.prepared.prepared.finalCtx) := by
    simpa [Nat.max_eq_left (by omega : 1 ≤ bodyFuel + 2),
      Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_cons_regular_at_max
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hCallRun hCallEmpty
  have hFullRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx
          (argsPrepared.prepared.prepared.requiredFuel + bodyFuel + 3)
          { stmts :=
              preArgs ++
                [Functions.Stmt.call targets functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget,
            argsPrepared.prepared.prepared.finalCtx) := by
    simpa [Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program preArgs
        [Functions.Stmt.call targets functionName lowerArgs]
        ctx argsPrepared.prepared.prepared.finalCtx target targetAfterArgs
        (Functions.Source.Effectful.Outcome.regular finalTarget)
        argsPrepared.prepared.prepared.finalCtx
        argsPrepared.prepared.prepared.requiredFuel (bodyFuel + 3)
        (FunctionsObserverExpression.Prepared.run_requiredFuel
          argsPrepared.prepared.prepared)
        hCallBlock
  obtain ⟨hFinalTarget, hFinalCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hFullRun (run_requiredFuel result)
  rw [hFinalTarget, hFinalCtx] at hFullRun
  exact requiredFuel_le_of_run result hFullRun

/--
The ordinary visible-target returned-call constructor admits an explicit
target-fuel bound.
-/
theorem ofReturnedBody_bounded
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
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
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
      { result :
          FunctionsObserverCall.ScopedReturnedCall
            contract transcript codeRel program functionName targets
            preArgs lowerArgs fresh layout sourceFinal target ctx //
        requiredFuel result ≤
          argsPrepared.prepared.prepared.requiredFuel + bodyFuel + 3 } := by
  obtain ⟨result⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofReturnedBody
      argsPrepared hTargetsNodup hTargetsVisible hFind body
      hReturnValues hLength hSourceFinal
  have hTargetsContain :
      ∀ name, name ∈ targets →
        argsPrepared.prepared.prepared.finalTarget.source.vars.contains name =
          true := by
    obtain
        ⟨_sourceShared, _sourceVars, _hSource, _hShared,
          hScoped, hSourceDomain⟩ :=
      argsPrepared.relation.2
    intro name hMem
    exact
      StateRelation.Vars.target_contains_of_scopedExact
        hScoped hSourceDomain (hTargetsVisible name hMem)
  exact
    ⟨⟨result,
      requiredFuel_le_of_parts
        argsPrepared hTargetsNodup hTargetsContain hFind body
        hReturnValues hLength result⟩⟩

/--
Fresh declaration targets use the same call execution bound; only the
writeback relation differs in the ordinary pass-owned constructor.
-/
theorem ofReturnedBodyFresh_bounded
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
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
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
      { result :
          FunctionsObserverCall.ScopedReturnedCall
            contract transcript codeRel program functionName targets
            preArgs lowerArgs fresh (targets ++ layout)
            sourceFinal target ctx //
        requiredFuel result ≤
          argsPrepared.prepared.prepared.requiredFuel + bodyFuel + 3 } := by
  obtain ⟨result⟩ :=
    FunctionsObserverCall.ScopedReturnedCall.ofReturnedBodyFresh
      argsPrepared hTargetsNodup hTargetsFresh hTargetsContain hFind body
      hReturnValues hLength hSourceFinal
  exact
    ⟨⟨result,
      requiredFuel_le_of_parts
        argsPrepared hTargetsNodup hTargetsContain hFind body
        hReturnValues hLength result⟩⟩

/--
Source-fuel lifting for returned calls. Argument preparation and the recursive
body are strictly smaller source computations, so the pass-owned target budget
absorbs both child runs and the three call-wrapper units.
-/
theorem ofReturnedBody_sourceBounded
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
    {bodyFuel argsSourceFuel bodySourceFuel sourceFuel : Nat}
    {sourceAfterArgs sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh layout
        sourceAfterArgs target ctx argValues)
    (hArgsBound :
      argsPrepared.prepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.targetBudget argsSourceFuel)
    (hArgsFuel : argsSourceFuel < sourceFuel)
    (hTargetsNodup : targets.Nodup)
    (hTargetsVisible :
      ∀ name, name ∈ targets → name ∈ layout)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hBodyBound :
      bodyFuel ≤ FunctionsObserverFuel.targetBudget bodySourceFuel)
    (hBodyFuel : bodySourceFuel < sourceFuel)
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
      { result :
          FunctionsObserverCall.ScopedReturnedCall
            contract transcript codeRel program functionName targets
            preArgs lowerArgs fresh layout sourceFinal target ctx //
        requiredFuel result ≤
          FunctionsObserverFuel.targetBudget sourceFuel } := by
  obtain ⟨bounded⟩ :=
    ofReturnedBody_bounded
      argsPrepared hTargetsNodup hTargetsVisible hFind body
      hReturnValues hLength hSourceFinal
  have hBudget :=
    FunctionsObserverFuel.two_children_add_eight_le_of_lt
      hArgsFuel hBodyFuel
  exact
    ⟨⟨bounded.1, by
        calc
          requiredFuel bounded.1 ≤
              argsPrepared.prepared.prepared.requiredFuel +
                bodyFuel + 3 :=
            bounded.2
          _ ≤
              FunctionsObserverFuel.targetBudget argsSourceFuel +
                FunctionsObserverFuel.targetBudget bodySourceFuel + 8 := by
            omega
          _ ≤ FunctionsObserverFuel.targetBudget sourceFuel :=
            hBudget⟩⟩

/--
Source-fuel lifting for fresh declaration targets. The target declaration
writeback changes the final layout but does not add runtime work.
-/
theorem ofReturnedBodyFresh_sourceBounded
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
    {bodyFuel argsSourceFuel bodySourceFuel sourceFuel : Nat}
    {sourceAfterArgs sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh layout
        sourceAfterArgs target ctx argValues)
    (hArgsBound :
      argsPrepared.prepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.targetBudget argsSourceFuel)
    (hArgsFuel : argsSourceFuel < sourceFuel)
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
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hBodyBound :
      bodyFuel ≤ FunctionsObserverFuel.targetBudget bodySourceFuel)
    (hBodyFuel : bodySourceFuel < sourceFuel)
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
      { result :
          FunctionsObserverCall.ScopedReturnedCall
            contract transcript codeRel program functionName targets
            preArgs lowerArgs fresh (targets ++ layout)
            sourceFinal target ctx //
        requiredFuel result ≤
          FunctionsObserverFuel.targetBudget sourceFuel } := by
  obtain ⟨bounded⟩ :=
    ofReturnedBodyFresh_bounded
      argsPrepared hTargetsNodup hTargetsFresh hTargetsContain hFind body
      hReturnValues hLength hSourceFinal
  have hBudget :=
    FunctionsObserverFuel.two_children_add_eight_le_of_lt
      hArgsFuel hBodyFuel
  exact
    ⟨⟨bounded.1, by
        calc
          requiredFuel bounded.1 ≤
              argsPrepared.prepared.prepared.requiredFuel +
                bodyFuel + 3 :=
            bounded.2
          _ ≤
              FunctionsObserverFuel.targetBudget argsSourceFuel +
                FunctionsObserverFuel.targetBudget bodySourceFuel + 8 := by
            omega
          _ ≤ FunctionsObserverFuel.targetBudget sourceFuel :=
            hBudget⟩⟩

/--
Heterogeneous source-cost lifting for visible returned-call targets.
-/
theorem ofReturnedBody_sourceBoundedOfCosts
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
    {bodyFuel argsSourceFuel bodySourceFuel sourceFuel : Nat}
    {argsStatic bodyStatic resultStatic : Nat}
    {sourceAfterArgs sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh layout
        sourceAfterArgs target ctx argValues)
    (hArgsBound :
      argsPrepared.prepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.executionBudget
          argsStatic argsSourceFuel)
    (hArgsFuel : argsSourceFuel < sourceFuel)
    (hTargetsNodup : targets.Nodup)
    (hTargetsVisible :
      ∀ name, name ∈ targets → name ∈ layout)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hBodyBound :
      bodyFuel ≤
        FunctionsObserverFuel.executionBudget
          bodyStatic bodySourceFuel)
    (hBodyFuel : bodySourceFuel < sourceFuel)
    (hStatic :
      argsStatic + bodyStatic + 1 ≤ resultStatic)
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
      { result :
          FunctionsObserverCall.ScopedReturnedCall
            contract transcript codeRel program functionName targets
            preArgs lowerArgs fresh layout sourceFinal target ctx //
        requiredFuel result ≤
          FunctionsObserverFuel.executionBudget
            resultStatic sourceFuel } := by
  obtain ⟨bounded⟩ :=
    ofReturnedBody_bounded
      argsPrepared hTargetsNodup hTargetsVisible hFind body
      hReturnValues hLength hSourceFinal
  have hChildren :=
    FunctionsObserverFuel.executionBudget_static_two_children_add_eight_le_of_lt
      argsStatic bodyStatic hArgsFuel hBodyFuel
  have hResultStatic :=
    FunctionsObserverFuel.executionBudget_static_mono hStatic sourceFuel
  exact
    ⟨⟨bounded.1, by
        calc
          requiredFuel bounded.1 ≤
              argsPrepared.prepared.prepared.requiredFuel +
                bodyFuel + 3 :=
            bounded.2
          _ ≤
              FunctionsObserverFuel.executionBudget
                  argsStatic argsSourceFuel +
                FunctionsObserverFuel.executionBudget
                  bodyStatic bodySourceFuel + 8 := by
            omega
          _ ≤
              FunctionsObserverFuel.executionBudget
                (argsStatic + bodyStatic + 1) sourceFuel :=
            hChildren
          _ ≤
              FunctionsObserverFuel.executionBudget
                resultStatic sourceFuel :=
            hResultStatic⟩⟩

/--
Heterogeneous source-cost lifting for fresh returned-call declaration targets.
-/
theorem ofReturnedBodyFresh_sourceBoundedOfCosts
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
    {bodyFuel argsSourceFuel bodySourceFuel sourceFuel : Nat}
    {argsStatic bodyStatic resultStatic : Nat}
    {sourceAfterArgs sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh layout
        sourceAfterArgs target ctx argValues)
    (hArgsBound :
      argsPrepared.prepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.executionBudget
          argsStatic argsSourceFuel)
    (hArgsFuel : argsSourceFuel < sourceFuel)
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
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody argsPrepared.prepared.prepared.finalTarget)
    (hBodyBound :
      bodyFuel ≤
        FunctionsObserverFuel.executionBudget
          bodyStatic bodySourceFuel)
    (hBodyFuel : bodySourceFuel < sourceFuel)
    (hStatic :
      argsStatic + bodyStatic + 1 ≤ resultStatic)
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
      { result :
          FunctionsObserverCall.ScopedReturnedCall
            contract transcript codeRel program functionName targets
            preArgs lowerArgs fresh (targets ++ layout)
            sourceFinal target ctx //
        requiredFuel result ≤
          FunctionsObserverFuel.executionBudget
            resultStatic sourceFuel } := by
  obtain ⟨bounded⟩ :=
    ofReturnedBodyFresh_bounded
      argsPrepared hTargetsNodup hTargetsFresh hTargetsContain hFind body
      hReturnValues hLength hSourceFinal
  have hChildren :=
    FunctionsObserverFuel.executionBudget_static_two_children_add_eight_le_of_lt
      argsStatic bodyStatic hArgsFuel hBodyFuel
  have hResultStatic :=
    FunctionsObserverFuel.executionBudget_static_mono hStatic sourceFuel
  exact
    ⟨⟨bounded.1, by
        calc
          requiredFuel bounded.1 ≤
              argsPrepared.prepared.prepared.requiredFuel +
                bodyFuel + 3 :=
            bounded.2
          _ ≤
              FunctionsObserverFuel.executionBudget
                  argsStatic argsSourceFuel +
                FunctionsObserverFuel.executionBudget
                  bodyStatic bodySourceFuel + 8 := by
            omega
          _ ≤
              FunctionsObserverFuel.executionBudget
                (argsStatic + bodyStatic + 1) sourceFuel :=
            hChildren
          _ ≤
              FunctionsObserverFuel.executionBudget
                resultStatic sourceFuel :=
            hResultStatic⟩⟩

end ScopedReturnedCall

namespace PreparedValue

/--
A value-returning function call adds six target-fuel units around argument
preparation and the recursively executed function body: three for the hidden
return-slot declaration block and three for the call statement block.
-/
theorem ofReturnedCall_requiredFuel_le
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
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
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
    (FunctionsObserverCall.PreparedValue.ofReturnedCall
        argsPrepared hFresh hFind body hSourceFinal
        hReturnValues).requiredFuel ≤
      argsPrepared.prepared.requiredFuel + bodyFuel + 6 := by
  let targetAfterArgs := argsPrepared.prepared.finalTarget
  let targetWithZero :=
    targetAfterArgs.withSource
      (targetAfterArgs.source.insert tmp Functions.Source.zero)
  have hNotMem : tmp ∉ argsFresh.used :=
    Fresh.not_mem_of_fresh? hFresh
  have hTargetHidden : targetAfterArgs.source.vars tmp = none :=
    argsPrepared.prepared.domain.lookup_none hNotMem
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
  have hZeroTarget :
      zeroPrepared.finalTarget = targetWithZero := by
    rfl
  have hBody' :
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
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
          program fn argValues (bodyFuel + 1)
          zeroPrepared.finalTarget =
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
  let targetAfterCall :=
    hBody'.bodyOutcome.state.withSource
      { shared := hBody'.bodyOutcome.state.source.shared
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
          (.call [tmp] functionName lowerArgs)
          zeroPrepared.finalTarget =
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
  have hCallEmpty :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program zeroPrepared.finalCtx 1 { stmts := [] }
          targetAfterCall =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfterCall,
            zeroPrepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_nil
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program zeroPrepared.finalCtx 0 targetAfterCall
  have hCallBlock :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program zeroPrepared.finalCtx (bodyFuel + 3)
          { stmts :=
              [Functions.Stmt.call [tmp] functionName lowerArgs] }
          zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfterCall,
            zeroPrepared.finalCtx) := by
    simpa [Nat.max_eq_left (by omega : 1 ≤ bodyFuel + 2),
      Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_cons_regular_at_max
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hCallRun hCallEmpty
  have hZeroRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.finalCtx 3
          { stmts :=
              [Functions.Stmt.let_ tmp (.lit Functions.Source.zero)] }
          targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            zeroPrepared.finalTarget,
            zeroPrepared.finalCtx) :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program
      (FunctionsObserverExpression.Prepared.requiredFuel_generated_le
        (program := program)
        hFresh hZeroEval argsPrepared.prepared.rel
        argsPrepared.prepared.domain argsPrepared.prepared.scope)
      (FunctionsObserverExpression.Prepared.run_requiredFuel zeroPrepared)
  have hSuffixRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.finalCtx (bodyFuel + 6)
          { stmts :=
              [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                Functions.Stmt.call [tmp] functionName lowerArgs] }
          targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfterCall,
            zeroPrepared.finalCtx) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero)]
        [Functions.Stmt.call [tmp] functionName lowerArgs]
        argsPrepared.prepared.finalCtx zeroPrepared.finalCtx
        targetAfterArgs zeroPrepared.finalTarget
        (Functions.Source.Effectful.Outcome.regular targetAfterCall)
        zeroPrepared.finalCtx 3 (bodyFuel + 3)
        hZeroRun hCallBlock
  have hFullRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx
          (argsPrepared.prepared.requiredFuel + bodyFuel + 6)
          { stmts :=
              preArgs ++
                [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
                  Functions.Stmt.call [tmp] functionName lowerArgs] }
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfterCall,
            zeroPrepared.finalCtx) := by
    simpa [Nat.add_assoc] using
      Functions.Source.Effectful.Block.runOpen_append_regular_at_add
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program preArgs
        [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
          Functions.Stmt.call [tmp] functionName lowerArgs]
        ctx argsPrepared.prepared.finalCtx target targetAfterArgs
        (Functions.Source.Effectful.Outcome.regular targetAfterCall)
        zeroPrepared.finalCtx argsPrepared.prepared.requiredFuel
        (bodyFuel + 6)
        (FunctionsObserverExpression.Prepared.run_requiredFuel
          argsPrepared.prepared)
        hSuffixRun
  let result :=
    FunctionsObserverCall.PreparedValue.ofReturnedCall
      argsPrepared hFresh hFind body hSourceFinal hReturnValues
  have hResultRun :=
    FunctionsObserverExpression.PreparedValue.run_requiredFuel result
  obtain ⟨hFinalTarget, hFinalCtx⟩ :=
    Functions.Source.Effectful.Block.runOpen_regular_unique
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hFullRun hResultRun
  rw [hFinalTarget, hFinalCtx] at hFullRun
  exact
    FunctionsObserverExpression.PreparedValue.requiredFuel_le_of_run
      result hFullRun

/--
Source-fuel lifting for a value-returning call. Argument preparation and the
function body are strictly smaller source computations; the shared two-child
budget absorbs both plus the six call-prelude units.
-/
theorem ofReturnedCall_sourceBounded
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
    {bodyFuel argsSourceFuel bodySourceFuel sourceFuel staticCost : Nat}
    {sourceCaller sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Word}
    (argsPrepared :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program preArgs lowerArgs argsFresh
        sourceCaller target ctx argValues)
    (hArgsBound :
      argsPrepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.executionBudget
          staticCost argsSourceFuel)
    (hArgsFuel : argsSourceFuel < sourceFuel)
    (hFresh : Fresh.fresh? argsFresh = some (tmp, finalFresh))
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody
        (argsPrepared.prepared.finalTarget.withSource
          (argsPrepared.prepared.finalTarget.source.insert
            tmp Functions.Source.zero)))
    (hBodyBound :
      bodyFuel ≤
        FunctionsObserverFuel.executionBudget
          staticCost bodySourceFuel)
    (hBodyFuel : bodySourceFuel < sourceFuel)
    (hSourceFinal :
      sourceFinal =
        sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
    (hReturnValues :
      List.map sourceAfterBody.source.lookup! fn.returns = [value]) :
    FunctionsObserverFuel.PreparedValue.Bounded staticCost sourceFuel
      (FunctionsObserverCall.PreparedValue.ofReturnedCall
        argsPrepared hFresh hFind body hSourceFinal hReturnValues) := by
  have hRequired :=
    ofReturnedCall_requiredFuel_le
      argsPrepared hFresh hFind body hSourceFinal hReturnValues
  have hBudget :=
    FunctionsObserverFuel.executionBudget_two_children_add_eight_le_of_lt
      staticCost hArgsFuel hBodyFuel
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded]
  omega

/--
Heterogeneous source-cost lifting for a value-returning call. This is the
call-aware form used when argument syntax and the selected callee body carry
different source-owned static costs.
-/
theorem ofReturnedCall_sourceBoundedOfCosts
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
    {bodyFuel argsSourceFuel bodySourceFuel sourceFuel : Nat}
    {argsStatic bodyStatic resultStatic : Nat}
    {sourceCaller sourceAfterBody sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {value : Word}
    (argsPrepared :
      FunctionsObserverExpression.PreparedArgs
        contract transcript codeRel program preArgs lowerArgs argsFresh
        sourceCaller target ctx argValues)
    (hArgsBound :
      argsPrepared.prepared.requiredFuel ≤
        FunctionsObserverFuel.executionBudget
          argsStatic argsSourceFuel)
    (hArgsFuel : argsSourceFuel < sourceFuel)
    (hFresh : Fresh.fresh? argsFresh = some (tmp, finalFresh))
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (body :
      FunctionsObserverCall.ReturnedBody
        contract transcript codeRel program fn argValues bodyFuel
        sourceAfterBody
        (argsPrepared.prepared.finalTarget.withSource
          (argsPrepared.prepared.finalTarget.source.insert
            tmp Functions.Source.zero)))
    (hBodyBound :
      bodyFuel ≤
        FunctionsObserverFuel.executionBudget
          bodyStatic bodySourceFuel)
    (hBodyFuel : bodySourceFuel < sourceFuel)
    (hStatic :
      argsStatic + bodyStatic + 1 ≤ resultStatic)
    (hSourceFinal :
      sourceFinal =
        sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
    (hReturnValues :
      List.map sourceAfterBody.source.lookup! fn.returns = [value]) :
    FunctionsObserverFuel.PreparedValue.Bounded resultStatic sourceFuel
      (FunctionsObserverCall.PreparedValue.ofReturnedCall
        argsPrepared hFresh hFind body hSourceFinal hReturnValues) := by
  have hRequired :=
    ofReturnedCall_requiredFuel_le
      argsPrepared hFresh hFind body hSourceFinal hReturnValues
  have hChildren :=
    FunctionsObserverFuel.executionBudget_static_two_children_add_eight_le_of_lt
      argsStatic bodyStatic hArgsFuel hBodyFuel
  have hResultStatic :=
    FunctionsObserverFuel.executionBudget_static_mono hStatic sourceFuel
  dsimp [FunctionsObserverFuel.PreparedValue.Bounded]
  omega

end PreparedValue

namespace ScopedPreparedValue

/--
Quantitative forward preservation for a one-result internal function call.

The argument prelude is bounded by the runtime cost of the source arguments,
and the recursively selected body is bounded by its source statement cost.
The source lookup connects that body cost to the call expression's
source-owned runtime cost.
-/
theorem ofFunctionCall_bounded
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
      RecursiveScopedExpressionForwardBounded
        contract transcript codeRel sourceProgram targetProgram profile fuel)
    (hBody :
      RecursiveBodyForwardBounded
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
      { result :
          FunctionsObserverExpression.ScopedPreparedValue
            contract transcript codeRel targetProgram.toFunctions
            pre lower final vars sourceFinal target ctx value //
        FunctionsObserverFuel.PreparedValue.Bounded
          (FunctionsObserverStaticCost.runtimeExpr sourceProgram
            (.Call (.inr functionName) args))
          fuel result.prepared } := by
  obtain
      ⟨callFuel, sourceAfterArgs, reversedValues, returnValues,
        hFuel, hArgsRun, hCallRun, hValue⟩ :=
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
            { result :
                FunctionsObserverExpression.ScopedPreparedArgs
                  contract transcript codeRel targetProgram.toFunctions
                  preArgs lowerArgs argsFresh vars sourceAfterArgs target ctx
                  reversedValues.reverse //
              FunctionsObserverFuel.PreparedArgs.Bounded
                (FunctionsObserverStaticCost.runtimeExprList
                  sourceProgram args)
                bodyFuel.succ result.prepared } := by
        cases hArgsLowering with
        | empty =>
            simp [Yul.Source.Effectful.evalArgs] at hArgsRun
            rcases hArgsRun with ⟨rfl, rfl⟩
            let prepared :=
              FunctionsObserverExpression.PreparedArgs.empty
                (contract := contract)
                (program := targetProgram.toFunctions)
                (StateRelation.Replay.rel_of_scopedExact hRel)
                hDomain hScope
            let result :
                FunctionsObserverExpression.ScopedPreparedArgs
                  contract transcript codeRel targetProgram.toFunctions
                  [] [] initial vars source target ctx [] :=
              { prepared := prepared
                relation := hRel }
            refine ⟨⟨result, ?_⟩⟩
            simpa [FunctionsObserverStaticCost.runtimeExprList,
              result, prepared] using
              FunctionsObserverExpressionFuel.PreparedArgs.empty_bounded
                (contract := contract)
                (program := targetProgram.toFunctions)
                bodyFuel.succ
                (StateRelation.Replay.rel_of_scopedExact hRel)
                hDomain hScope
        | bound hNonempty hArgsLowering =>
            obtain ⟨bounded⟩ :=
              FunctionsObserverExpressionFuel.ScopedPreparedArgs.ofUncheckedLowering_bounded
                  (FunctionsObserverStaticCost.runtimeExpr sourceProgram)
                  hArgsLowering
                  (fun expr hMem =>
                    SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem)
                  (fun hLt hArgOk hExprLower hExprRel hExprDomain
                      hExprScope hExprRun =>
                    hExpr (by omega) hArgOk hExprLower hExprRel
                      hExprDomain hExprScope hExprRun)
                  hRel hDomain hScope hArgsRun
            exact
              ⟨⟨bounded.1, by
                  simpa
                    [FunctionsObserverStaticCost.runtimeExprList_eq_exprListBy] using
                    bounded.2⟩⟩
      obtain ⟨preparedArgsBounded⟩ := hPreparedArgs
      let preparedArgs := preparedArgsBounded.1
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
              { shared := targetCaller.source.shared
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
      obtain ⟨targetBodyFuel, returnedBodyBoundedNonempty⟩ :=
        hBody (by omega) hLowerBody hParams hFnReturns
          (by simpa [hParams] using hParamStore)
          hReserved hBodyNames hBodyOk hEntry hBodyRun
      obtain ⟨returnedBodyBounded⟩ := returnedBodyBoundedNonempty
      let returnedBody := returnedBodyBounded.1
      have hReturnedValues :
          List.map sourceAfterBody.source.lookup! fn.returns = [value] := by
        have hReturnValue :
            value = sourceAfterBody.source.lookup! returnName := by
          rw [hSourceReturns] at hValue
          simpa using hValue
        rw [hFnReturns]
        simp [identNames, identName, ← hReturnValue]
      let prepared :=
        FunctionsObserverCall.PreparedValue.ofReturnedCall
          preparedArgs.prepared hFresh hFind returnedBody
          hSourceFinal hReturnedValues
      have hArgsBound :
          preparedArgs.prepared.prepared.requiredFuel ≤
            FunctionsObserverFuel.executionBudget
              (FunctionsObserverStaticCost.runtimeExprList
                sourceProgram args)
              bodyFuel.succ := by
        exact preparedArgsBounded.2
      have hBodyStatic :
          FunctionsObserverStaticCost.stmtList body ≤
            FunctionsObserverStaticCost.calleeCost
              sourceProgram functionName :=
        FunctionsObserverStaticCost.function_body_le_calleeCost_of_lookup
          hLookup
      have hStatic :
          FunctionsObserverStaticCost.runtimeExprList sourceProgram args +
                FunctionsObserverStaticCost.stmtList body + 1 ≤
            FunctionsObserverStaticCost.runtimeExpr sourceProgram
              (.Call (.inr functionName) args) := by
        simp only [FunctionsObserverStaticCost.runtimeExpr]
        omega
      have hPreparedBounded :
          FunctionsObserverFuel.PreparedValue.Bounded
            (FunctionsObserverStaticCost.runtimeExpr sourceProgram
              (.Call (.inr functionName) args))
            fuel prepared := by
        exact
          PreparedValue.ofReturnedCall_sourceBoundedOfCosts
            preparedArgs.prepared hArgsBound (by omega)
            hFresh hFind returnedBody returnedBodyBounded.2 (by omega)
            hStatic hSourceFinal hReturnedValues
      let result :
          FunctionsObserverExpression.ScopedPreparedValue
            contract transcript codeRel targetProgram.toFunctions
            (preArgs ++
              [.let_ tmp (.lit Functions.Source.zero),
                .call [tmp] functionName lowerArgs])
            (.var tmp) final vars sourceFinal target ctx value :=
        { prepared := prepared
          relation := by
            apply StateRelation.Replay.scopedExact_of_rel_store prepared.rel
            rw [hSourceFinal]
            change
              StateRelation.Vars.DomainExact vars
                (((sourceAfterBody.source.reviveJump.overwrite?
                  sourceAfterArgs.source).setStore
                    sourceAfterArgs.source).store)
            have hRestoredStore :
                ((sourceAfterBody.source.reviveJump.overwrite?
                    sourceAfterArgs.source).setStore
                      sourceAfterArgs.source).store =
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
                preparedArgs.relation }
      exact
        ⟨⟨result, by
            simpa [result, prepared] using hPreparedBounded⟩⟩

end ScopedPreparedValue

namespace RecursiveScopedValueForwardBounded

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
      RecursiveBodyForwardBounded
        contract transcript codeRel sourceProgram targetProgram profile
        bound) :
    RecursiveScopedValueForwardBounded
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  intro exprFuel
  induction exprFuel using Nat.strong_induction_on with
  | h exprFuel ih =>
      intro before after layout expr pre lower source source'
        target ctx values hFuel hOk hLower hRel hDomain hScope hRun
      have hSmallerValue :
          RecursiveScopedValueForwardBounded
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
          RecursiveScopedExpressionForwardBounded
            contract transcript codeRel sourceProgram targetProgram
            profile exprFuel :=
        RecursiveScopedValueForwardBounded.expression hSmallerValue
      have hSmallerBody :
          RecursiveBodyForwardBounded
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
          simpa [FunctionsObserverStaticCost.runtimeExpr] using
            FunctionsObserverExpressionFuel.ScopedPreparedValue.ofLiteral_bounded
                hLower hRel hDomain hScope hRun
      | Var name =>
          simpa [FunctionsObserverStaticCost.runtimeExpr] using
            FunctionsObserverExpressionFuel.ScopedPreparedValue.ofVariable_bounded
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
                FunctionsObserverExpressionFuel.ScopedPreparedValue.ofPrimitive_bounded
                    (sourceProgram := sourceProgram)
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
                                  ScopedPreparedValue.ofFunctionCall_bounded
                                    hDecomposition hLower hProgramOk hOk
                                    hSmallerExpr hSmallerBody hRel
                                    hDomain hScope hEval⟩
                          | cons next tail =>
                              simp at hLength

end RecursiveScopedValueForwardBounded

end FunctionsObserverCallFuel
end Yul
end EvmCompiler
