import EvmCompiler.Functions.EffectSemanticsInversion
import EvmCompiler.Yul.FunctionsObserverCall
import EvmCompiler.Yul.FunctionsObserverFuel

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCallFuel

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

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

end ScopedReturnedCall

end FunctionsObserverCallFuel
end Yul
end EvmCompiler
