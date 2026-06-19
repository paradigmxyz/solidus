import EvmCompiler.Yul.FunctionsInteractionPreparedCall

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionCall

open FunctionsInteractionRelation
open FunctionsInteractionPrimitive

/-- Function-body completion excludes uncaught break/continue. Recursive
statement preservation supplies this relation for validated function bodies. -/
inductive FunctionBodyDoneRel (layout : List Functions.Name) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Prop where
  | error {source target} :
      ErrorRel source target →
        FunctionBodyDoneRel layout (.error source) (.error target)
  | returned {source target ctx} :
      ScopedOutcomeRel layout source target →
      (target.mode = .regular ∨ target.mode = .leave) →
        FunctionBodyDoneRel layout (.ok source) (.ok (target, ctx))
  | terminal {source target ctx} :
      TerminalFailureRel source target →
        FunctionBodyDoneRel layout (.error source) (.ok (target, ctx))

/-- Result relation after canonical `runBody`, before the call statement writes
returned values into its target locals. -/
inductive RunBodyDoneRel
    (callerLayout : List Functions.Name)
    (sourceCaller : Yul.InteractionSemantics.State)
    (targetCaller : Functions.InteractionSemantics.State)
    (results : Nat) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Assembly.Word) →
      Except EVMException Functions.InteractionSemantics.CallResult → Prop where
  | error {source target} :
      ErrorRel source target →
        RunBodyDoneRel callerLayout sourceCaller targetCaller results
          (.error source) (.error target)
  | returned {sourceAfter targetAfter values} :
      ScopedStateRel callerLayout sourceAfter
        { shared := targetAfter.shared, vars := targetCaller.vars } →
      values.length = results →
        RunBodyDoneRel callerLayout sourceCaller targetCaller results
          (.ok (sourceAfter, values))
          (.ok (Functions.Source.Effectful.CallResult.returned
            targetAfter values))
  | terminal {source kind target} :
      TerminalFailureRel source
        (Functions.Source.Effectful.Outcome.halt kind target) →
        RunBodyDoneRel callerLayout sourceCaller targetCaller results
          (.error source)
          (.ok (Functions.Source.Effectful.CallResult.halted kind target))

/-- Lift a related validated function body through canonical Functions
`runBody`. The caller frame is restored only on ordinary return; terminal
effects retain the callee's terminal state. -/
theorem runBodyForward
    {targetBodyFuel : Nat}
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Assembly.Word} {paramStore : Locals.Source.Store}
    {results : Nat}
    {callerLayout : List Functions.Name}
    {sourceCaller : Yul.InteractionSemantics.State}
    {targetCaller : Functions.InteractionSemantics.State}
    {sourceBody :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State}
    {targetBody :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hParams :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hCaller : ScopedStateRel callerLayout sourceCaller targetCaller)
    (hResults : fn.returns.length = results)
    (hBody :
      Simulation.Interaction.ForwardRel
        FunctionsInteractionPrimitive.Truncated
        (FunctionBodyDoneRel (fn.returns ++ fn.params))
        sourceBody targetBody)
    (hTargetBody :
      targetBody =
        Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) targetBodyFuel fn.body
          (Functions.InteractionSemantics.stateModel.withSource targetCaller
            { shared :=
                (Functions.InteractionSemantics.stateModel.source
                  targetCaller).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore })) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated
      (RunBodyDoneRel callerLayout sourceCaller targetCaller results)
      (Simulation.Interaction.bind sourceBody fun sourceAfterBody =>
        pure
          (((sourceAfterBody.reviveJump.overwrite? sourceCaller).setStore
              sourceCaller),
            List.map sourceAfterBody.lookup! fn.returns))
      (Functions.InteractionSemantics.FunDef.openRunBody
        program fn args (targetBodyFuel + 1) targetCaller) := by
  subst targetBody
  unfold Functions.InteractionSemantics.FunDef.openRunBody
    Functions.Source.Canonical.FunDef.runBody
    Functions.Source.Effectful.Control.FunDef.runBody
  rw [hParams]
  change
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated
      (RunBodyDoneRel callerLayout sourceCaller targetCaller results)
      (Simulation.Interaction.bind sourceBody _)
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) targetBodyFuel fn.body
          (Functions.InteractionSemantics.stateModel.withSource targetCaller
            { shared :=
                (Functions.InteractionSemantics.stateModel.source
                  targetCaller).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore })) _)
  apply Simulation.Interaction.ForwardRel.bind_custom hBody
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | @terminal source target ctx hTerminal =>
      rcases target with ⟨targetState, targetMode⟩
      cases targetMode with
      | halt kind =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal hTerminal)
      | regular | brk | cont | leave =>
          cases hTerminal
  | @returned source target ctx hScoped hMode =>
      have hFrame := hScoped.revived_state
      have hReturns :
          Functions.Source.Store.lookupMany fn.returns target.state.vars =
            some (List.map source.lookup! fn.returns) := by
        simpa [lookupBang_reviveJump] using
          hFrame.lookupMany (by
            intro name hMem
            exact List.mem_append_left fn.params hMem)
      have hRestored := hCaller.restore_call hFrame
      have hLength :
          (List.map source.lookup! fn.returns).length = results := by
        simp [hResults]
      have hReturns' :
          Functions.Source.Store.lookupMany fn.returns
              (Functions.InteractionSemantics.stateModel.vars target.state) =
            some (List.map source.lookup! fn.returns) := by
        exact hReturns
      rcases hMode with hMode | hMode
      · simp only
        rw [hMode, hReturns']
        exact Simulation.Interaction.ForwardRel.done
          (RunBodyDoneRel.returned
            (sourceCaller := sourceCaller) hRestored hLength)
      · simp only
        rw [hMode, hReturns']
        exact Simulation.Interaction.ForwardRel.done
          (RunBodyDoneRel.returned
            (sourceCaller := sourceCaller) hRestored hLength)

/-- Write one returned value into the fresh temporary used by internal-call
expression lowering. Ordinary errors and terminal halts pass through without
manufacturing a source result. -/
theorem finishSingleForward
    {before final : Fresh.State} {tmp : Functions.Name}
    {layout : List Functions.Name}
    {entry targetBefore targetCaller :
      Functions.InteractionSemantics.State}
    {sourceCaller : Yul.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceCall :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Assembly.Word)}
    {targetRunBody :
      Simulation.Interaction EVMException
        Functions.InteractionSemantics.CallResult}
    (hFresh : Fresh.fresh? before = some (tmp, final))
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hCallerState : targetCaller =
      targetBefore.insert tmp Functions.Source.zero)
    (hDomain : TargetDomainWithin before.used targetBefore.vars)
    (hExtends : TargetExtends entry.vars targetBefore.vars)
    (hRunBody :
      Simulation.Interaction.ForwardRel Truncated
        (RunBodyDoneRel layout sourceCaller targetCaller 1)
        sourceCall targetRunBody) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedArgs.DoneRel
        layout final [.var tmp] entry)
      sourceCall
      (Simulation.Interaction.bind targetRunBody
        (Functions.InteractionSemantics.Stmt.finishCall
          [tmp] ctx targetCaller)) := by
  apply Simulation.Interaction.ForwardRel.bind_right hRunBody
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminal =>
      exact Simulation.Interaction.ForwardRel.done (.terminal hTerminal)
  | @returned sourceAfter targetAfter values hScoped hLength =>
      obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLength
      obtain ⟨hFinalUsed, hTmpFresh⟩ := Fresh.fresh?_components hFresh
      have hTmpLayout : tmp ∉ layout := by
        intro hMem
        exact hTmpFresh (hLayout tmp hMem)
      have hTmpNone : targetBefore.vars tmp = none :=
        hDomain.lookup_none hTmpFresh
      have hInsertExtends :
          TargetExtends targetBefore.vars
            (Locals.Source.Store.insert targetBefore.vars tmp value) :=
        TargetExtends.insert_fresh hTmpNone
      have hFinalExtends :
          TargetExtends entry.vars
            (Locals.Source.Store.insert targetBefore.vars tmp value) :=
        TargetExtends.trans hExtends hInsertExtends
      have hFinalDomain :
          TargetDomainWithin final.used
            (Locals.Source.Store.insert targetBefore.vars tmp value) := by
        rw [hFinalUsed]
        exact hDomain.insert hTmpFresh
      have hFinalScoped := hScoped.insert_private hTmpLayout value
      have hStable :
          FunctionsInteractionExpression.StableArgs [.var tmp]
            { shared := targetAfter.shared
              vars := Locals.Source.Store.insert targetBefore.vars tmp value }
            [value] := by
        apply FunctionsInteractionExpression.StableArgs.cons
        · apply FunctionsInteractionExpression.StableValue.var
          simp [Locals.Source.Store.insert]
        · exact FunctionsInteractionExpression.StableArgs.nil _
      subst targetCaller
      have hOverwrite :
          Locals.Source.Store.insert
              (Locals.Source.Store.insert targetBefore.vars tmp
                Functions.Source.zero)
              tmp value =
            Locals.Source.Store.insert targetBefore.vars tmp value := by
        funext key
        by_cases hKey : key = tmp
        · subst key
          simp
        · simp [Locals.Source.Store.insert_of_ne hKey]
      have hFinalScoped' :
          ScopedStateRel layout sourceAfter
            { shared := targetAfter.shared
              vars := Locals.Source.Store.insert
                targetBefore.vars tmp value } := by
        change
          ScopedStateRel layout sourceAfter
            { shared := targetAfter.shared
              vars := Locals.Source.Store.insert
                (Locals.Source.Store.insert targetBefore.vars tmp
                  Functions.Source.zero)
                tmp value } at hFinalScoped
        rw [hOverwrite] at hFinalScoped
        exact hFinalScoped
      have hFinish :
          Functions.InteractionSemantics.Stmt.finishCall [tmp] ctx
              (targetBefore.insert tmp Functions.Source.zero)
              (Functions.Source.Effectful.CallResult.returned
                targetAfter [value]) =
            pure
              (Functions.Source.Effectful.Outcome.regular
                { shared := targetAfter.shared
                  vars := Locals.Source.Store.insert
                    targetBefore.vars tmp value },
                ctx) := by
        simp [Functions.InteractionSemantics.Stmt.finishCall,
          Functions.Source.Store.assignMany,
          Locals.Source.State.insert,
          Locals.Source.Store.contains, hOverwrite,
          Functions.InteractionSemantics.stateModel,
          Locals.InteractionSemantics.stateModel,
          Locals.Source.Effectful.Ordinary.stateModel,
          Locals.Source.Effectful.StateModel.vars,
          Locals.Source.Effectful.StateModel.withSource]
        rfl
      simp only
      rw [hFinish]
      exact
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated)
          (FunctionsInteractionPreparedArgs.DoneRel.regular
            hStable hFinalScoped' hFinalDomain hFinalExtends))

/-- Package one related regular/leave function body through the canonical
Functions `runBody` wrapper. Return values are read from the related source
frame, while caller locals are restored and callee shared-world effects are
retained. -/
theorem returnedBody
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Assembly.Word} {bodyFuel : Nat}
    {callerLayout : List Functions.Name}
    {sourceCaller sourceAfterBody : Yul.InteractionSemantics.State}
    {targetCaller targetAfterBody : Functions.InteractionSemantics.State}
    {bodyOutcome : Functions.InteractionSemantics.Outcome}
    {finalCtx : Functions.Source.Ctx}
    {paramStore : Locals.Source.Store}
    (hParams :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBody :
      Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) bodyFuel fn.body
          (Functions.InteractionSemantics.stateModel.withSource targetCaller
            { shared :=
                (Functions.InteractionSemantics.stateModel.source
                  targetCaller).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore }) =
        .done (.ok (bodyOutcome, finalCtx)))
    (hMode : bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave)
    (hBodyState : bodyOutcome.state = targetAfterBody)
    (hBodyRel : ScopedStateRel (fn.returns ++ fn.params)
      sourceAfterBody.reviveJump targetAfterBody)
    (hCaller : ScopedStateRel callerLayout sourceCaller targetCaller) :
    ∃ returnValues,
      Functions.InteractionSemantics.FunDef.openRunBody
          program fn args (bodyFuel + 1) targetCaller =
        .done (.ok
          (Functions.Source.Effectful.CallResult.returned
            targetAfterBody returnValues)) ∧
      returnValues =
        List.map sourceAfterBody.lookup! fn.returns ∧
      ScopedStateRel callerLayout
        ((sourceAfterBody.reviveJump.overwrite? sourceCaller).setStore
          sourceCaller)
        { shared := targetAfterBody.shared, vars := targetCaller.vars } := by
  have hReturns :
      Functions.Source.Store.lookupMany fn.returns targetAfterBody.vars =
        some (List.map sourceAfterBody.lookup! fn.returns) :=
    by
      simpa [lookupBang_reviveJump] using
        hBodyRel.lookupMany (by
          intro name hMem
          exact List.mem_append_left fn.params hMem)
  have hRunBody :
      Functions.InteractionSemantics.FunDef.openRunBody
          program fn args (bodyFuel + 1) targetCaller =
        .done (.ok
          (Functions.Source.Effectful.CallResult.returned targetAfterBody
            (List.map sourceAfterBody.lookup! fn.returns))) := by
    have hReturns' :
        Functions.Source.Store.lookupMany fn.returns
            (Functions.InteractionSemantics.stateModel.vars
              bodyOutcome.state) =
          some (List.map sourceAfterBody.lookup! fn.returns) := by
      rw [hBodyState]
      exact hReturns
    exact
      Functions.InteractionSemantics.FunDef.openRunBody_returned_of_parts
        hParams hBody hMode hReturns' hBodyState
  exact
    ⟨List.map sourceAfterBody.lookup! fn.returns, hRunBody, rfl,
      hCaller.restore_call hBodyRel⟩

/-- Package one related terminal function body through canonical `runBody`.
There is no return lookup or caller-local restoration after a halt. -/
theorem haltedBody
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Assembly.Word} {bodyFuel : Nat}
    {targetCaller haltedState : Functions.InteractionSemantics.State}
    {kind : Assembly.HaltKind} {finalCtx : Functions.Source.Ctx}
    {paramStore : Locals.Source.Store}
    (hParams :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBody :
      Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) bodyFuel fn.body
          (Functions.InteractionSemantics.stateModel.withSource targetCaller
            { shared :=
                (Functions.InteractionSemantics.stateModel.source
                  targetCaller).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore }) =
        .done (.ok
          (Functions.Source.Effectful.Outcome.halt kind haltedState,
            finalCtx))) :
    Functions.InteractionSemantics.FunDef.openRunBody
        program fn args (bodyFuel + 1) targetCaller =
      .done (.ok
        (Functions.Source.Effectful.CallResult.halted kind haltedState)) := by
  exact Functions.InteractionSemantics.FunDef.openRunBody_halted_of_parts
    hParams hBody

end FunctionsInteractionCall
end Yul
end EvmCompiler
