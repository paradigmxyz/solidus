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
    (targetCaller : Functions.InteractionSemantics.State) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Assembly.Word) →
      Except EVMException Functions.InteractionSemantics.CallResult → Prop where
  | error {source target} :
      ErrorRel source target →
        RunBodyDoneRel callerLayout sourceCaller targetCaller
          (.error source) (.error target)
  | returned {sourceAfter targetAfter values} :
      ScopedStateRel callerLayout sourceAfter
        { shared := targetAfter.shared, vars := targetCaller.vars } →
        RunBodyDoneRel callerLayout sourceCaller targetCaller
          (.ok (sourceAfter, values))
          (.ok (Functions.Source.Effectful.CallResult.returned
            targetAfter values))
  | terminal {source kind target} :
      TerminalFailureRel source
        (Functions.Source.Effectful.Outcome.halt kind target) →
        RunBodyDoneRel callerLayout sourceCaller targetCaller
          (.error source)
          (.ok (Functions.Source.Effectful.CallResult.halted kind target))

/-- Lift a related validated function body through canonical Functions
`runBody`. The caller frame is restored only on ordinary return; terminal
effects retain the callee's terminal state. -/
theorem runBodyForward
    {targetBodyFuel : Nat}
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Assembly.Word} {paramStore : Locals.Source.Store}
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
      (RunBodyDoneRel callerLayout sourceCaller targetCaller)
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
      (RunBodyDoneRel callerLayout sourceCaller targetCaller)
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
            (sourceCaller := sourceCaller) hRestored)
      · simp only
        rw [hMode, hReturns']
        exact Simulation.Interaction.ForwardRel.done
          (RunBodyDoneRel.returned
            (sourceCaller := sourceCaller) hRestored)

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
