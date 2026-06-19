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

/-- Finish a multi-result source call and the canonical Functions target
writeback under a caller-supplied relation for the updated lexical domain. -/
theorem finishManyForward
    {results : Nat} {targets : List Functions.Name}
    {layout finalLayout : List Functions.Name}
    {sourceCaller : Yul.InteractionSemantics.State}
    {targetCaller : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceCall : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Assembly.Word)}
    {targetRunBody : Functions.InteractionSemantics.Open
      Functions.InteractionSemantics.CallResult}
    (hTargetCount : targets.length = results)
    (hContains : ∀ name, name ∈ targets →
      targetCaller.vars.contains name = true)
    (hWriteback :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State}
        {values : List Assembly.Word} {finalVars : Locals.Source.Store},
        ScopedStateRel layout sourceAfter
            { shared := targetAfter.shared, vars := targetCaller.vars } →
        Functions.Source.Store.insertMany targets values
            targetCaller.vars = some finalVars →
        ScopedStateRel finalLayout
          (sourceAfter.multifill targets values)
          { shared := targetAfter.shared, vars := finalVars })
    (hRunBody :
      Simulation.Interaction.ForwardRel Truncated
        (RunBodyDoneRel layout sourceCaller targetCaller results)
        sourceCall targetRunBody) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel finalLayout)
      (Simulation.Interaction.bind sourceCall fun result =>
        pure (result.1.multifill targets result.2))
      (Simulation.Interaction.bind targetRunBody
        (Functions.InteractionSemantics.Stmt.finishCall
          targets ctx targetCaller)) := by
  apply Simulation.Interaction.ForwardRel.bind_custom hRunBody
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminal =>
      exact Simulation.Interaction.ForwardRel.done (.terminal hTerminal)
  | @returned sourceAfter targetAfter values hScoped hLength =>
      have hValuesLength : values.length = targets.length := by
        omega
      obtain ⟨finalVars, hAssign⟩ :=
        Functions.Source.Store.assignMany_exists_of_length_of_contains
          (store := targetCaller.vars) hValuesLength hContains
      have hInsert :
          Functions.Source.Store.insertMany targets values
              targetCaller.vars = some finalVars :=
        Functions.Source.Store.insertMany_of_assignMany hAssign
      have hFinal := hWriteback hScoped hInsert
      have hFinish :
          Functions.InteractionSemantics.Stmt.finishCall targets ctx
              targetCaller
              (Functions.Source.Effectful.CallResult.returned
                targetAfter values) =
            pure
              (Functions.Source.Effectful.Outcome.regular
                { shared := targetAfter.shared, vars := finalVars }, ctx) := by
        simp [Functions.InteractionSemantics.Stmt.finishCall, hAssign,
          Functions.InteractionSemantics.stateModel,
          Locals.InteractionSemantics.stateModel,
          Locals.Source.Effectful.Ordinary.stateModel,
          Locals.Source.Effectful.StateModel.vars,
          Locals.Source.Effectful.StateModel.withSource]
        rfl
      simp only
      rw [hFinish]
      exact Simulation.Interaction.ForwardRel.done
        (.ok
          ⟨finalLayout,
            FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinal,
            fun _hRegular => rfl⟩)

/-- Multi-result call writeback introducing fresh source bindings. -/
theorem finishManyFresh
    {results : Nat} {targets : List Functions.Name}
    {layout : List Functions.Name}
    {sourceCaller : Yul.InteractionSemantics.State}
    {targetCaller : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceCall : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Assembly.Word)}
    {targetRunBody : Functions.InteractionSemantics.Open
      Functions.InteractionSemantics.CallResult}
    (hTargetCount : targets.length = results)
    (hNodup : targets.Nodup)
    (hFresh : ∀ name, name ∈ targets → name ∉ layout)
    (hContains : ∀ name, name ∈ targets →
      targetCaller.vars.contains name = true)
    (hRunBody :
      Simulation.Interaction.ForwardRel Truncated
        (RunBodyDoneRel layout sourceCaller targetCaller results)
        sourceCall targetRunBody) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel (targets ++ layout))
      (Simulation.Interaction.bind sourceCall fun result =>
        pure (result.1.multifill targets result.2))
      (Simulation.Interaction.bind targetRunBody
        (Functions.InteractionSemantics.Stmt.finishCall
          targets ctx targetCaller)) :=
  finishManyForward hTargetCount hContains
    (fun hScoped hInsert =>
      hScoped.multifill_insertMany hNodup hFresh hInsert)
    hRunBody

/-- Multi-result call writeback updating existing source-visible bindings. -/
theorem finishManyVisible
    {results : Nat} {targets : List Functions.Name}
    {layout : List Functions.Name}
    {sourceCaller : Yul.InteractionSemantics.State}
    {targetCaller : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceCall : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Assembly.Word)}
    {targetRunBody : Functions.InteractionSemantics.Open
      Functions.InteractionSemantics.CallResult}
    (hTargetCount : targets.length = results)
    (hNodup : targets.Nodup)
    (hVisible : ∀ name, name ∈ targets → name ∈ layout)
    (hContains : ∀ name, name ∈ targets →
      targetCaller.vars.contains name = true)
    (hRunBody :
      Simulation.Interaction.ForwardRel Truncated
        (RunBodyDoneRel layout sourceCaller targetCaller results)
        sourceCall targetRunBody) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel layout)
      (Simulation.Interaction.bind sourceCall fun result =>
        pure (result.1.multifill targets result.2))
      (Simulation.Interaction.bind targetRunBody
        (Functions.InteractionSemantics.Stmt.finishCall
          targets ctx targetCaller)) :=
  finishManyForward hTargetCount hContains
    (fun hScoped hInsert =>
      hScoped.multifill_insertMany_visible hNodup hVisible hInsert)
    hRunBody

/-- Attach canonical argument evaluation and function lookup around one
already-related function body, yielding the real generated call statement. -/
theorem callStmtForward
    {targetBodyFuel : Nat}
    {program : Functions.Program} {fn : Functions.FunDef}
    {functionName tmp : Functions.Name}
    {lowerArgs : List (Locals.Expr 1)} {args : List Assembly.Word}
    {before final : Fresh.State} {layout : List Functions.Name}
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
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (hStable : FunctionsInteractionExpression.StableArgs
      lowerArgs targetCaller args)
    (hFresh : Fresh.fresh? before = some (tmp, final))
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hCallerState : targetCaller =
      targetBefore.insert tmp Functions.Source.zero)
    (hDomain : TargetDomainWithin before.used targetBefore.vars)
    (hExtends : TargetExtends entry.vars targetBefore.vars)
    (hRunBody :
      Simulation.Interaction.ForwardRel Truncated
        (RunBodyDoneRel layout sourceCaller targetCaller 1)
        sourceCall targetRunBody)
    (hTargetRunBody :
      targetRunBody =
        Functions.InteractionSemantics.FunDef.openRunBody
          program fn args (targetBodyFuel + 1) targetCaller) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedArgs.DoneRel
        layout final [.var tmp] entry)
      sourceCall
      (Functions.InteractionSemantics.Stmt.openRun program ctx
        (targetBodyFuel + 2) (.call [tmp] functionName lowerArgs)
        targetCaller) := by
  subst targetRunBody
  have hFinished := finishSingleForward (ctx := ctx)
    hFresh hLayout hCallerState hDomain hExtends hRunBody
  have hArgsEval := hStable.openEval
    (TargetExtends.refl targetCaller.vars)
  unfold Functions.InteractionSemantics.ArgList.openEval
    Functions.Source.Canonical.ArgList.eval at hArgsEval
  rw [show targetBodyFuel + 2 = (targetBodyFuel + 1) + 1 by omega,
    Functions.InteractionSemantics.Stmt.openRun_call]
  rw [hArgsEval]
  simp only [Simulation.Interaction.bind_done_ok, hFind,
    Option.elim_some]
  simpa [Functions.InteractionSemantics.FunDef.openRunBody,
    Functions.Source.Canonical.FunDef.runBody] using hFinished

/-- Prefix the generated fresh-zero declaration around one related call
statement, yielding the exact two-statement internal-call suffix. -/
theorem letCallBlockForward
    {targetBodyFuel : Nat}
    {program : Functions.Program} {functionName tmp : Functions.Name}
    {lowerArgs : List (Locals.Expr 1)}
    {final : Fresh.State} {layout : List Functions.Name}
    {entry targetBefore targetCaller :
      Functions.InteractionSemantics.State}
    {sourceCall :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Assembly.Word)}
    {ctx : Functions.Source.Ctx}
    (hCallerState : targetCaller =
      targetBefore.insert tmp Functions.Source.zero)
    (hCall :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgs.DoneRel
          layout final [.var tmp] entry)
        sourceCall
        (Functions.InteractionSemantics.Stmt.openRun program
          { ctx with scope := tmp :: ctx.scope }
          (targetBodyFuel + 2)
          (.call [tmp] functionName lowerArgs) targetCaller)) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedArgs.DoneRel
        layout final [.var tmp] entry)
      sourceCall
      (Functions.InteractionSemantics.Block.openRun program ctx
        (targetBodyFuel + 4)
        { stmts :=
            [.let_ tmp (.lit Functions.Source.zero),
              .call [tmp] functionName lowerArgs] }
        targetBefore) := by
  have hSingleton :=
    FunctionsInteractionPreparedArgs.singletonTarget
      (targetFuel := targetBodyFuel + 1) hCall
  rw [show targetBodyFuel + 4 = (targetBodyFuel + 3) + 1 by omega,
    Functions.InteractionSemantics.Block.openRun_cons]
  have hLet := Functions.InteractionSemantics.Stmt.openRun_let_lit
    program ctx (targetBodyFuel + 3) tmp Functions.Source.zero targetBefore
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hLet
  rw [hLet]
  change
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedArgs.DoneRel
        layout final [.var tmp] entry)
      sourceCall
      (Functions.InteractionSemantics.Block.openRun program
        { ctx with scope := tmp :: ctx.scope }
        (targetBodyFuel + 3)
        { stmts := [.call [tmp] functionName lowerArgs] }
        (targetBefore.insert tmp Functions.Source.zero))
  simpa [hCallerState] using hSingleton

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
