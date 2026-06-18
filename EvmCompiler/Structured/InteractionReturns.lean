import EvmCompiler.Structured.InteractionSemantics

namespace EvmCompiler
namespace Structured
namespace InteractionReturns

/-- Every non-halting leaf retains the incoming procedure-return stack. -/
def OutcomeReturnsEq (returns : List ReturnDest) :
    Except EVMException Structured.Outcome -> Prop
  | .error _ => True
  | .ok outcome =>
      match outcome.mode with
      | .halt _ => True
      | .regular | .brk | .cont | .leave =>
          outcome.state.returns = returns

private theorem popReturn_returns_eq
    {source bodyState returned : RunState}
    {callerStack : EvmYul.Stack Word} {retc : Nat}
    {frame : ReturnDest}
    (hReturns :
      bodyState.returns =
        (source.pushReturn callerStack retc).returns)
    (hPop : bodyState.popReturn? = some (frame, returned)) :
    returned.returns = source.returns := by
  simp only [RunState.pushReturn_returns] at hReturns
  unfold RunState.popReturn? at hPop
  rw [hReturns] at hPop
  simp at hPop
  rw [← hPop.2]

mutual

theorem Block.openRun_returns
    (program : Structured.Program) :
    forall (fuel : Nat) (block : Structured.Block) (state : RunState),
      Simulation.Interaction.AllDone
        (OutcomeReturnsEq state.returns)
        (InteractionSemantics.Block.openRun program fuel block state) := by
  intro fuel block state
  cases fuel with
  | zero =>
      exact Simulation.Interaction.AllDone.done True.intro
  | succ fuel =>
      rcases block with ⟨stmts⟩
      cases stmts with
      | nil =>
          exact Simulation.Interaction.AllDone.done rfl
      | cons stmt rest =>
          unfold InteractionSemantics.Block.openRun
          simp only [EffectSemantics.Control.Block.run]
          apply Simulation.Interaction.AllDone.bind
            (Stmt.openRun_returns program fuel stmt state)
          · intro _err _hError
            trivial
          · intro outcome hOutcome
            rcases outcome with ⟨middle, mode⟩
            cases mode with
            | regular =>
                apply Simulation.Interaction.AllDone.mono
                  (Block.openRun_returns program fuel
                    { stmts := rest } middle)
                intro final hFinal
                cases final with
                | error _ => trivial
                | ok finalOutcome =>
                    cases hMode : finalOutcome.mode with
                    | halt kind =>
                        simp [OutcomeReturnsEq, hMode]
                    | regular | brk | cont | leave =>
                        have hMiddle : middle.returns = state.returns := by
                          simpa [OutcomeReturnsEq] using hOutcome
                        have hRest :
                            finalOutcome.state.returns = middle.returns := by
                          simpa [OutcomeReturnsEq, hMode] using hFinal
                        simpa [OutcomeReturnsEq, hMode] using
                          hRest.trans hMiddle
            | brk | cont | leave =>
                exact Simulation.Interaction.AllDone.done (by
                  simpa [OutcomeReturnsEq] using hOutcome)
            | halt kind =>
                exact Simulation.Interaction.AllDone.done True.intro

theorem Stmt.openRun_returns
    (program : Structured.Program) :
    forall (fuel : Nat) (stmt : Structured.Stmt) (state : RunState),
      Simulation.Interaction.AllDone
        (OutcomeReturnsEq state.returns)
        (InteractionSemantics.Stmt.openRun program fuel stmt state) := by
  intro fuel stmt state
  cases stmt with
  | code code =>
      unfold InteractionSemantics.Stmt.openRun
      simp only [EffectSemantics.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.bind
        (InteractionSemantics.Code.openRun_returns code state)
      · intro _err _hError
        trivial
      · intro final hFinal
        exact Simulation.Interaction.AllDone.done (by
          simpa [OutcomeReturnsEq] using hFinal)
  | if_ cond body =>
      cases fuel with
      | zero =>
          exact Simulation.Interaction.AllDone.done True.intro
      | succ fuel =>
          unfold InteractionSemantics.Stmt.openRun
          simp only [EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.bind
            (InteractionSemantics.Code.openRunCondition_returns cond state)
          · intro _err _hError
            trivial
          · intro result hCond
            rcases result with ⟨afterCond, condTrue⟩
            cases condTrue with
            | false =>
                exact Simulation.Interaction.AllDone.done (by
                  simpa [OutcomeReturnsEq,
                    InteractionSemantics.Code.ConditionReturnsEq] using hCond)
            | true =>
                apply Simulation.Interaction.AllDone.mono
                  (Block.openRun_returns program fuel body afterCond)
                intro final hFinal
                cases final with
                | error _ => trivial
                | ok outcome =>
                    cases hMode : outcome.mode with
                    | halt kind =>
                        simp [OutcomeReturnsEq, hMode]
                    | regular | brk | cont | leave =>
                        have hAfter : afterCond.returns = state.returns := by
                          simpa [InteractionSemantics.Code.ConditionReturnsEq]
                            using hCond
                        have hBody : outcome.state.returns = afterCond.returns := by
                          simpa [OutcomeReturnsEq, hMode] using hFinal
                        simpa [OutcomeReturnsEq, hMode] using
                          hBody.trans hAfter
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero =>
          exact Simulation.Interaction.AllDone.done True.intro
      | succ fuel =>
          unfold InteractionSemantics.Stmt.openRun
          simp only [EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.bind
            (InteractionSemantics.Code.openRun_returns scrutinee state)
          · intro _err _hError
            trivial
          · intro afterScrutinee hScrutinee
            cases hPop : afterScrutinee.evm.stack.pop with
            | none =>
                simp only [EffectSemantics.Ordinary.runStateModel_evm, hPop]
                exact Simulation.Interaction.AllDone.done True.intro
            | some popped =>
                rcases popped with ⟨stack, value⟩
                let afterPop :=
                  afterScrutinee.withEVM
                    { afterScrutinee.evm with stack := stack }
                cases hSelect : Structured.Switch.select
                    value cases defaultBody with
                | none =>
                    simp only [EffectSemantics.Ordinary.runStateModel_evm,
                      EffectSemantics.Ordinary.runStateModel_withEVM,
                      hPop, hSelect]
                    exact Simulation.Interaction.AllDone.done (by
                      have hAfter : afterScrutinee.returns = state.returns := by
                        simpa [InteractionSemantics.ReturnsEq] using hScrutinee
                      simpa [OutcomeReturnsEq, afterPop] using hAfter)
                | some selected =>
                    simp only [EffectSemantics.Ordinary.runStateModel_evm,
                      EffectSemantics.Ordinary.runStateModel_withEVM,
                      hPop, hSelect]
                    apply Simulation.Interaction.AllDone.mono
                      (Block.openRun_returns program fuel selected afterPop)
                    intro final hFinal
                    cases final with
                    | error _ => trivial
                    | ok outcome =>
                        cases hMode : outcome.mode with
                        | halt kind =>
                            simp [OutcomeReturnsEq, hMode]
                        | regular | brk | cont | leave =>
                            have hAfter :
                                afterScrutinee.returns = state.returns := by
                              simpa [InteractionSemantics.ReturnsEq] using
                                hScrutinee
                            have hBody :
                                outcome.state.returns = afterPop.returns := by
                              simpa [OutcomeReturnsEq, hMode] using hFinal
                            simpa [OutcomeReturnsEq, hMode] using
                              hBody.trans (by simpa [afterPop] using hAfter)
  | for_ init cond post body =>
      cases fuel with
      | zero =>
          exact Simulation.Interaction.AllDone.done True.intro
      | succ fuel =>
          unfold InteractionSemantics.Stmt.openRun
          simp only [EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.bind
            (Block.openRun_returns program fuel init state)
          · intro _err _hError
            trivial
          · intro initOutcome hInit
            rcases initOutcome with ⟨afterInit, initMode⟩
            cases initMode with
            | regular =>
                apply Simulation.Interaction.AllDone.mono
                  (Stmt.openRunForLoop_returns program fuel cond post body
                    afterInit)
                intro final hFinal
                cases final with
                | error _ => trivial
                | ok outcome =>
                    cases hMode : outcome.mode with
                    | halt kind =>
                        simp [OutcomeReturnsEq, hMode]
                    | regular | brk | cont | leave =>
                        have hAfter : afterInit.returns = state.returns := by
                          simpa [OutcomeReturnsEq] using hInit
                        have hLoop : outcome.state.returns = afterInit.returns := by
                          simpa [OutcomeReturnsEq, hMode] using hFinal
                        simpa [OutcomeReturnsEq, hMode] using
                          hLoop.trans hAfter
            | brk | cont =>
                exact Simulation.Interaction.AllDone.done True.intro
            | leave =>
                exact Simulation.Interaction.AllDone.done (by
                  simpa [OutcomeReturnsEq] using hInit)
            | halt kind =>
                exact Simulation.Interaction.AllDone.done True.intro
  | brk | cont =>
      unfold InteractionSemantics.Stmt.openRun
      simp only [EffectSemantics.Control.Stmt.run]
      exact Simulation.Interaction.AllDone.done (by
        simp [OutcomeReturnsEq])
  | leave =>
      unfold InteractionSemantics.Stmt.openRun
      simp only [EffectSemantics.Control.Stmt.run,
        EffectSemantics.Ordinary.runStateModel_returns]
      cases hReturns : state.returns with
      | nil =>
          exact Simulation.Interaction.AllDone.done True.intro
      | cons head tail =>
          exact Simulation.Interaction.AllDone.done (by
            simp [OutcomeReturnsEq, hReturns])
  | call name =>
      cases fuel with
      | zero =>
          exact Simulation.Interaction.AllDone.done True.intro
      | succ fuel =>
          unfold InteractionSemantics.Stmt.openRun
          simp only [EffectSemantics.Control.Stmt.run,
            EffectSemantics.Ordinary.runStateModel_evm,
            EffectSemantics.Ordinary.runStateModel_withEVM,
            EffectSemantics.Ordinary.runStateModel_pushReturn,
            EffectSemantics.Ordinary.runStateModel_popReturn?]
          cases hLookup : ProcList.lookup? name program.procs with
          | none =>
              simp only [hLookup]
              exact Simulation.Interaction.AllDone.done True.intro
          | some proc =>
              simp only [hLookup]
              cases hSplit : StackFrame.splitArgs?
                  proc.argc state.evm.stack with
              | none =>
                  simp only [hSplit]
                  exact Simulation.Interaction.AllDone.done True.intro
              | some split =>
                  rcases split with ⟨args, callerStack⟩
                  simp only [hSplit]
                  let callState :=
                    (state.withEVM
                      { state.evm with stack := args }).pushReturn
                        callerStack proc.retc
                  apply Simulation.Interaction.AllDone.bind
                    (Block.openRun_returns program fuel proc.body callState)
                  · intro _err _hError
                    trivial
                  · intro outcome hBody
                    rcases outcome with ⟨bodyState, bodyMode⟩
                    cases bodyMode with
                    | regular | leave =>
                        cases hPop : bodyState.popReturn? with
                        | none =>
                            exact Simulation.Interaction.AllDone.done True.intro
                        | some popped =>
                            rcases popped with ⟨frame, returned⟩
                            cases hAttach : StackFrame.attachReturns?
                                frame bodyState.evm.stack with
                            | none =>
                                simp only [hPop, hAttach]
                                exact Simulation.Interaction.AllDone.done
                                  True.intro
                            | some stack =>
                                simp only [hPop, hAttach]
                                have hBodyReturns :
                                    bodyState.returns = callState.returns := by
                                  simpa [OutcomeReturnsEq] using hBody
                                have hReturned :=
                                  popReturn_returns_eq hBodyReturns hPop
                                exact Simulation.Interaction.AllDone.done (by
                                  simpa [OutcomeReturnsEq, callState] using
                                    hReturned)
                    | brk | cont =>
                        exact Simulation.Interaction.AllDone.done True.intro
                    | halt kind =>
                        exact Simulation.Interaction.AllDone.done True.intro
  | terminal kind =>
      unfold InteractionSemantics.Stmt.openRun
      simp only [EffectSemantics.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.bind
        (Simulation.Interaction.AllDone.trivial
          (InteractionSemantics.handler.stepTerminal kind state))
      · intro _err _hError
        trivial
      · intro _final _hFinal
        exact Simulation.Interaction.AllDone.done True.intro

theorem Stmt.openRunForLoop_returns
    (program : Structured.Program) :
    forall (fuel : Nat) (cond : Structured.Code)
      (post body : Structured.Block) (state : RunState),
      Simulation.Interaction.AllDone
        (OutcomeReturnsEq state.returns)
        (InteractionSemantics.Stmt.openRunForLoop
          program fuel cond post body state) := by
  intro fuel cond post body state
  cases fuel with
  | zero =>
      exact Simulation.Interaction.AllDone.done True.intro
  | succ fuel =>
      unfold InteractionSemantics.Stmt.openRunForLoop
      simp only [EffectSemantics.Control.Stmt.runForLoop]
      apply Simulation.Interaction.AllDone.bind
        (InteractionSemantics.Code.openRunCondition_returns cond state)
      · intro _err _hError
        trivial
      · intro result hCond
        rcases result with ⟨afterCond, condTrue⟩
        have hAfterCond : afterCond.returns = state.returns := by
          simpa [InteractionSemantics.Code.ConditionReturnsEq] using hCond
        cases condTrue with
        | false =>
            exact Simulation.Interaction.AllDone.done (by
              simpa [OutcomeReturnsEq] using hAfterCond)
        | true =>
            apply Simulation.Interaction.AllDone.bind
              (Block.openRun_returns program fuel body afterCond)
            · intro _err _hError
              trivial
            · intro bodyOutcome hBody
              rcases bodyOutcome with ⟨afterBody, bodyMode⟩
              cases bodyMode with
              | brk =>
                  exact Simulation.Interaction.AllDone.done (by
                    have hBodyReturns :
                        afterBody.returns = afterCond.returns := by
                      simpa [OutcomeReturnsEq] using hBody
                    simpa [OutcomeReturnsEq] using
                      hBodyReturns.trans hAfterCond)
              | leave =>
                  exact Simulation.Interaction.AllDone.done (by
                    have hBodyReturns :
                        afterBody.returns = afterCond.returns := by
                      simpa [OutcomeReturnsEq] using hBody
                    simpa [OutcomeReturnsEq] using
                      hBodyReturns.trans hAfterCond)
              | halt kind =>
                  exact Simulation.Interaction.AllDone.done True.intro
              | regular | cont =>
                  apply Simulation.Interaction.AllDone.bind
                    (Block.openRun_returns program fuel post afterBody)
                  · intro _err _hError
                    trivial
                  · intro postOutcome hPost
                    rcases postOutcome with ⟨afterPost, postMode⟩
                    cases postMode with
                    | regular =>
                        apply Simulation.Interaction.AllDone.mono
                          (Stmt.openRunForLoop_returns program fuel cond post
                            body afterPost)
                        intro final hFinal
                        cases final with
                        | error _ => trivial
                        | ok outcome =>
                            cases hMode : outcome.mode with
                            | halt kind =>
                                simp [OutcomeReturnsEq, hMode]
                            | regular | brk | cont | leave =>
                                have hBodyReturns :
                                    afterBody.returns = afterCond.returns := by
                                  simpa [OutcomeReturnsEq] using hBody
                                have hPostReturns :
                                    afterPost.returns = afterBody.returns := by
                                  simpa [OutcomeReturnsEq] using hPost
                                have hLoopReturns :
                                    outcome.state.returns =
                                      afterPost.returns := by
                                  simpa [OutcomeReturnsEq, hMode] using hFinal
                                simpa [OutcomeReturnsEq, hMode] using
                                  hLoopReturns.trans
                                    (hPostReturns.trans
                                      (hBodyReturns.trans hAfterCond))
                    | brk | cont =>
                        exact Simulation.Interaction.AllDone.done True.intro
                    | leave =>
                        exact Simulation.Interaction.AllDone.done (by
                          have hBodyReturns :
                              afterBody.returns = afterCond.returns := by
                            simpa [OutcomeReturnsEq] using hBody
                          have hPostReturns :
                              afterPost.returns = afterBody.returns := by
                            simpa [OutcomeReturnsEq] using hPost
                          simpa [OutcomeReturnsEq] using
                            hPostReturns.trans
                              (hBodyReturns.trans hAfterCond))
                    | halt kind =>
                        exact Simulation.Interaction.AllDone.done True.intro
end

end InteractionReturns
end Structured
end EvmCompiler
