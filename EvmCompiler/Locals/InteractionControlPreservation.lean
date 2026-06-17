import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Locals
namespace InteractionPreservation
namespace Stmt.Forward

/-- Policy-indexed scoped cleanup, owned by the Locals control proof layer. -/
theorem policyScopedBlock_generated
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    (bodyCode : List Expressions.Stmt) (cleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hLayout : ∃ pre, bodyCtx.layout = pre ++ targetCtx.layout)
    (hCleanup :
      bodyCtx.cleanupTo? targetCtx.layout.length = some cleanup)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyScopedOutcomeRel policy targetCtx suffix returns)
      (InteractionSemantics.Block.openRunScoped
        sourceProgram sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := bodyCode ++ Locals.codeStmt cleanup } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold InteractionSemantics.Block.openRunScoped
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  unfold Locals.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyScopedOutcomeRel policy targetCtx suffix returns)
      (Simulation.Interaction.bind
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        _)
      _
  apply Simulation.Interaction.ForwardRel.bind hBody
  intro sourceResult targetResult hResult
  cases hResult with
  | @regular sourceAfter sourceAfterCtx targetAfter
      hPolicyCtx hInnerCtx hState =>
      obtain ⟨pre, hLayout⟩ := hLayout
      obtain ⟨afterCleanup, hCleanupRun, hFinal⟩ :=
        hState.openRun_cleanupTo hLayout hCleanup
      have hTargetCleanup :=
        TargetBlock.openRun_single_code_done
          targetProgram (targetFuel - bodyCode.length)
          cleanup targetAfter afterCleanup
          hCleanupFuel hCleanupRun
      simp only [Structured.Outcome.regular_mode,
        Structured.Outcome.regular_state,
        Locals.Source.Effectful.Outcome.regular,
        Locals.codeStmt]
      rw [hTargetCleanup]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      apply PolicyScopedResultRel.regular
      simpa [hCtx.layout] using hFinal
  | brk hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.brk hPolicy hState
  | cont hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.cont hPolicy hState
  | leave hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.leave hPolicy hState
  | halt hPolicyCtx hShared hReturns =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.halt hShared hReturns

/-- Fuel-aligned recursion for the canonical source and target loop owners. -/
theorem forLoop_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (loopSourceCtx postSourceCtx bodySourceCtx : Locals.Source.Ctx)
    (loopTargetCtx postTargetCtx bodyTargetCtx : Locals.Ctx)
    (postFinalCtx bodyFinalCtx : Locals.Ctx)
    (slack : Nat)
    (cond : Locals.Expr 1) (post body : Locals.Block)
    (condCode : Structured.Code)
    (postCode bodyCode : List Expressions.Stmt)
    (postCleanup bodyCleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    (hLoopCtx : Frame.CtxRel loopSourceCtx loopTargetCtx)
    (hPostCtx : Frame.CtxRel postSourceCtx postTargetCtx)
    (hBodyCtx : Frame.CtxRel bodySourceCtx bodyTargetCtx)
    (hPostTargetLayout :
      postTargetCtx.layout = loopTargetCtx.layout)
    (hBodyTargetLayout :
      bodyTargetCtx.layout = loopTargetCtx.layout)
    (hPostLayout :
      ∃ pre, postFinalCtx.layout = pre ++ postTargetCtx.layout)
    (hBodyLayout :
      ∃ pre, bodyFinalCtx.layout = pre ++ bodyTargetCtx.layout)
    (hPostCleanup :
      postFinalCtx.cleanupTo? postTargetCtx.layout.length =
        some postCleanup)
    (hBodyCleanup :
      bodyFinalCtx.cleanupTo? bodyTargetCtx.layout.length =
        some bodyCleanup)
    (hPostSlack : postCode.length + 2 ≤ slack)
    (hBodySlack : bodyCode.length + 2 ≤ slack)
    (hCondScoped : Scope.ExprScoped loopTargetCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode loopTargetCtx 0 cond = some condCode)
    (hPost :
      ∀ (fuel : Nat)
        {source : Locals.Source.State}
        {target : Structured.RunState},
        Frame.StateRel loopTargetCtx.layout suffix returns source target →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel ControlPolicy.noLoop
              postFinalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram postSourceCtx fuel post source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + slack)
                { stmts := postCode } target))
    (hBody :
      ∀ (fuel : Nat)
        {source : Locals.Source.State}
        {target : Structured.RunState},
        Frame.StateRel loopTargetCtx.layout suffix returns source target →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel
              (ControlPolicy.loop loopSourceCtx.scope)
              bodyFinalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram bodySourceCtx fuel body source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + slack)
                { stmts := bodyCode } target)) :
    ∀ (fuel : Nat)
      {source : Locals.Source.State}
      {target : Structured.RunState},
      Frame.StateRel loopTargetCtx.layout suffix returns source target →
        Simulation.Interaction.ForwardRel
          Block.FuelTruncated
          (PolicyScopedOutcomeRel ControlPolicy.noLoop
            loopTargetCtx suffix returns)
          (InteractionSemantics.Stmt.openRunForLoop
            sourceProgram loopSourceCtx cond postSourceCtx post
              bodySourceCtx body fuel source)
          (Expressions.InteractionSemantics.Stmt.openRunForLoop
            targetProgram (fuel + slack) (.code condCode)
              { stmts := postCode ++ Locals.codeStmt postCleanup }
              { stmts := bodyCode ++ Locals.codeStmt bodyCleanup }
              target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target hInitial
      unfold InteractionSemantics.Stmt.openRunForLoop
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.runForLoop]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ fuel ih =>
      intro source target hInitial
      have hTargetFuel :
          fuel + 1 + slack = (fuel + slack) + 1 := by
        omega
      rw [hTargetFuel]
      unfold InteractionSemantics.Stmt.openRunForLoop
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
        Expressions.InteractionSemantics.Stmt.openRunForLoop
      simp only [Locals.Source.Effectful.Control.Stmt.runForLoop,
        Expressions.EffectSemantics.Control.Stmt.runForLoop]
      have hCond :=
        Expr.openEvalCondition_compileCode
          cond loopTargetCtx hCondScoped hCondSupported
          hCondCompile hInitial
      apply Simulation.Interaction.ForwardRel.bind
        (Simulation.Interaction.ForwardRel.ofRel hCond)
      intro sourceResult targetResult hResult
      rcases sourceResult with ⟨sourceAfterCond, sourceCond⟩
      rcases targetResult with ⟨targetAfterCond, targetCond⟩
      cases hResult.condition
      cases sourceCond with
      | false =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          apply PolicyScopedResultRel.regular
          simpa [hLoopCtx.layout] using hResult.state.restrictSelf
      | true =>
          have hBodyCleanupFuel :
              2 ≤ (fuel + slack) - bodyCode.length := by
            omega
          have hBodyScoped :=
            policyScopedBlock_generated
              (ControlPolicy.loop loopSourceCtx.scope)
              sourceProgram targetProgram bodySourceCtx
              bodyTargetCtx bodyFinalCtx fuel (fuel + slack)
              body bodyCode bodyCleanup hBodyCtx hBodyLayout
              hBodyCleanup hBodyCleanupFuel (hBody fuel hResult.state)
          have hPostCleanupFuel :
              2 ≤ (fuel + slack) - postCode.length := by
            omega
          have hContinue :
              ∀ {sourceAfter : Locals.Source.State}
                {targetAfter : Structured.RunState},
                Frame.StateRel loopTargetCtx.layout suffix returns
                    sourceAfter targetAfter →
                  Simulation.Interaction.ForwardRel
                    Block.FuelTruncated
                    (PolicyScopedOutcomeRel ControlPolicy.noLoop
                      loopTargetCtx suffix returns)
                    (Simulation.Interaction.bind
                      (InteractionSemantics.Block.openRunScoped
                        sourceProgram postSourceCtx post fuel sourceAfter)
                      (fun postOutcome =>
                        match postOutcome.mode with
                        | .regular =>
                            InteractionSemantics.Stmt.openRunForLoop
                              sourceProgram loopSourceCtx cond
                              postSourceCtx post bodySourceCtx body
                              fuel postOutcome.state
                        | .brk | .cont =>
                            Simulation.Interaction.error
                              (.InvalidInstruction : EVMException)
                        | .leave | .halt _ =>
                            Simulation.Interaction.pure postOutcome))
                    (Simulation.Interaction.bind
                      (Expressions.InteractionSemantics.Block.openRun
                        targetProgram (fuel + slack)
                          { stmts :=
                              postCode ++ Locals.codeStmt postCleanup }
                          targetAfter)
                      (fun postOutcome =>
                        match postOutcome.mode with
                        | .regular =>
                            Expressions.InteractionSemantics.Stmt.openRunForLoop
                              targetProgram (fuel + slack)
                              (.code condCode)
                              { stmts :=
                                  postCode ++ Locals.codeStmt postCleanup }
                              { stmts :=
                                  bodyCode ++ Locals.codeStmt bodyCleanup }
                              postOutcome.state
                        | .brk | .cont =>
                            Simulation.Interaction.error
                              (.InvalidInstruction : EVMException)
                        | .leave | .halt _ =>
                            Simulation.Interaction.pure postOutcome)) := by
            intro sourceAfter targetAfter hAfter
            have hPostScoped :=
              policyScopedBlock_generated
                ControlPolicy.noLoop sourceProgram targetProgram
                postSourceCtx postTargetCtx postFinalCtx
                fuel (fuel + slack) post postCode postCleanup
                hPostCtx hPostLayout hPostCleanup hPostCleanupFuel
                (hPost fuel (by
                  simpa [hPostTargetLayout] using hAfter))
            apply Simulation.Interaction.ForwardRel.bind hPostScoped
            intro sourcePost targetPost hPostResult
            cases hPostResult with
            | regular hPostState =>
                exact ih (by
                  simpa [hPostTargetLayout] using hPostState)
            | brk hImpossible hPostState =>
                exact False.elim hImpossible
            | cont hImpossible hPostState =>
                exact False.elim hImpossible
            | leave hPolicy hPostState =>
                apply Simulation.Interaction.ForwardRel.done
                apply Simulation.Interaction.ExceptRel.ok
                exact PolicyScopedResultRel.leave trivial hPostState
            | halt hShared hReturns =>
                apply Simulation.Interaction.ForwardRel.done
                apply Simulation.Interaction.ExceptRel.ok
                exact PolicyScopedResultRel.halt hShared hReturns
          apply Simulation.Interaction.ForwardRel.bind hBodyScoped
          intro sourceBody targetBody hBodyResult
          cases hBodyResult with
          | regular hBodyState =>
              exact hContinue (by
                simpa [hBodyTargetLayout] using hBodyState)
          | brk hFrame hBodyState =>
              cases hFrame
              apply Simulation.Interaction.ForwardRel.done
              apply Simulation.Interaction.ExceptRel.ok
              apply PolicyScopedResultRel.regular
              simpa [hLoopCtx.layout] using hBodyState
          | cont hFrame hBodyState =>
              cases hFrame
              exact hContinue (by
                simpa [hLoopCtx.layout] using hBodyState)
          | leave hPolicy hBodyState =>
              apply Simulation.Interaction.ForwardRel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact PolicyScopedResultRel.leave trivial hBodyState
          | halt hShared hReturns =>
              apply Simulation.Interaction.ForwardRel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact PolicyScopedResultRel.halt hShared hReturns

end Stmt.Forward

namespace Block

/-- Policy-indexed sequence composition for exact abrupt frames. -/
theorem policy_forward_cons
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (middleCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (stmt : Locals.Stmt) (rest : List Locals.Stmt)
    (headCode tailCode : List Expressions.Stmt)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hEntryPolicy : Stmt.ControlPolicy.ContextCompatible policy sourceCtx)
    (hHead :
      Simulation.Interaction.ForwardRel
        FuelTruncated
        (Stmt.PolicyOpenOutcomeRel policy middleCtx suffix returns)
        (InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hTail :
      ∀ {sourceMid : Locals.Source.State}
        {targetMid : Structured.RunState}
        {sourceMidCtx : Locals.Source.Ctx},
        Stmt.ControlPolicy.ContextCompatible policy sourceMidCtx →
        Frame.CtxRel sourceMidCtx middleCtx →
        Frame.StateRel middleCtx.layout suffix returns
            sourceMid targetMid →
          Simulation.Interaction.ForwardRel
            FuelTruncated
            (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceMidCtx sourceFuel
                { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetFuel - headCode.length)
                { stmts := tailCode } targetMid)) :
    Simulation.Interaction.ForwardRel
      FuelTruncated
      (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Block.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := headCode ++ tailCode } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold InteractionSemantics.Block.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Block.runOpen]
  apply Simulation.Interaction.ForwardRel.bind hHead
  intro sourceResult targetResult hResult
  cases hResult with
  | regular hPolicyCtx hCtx hState =>
      exact hTail hPolicyCtx hCtx hState
  | brk hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.brk hEntryPolicy hPolicy hState
  | cont hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.cont hEntryPolicy hPolicy hState
  | leave hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.leave hEntryPolicy hPolicy hState
  | halt hPolicyCtx hShared hReturns =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.halt hEntryPolicy hShared hReturns

end Block
end InteractionPreservation
end Locals
end EvmCompiler
