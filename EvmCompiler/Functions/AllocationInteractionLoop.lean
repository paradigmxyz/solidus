import EvmCompiler.Functions.AllocationInteractionControl

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionLoop

open AllocationInteractionRelation
open AllocationInteractionComposition

abbrev LoopResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns live : List Functions.Name) (frameBase : Nat)
    (entryMode : ActivationMode) (loopCtx : Functions.Source.Ctx)
    (sourceOutcome : Functions.InteractionSemantics.Outcome)
    (targetOutcome : Expressions.InteractionSemantics.Outcome) : Prop :=
  ControlResultRel contract lowerCtx lowerState localsCtx plan returns live
    frameBase entryMode loopCtx loopCtx (sourceOutcome, loopCtx) targetOutcome

abbrev OpenLoopResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns live : List Functions.Name) (frameBase : Nat)
    (entryMode : ActivationMode) (loopCtx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (LoopResultRel contract lowerCtx lowerState localsCtx plan returns live
      frameBase entryMode loopCtx)

abbrev ScopedResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns live : List Functions.Name) (frameBase : Nat)
    (entryMode : ActivationMode) (ctx : Functions.Source.Ctx)
    (sourceOutcome : Functions.InteractionSemantics.Outcome)
    (targetOutcome : Expressions.InteractionSemantics.Outcome) : Prop :=
  ControlResultRel contract lowerCtx lowerState localsCtx plan returns live
    frameBase entryMode ctx ctx (sourceOutcome, ctx) targetOutcome

abbrev OpenScopedResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns live : List Functions.Name) (frameBase : Nat)
    (entryMode : ActivationMode) (ctx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (ScopedResultRel contract lowerCtx lowerState localsCtx plan returns live
      frameBase entryMode ctx)

/--
Exact open-world preservation for the recursive loop owner, provided the source
loop succeeds on every external-world branch. Body and post are ordinary
scoped-block preservation callbacks; no compiler or cursor reasoning occurs
inside this semantic induction.
-/
theorem forward
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name} {frameBase slack : Nat}
    {loopCtx postCtx bodyCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1} {post body : Functions.Block}
    {targetCond : Expressions.Expr 1}
    {targetPost targetBody : Expressions.Block}
    (hLoopScope : loopCtx.scope = live)
    (hBodyBreak : bodyCtx.breakScope? = some live)
    (hBodyContinue : bodyCtx.continueScope? = some live)
    (hCond :
      ∀ {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Rel
            (Simulation.Interaction.ExceptRel
              (fun left right : EVMException => left = right)
              (ActivationConditionResultRel contract plan live frameBase mode
                target))
            (Functions.InteractionSemantics.Expr.openEvalCondition cond source)
            (Expressions.InteractionSemantics.Expr.openRunCondition
              targetCond target))
    (hBody :
      ∀ (fuel : Nat) {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Rel
            (OpenScopedResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode bodyCtx)
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetBody target))
    (hPost :
      ∀ (fuel : Nat) {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Rel
            (OpenScopedResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode postCtx)
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetPost target)) :
    ∀ (fuel : Nat) {mode source target},
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan live frameBase mode source target →
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRunForLoop program loopCtx
          cond postCtx post bodyCtx body fuel source) →
        Simulation.Interaction.Rel
          (OpenLoopResultRel contract lowerCtx lowerState localsCtx plan
            returns live frameBase mode loopCtx)
          (Functions.InteractionSemantics.Stmt.openRunForLoop program loopCtx
            cond postCtx post bodyCtx body fuel source)
          (Expressions.InteractionSemantics.Stmt.openRunForLoop expressions
            (fuel + slack) targetCond targetPost targetBody target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro mode source target hInitial hSuccess
      unfold Functions.InteractionSemantics.Stmt.openRunForLoop at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.runForLoop] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false
          (.InvalidInstruction : EVMException) hSuccess)
  | succ fuel ih =>
      intro mode source target hInitial hSuccess
      have hTargetFuel : fuel + 1 + slack = (fuel + slack) + 1 := by
        omega
      rw [hTargetFuel]
      unfold Functions.InteractionSemantics.Stmt.openRunForLoop
        Expressions.InteractionSemantics.Stmt.openRunForLoop
      simp only [Functions.Source.Effectful.Control.Stmt.runForLoop,
        Expressions.EffectSemantics.Control.Stmt.runForLoop]
      unfold Functions.InteractionSemantics.Stmt.openRunForLoop at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.runForLoop] at hSuccess
      have hCondSuccess :=
        Simulation.Interaction.Successful.bind_inv hSuccess
      have hCondRel := hCond hInitial
      have hVars :=
        Locals.InteractionStatePreservation.expr_openEvalCondition_vars
          cond source
      have hCondStrong :=
        Simulation.Interaction.Rel.strengthen_left
          (Simulation.Interaction.Rel.strengthen_left hCondRel hVars)
          hCondSuccess
      apply Simulation.Interaction.Rel.bind_custom hCondStrong
      intro sourceDone targetDone hDone
      rcases hDone with ⟨⟨hRelated, hVarsDone⟩, hContinuationSuccess⟩
      cases hRelated with
      | error hError => exact False.elim hContinuationSuccess
      | @ok sourceResult targetResult hResult =>
          rcases sourceResult with ⟨sourceAfterCond, sourceCond⟩
          rcases targetResult with ⟨targetAfterCond, targetCond⟩
          cases hResult.condition
          have hDefined : LiveDefined live sourceAfterCond :=
            hInitial.defined.congr_vars hVarsDone
          have hAfterCond :
              AllocationContext.ActivationInvariant contract lowerCtx
                lowerState localsCtx plan live frameBase mode sourceAfterCond
                targetAfterCond :=
            { compiler := hInitial.compiler
              planWF := hInitial.planWF
              defined := hDefined
              state := hResult.state
              stackLength :=
                (congrArg List.length hResult.stack).trans
                  hInitial.stackLength }
          cases sourceCond with
          | false =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.regular
                (by simpa [hLoopScope] using hAfterCond.restrict_source_live)
                (SameFrame.refl mode)
                (Functions.Source.Ctx.SameControl.refl loopCtx)
          | true =>
              have hBodySuccess :=
                Simulation.Interaction.Successful.bind_inv
                  hContinuationSuccess
              have hBodyRel := hBody fuel hAfterCond
              have hBodyStrong :=
                Simulation.Interaction.Rel.strengthen_left hBodyRel
                  hBodySuccess
              apply Simulation.Interaction.Rel.bind_custom hBodyStrong
              intro bodySourceDone bodyTargetDone hBodyDone
              rcases hBodyDone with
                ⟨hBodyRelated, hAfterBodySuccess⟩
              cases hBodyRelated with
              | error hError => exact False.elim hAfterBodySuccess
              | @ok bodySourceOutcome bodyTargetOutcome hBodyResult =>
                  have hContinue :
                      ∀ {bodyMode bodySource bodyTarget}
                        (hFrame : SameFrame mode bodyMode),
                        AllocationContext.ActivationInvariant contract
                            lowerCtx lowerState localsCtx plan live frameBase
                            bodyMode bodySource bodyTarget →
                        Simulation.Interaction.Successful
                          (Simulation.Interaction.bind
                            (Functions.InteractionSemantics.Block.openRunScoped
                              program postCtx post fuel bodySource)
                            (fun postOutcome =>
                              match postOutcome.mode with
                              | .regular =>
                                  Functions.InteractionSemantics.Stmt.openRunForLoop
                                    program loopCtx cond postCtx post bodyCtx
                                      body fuel postOutcome.state
                              | .brk | .cont =>
                                  Simulation.Interaction.error
                                    (.InvalidInstruction : EVMException)
                              | .leave | .halt _ =>
                                  Simulation.Interaction.pure postOutcome)) →
                          Simulation.Interaction.Rel
                            (OpenLoopResultRel contract lowerCtx lowerState
                              localsCtx plan returns live frameBase mode loopCtx)
                            (Simulation.Interaction.bind
                              (Functions.InteractionSemantics.Block.openRunScoped
                                program postCtx post fuel bodySource)
                              (fun postOutcome =>
                                match postOutcome.mode with
                                | .regular =>
                                    Functions.InteractionSemantics.Stmt.openRunForLoop
                                      program loopCtx cond postCtx post bodyCtx
                                        body fuel postOutcome.state
                                | .brk | .cont =>
                                    Simulation.Interaction.error
                                      (.InvalidInstruction : EVMException)
                                | .leave | .halt _ =>
                                    Simulation.Interaction.pure postOutcome))
                            (Simulation.Interaction.bind
                              (Expressions.InteractionSemantics.Block.openRun
                                expressions (fuel + slack) targetPost
                                  bodyTarget)
                              (fun postOutcome =>
                                match postOutcome.mode with
                                | .regular =>
                                    Expressions.InteractionSemantics.Stmt.openRunForLoop
                                      expressions (fuel + slack) targetCond
                                        targetPost targetBody postOutcome.state
                                | .brk | .cont =>
                                    Simulation.Interaction.error
                                      (.InvalidInstruction : EVMException)
                                | .leave | .halt _ =>
                                    Simulation.Interaction.pure postOutcome)) := by
                    intro bodyMode bodySource bodyTarget hFrame
                      hBodyInvariant hPostAndLoopSuccess
                    have hPostSuccess :=
                      Simulation.Interaction.Successful.bind_inv
                        hPostAndLoopSuccess
                    have hPostRel := hPost fuel hBodyInvariant
                    have hPostStrong :=
                      Simulation.Interaction.Rel.strengthen_left hPostRel
                        hPostSuccess
                    apply Simulation.Interaction.Rel.bind_custom hPostStrong
                    intro postSourceDone postTargetDone hPostDone
                    rcases hPostDone with
                      ⟨hPostRelated, hAfterPostSuccess⟩
                    cases hPostRelated with
                    | error hError => exact False.elim hAfterPostSuccess
                    | @ok postSourceOutcome postTargetOutcome hPostResult =>
                        cases hPostResult with
                        | regular hPostInvariant postFrame postControl =>
                            have hRecursive :=
                              ih hPostInvariant hAfterPostSuccess
                            apply Simulation.Interaction.Rel.mono hRecursive
                            intro sourceDone targetDone hDone
                            cases hDone with
                            | error hError => exact .error hError
                            | ok hResult =>
                                exact .ok
                                  (ControlResultRel.prepend_frame
                                    (hFrame.trans postFrame) hResult)
                        | @nonregular sourceOutcome targetOutcome finalCtx
                            postMode hNonregular postFrame postControl
                            postState =>
                            cases postState with
                            | regular state =>
                                exact False.elim (hNonregular rfl)
                            | brk defined stackLength modeMatches state =>
                                exact False.elim
                                  (Simulation.Interaction.Successful.error_false
                                    (.InvalidInstruction : EVMException)
                                    hAfterPostSuccess)
                            | cont defined stackLength modeMatches state =>
                                exact False.elim
                                  (Simulation.Interaction.Successful.error_false
                                    (.InvalidInstruction : EVMException)
                                    hAfterPostSuccess)
                            | leave state =>
                                apply Simulation.Interaction.Rel.done
                                apply Simulation.Interaction.ExceptRel.ok
                                exact ControlResultRel.nonregular
                                  (mode := postMode) hNonregular
                                  (hFrame.trans postFrame)
                                  (Functions.Source.Ctx.SameControl.refl loopCtx)
                                  (.leave state)
                            | halt kind state =>
                                apply Simulation.Interaction.Rel.done
                                apply Simulation.Interaction.ExceptRel.ok
                                exact ControlResultRel.nonregular
                                  (mode := postMode) hNonregular
                                  (hFrame.trans postFrame)
                                  (Functions.Source.Ctx.SameControl.refl loopCtx)
                                  (.halt kind state)
                  cases hBodyResult with
                  | regular hBodyInvariant bodyFrame bodyControl =>
                      exact hContinue bodyFrame hBodyInvariant
                        hAfterBodySuccess
                  | @nonregular sourceOutcome targetOutcome finalCtx bodyMode
                      hNonregular bodyFrame bodyControl bodyState =>
                      cases bodyState with
                      | regular state => exact False.elim (hNonregular rfl)
                      | brk defined stackLength modeMatches state =>
                          have hDefined := defined
                          simp [AllocationInteractionStatement.outcomeLive,
                            hBodyBreak] at hDefined
                          have hModeMatches : bodyMode.Matches plan live := by
                            simpa [AllocationInteractionStatement.outcomeLive,
                              hBodyBreak] using modeMatches
                          have hState := state
                          simp [AllocationInteractionStatement.outcomeLive,
                            hBodyBreak] at hState
                          have hStackLength := stackLength
                          simp [AllocationInteractionStatement.outcomeLive,
                            hBodyBreak] at hStackLength
                          have hModeEq :=
                            bodyFrame.eq_of_matches
                              hAfterCond.compiler.mode_matches hModeMatches
                          cases hModeEq
                          apply Simulation.Interaction.Rel.done
                          apply Simulation.Interaction.ExceptRel.ok
                          exact ControlResultRel.regular
                            (AllocationContext.ActivationInvariant.ofOutcomeState
                              hAfterCond.compiler hAfterCond.planWF hDefined
                                hState hStackLength)
                            bodyFrame
                            (Functions.Source.Ctx.SameControl.refl loopCtx)
                      | cont defined stackLength modeMatches state =>
                          have hDefined := defined
                          simp [AllocationInteractionStatement.outcomeLive,
                            hBodyContinue] at hDefined
                          have hModeMatches : bodyMode.Matches plan live := by
                            simpa [AllocationInteractionStatement.outcomeLive,
                              hBodyContinue] using modeMatches
                          have hState := state
                          simp [AllocationInteractionStatement.outcomeLive,
                            hBodyContinue] at hState
                          have hStackLength := stackLength
                          simp [AllocationInteractionStatement.outcomeLive,
                            hBodyContinue] at hStackLength
                          have hModeEq :=
                            bodyFrame.eq_of_matches
                              hAfterCond.compiler.mode_matches hModeMatches
                          cases hModeEq
                          exact hContinue bodyFrame
                            (AllocationContext.ActivationInvariant.ofOutcomeState
                              hAfterCond.compiler hAfterCond.planWF hDefined
                                hState hStackLength)
                            hAfterBodySuccess
                      | leave state =>
                          apply Simulation.Interaction.Rel.done
                          apply Simulation.Interaction.ExceptRel.ok
                          exact ControlResultRel.nonregular
                            (mode := bodyMode) hNonregular bodyFrame
                            (Functions.Source.Ctx.SameControl.refl loopCtx)
                            (.leave state)
                      | halt kind state =>
                          apply Simulation.Interaction.Rel.done
                          apply Simulation.Interaction.ExceptRel.ok
                          exact ControlResultRel.nonregular
                            (mode := bodyMode) hNonregular bodyFrame
                            (Functions.Source.Ctx.SameControl.refl loopCtx)
                            (.halt kind state)

end AllocationInteractionLoop
end Functions
end EvmCompiler
