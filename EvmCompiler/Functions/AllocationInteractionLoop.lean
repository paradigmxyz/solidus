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

/-- Effect composition across the representation change recorded by control. -/
structure EffectAlgebra
    (Effect : ActivationMode → TargetState → TargetState → Prop) : Prop where
  transSame :
    ∀ {beforeMode afterMode first second third},
      Effect beforeMode first second →
      SameFrame beforeMode afterMode →
      Effect afterMode second third →
      Effect beforeMode first third

namespace EffectAlgebra

theorem trivial :
    EffectAlgebra (fun _mode _before _after => True) :=
  ⟨by intros; trivial⟩

end EffectAlgebra

/-- Semantic loop result paired with one abstract target effect. -/
abbrev OpenLoopEffectResultRel
    (Effect : ActivationMode → TargetState → TargetState → Prop)
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns live : List Functions.Name) (frameBase : Nat)
    (entryMode : ActivationMode) (loopCtx : Functions.Source.Ctx)
    (targetInitial : TargetState) :=
  fun sourceDone targetDone =>
    OpenLoopResultRel contract lowerCtx lowerState localsCtx plan returns live
        frameBase entryMode loopCtx sourceDone targetDone ∧
      Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (fun _source target =>
          Effect entryMode targetInitial target.state)
        sourceDone targetDone

/-- Semantic scoped result paired with one abstract target effect. -/
abbrev OpenScopedEffectResultRel
    (Effect : ActivationMode → TargetState → TargetState → Prop)
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns live : List Functions.Name) (frameBase : Nat)
    (entryMode : ActivationMode) (ctx : Functions.Source.Ctx)
    (targetInitial : TargetState) :=
  fun sourceDone targetDone =>
    OpenScopedResultRel contract lowerCtx lowerState localsCtx plan returns live
        frameBase entryMode ctx sourceDone targetDone ∧
      Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (fun _source target =>
          Effect entryMode targetInitial target.state)
        sourceDone targetDone

/--
Exact open-world preservation for the recursive loop owner carrying one
composable target effect. Body and post are ordinary scoped-block preservation
callbacks; no compiler or cursor reasoning occurs inside this semantic
induction.
-/
theorem forward_effect
    {Effect : ActivationMode → TargetState → TargetState → Prop}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name} {frameBase slack fuelBound : Nat}
    {loopCtx postCtx bodyCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1} {post body : Functions.Block}
    {targetCond : Expressions.Expr 1}
    {targetPost targetBody : Expressions.Block}
    (effectAlgebra : EffectAlgebra Effect)
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
              (fun sourceResult targetResult =>
                ActivationConditionResultRel contract plan live frameBase mode
                    target sourceResult targetResult ∧
                  Effect mode target targetResult.1))
            (Functions.InteractionSemantics.Expr.openEvalCondition cond source)
            (Expressions.InteractionSemantics.Expr.openRunCondition
              targetCond target))
    (hBody :
      ∀ (fuel : Nat) {mode source target},
        fuel < fuelBound →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body fuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel Effect contract lowerCtx lowerState
              localsCtx plan returns live frameBase mode bodyCtx target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetBody target))
    (hPost :
      ∀ (fuel : Nat) {mode source target},
        fuel < fuelBound →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post fuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel Effect contract lowerCtx lowerState
              localsCtx plan returns live frameBase mode postCtx target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetPost target)) :
    ∀ (fuel : Nat) {mode source target},
      fuel ≤ fuelBound →
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan live frameBase mode source target →
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRunForLoop program loopCtx
          cond postCtx post bodyCtx body fuel source) →
        Simulation.Interaction.Rel
          (OpenLoopEffectResultRel Effect contract lowerCtx lowerState
            localsCtx plan returns live frameBase mode loopCtx target)
          (Functions.InteractionSemantics.Stmt.openRunForLoop program loopCtx
            cond postCtx post bodyCtx body fuel source)
          (Expressions.InteractionSemantics.Stmt.openRunForLoop expressions
            (fuel + slack) targetCond targetPost targetBody target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro mode source target hFuelBound hInitial hSuccess
      unfold Functions.InteractionSemantics.Stmt.openRunForLoop at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.runForLoop] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false
          (.InvalidInstruction : EVMException) hSuccess)
  | succ fuel ih =>
      intro mode source target hFuelBound hInitial hSuccess
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
          rcases hResult with ⟨hConditionResult, hCondEffect⟩
          cases hConditionResult.condition
          have hDefined : LiveDefined live sourceAfterCond :=
            hInitial.defined.congr_vars hVarsDone
          have hAfterCond :
              AllocationContext.ActivationInvariant contract lowerCtx
                lowerState localsCtx plan live frameBase mode sourceAfterCond
                targetAfterCond :=
            { compiler := hInitial.compiler
              planWF := hInitial.planWF
              defined := hDefined
              state := hConditionResult.state
              stackLength :=
                (congrArg List.length hConditionResult.stack).trans
                  hInitial.stackLength }
          cases sourceCond with
          | false =>
              apply Simulation.Interaction.Rel.done
              constructor
              · apply Simulation.Interaction.ExceptRel.ok
                exact ControlResultRel.regular
                  (by simpa [hLoopScope] using hAfterCond.restrict_source_live)
                  (SameFrame.refl mode)
                  (Functions.Source.Ctx.SameControl.refl loopCtx)
              · exact Simulation.Interaction.ExceptRel.ok hCondEffect
          | true =>
              have hBodySuccess :=
                Simulation.Interaction.Successful.bind_inv
                  hContinuationSuccess
              have hBodyRunSuccess :
                  Simulation.Interaction.Successful
                    (Functions.InteractionSemantics.Block.openRunScoped
                      program bodyCtx body fuel sourceAfterCond) := by
                apply Simulation.Interaction.AllDone.mono hBodySuccess
                intro outcome hOutcome
                cases outcome with
                | error err => exact hOutcome
                | ok value => trivial
              have hBodyRel :=
                hBody fuel (by omega) hAfterCond hBodyRunSuccess
              have hBodyStrong :=
                Simulation.Interaction.Rel.strengthen_left hBodyRel
                  hBodySuccess
              apply Simulation.Interaction.Rel.bind_custom hBodyStrong
              intro bodySourceDone bodyTargetDone hBodyDone
              rcases hBodyDone with
                ⟨hBodyRelated, hAfterBodySuccess⟩
              rcases hBodyRelated with ⟨hBodySemantic, hBodyEffectRel⟩
              cases hBodySemantic with
              | error hError => exact False.elim hAfterBodySuccess
              | @ok bodySourceOutcome bodyTargetOutcome hBodyResult =>
                  have hBodyEffect :
                      Effect mode targetAfterCond bodyTargetOutcome.state := by
                    cases hBodyEffectRel with
                    | ok hEffect => exact hEffect
                  have hThroughBody :
                      Effect mode target bodyTargetOutcome.state :=
                    effectAlgebra.transSame hCondEffect (SameFrame.refl mode)
                      hBodyEffect
                  have hContinue :
                      ∀ {bodyMode bodySource bodyTarget}
                        (hFrame : SameFrame mode bodyMode),
                        Effect mode target bodyTarget →
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
                            (OpenLoopEffectResultRel Effect contract lowerCtx
                              lowerState localsCtx plan returns live frameBase
                              mode loopCtx target)
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
                    intro bodyMode bodySource bodyTarget hFrame hBodyEffect
                      hBodyInvariant hPostAndLoopSuccess
                    have hPostSuccess :=
                      Simulation.Interaction.Successful.bind_inv
                        hPostAndLoopSuccess
                    have hPostRunSuccess :
                        Simulation.Interaction.Successful
                          (Functions.InteractionSemantics.Block.openRunScoped
                            program postCtx post fuel bodySource) := by
                      apply Simulation.Interaction.AllDone.mono hPostSuccess
                      intro outcome hOutcome
                      cases outcome with
                      | error err => exact hOutcome
                      | ok value => trivial
                    have hPostRel :=
                      hPost fuel (by omega) hBodyInvariant hPostRunSuccess
                    have hPostStrong :=
                      Simulation.Interaction.Rel.strengthen_left hPostRel
                        hPostSuccess
                    apply Simulation.Interaction.Rel.bind_custom hPostStrong
                    intro postSourceDone postTargetDone hPostDone
                    rcases hPostDone with
                      ⟨hPostRelated, hAfterPostSuccess⟩
                    rcases hPostRelated with ⟨hPostSemantic, hPostEffectRel⟩
                    cases hPostSemantic with
                    | error hError => exact False.elim hAfterPostSuccess
                    | @ok postSourceOutcome postTargetOutcome hPostResult =>
                        have hPostEffect :
                            Effect bodyMode bodyTarget
                              postTargetOutcome.state := by
                          cases hPostEffectRel with
                          | ok hEffect => exact hEffect
                        have hThroughPost :
                            Effect mode target postTargetOutcome.state :=
                          effectAlgebra.transSame hBodyEffect hFrame hPostEffect
                        cases hPostResult with
                        | regular hPostInvariant postFrame postControl =>
                            have hRecursive :=
                              ih (by omega) hPostInvariant hAfterPostSuccess
                            apply Simulation.Interaction.Rel.mono hRecursive
                            intro sourceDone targetDone hDone
                            rcases hDone with ⟨hSemantic, hEffectRel⟩
                            constructor
                            · cases hSemantic with
                              | error hError => exact .error hError
                              | ok hResult =>
                                  exact .ok
                                    (ControlResultRel.prepend_frame
                                      (hFrame.trans postFrame) hResult)
                            · cases hEffectRel with
                              | error hError => exact .error hError
                              | ok hRecursiveEffect =>
                                  exact .ok
                                    (effectAlgebra.transSame hThroughPost
                                      (hFrame.trans postFrame)
                                      hRecursiveEffect)
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
                                constructor
                                · apply Simulation.Interaction.ExceptRel.ok
                                  exact ControlResultRel.nonregular
                                    (mode := postMode) hNonregular
                                    (hFrame.trans postFrame)
                                    (Functions.Source.Ctx.SameControl.refl loopCtx)
                                    (.leave state)
                                · exact Simulation.Interaction.ExceptRel.ok
                                    hThroughPost
                            | halt kind state =>
                                apply Simulation.Interaction.Rel.done
                                constructor
                                · apply Simulation.Interaction.ExceptRel.ok
                                  exact ControlResultRel.nonregular
                                    (mode := postMode) hNonregular
                                    (hFrame.trans postFrame)
                                    (Functions.Source.Ctx.SameControl.refl loopCtx)
                                    (.halt kind state)
                                · exact Simulation.Interaction.ExceptRel.ok
                                    hThroughPost
                  cases hBodyResult with
                  | regular hBodyInvariant bodyFrame bodyControl =>
                      exact hContinue bodyFrame hThroughBody hBodyInvariant
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
                          constructor
                          · apply Simulation.Interaction.ExceptRel.ok
                            exact ControlResultRel.regular
                              (AllocationContext.ActivationInvariant.ofOutcomeState
                                hAfterCond.compiler hAfterCond.planWF hDefined
                                  hState hStackLength)
                              bodyFrame
                              (Functions.Source.Ctx.SameControl.refl loopCtx)
                          · exact Simulation.Interaction.ExceptRel.ok hThroughBody
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
                          exact hContinue bodyFrame hThroughBody
                            (AllocationContext.ActivationInvariant.ofOutcomeState
                              hAfterCond.compiler hAfterCond.planWF hDefined
                                hState hStackLength)
                            hAfterBodySuccess
                      | leave state =>
                          apply Simulation.Interaction.Rel.done
                          constructor
                          · apply Simulation.Interaction.ExceptRel.ok
                            exact ControlResultRel.nonregular
                              (mode := bodyMode) hNonregular bodyFrame
                              (Functions.Source.Ctx.SameControl.refl loopCtx)
                              (.leave state)
                          · exact Simulation.Interaction.ExceptRel.ok hThroughBody
                      | halt kind state =>
                          apply Simulation.Interaction.Rel.done
                          constructor
                          · apply Simulation.Interaction.ExceptRel.ok
                            exact ControlResultRel.nonregular
                              (mode := bodyMode) hNonregular bodyFrame
                              (Functions.Source.Ctx.SameControl.refl loopCtx)
                              (.halt kind state)
                          · exact Simulation.Interaction.ExceptRel.ok hThroughBody

/-- The semantic-only loop theorem is the trivial-effect specialization. -/
theorem forward
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name} {frameBase slack fuelBound : Nat}
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
        fuel < fuelBound →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body fuel source) →
          Simulation.Interaction.Rel
            (OpenScopedResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode bodyCtx)
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetBody target))
    (hPost :
      ∀ (fuel : Nat) {mode source target},
        fuel < fuelBound →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post fuel source) →
          Simulation.Interaction.Rel
            (OpenScopedResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode postCtx)
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetPost target)) :
    ∀ (fuel : Nat) {mode source target},
      fuel ≤ fuelBound →
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
  intro fuel mode source target hFuel hInitial hSuccess
  have hCondEffect :
      ∀ {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Rel
            (Simulation.Interaction.ExceptRel
              (fun left right : EVMException => left = right)
              (fun sourceResult targetResult =>
                ActivationConditionResultRel contract plan live frameBase mode
                    target sourceResult targetResult ∧
                  True))
            (Functions.InteractionSemantics.Expr.openEvalCondition cond source)
            (Expressions.InteractionSemantics.Expr.openRunCondition
              targetCond target) := by
    intro mode source target hInvariant
    apply Simulation.Interaction.Rel.mono (hCond hInvariant)
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError => exact .error hError
    | ok hResult => exact .ok ⟨hResult, trivial⟩
  have hBodyEffect :
      ∀ (innerFuel : Nat) {mode source target},
        innerFuel < fuelBound →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body innerFuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel (fun _ _ _ => True) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode bodyCtx target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body innerFuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (innerFuel + slack) targetBody target) := by
    intro innerFuel mode source target hBound hInvariant hRunSuccess
    apply Simulation.Interaction.Rel.mono
      (hBody innerFuel hBound hInvariant hRunSuccess)
    intro sourceDone targetDone hDone
    constructor
    · exact hDone
    · cases hDone with
      | error hError => exact .error hError
      | ok _ => exact .ok trivial
  have hPostEffect :
      ∀ (innerFuel : Nat) {mode source target},
        innerFuel < fuelBound →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post innerFuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel (fun _ _ _ => True) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode postCtx target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post innerFuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (innerFuel + slack) targetPost target) := by
    intro innerFuel mode source target hBound hInvariant hRunSuccess
    apply Simulation.Interaction.Rel.mono
      (hPost innerFuel hBound hInvariant hRunSuccess)
    intro sourceDone targetDone hDone
    constructor
    · exact hDone
    · cases hDone with
      | error hError => exact .error hError
      | ok _ => exact .ok trivial
  apply Simulation.Interaction.Rel.mono
    (forward_effect (Effect := fun _ _ _ => True) EffectAlgebra.trivial
      hLoopScope hBodyBreak hBodyContinue hCondEffect hBodyEffect hPostEffect
      fuel hFuel hInitial hSuccess)
  intro sourceDone targetDone hDone
  exact hDone.1

end AllocationInteractionLoop
end Functions
end EvmCompiler
