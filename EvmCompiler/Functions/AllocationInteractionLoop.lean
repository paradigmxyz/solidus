import EvmCompiler.Functions.AllocationInteractionControl
import EvmCompiler.Expressions.InteractionReturns

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
    (Effect :
      ActivationMode → TargetState → TargetState → Locals.Source.Mode → Prop) where
  Ready : TargetState → Prop
  Context : ActivationMode → Prop
  transSame :
    ∀ {beforeMode afterMode first second third outcomeMode},
      Effect beforeMode first second .regular →
      SameFrame beforeMode afterMode →
      Effect afterMode second third outcomeMode →
      Effect beforeMode first third outcomeMode
  ready :
    ∀ {mode before after}, Effect mode before after .regular → Ready after
  reindexNonhalt :
    ∀ {mode before after outcomeMode replacement},
      Effect mode before after outcomeMode →
      (∀ kind, outcomeMode ≠ .halt kind) →
      Effect mode before after replacement
  contextSame :
    ∀ {beforeMode afterMode},
      Context beforeMode → SameFrame beforeMode afterMode → Context afterMode

namespace EffectAlgebra

def trivial :
    EffectAlgebra (fun _mode _before _after _outcomeMode => True) :=
  { Ready := fun _ => True
    Context := fun _ => True
    transSame := by intros; trivial
    ready := by intros; trivial
    reindexNonhalt := by intros; trivial
    contextSame := by intros; trivial }

end EffectAlgebra

/-- Semantic loop result paired with one abstract target effect. -/
abbrev OpenLoopEffectResultRel
    (Effect :
      ActivationMode → TargetState → TargetState → Locals.Source.Mode → Prop)
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
        (fun source target =>
          Effect entryMode targetInitial target.state source.mode)
        sourceDone targetDone

/-- Semantic scoped result paired with one abstract target effect. -/
abbrev OpenScopedEffectResultRel
    (Effect :
      ActivationMode → TargetState → TargetState → Locals.Source.Mode → Prop)
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
        (fun source target =>
          Effect entryMode targetInitial target.state source.mode)
        sourceDone targetDone

/-- The canonical Functions control semantics parameterized only by its
primitive capability. Both ordinary and reservation-guarded execution use
this interface, so the recursive loop simulation is proved once. -/
structure SourceSemantics where
  primitive :
    Functions.Source.Canonical.PrimitiveSemantics
      (Simulation.Interaction EVMException) SourceState
  conditionVars :
    ∀ (cond : Functions.Expr 1) (source : SourceState),
      Simulation.Interaction.AllDone
        (Locals.InteractionStatePreservation.ResultVars
          (α := Bool) source)
        (Locals.Source.Effectful.Expr.Control.evalCondition
          Functions.InteractionSemantics.stateModel primitive cond source)
  argumentVars :
    ∀ (args : List (Functions.Expr 1)) (source : SourceState),
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result => result.1.vars = source.vars)
        (Functions.Source.Canonical.ArgList.eval
          Functions.InteractionSemantics.stateModel primitive args source)

namespace SourceSemantics

def openEvalCondition (semantics : SourceSemantics)
    (cond : Functions.Expr 1) (source : SourceState) :=
  Locals.Source.Effectful.Expr.Control.evalCondition
    Functions.InteractionSemantics.stateModel semantics.primitive cond source

def openRunScoped (semantics : SourceSemantics)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (block : Functions.Block) (fuel : Nat) (source : SourceState) :=
  Functions.Source.Canonical.Block.runScoped
    Functions.InteractionSemantics.stateModel semantics.primitive
    program ctx block fuel source

def openRunBlock (semantics : SourceSemantics)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (block : Functions.Block) (source : SourceState) :=
  Functions.Source.Canonical.Block.runOpen
    Functions.InteractionSemantics.stateModel semantics.primitive
    program ctx fuel block source

def openRunStmt (semantics : SourceSemantics)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (stmt : Functions.Stmt) (source : SourceState) :=
  Functions.Source.Canonical.Stmt.run
    Functions.InteractionSemantics.stateModel semantics.primitive
    program ctx fuel stmt source

def openArgList (semantics : SourceSemantics)
    (args : List (Functions.Expr 1)) (source : SourceState) :=
  Functions.Source.Canonical.ArgList.eval
    Functions.InteractionSemantics.stateModel semantics.primitive args source

def openFunBody (semantics : SourceSemantics)
    (program : Functions.Program) (fn : Functions.FunDef)
    (args : List Word) (fuel : Nat) (source : SourceState) :=
  Functions.Source.Canonical.FunDef.runBody
    Functions.InteractionSemantics.stateModel semantics.primitive
    program fn args fuel source

def openRunForLoop (semantics : SourceSemantics)
    (program : Functions.Program) (loopCtx : Functions.Source.Ctx)
    (cond : Functions.Expr 1) (postCtx : Functions.Source.Ctx)
    (post : Functions.Block) (bodyCtx : Functions.Source.Ctx)
    (body : Functions.Block) (fuel : Nat) (source : SourceState) :=
  Functions.Source.Effectful.Control.Stmt.runForLoop
    Functions.InteractionSemantics.stateModel semantics.primitive
    program loopCtx cond postCtx post bodyCtx body fuel source

def ordinary : SourceSemantics where
  primitive := Functions.InteractionSemantics.primitiveSemantics
  conditionVars :=
    Locals.InteractionStatePreservation.expr_openEvalCondition_vars
  argumentVars := Functions.InteractionSemantics.ArgList.openEval_vars_eq

end SourceSemantics

/--
Exact open-world preservation for the recursive loop owner carrying one
composable target effect. Body and post are ordinary scoped-block preservation
callbacks; no compiler or cursor reasoning occurs inside this semantic
induction.
-/
theorem forward_effect_with
    {Effect :
      ActivationMode → TargetState → TargetState → Locals.Source.Mode → Prop}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name} {frameBase slack fuelBound : Nat}
    {targetReturns : List Structured.ReturnDest}
    {rootMode : ActivationMode}
    {loopCtx postCtx bodyCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1} {post body : Functions.Block}
    {targetCond : Expressions.Expr 1}
    {targetPost targetBody : Expressions.Block}
    (sourceModel : SourceSemantics)
    (effectAlgebra : EffectAlgebra Effect)
    (hLoopScope : loopCtx.scope = live)
    (hBodyBreak : bodyCtx.breakScope? = some live)
    (hBodyContinue : bodyCtx.continueScope? = some live)
    (hCond :
      ∀ {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          effectAlgebra.Ready target →
          Simulation.Interaction.Successful
            (sourceModel.openEvalCondition
              cond source) →
          Simulation.Interaction.Rel
            (Simulation.Interaction.ExceptRel
              (fun left right : EVMException => left = right)
              (fun sourceResult targetResult =>
                ActivationConditionResultRel contract plan live frameBase mode
                    target sourceResult targetResult ∧
                  Effect mode target targetResult.1 .regular))
            (sourceModel.openEvalCondition cond source)
            (Expressions.InteractionSemantics.Expr.openRunCondition
              targetCond target))
    (hBody :
      ∀ (fuel : Nat) {mode source target} {effectInitial : TargetState},
        fuel < fuelBound →
        effectAlgebra.Context mode →
        SameFrame rootMode mode →
        Effect mode effectInitial target .regular →
        target.returns = targetReturns →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (sourceModel.openRunScoped
              program bodyCtx body fuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel Effect contract lowerCtx lowerState
              localsCtx plan returns live frameBase mode bodyCtx target)
            (sourceModel.openRunScoped
              program bodyCtx body fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetBody target))
    (hPost :
      ∀ (fuel : Nat) {effectMode mode : ActivationMode} {source target}
        {effectInitial : TargetState},
        fuel < fuelBound →
        effectAlgebra.Context mode →
        SameFrame rootMode mode →
        SameFrame effectMode mode →
        Effect effectMode effectInitial target .regular →
        target.returns = targetReturns →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (sourceModel.openRunScoped
              program postCtx post fuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel Effect contract lowerCtx lowerState
              localsCtx plan returns live frameBase mode postCtx target)
            (sourceModel.openRunScoped
              program postCtx post fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetPost target)) :
    ∀ (fuel : Nat) {mode source target},
      fuel ≤ fuelBound →
      target.returns = targetReturns →
      SameFrame rootMode mode →
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan live frameBase mode source target →
      effectAlgebra.Ready target →
      effectAlgebra.Context mode →
      Simulation.Interaction.Successful
        (sourceModel.openRunForLoop program loopCtx
          cond postCtx post bodyCtx body fuel source) →
        Simulation.Interaction.Rel
          (OpenLoopEffectResultRel Effect contract lowerCtx lowerState
            localsCtx plan returns live frameBase mode loopCtx target)
          (sourceModel.openRunForLoop program loopCtx
            cond postCtx post bodyCtx body fuel source)
          (Expressions.InteractionSemantics.Stmt.openRunForLoop expressions
            (fuel + slack) targetCond targetPost targetBody target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro mode source target hFuelBound hTargetReturns hRootFrame hInitial
        hReady hContext hSuccess
      unfold SourceSemantics.openRunForLoop at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.runForLoop] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false
          (.InvalidInstruction : EVMException) hSuccess)
  | succ fuel ih =>
      intro mode source target hFuelBound hTargetReturns hRootFrame hInitial
        hReady hContext hSuccess
      have hTargetFuel : fuel + 1 + slack = (fuel + slack) + 1 := by
        omega
      rw [hTargetFuel]
      unfold SourceSemantics.openRunForLoop
        Expressions.InteractionSemantics.Stmt.openRunForLoop
      simp only [Functions.Source.Effectful.Control.Stmt.runForLoop,
        Expressions.EffectSemantics.Control.Stmt.runForLoop]
      unfold SourceSemantics.openRunForLoop at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.runForLoop] at hSuccess
      have hCondSuccess :=
        Simulation.Interaction.Successful.bind_inv hSuccess
      have hCondRunSuccess :=
        Simulation.Interaction.Successful.bind_left hSuccess
      have hCondRel := hCond hInitial hReady hCondRunSuccess
      have hVars := sourceModel.conditionVars cond source
      have hCondStrong :=
        Simulation.Interaction.Rel.strengthen_right
          (Simulation.Interaction.Rel.strengthen_left
            (Simulation.Interaction.Rel.strengthen_left hCondRel hVars)
            hCondSuccess)
          (Expressions.InteractionReturns.Expr.openRunCondition_returns
            targetCond target)
      apply Simulation.Interaction.Rel.bind_custom hCondStrong
      intro sourceDone targetDone hDone
      rcases hDone with
        ⟨⟨⟨hRelated, hVarsDone⟩, hContinuationSuccess⟩,
          hCondReturns⟩
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
                    (sourceModel.openRunScoped
                      program bodyCtx body fuel sourceAfterCond) := by
                apply Simulation.Interaction.AllDone.mono hBodySuccess
                intro outcome hOutcome
                cases outcome with
                | error err => exact hOutcome
                | ok value => trivial
              have hBodyRel :=
                hBody fuel (by omega) hContext hRootFrame hCondEffect
                  (by
                    have hAfterReturns :
                        targetAfterCond.returns = target.returns := by
                      simpa [
                        Structured.InteractionSemantics.Code.ConditionReturnsEq]
                        using hCondReturns
                    exact hAfterReturns.trans hTargetReturns)
                  hAfterCond
                  hBodyRunSuccess
              have hBodyStrong :=
                Simulation.Interaction.Rel.strengthen_right
                  (Simulation.Interaction.Rel.strengthen_left hBodyRel
                    hBodySuccess)
                  (Expressions.InteractionReturns.Block.openRun_returns
                    expressions (fuel + slack) targetBody targetAfterCond)
              apply Simulation.Interaction.Rel.bind_custom hBodyStrong
              intro bodySourceDone bodyTargetDone hBodyDone
              rcases hBodyDone with
                ⟨⟨hBodyRelated, hAfterBodySuccess⟩, hBodyReturnsDone⟩
              rcases hBodyRelated with ⟨hBodySemantic, hBodyEffectRel⟩
              cases hBodySemantic with
              | error hError => exact False.elim hAfterBodySuccess
              | @ok bodySourceOutcome bodyTargetOutcome hBodyResult =>
                  have hBodyEffect :
                      Effect mode targetAfterCond bodyTargetOutcome.state
                        bodySourceOutcome.mode := by
                    cases hBodyEffectRel with
                    | ok hEffect => exact hEffect
                  have hThroughBody :
                      Effect mode target bodyTargetOutcome.state
                        bodySourceOutcome.mode :=
                    effectAlgebra.transSame hCondEffect (SameFrame.refl mode)
                      hBodyEffect
                  have hContinue :
                      ∀ {bodyMode bodySource bodyTarget}
                        (hFrame : SameFrame mode bodyMode),
                        Effect mode target bodyTarget .regular →
                        bodyTarget.returns = targetReturns →
                        AllocationContext.ActivationInvariant contract
                            lowerCtx lowerState localsCtx plan live frameBase
                            bodyMode bodySource bodyTarget →
                        Simulation.Interaction.Successful
                          (Simulation.Interaction.bind
                            (sourceModel.openRunScoped
                              program postCtx post fuel bodySource)
                            (fun postOutcome =>
                              match postOutcome.mode with
                              | .regular =>
                                  sourceModel.openRunForLoop
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
                              (sourceModel.openRunScoped
                                program postCtx post fuel bodySource)
                              (fun postOutcome =>
                                match postOutcome.mode with
                                | .regular =>
                                    sourceModel.openRunForLoop
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
                      hBodyReturns hBodyInvariant hPostAndLoopSuccess
                    have hPostSuccess :=
                      Simulation.Interaction.Successful.bind_inv
                        hPostAndLoopSuccess
                    have hPostRunSuccess :
                        Simulation.Interaction.Successful
                          (sourceModel.openRunScoped
                            program postCtx post fuel bodySource) := by
                      apply Simulation.Interaction.AllDone.mono hPostSuccess
                      intro outcome hOutcome
                      cases outcome with
                      | error err => exact hOutcome
                      | ok value => trivial
                    have hPostRel :=
                      hPost fuel (by omega)
                        (effectAlgebra.contextSame hContext hFrame)
                        (hRootFrame.trans hFrame) hFrame
                        hBodyEffect hBodyReturns hBodyInvariant hPostRunSuccess
                    have hPostStrong :=
                      Simulation.Interaction.Rel.strengthen_right
                        (Simulation.Interaction.Rel.strengthen_left hPostRel
                          hPostSuccess)
                        (Expressions.InteractionReturns.Block.openRun_returns
                          expressions (fuel + slack) targetPost bodyTarget)
                    apply Simulation.Interaction.Rel.bind_custom hPostStrong
                    intro postSourceDone postTargetDone hPostDone
                    rcases hPostDone with
                      ⟨⟨hPostRelated, hAfterPostSuccess⟩, hPostReturnsDone⟩
                    rcases hPostRelated with ⟨hPostSemantic, hPostEffectRel⟩
                    cases hPostSemantic with
                    | error hError => exact False.elim hAfterPostSuccess
                    | @ok postSourceOutcome postTargetOutcome hPostResult =>
                        have hPostEffect :
                            Effect bodyMode bodyTarget
                              postTargetOutcome.state
                              postSourceOutcome.mode := by
                          cases hPostEffectRel with
                          | ok hEffect => exact hEffect
                        have hThroughPost :
                            Effect mode target postTargetOutcome.state
                              postSourceOutcome.mode :=
                          effectAlgebra.transSame hBodyEffect hFrame hPostEffect
                        cases hPostResult with
                        | @regular postSourceFinal postTargetFinal postMode
                            hPostInvariant postFrame postControl =>
                            have hRecursive :=
                              ih (by omega)
                                (by
                                  have hPostReturns :
                                      postTargetFinal.returns =
                                        bodyTarget.returns := by
                                    simpa [
                                      Structured.InteractionReturns.OutcomeReturnsEq]
                                      using hPostReturnsDone
                                  exact hPostReturns.trans hBodyReturns)
                                (hRootFrame.trans hFrame |>.trans postFrame)
                                hPostInvariant
                                (effectAlgebra.ready hPostEffect)
                                (effectAlgebra.contextSame hContext
                                  (hFrame.trans postFrame))
                                hAfterPostSuccess
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
                  | @regular bodySourceFinal bodyTargetFinal bodyMode
                      hBodyInvariant bodyFrame bodyControl =>
                      exact hContinue bodyFrame hThroughBody
                        (by
                          have hBodyReturns :
                              bodyTargetFinal.returns =
                                targetAfterCond.returns := by
                            simpa [
                              Structured.InteractionReturns.OutcomeReturnsEq]
                              using hBodyReturnsDone
                          have hAfterReturns :
                              targetAfterCond.returns = target.returns := by
                            simpa [
                              Structured.InteractionSemantics.Code.ConditionReturnsEq]
                              using hCondReturns
                          exact hBodyReturns.trans
                            (hAfterReturns.trans hTargetReturns))
                        hBodyInvariant hAfterBodySuccess
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
                          · exact Simulation.Interaction.ExceptRel.ok
                              (effectAlgebra.reindexNonhalt hThroughBody (by
                                intro kind hEq
                                cases hEq))
                      | @cont bodySourceFinal bodyTargetFinal defined
                          stackLength modeMatches state =>
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
                            (effectAlgebra.reindexNonhalt hThroughBody (by
                              intro kind hEq
                              cases hEq))
                            (by
                              have hBodyReturns :
                                  bodyTargetFinal.returns =
                                    targetAfterCond.returns := by
                                simpa [
                                  Structured.InteractionReturns.OutcomeReturnsEq]
                                  using hBodyReturnsDone
                              have hAfterReturns :
                                  targetAfterCond.returns = target.returns := by
                                simpa [
                                  Structured.InteractionSemantics.Code.ConditionReturnsEq]
                                  using hCondReturns
                              exact hBodyReturns.trans
                                (hAfterReturns.trans hTargetReturns))
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
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Expr.openEvalCondition
              cond source) →
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
  let targetReturns := target.returns
  let rootMode := mode
  have hCondEffect :
      ∀ {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          True →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Expr.openEvalCondition
              cond source) →
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
    intro mode source target hInvariant _hReady hCondSuccess
    apply Simulation.Interaction.Rel.mono (hCond hInvariant hCondSuccess)
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError => exact .error hError
    | ok hResult => exact .ok ⟨hResult, trivial⟩
  have hBodyEffect :
      ∀ (innerFuel : Nat) {mode source target}
        {effectInitial : TargetState},
        innerFuel < fuelBound →
        True →
        SameFrame rootMode mode →
        True →
        target.returns = targetReturns →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body innerFuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel (fun _ _ _ _ => True) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode bodyCtx target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body innerFuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (innerFuel + slack) targetBody target) := by
    intro innerFuel mode source target effectInitial hBound _hContext
      _hRootFrame _hEffect _hReturns hInvariant hRunSuccess
    apply Simulation.Interaction.Rel.mono
      (hBody innerFuel hBound hInvariant hRunSuccess)
    intro sourceDone targetDone hDone
    constructor
    · exact hDone
    · cases hDone with
      | error hError => exact .error hError
      | ok _ => exact .ok trivial
  have hPostEffect :
      ∀ (innerFuel : Nat) {effectMode mode : ActivationMode} {source target}
        {effectInitial : TargetState},
        innerFuel < fuelBound →
        True →
        SameFrame rootMode mode →
        SameFrame effectMode mode →
        True →
        target.returns = targetReturns →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post innerFuel source) →
          Simulation.Interaction.Rel
            (OpenScopedEffectResultRel (fun _ _ _ _ => True) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode postCtx target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post innerFuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (innerFuel + slack) targetPost target) := by
    intro innerFuel effectMode mode source target effectInitial hBound
      _hContext _hRootFrame _hSame _hEffect _hReturns hInvariant hRunSuccess
    apply Simulation.Interaction.Rel.mono
      (hPost innerFuel hBound hInvariant hRunSuccess)
    intro sourceDone targetDone hDone
    constructor
    · exact hDone
    · cases hDone with
      | error hError => exact .error hError
      | ok _ => exact .ok trivial
  apply Simulation.Interaction.Rel.mono
    (forward_effect_with (Effect := fun _ _ _ _ => True)
      SourceSemantics.ordinary EffectAlgebra.trivial
      hLoopScope hBodyBreak hBodyContinue hCondEffect hBodyEffect hPostEffect
      fuel hFuel (by simp [targetReturns]) (by simp [rootMode, SameFrame.refl])
      hInitial
      (by simp [EffectAlgebra.trivial])
      (by simp [EffectAlgebra.trivial]) hSuccess)
  intro sourceDone targetDone hDone
  exact hDone.1

end AllocationInteractionLoop
end Functions
end EvmCompiler
