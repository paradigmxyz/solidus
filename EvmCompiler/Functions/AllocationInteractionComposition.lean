import EvmCompiler.Functions.AllocationInteractionAssignment
import EvmCompiler.Functions.AllocationInteractionSafeSemantics
import EvmCompiler.Expressions.InteractionReturns

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionComposition

open AllocationInteractionRelation

abbrev SameControl := Functions.Source.Ctx.SameControl

/--
Recursive control result: regular execution retains the complete outgoing
compiler invariant; abrupt execution retains only its destination-indexed
activation relation.
-/
inductive ControlResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns regularLive : List Locals.Name) (frameBase : Nat)
    (entryMode : ActivationMode)
    (controlCtx regularCtx : Functions.Source.Ctx) :
    (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Expressions.InteractionSemantics.Outcome → Prop where
  | regular {source : SourceState} {target : TargetState}
      {mode : ActivationMode}
      (invariant :
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan regularLive frameBase mode source target)
      (sameFrame : SameFrame entryMode mode)
      (control : SameControl controlCtx regularCtx) :
      ControlResultRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase entryMode controlCtx regularCtx
        (Functions.Source.Effectful.Outcome.regular source, regularCtx)
        (Structured.EffectSemantics.Outcome.regular target)
  | nonregular
      {sourceOutcome : Functions.InteractionSemantics.Outcome}
      {targetOutcome : Expressions.InteractionSemantics.Outcome}
      {finalCtx : Functions.Source.Ctx} {mode : ActivationMode}
      (sourceNonregular : sourceOutcome.mode ≠ .regular)
      (sameFrame : SameFrame entryMode mode)
      (control : SameControl controlCtx finalCtx)
      (state :
        ActivationOutcomeRel contract plan
          (AllocationInteractionStatement.outcomeLive
            returns regularLive controlCtx sourceOutcome.mode)
          0 frameBase mode sourceOutcome targetOutcome) :
      ControlResultRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase entryMode controlCtx regularCtx
        (sourceOutcome, finalCtx) targetOutcome

abbrev OpenControlResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns regularLive : List Locals.Name) (frameBase : Nat)
    (entryMode : ActivationMode)
    (controlCtx regularCtx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (ControlResultRel contract lowerCtx lowerState localsCtx plan returns
      regularLive frameBase entryMode controlCtx regularCtx)

namespace ControlResultRel

/-- Outcome-selected live sets agree under equal control destinations. -/
theorem outcomeLive_eq_of_sameControl
    {returns regularLive : List Locals.Name}
    {before after : Functions.Source.Ctx}
    (hControl : SameControl before after)
    (mode : Locals.Source.Mode) :
    AllocationInteractionStatement.outcomeLive
        returns regularLive before mode =
      AllocationInteractionStatement.outcomeLive
        returns regularLive after mode := by
  cases mode with
  | regular => rfl
  | brk => simp [AllocationInteractionStatement.outcomeLive,
      hControl.breakScope]
  | cont => simp [AllocationInteractionStatement.outcomeLive,
      hControl.continueScope]
  | leave => rfl
  | halt kind => rfl

/-- Transport a result from an inner context to an outer equal-control context. -/
theorem transport_control
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns regularLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {outerCtx innerCtx regularCtx : Functions.Source.Ctx}
    {sourceResult :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx}
    {targetResult : Expressions.InteractionSemantics.Outcome}
    (hOuter : SameControl outerCtx innerCtx)
    (hRel :
      ControlResultRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase entryMode innerCtx regularCtx
        sourceResult targetResult) :
    ControlResultRel contract lowerCtx lowerState localsCtx plan returns
      regularLive frameBase entryMode outerCtx regularCtx
      sourceResult targetResult := by
  cases hRel with
  | regular invariant sameFrame control =>
      exact .regular invariant sameFrame (hOuter.trans control)
  | @nonregular sourceOutcome targetOutcome finalCtx mode hMode sameFrame
      control state =>
      refine ControlResultRel.nonregular (mode := mode) hMode
        sameFrame (hOuter.trans control) ?_
      rw [outcomeLive_eq_of_sameControl hOuter sourceOutcome.mode]
      exact state

/-- Prefix a recursive result with the frame relation of an earlier segment. -/
theorem prepend_frame
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns regularLive : List Locals.Name} {frameBase : Nat}
    {entryMode middleMode : ActivationMode}
    {controlCtx regularCtx : Functions.Source.Ctx}
    {sourceResult :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx}
    {targetResult : Expressions.InteractionSemantics.Outcome}
    (hFrame : SameFrame entryMode middleMode)
    (hRel :
      ControlResultRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase middleMode controlCtx regularCtx
        sourceResult targetResult) :
    ControlResultRel contract lowerCtx lowerState localsCtx plan returns
      regularLive frameBase entryMode controlCtx regularCtx
      sourceResult targetResult := by
  cases hRel with
  | regular invariant tailFrame control =>
      exact .regular invariant (hFrame.trans tailFrame) control
  | @nonregular sourceOutcome targetOutcome finalCtx mode
      hNonregular tailFrame control state =>
      exact ControlResultRel.nonregular (mode := mode)
        hNonregular (hFrame.trans tailFrame) control state

/-- Abrupt outcomes ignore the regular live set of an unreachable tail. -/
theorem reindex_nonregular_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {returns beforeLive afterLive : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {controlCtx : Functions.Source.Ctx}
    {sourceOutcome : Functions.InteractionSemantics.Outcome}
    {targetOutcome : Expressions.InteractionSemantics.Outcome}
    (hState :
      ActivationOutcomeRel contract plan
        (AllocationInteractionStatement.outcomeLive
          returns beforeLive controlCtx sourceOutcome.mode)
        0 frameBase mode sourceOutcome targetOutcome)
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    ActivationOutcomeRel contract plan
      (AllocationInteractionStatement.outcomeLive
        returns afterLive controlCtx sourceOutcome.mode)
      0 frameBase mode sourceOutcome targetOutcome := by
  cases hState with
  | regular state => exact False.elim (hNonregular rfl)
  | brk defined stackLength modeMatches state =>
      exact .brk defined stackLength modeMatches state
  | cont defined stackLength modeMatches state =>
      exact .cont defined stackLength modeMatches state
  | leave state => exact .leave state
  | halt kind state => exact .halt kind state

end ControlResultRel

/-- Prefix every regular result of an open computation with frame continuity. -/
theorem prepend_frame
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns regularLive : List Locals.Name} {frameBase : Nat}
    {entryMode middleMode : ActivationMode}
    {controlCtx regularCtx : Functions.Source.Ctx}
    {sourceRun :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetRun :
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    (hFrame : SameFrame entryMode middleMode)
    (hRel :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
          returns regularLive frameBase middleMode controlCtx regularCtx)
        sourceRun targetRun) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
        returns regularLive frameBase entryMode controlCtx regularCtx)
      sourceRun targetRun := by
  apply Simulation.Interaction.Rel.mono hRel
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .error hError
  | ok hResult =>
      exact .ok (ControlResultRel.prepend_frame hFrame hResult)

/-- Lift a fixed-mode adjacent statement theorem into recursive control form. -/
theorem lift_fixed
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns regularLive : List Locals.Name} {frameBase : Nat}
    {entryMode mode : ActivationMode}
    {controlCtx regularCtx : Functions.Source.Ctx}
    {sourceRun :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetRun :
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    (hFrame : SameFrame entryMode mode)
    (hControl : SameControl controlCtx regularCtx)
    (hRel :
      Simulation.Interaction.Rel
        (AllocationInteractionStatement.OpenStmtResultRel contract lowerCtx
          lowerState localsCtx plan returns regularLive frameBase mode
          controlCtx regularCtx)
        sourceRun targetRun) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase entryMode controlCtx regularCtx)
      sourceRun targetRun := by
  apply Simulation.Interaction.Rel.mono hRel
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .error hError
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceOutcome, resultCtx⟩
      change
        resultCtx = regularCtx ∧
          AllocationInteractionStatement.BoundaryOutcomeRel contract
            lowerCtx lowerState localsCtx plan returns regularLive frameBase
            mode controlCtx sourceOutcome targetResult at hResult
      rcases hResult with ⟨rfl, hBoundary⟩
      apply Simulation.Interaction.ExceptRel.ok
      cases hBoundary with
      | regular invariant =>
          exact .regular invariant hFrame hControl
      | brk defined stackLength modeMatches state =>
          exact ControlResultRel.nonregular (mode := mode)
            (by simp) hFrame hControl
            (.brk defined stackLength modeMatches state)
      | cont defined stackLength modeMatches state =>
          exact ControlResultRel.nonregular (mode := mode)
            (by simp) hFrame hControl
            (.cont defined stackLength modeMatches state)
      | leave state =>
          exact ControlResultRel.nonregular (mode := mode)
            (by simp) hFrame hControl (.leave state)
      | halt kind state =>
          exact ControlResultRel.nonregular (mode := mode)
            (by simp) hFrame hControl (.halt kind state)

/--
Compose one control result with a tail. Only regular execution invokes the
tail; abrupt execution is reindexed across its statically compiled but
dynamically unreachable code.
-/
theorem cons
    {contract : MemoryContract.Contract}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    {sourceHead :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetHead :
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    {sourceTail : SourceState → Functions.Source.Ctx →
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetTail : TargetState →
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract midLowerCtx midLowerState midLocals
          plan returns midLive frameBase entryMode controlCtx midCtx)
        sourceHead targetHead)
    (hTail :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx)
            (sourceTail sourceMid midCtx) (targetTail targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract finalLowerCtx finalLowerState finalLocals
        plan returns finalLive frameBase entryMode controlCtx finalCtx)
      (Simulation.Interaction.bind sourceHead
        (fun result =>
          match result.1.mode with
          | .regular => sourceTail result.1.state result.2
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, controlCtx)))
      (Simulation.Interaction.bind targetHead
        (fun outcome =>
          match outcome.mode with
          | .regular => targetTail outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome)) := by
  apply Simulation.Interaction.Rel.bind_custom hHead
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .done (.error hError)
  | ok hResult =>
      cases hResult with
      | regular invariant sameFrame control =>
          apply Simulation.Interaction.Rel.mono (hTail invariant)
          intro tailSource tailTarget hTailDone
          cases hTailDone with
          | error hError => exact .error hError
          | ok hTailResult =>
              exact .ok
                (ControlResultRel.prepend_frame sameFrame
                  (ControlResultRel.transport_control control hTailResult))
      | @nonregular sourceOutcome targetOutcome headCtx mode
          hNonregular sameFrame control state =>
          cases state with
          | regular regularState => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches state =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                (.brk defined stackLength modeMatches state)
          | cont defined stackLength modeMatches state =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                (.cont defined stackLength modeMatches state)
          | leave state =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                (.leave state)
          | halt kind state =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                (.halt kind state)

/-- Compose a successful source sequence while exposing success only for
reachable regular tails.  This is the resource-independent induction
interface shared by stack-only and scratch-backed runtimes. -/
theorem cons_successful
    {contract : MemoryContract.Contract}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    {targetInitial : TargetState}
    {sourceHead :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetHead :
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    {sourceTail : SourceState → Functions.Source.Ctx →
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetTail : TargetState →
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract midLowerCtx midLowerState midLocals
          plan returns midLive frameBase entryMode controlCtx midCtx)
        sourceHead targetHead)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Simulation.Interaction.bind sourceHead
          (fun result =>
            match result.1.mode with
            | .regular => sourceTail result.1.state result.2
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure (result.1, controlCtx))))
    (hTargetReturns :
      Simulation.Interaction.AllDone
        (Structured.InteractionReturns.OutcomeReturnsEq
          targetInitial.returns)
        targetHead)
    (hTail :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid →
          SameFrame entryMode mode →
          targetMid.returns = targetInitial.returns →
          Simulation.Interaction.Successful (sourceTail sourceMid midCtx) →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx)
            (sourceTail sourceMid midCtx) (targetTail targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract finalLowerCtx finalLowerState finalLocals
        plan returns finalLive frameBase entryMode controlCtx finalCtx)
      (Simulation.Interaction.bind sourceHead
        (fun result =>
          match result.1.mode with
          | .regular => sourceTail result.1.state result.2
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, controlCtx)))
      (Simulation.Interaction.bind targetHead
        (fun outcome =>
          match outcome.mode with
          | .regular => targetTail outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome)) := by
  have hHeadSuccessful :=
    Simulation.Interaction.Successful.bind_inv hSuccessful
  have hHeadStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left hHead hHeadSuccessful)
      hTargetReturns
  apply Simulation.Interaction.Rel.bind_custom hHeadStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨⟨hSemanticDone, hContinuation⟩, hReturns⟩
  cases hSemanticDone with
  | error _ => exact False.elim hContinuation
  | ok hSemanticResult =>
      cases hSemanticResult with
      | regular invariant sameFrame control =>
          apply Simulation.Interaction.Rel.mono
            (hTail invariant sameFrame hReturns hContinuation)
          intro tailSource tailTarget hTailDone
          cases hTailDone with
          | error hError => exact .error hError
          | ok hTailResult =>
              exact .ok
                (ControlResultRel.prepend_frame sameFrame
                  (ControlResultRel.transport_control control hTailResult))
      | @nonregular sourceOutcome targetOutcome headCtx mode
          hNonregular sameFrame control state =>
          cases state with
          | regular regularState => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.brk defined stackLength modeMatches state)))
          | cont defined stackLength modeMatches state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.cont defined stackLength modeMatches state)))
          | leave state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.leave state)))
          | halt kind state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.halt kind state)))

/-- Compose a source sequence while carrying reservation safety only for the
regular continuation reached on the same open-interaction branch. This is the
run-indexed replacement for a global source-memory oracle. -/
theorem cons_executionSafe
    {contract : MemoryContract.Contract}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    {targetInitial : TargetState}
    {safeHead sourceHead :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetHead :
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    {safeTail sourceTail : SourceState -> Functions.Source.Ctx ->
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetTail : TargetState ->
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract midLowerCtx midLowerState midLocals
          plan returns midLive frameBase entryMode controlCtx midCtx)
        sourceHead targetHead)
    (hHeadEq : safeHead = sourceHead)
    (hSafe :
      Simulation.Interaction.Successful
        (Simulation.Interaction.bind safeHead
          (fun result =>
            match result.1.mode with
            | .regular => safeTail result.1.state result.2
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure (result.1, controlCtx))))
    (hSuccessful :
      Simulation.Interaction.Successful
        (Simulation.Interaction.bind sourceHead
          (fun result =>
            match result.1.mode with
            | .regular => sourceTail result.1.state result.2
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure (result.1, controlCtx))))
    (hTargetReturns :
      Simulation.Interaction.AllDone
        (Structured.InteractionReturns.OutcomeReturnsEq
          targetInitial.returns)
        targetHead)
    (hTail :
      forall {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid ->
          SameFrame entryMode mode ->
          targetMid.returns = targetInitial.returns ->
          Simulation.Interaction.Successful
            (sourceTail sourceMid midCtx) ->
          Simulation.Interaction.Successful
            (safeTail sourceMid midCtx) ->
          Simulation.Interaction.Rel
            (OpenControlResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx)
            (sourceTail sourceMid midCtx) (targetTail targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract finalLowerCtx finalLowerState finalLocals
        plan returns finalLive frameBase entryMode controlCtx finalCtx)
      (Simulation.Interaction.bind sourceHead
        (fun result =>
          match result.1.mode with
          | .regular => sourceTail result.1.state result.2
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, controlCtx)))
      (Simulation.Interaction.bind targetHead
        (fun outcome =>
          match outcome.mode with
          | .regular => targetTail outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome)) := by
  have hHeadSuccessful :=
    Simulation.Interaction.Successful.bind_inv hSuccessful
  have hSafeHead := Simulation.Interaction.Successful.bind_inv hSafe
  have hSafeHead' :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => False
          | .ok result =>
              Simulation.Interaction.Successful
                (match result.1.mode with
                | .regular => safeTail result.1.state result.2
                | .brk | .cont | .leave | .halt _ =>
                    Simulation.Interaction.pure
                      (result.1, controlCtx)))
        sourceHead := by
    rw [← hHeadEq]
    apply Simulation.Interaction.AllDone.mono hSafeHead
    intro outcome hOutcome
    cases outcome with
    | error _ => exact hOutcome
    | ok result =>
        rcases result with ⟨sourceOutcome, sourceCtx⟩
        exact hOutcome
  have hHeadStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left
        (Simulation.Interaction.Rel.strengthen_left hHead hHeadSuccessful)
        hSafeHead')
      hTargetReturns
  apply Simulation.Interaction.Rel.bind_custom hHeadStrong
  intro sourceDone targetDone hDone
  rcases hDone with
    ⟨⟨⟨hSemanticDone, hContinuation⟩, hSafeContinuation⟩, hReturns⟩
  cases hSemanticDone with
  | error _ => exact False.elim hContinuation
  | ok hSemanticResult =>
      cases hSemanticResult with
      | regular invariant sameFrame control =>
          apply Simulation.Interaction.Rel.mono
            (hTail invariant sameFrame hReturns hContinuation
              hSafeContinuation)
          intro tailSource tailTarget hTailDone
          cases hTailDone with
          | error hError => exact .error hError
          | ok hTailResult =>
              exact .ok
                (ControlResultRel.prepend_frame sameFrame
                  (ControlResultRel.transport_control control hTailResult))
      | @nonregular sourceOutcome targetOutcome headCtx mode
          hNonregular sameFrame control state =>
          cases state with
          | regular regularState => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.brk defined stackLength modeMatches state)))
          | cont defined stackLength modeMatches state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.cont defined stackLength modeMatches state)))
          | leave state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.leave state)))
          | halt kind state =>
              exact .done (.ok
                (ControlResultRel.nonregular (mode := mode) hNonregular
                  sameFrame (Functions.Source.Ctx.SameControl.refl controlCtx)
                  (.halt kind state)))

/-- Compose the real source statement-list and compiled target block runners. -/
theorem block_cons
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {sourceFuel targetFuel : Nat}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {headCode tailCode : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract midLowerCtx midLowerState midLocals
          plan returns midLive frameBase entryMode controlCtx midCtx)
        (Functions.InteractionSemantics.Stmt.openRun
          sourceProgram controlCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hTail :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx)
            (Functions.InteractionSemantics.Block.openRun
              sourceProgram midCtx sourceFuel { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetFuel - headCode.length)
                { stmts := tailCode } targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract finalLowerCtx finalLowerState finalLocals
        plan returns finalLive frameBase entryMode controlCtx finalCtx)
      (Functions.InteractionSemantics.Block.openRun sourceProgram controlCtx
        (sourceFuel + 1) { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := headCode ++ tailCode } target) := by
  rw [Functions.InteractionSemantics.Block.openRun_cons,
    Expressions.InteractionSemantics.Block.openRun_append]
  exact
    cons
      (finalLowerCtx := finalLowerCtx)
      (finalLowerState := finalLowerState)
      (finalLocals := finalLocals)
      (finalLive := finalLive)
      (finalCtx := finalCtx)
      (sourceTail := fun sourceMid ctx =>
        Functions.InteractionSemantics.Block.openRun sourceProgram ctx
          sourceFuel { stmts := rest } sourceMid)
      (targetTail := fun targetMid =>
        Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetFuel - headCode.length) { stmts := tailCode } targetMid)
      hHead hTail

/-- Successful source statement-list composition with a reachable-tail
induction hypothesis and no allocator-specific premises. -/
theorem block_cons_successful
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {sourceFuel targetFuel : Nat}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {headCode tailCode : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract midLowerCtx midLowerState midLocals
          plan returns midLive frameBase entryMode controlCtx midCtx)
        (Functions.InteractionSemantics.Stmt.openRun
          sourceProgram controlCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun sourceProgram controlCtx
          (sourceFuel + 1) { stmts := stmt :: rest } source))
    (hTail :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid →
          SameFrame entryMode mode →
          targetMid.returns = target.returns →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun
              sourceProgram midCtx sourceFuel { stmts := rest } sourceMid) →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx)
            (Functions.InteractionSemantics.Block.openRun
              sourceProgram midCtx sourceFuel { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetFuel - headCode.length) { stmts := tailCode } targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract finalLowerCtx finalLowerState finalLocals
        plan returns finalLive frameBase entryMode controlCtx finalCtx)
      (Functions.InteractionSemantics.Block.openRun sourceProgram controlCtx
        (sourceFuel + 1) { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := headCode ++ tailCode } target) := by
  rw [Functions.InteractionSemantics.Block.openRun_cons] at hSuccessful ⊢
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  exact
    cons_successful
      (finalLowerCtx := finalLowerCtx)
      (finalLowerState := finalLowerState)
      (finalLocals := finalLocals)
      (finalLive := finalLive) (finalCtx := finalCtx)
      (sourceTail := fun sourceMid ctx =>
        Functions.InteractionSemantics.Block.openRun sourceProgram ctx
          sourceFuel { stmts := rest } sourceMid)
      (targetTail := fun targetMid =>
        Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetFuel - headCode.length) { stmts := tailCode } targetMid)
      hHead hSuccessful
      (Expressions.InteractionReturns.Block.openRun_returns
        targetProgram targetFuel { stmts := headCode } target)
      hTail

/-- Statement-list composition driven by one checked source execution. The
tail callback receives guarded success for precisely the reached regular tail. -/
theorem block_cons_executionSafe
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {sourceFuel targetFuel : Nat}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {headCode tailCode : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract midLowerCtx midLowerState midLocals
          plan returns midLive frameBase entryMode controlCtx midCtx)
        (Functions.InteractionSemantics.Stmt.openRun
          sourceProgram controlCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        sourceProgram controlCtx (sourceFuel + 1)
        { stmts := stmt :: rest } source)
    (hTail :
      forall {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid ->
          SameFrame entryMode mode ->
          targetMid.returns = target.returns ->
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun
              sourceProgram midCtx sourceFuel { stmts := rest } sourceMid) ->
          AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
            sourceProgram midCtx sourceFuel { stmts := rest } sourceMid ->
          Simulation.Interaction.Rel
            (OpenControlResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx)
            (Functions.InteractionSemantics.Block.openRun
              sourceProgram midCtx sourceFuel { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetFuel - headCode.length) { stmts := tailCode } targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract finalLowerCtx finalLowerState finalLocals
        plan returns finalLive frameBase entryMode controlCtx finalCtx)
      (Functions.InteractionSemantics.Block.openRun sourceProgram controlCtx
        (sourceFuel + 1) { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := headCode ++ tailCode } target) := by
  have hOrdinary := hSafe.ordinarySuccessful
  have hSafeCons := hSafe
  unfold AllocationInteractionSafeSemantics.Block.ExecutionSafe at hSafeCons
  rw [AllocationInteractionSafeSemantics.Block.openRun_cons] at hSafeCons
  have hSafeHead := Simulation.Interaction.Successful.bind_left hSafeCons
  have hHeadEq :
      AllocationInteractionSafeSemantics.Stmt.openRun contract sourceProgram
          controlCtx sourceFuel stmt source =
        Functions.InteractionSemantics.Stmt.openRun sourceProgram controlCtx
          sourceFuel stmt source := by
    exact Functions.InteractionRefinement.Stmt.run_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (AllocationInteractionSafeSemantics.primitive_successRefines_ordinary
        contract)
      sourceProgram controlCtx sourceFuel stmt source hSafeHead
  rw [Functions.InteractionSemantics.Block.openRun_cons] at hOrdinary ⊢
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  exact
    cons_executionSafe
      (finalLowerCtx := finalLowerCtx)
      (finalLowerState := finalLowerState)
      (finalLocals := finalLocals)
      (finalLive := finalLive) (finalCtx := finalCtx)
      (safeTail := fun sourceMid ctx =>
        AllocationInteractionSafeSemantics.Block.openRun contract sourceProgram
          ctx sourceFuel { stmts := rest } sourceMid)
      (sourceTail := fun sourceMid ctx =>
        Functions.InteractionSemantics.Block.openRun sourceProgram ctx
          sourceFuel { stmts := rest } sourceMid)
      (targetTail := fun targetMid =>
        Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetFuel - headCode.length) { stmts := tailCode } targetMid)
      hHead hHeadEq hSafeCons hOrdinary
      (Expressions.InteractionReturns.Block.openRun_returns
        targetProgram targetFuel { stmts := headCode } target)
      hTail

/-- Empty source and target blocks preserve the current activation invariant. -/
theorem block_nil
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {sourceFuel targetFuel : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Locals.Name} {frameBase : Nat}
    {mode : ActivationMode} {ctx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan returns
        live frameBase mode ctx ctx)
      (Functions.InteractionSemantics.Block.openRun sourceProgram ctx
        (sourceFuel + 1) { stmts := [] } source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetFuel + 1) { stmts := [] } target) := by
  rw [Functions.InteractionSemantics.Block.openRun_nil,
    Expressions.InteractionSemantics.Block.openRun_nil]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact .regular hInvariant (SameFrame.refl mode)
    (Functions.Source.Ctx.SameControl.refl ctx)

end AllocationInteractionComposition
end Functions
end EvmCompiler
