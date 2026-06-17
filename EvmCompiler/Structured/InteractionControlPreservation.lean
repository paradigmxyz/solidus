import EvmCompiler.Structured.InteractionPreservation
import EvmCompiler.Structured.TypedCfgCompilerFacts
import EvmCompiler.Structured.TypedCfgCompilerFreshness

namespace EvmCompiler
namespace Structured
namespace InteractionControlPreservation

namespace OpenOutcome

/--
Labels at which one Structured fragment returns control to its enclosing
compiler context.
-/
def IsJumpBoundary (ctx : TypedCfgCompiler.Context)
    (regular label : Assembly.Label) : Prop :=
  label = regular ∨
    ctx.breakLabel? = some label ∨
    ctx.continueLabel? = some label ∨
    ctx.leaveLabel? = some label

def continuationMatches?
    (returns : List ReturnDest) (tokens : List Word)
    (expectedLabel : Option Assembly.Label)
    (expectedShape : Option TypedCfg.Shape)
    (label : Assembly.Label) (state : EVMState) : Bool :=
  match expectedLabel, expectedShape with
  | some expected, some shape =>
      label == expected &&
        TypedCfgPreservation.activationFrameMatches?
          returns tokens shape state
  | _, _ => false

theorem continuationMatches?_eq_false_of_ne
    {returns : List ReturnDest} {tokens : List Word}
    {expectedLabel : Option Assembly.Label}
    {expectedShape : Option TypedCfg.Shape}
    {label : Assembly.Label} {state : EVMState}
    (hNe :
      ∀ expected, expectedLabel = some expected →
        label ≠ expected) :
    continuationMatches? returns tokens expectedLabel expectedShape
        label state = false := by
  cases hLabel : expectedLabel with
  | none =>
      simp [continuationMatches?, hLabel]
  | some expected =>
      have hExpectedNe := hNe expected hLabel
      cases hShape : expectedShape with
      | none =>
          simp [continuationMatches?, hLabel, hShape]
      | some shape =>
          simp [
            continuationMatches?, hLabel, hShape, hExpectedNe]

def stopJump (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (label : Assembly.Label) (state : EVMState) : Bool :=
  continuationMatches? returns tokens
      (some regular) result.fallthrough? label state ||
    continuationMatches? returns tokens
      ctx.breakLabel? ctx.breakShape? label state ||
    continuationMatches? returns tokens
      ctx.continueLabel? ctx.continueShape? label state ||
    continuationMatches? returns tokens
      ctx.leaveLabel? ctx.leaveShape? label state

@[simp] theorem stopJump_regular
    {result : TypedCfgCompiler.Result}
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (shape : TypedCfg.Shape) (state : EVMState)
    (hShape : result.fallthrough? = some shape)
    (hFrame :
      TypedCfgPreservation.activationFrameMatches?
        returns tokens shape state = true) :
    stopJump result ctx regular returns tokens regular state = true := by
  simp [stopJump, continuationMatches?, hShape, hFrame]

theorem stopJump_restLabel_eq_false
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply : LabelSupply}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (returns : List ReturnDest) (tokens : List Word)
    (state : EVMState) :
    stopJump result ctx regular returns tokens
        (TypedCfgCompiler.restLabel supply) state = false := by
  have hRegularNe :
      TypedCfgCompiler.restLabel supply ≠ regular :=
    hBefore.regular.restLabel_ne
  have hRegular :
      continuationMatches? returns tokens
          (some regular) result.fallthrough?
          (TypedCfgCompiler.restLabel supply) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected => by
        cases Option.some.inj hExpected
        exact hRegularNe)
  have hBreak :
      continuationMatches? returns tokens
          ctx.breakLabel? ctx.breakShape?
          (TypedCfgCompiler.restLabel supply) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.breakLabel expected hExpected).restLabel_ne)
  have hContinue :
      continuationMatches? returns tokens
          ctx.continueLabel? ctx.continueShape?
          (TypedCfgCompiler.restLabel supply) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.continueLabel expected hExpected).restLabel_ne)
  have hLeave :
      continuationMatches? returns tokens
          ctx.leaveLabel? ctx.leaveShape?
          (TypedCfgCompiler.restLabel supply) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.leaveLabel expected hExpected).restLabel_ne)
  simp [stopJump, hRegular, hBreak, hContinue, hLeave]

/--
Source-visible stack capacity at every Structured lexical continuation.

The compiler result owns the regular fallthrough shape. The compiler context
owns the shapes of lexical exits. Halted execution needs no subsequent
Structured frame.
-/
def FrameFits (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (outcome : Structured.Outcome) : Prop :=
  match outcome.mode with
  | .regular =>
      ∃ shape,
        result.fallthrough? = some shape ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            shape outcome.state.evm.stack.length
  | .brk =>
      ∃ shape,
        ctx.breakShape? = some shape ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            shape outcome.state.evm.stack.length
  | .cont =>
      ∃ shape,
        ctx.continueShape? = some shape ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            shape outcome.state.evm.stack.length
  | .leave =>
      ∃ shape,
        ctx.leaveShape? = some shape ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            shape outcome.state.evm.stack.length
  | .halt _ =>
      True

/--
Every nonhalting fragment outcome returns to the dynamic activation from which
the fragment started. A halt may retain nested internal-call frames because no
return dispatch follows it.
-/
def ActivationRestored
    (returns : List ReturnDest) (outcome : Structured.Outcome) : Prop :=
  match outcome.mode with
  | .halt _ => True
  | .regular | .brk | .cont | .leave =>
      outcome.state.returns = returns

/--
The existing outcome-indexed Structured-to-TypedCfg relation, strengthened
with the source-frame shape and dynamic-activation invariant needed by the next
adjacent compiler fragment.
-/
def Rel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (source : Structured.Outcome) (target : TypedCfg.Outcome) : Prop :=
  TypedCfgPreservation.OutcomeSimulation.Rel
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      tokens source target ∧
    FrameFits result ctx source ∧
      ActivationRestored returns source

abbrev OutcomeDoneRel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word) :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError : EVMException => True)
    (Rel result ctx regular returns tokens)

/--
Whether a regular fragment exit is an externally visible boundary or an
internal continuation that the enclosing fragment must resume.
-/
inductive RegularExit where
  | stop
  | resume
  deriving DecidableEq

def SegmentRunRel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (regularExit : RegularExit)
    (source : Structured.Outcome) :
    TypedCfg.Control.Program.RunResult → Prop :=
  match regularExit, source.mode with
  | .resume, .regular =>
      fun
      | .exhausted label target =>
          Rel result ctx regular returns tokens source
            (.jump label target)
      | .stopped _ => False
  | _, _ =>
      fun
      | .exhausted _ _ => False
      | .stopped target =>
          Rel result ctx regular returns tokens source target

abbrev SegmentDoneRel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (regularExit : RegularExit) :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError : EVMException => True)
    (SegmentRunRel result ctx regular returns tokens regularExit)

abbrev RunRel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word) :=
  SegmentRunRel result ctx regular returns tokens .stop

abbrev DoneRel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word) :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError : EVMException => True)
    (RunRel result ctx regular returns tokens)

theorem Rel.append_right
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome} {target : TypedCfg.Outcome}
    (hRel : Rel right ctx regular returns tokens source target) :
    Rel (left.append right) ctx regular returns tokens source target := by
  simpa [Rel, FrameFits, TypedCfgCompiler.Result.append] using hRel

theorem Rel.change_regular_of_nonregular
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {leftRegular rightRegular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome} {target : TypedCfg.Outcome}
    (hMode : source.mode ≠ .regular)
    (hRel :
      Rel left ctx leftRegular returns tokens source target) :
    Rel right ctx rightRegular returns tokens source target := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  rcases source with ⟨sourceState, sourceMode⟩
  cases sourceMode with
  | regular =>
      exact False.elim (hMode rfl)
  | brk =>
      exact
        ⟨by
          obtain ⟨label, targetState, hLabel, rfl, hState⟩ :=
            TypedCfgPreservation.OutcomeSimulation.Rel.brk_elim
              hOutcome
          exact
            TypedCfgPreservation.OutcomeSimulation.Rel.brk_iff.mpr
              ⟨by
                simpa [
                  TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                  using hLabel,
                hState⟩,
          by simpa [FrameFits] using hFits,
          by simpa [ActivationRestored] using hRestored⟩
  | cont =>
      exact
        ⟨by
          obtain ⟨label, targetState, hLabel, rfl, hState⟩ :=
            TypedCfgPreservation.OutcomeSimulation.Rel.cont_elim
              hOutcome
          exact
            TypedCfgPreservation.OutcomeSimulation.Rel.cont_iff.mpr
              ⟨by
                simpa [
                  TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                  using hLabel,
                hState⟩,
          by simpa [FrameFits] using hFits,
          by simpa [ActivationRestored] using hRestored⟩
  | leave =>
      exact
        ⟨by
          obtain ⟨label, targetState, hLabel, rfl, hState⟩ :=
            TypedCfgPreservation.OutcomeSimulation.Rel.leave_elim
              hOutcome
          exact
            TypedCfgPreservation.OutcomeSimulation.Rel.leave_iff.mpr
              ⟨by
                simpa [
                  TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                  using hLabel,
                hState⟩,
          by simpa [FrameFits] using hFits,
          by simpa [ActivationRestored] using hRestored⟩
  | halt kind =>
      exact
        ⟨by
          obtain
              ⟨targetState, targetFinal, rfl, hStep, hState⟩ :=
            TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim
              hOutcome
          exact
            TypedCfgPreservation.OutcomeSimulation.Rel.halt_iff.mpr
              ⟨rfl, targetFinal, hStep, hState⟩,
          by simpa [FrameFits] using hFits,
          by simpa [ActivationRestored] using hRestored⟩

theorem SegmentRunRel.append_right_stop
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Control.Program.RunResult}
    (hRun :
      SegmentRunRel right ctx regular returns tokens .stop
        source target) :
    SegmentRunRel (left.append right) ctx regular returns tokens .stop
      source target := by
  cases target with
  | exhausted label state =>
      exact False.elim hRun
  | stopped outcome =>
      exact Rel.append_right hRun

theorem SegmentDoneRel.append_right_stop
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Except EVMException Structured.Outcome}
    {target :
      Except EVMException TypedCfg.Control.Program.RunResult}
    (hDone :
      SegmentDoneRel right ctx regular returns tokens .stop
        source target) :
    SegmentDoneRel (left.append right) ctx regular returns tokens .stop
      source target := by
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hRun =>
      exact
        Simulation.Interaction.ExceptRel.ok
          (SegmentRunRel.append_right_stop hRun)

/--
Fixed-fuel preservation for a fragment executed under an enclosing fragment's
boundary policy.

The fragment result and regular label describe the source outcome relation.
The boundary result and regular label determine where the one canonical target
runner stops. Keeping these roles separate is what makes adjacent statement
sequencing compositional.
-/
def PreservesWithin (fragmentResult boundaryResult :
      TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context)
    (fragmentRegular boundaryRegular : Assembly.Label)
    (regularExit : RegularExit)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (targetFuel : Nat) : Prop :=
  ∀ target,
    TypedCfgPreservation.StateRel source tokens target →
      Simulation.Interaction.Rel
        (SegmentDoneRel fragmentResult ctx fragmentRegular
          source.returns tokens regularExit)
        sourceRun
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          (stopJump boundaryResult ctx boundaryRegular
            source.returns tokens)
          cfg targetFuel entry target)

namespace PreservesWithin

/--
Compose two adjacent Structured fragments under one enclosing stop policy.

The head's regular exit is tagged as exhausted, so the canonical target
fuel-add theorem resumes exactly those branches. Every nonregular head outcome
is already stopped and bypasses the tail.
-/
theorem sequence
    {headResult tailResult boundaryResult :
      TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry middle boundaryRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState →
        Simulation.Interaction EVMException Structured.Outcome}
    {headFuel tailFuel : Nat}
    (hHead :
      PreservesWithin headResult boundaryResult cfg entry ctx
        middle boundaryRegular .resume source tokens
        headRun headFuel)
    (hTail :
      ∀ middleSource,
        middleSource.returns = source.returns →
          PreservesWithin tailResult boundaryResult cfg middle ctx
            boundaryRegular boundaryRegular .stop
            middleSource tokens (tailRun middleSource) tailFuel) :
    PreservesWithin (headResult.append tailResult) boundaryResult
      cfg entry ctx boundaryRegular boundaryRegular .stop
      source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      (headFuel + tailFuel) := by
  intro target hStateRel
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_add]
  apply Simulation.Interaction.Rel.bind_custom
    (hHead target hStateRel)
  intro sourceDone targetDone hDone
  cases sourceDone with
  | error sourceError =>
      cases targetDone with
      | error targetError =>
          exact
            Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error trivial)
      | ok targetResult =>
          cases hDone
  | ok headOutcome =>
      cases targetDone with
      | error targetError =>
          cases hDone
      | ok targetResult =>
          cases hDone with
          | ok hRun =>
              rcases headOutcome with ⟨middleSource, headMode⟩
              cases headMode with
              | regular =>
                  cases targetResult with
                  | exhausted label targetMiddle =>
                      change
                        Rel headResult ctx middle source.returns tokens
                          (Structured.Outcome.regular middleSource)
                          (.jump label targetMiddle)
                        at hRun
                      rcases hRun with
                        ⟨hOutcome, _hFits, hRestored⟩
                      rcases
                          TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mp
                            hOutcome with
                        ⟨hLabel, hMiddleStateRel⟩
                      have hReturns :
                          middleSource.returns = source.returns := by
                        simpa [ActivationRestored] using hRestored
                      have hTailRel :=
                        hTail middleSource hReturns
                          targetMiddle hMiddleStateRel
                      have hTailRel' :
                          Simulation.Interaction.Rel
                            (SegmentDoneRel
                              (headResult.append tailResult)
                              ctx boundaryRegular
                              middleSource.returns tokens .stop)
                            (tailRun middleSource)
                            (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                              (stopJump boundaryResult ctx boundaryRegular
                                middleSource.returns tokens)
                              cfg tailFuel middle targetMiddle) := by
                        apply Simulation.Interaction.Rel.mono hTailRel
                        intro sourceFinal targetFinal hFinal
                        exact
                          SegmentDoneRel.append_right_stop
                            (left := headResult) hFinal
                      simpa [
                        TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithStop,
                        hLabel, hReturns] using hTailRel'
                  | stopped targetOutcome =>
                      exact False.elim hRun
              | brk =>
                  cases targetResult with
                  | exhausted label targetMiddle =>
                      exact False.elim hRun
                  | stopped targetOutcome =>
                      change
                        Rel headResult ctx middle source.returns tokens
                          (Structured.Outcome.brk middleSource)
                          targetOutcome
                        at hRun
                      have hFinalRel :=
                        Rel.change_regular_of_nonregular
                          (left := headResult)
                          (right := headResult.append tailResult)
                          (leftRegular := middle)
                          (rightRegular := boundaryRegular)
                          (by simp) hRun
                      exact
                        Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok hFinalRel)
              | cont =>
                  cases targetResult with
                  | exhausted label targetMiddle =>
                      exact False.elim hRun
                  | stopped targetOutcome =>
                      change
                        Rel headResult ctx middle source.returns tokens
                          (Structured.Outcome.cont middleSource)
                          targetOutcome
                        at hRun
                      have hFinalRel :=
                        Rel.change_regular_of_nonregular
                          (left := headResult)
                          (right := headResult.append tailResult)
                          (leftRegular := middle)
                          (rightRegular := boundaryRegular)
                          (by simp) hRun
                      exact
                        Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok hFinalRel)
              | leave =>
                  cases targetResult with
                  | exhausted label targetMiddle =>
                      exact False.elim hRun
                  | stopped targetOutcome =>
                      change
                        Rel headResult ctx middle source.returns tokens
                          (Structured.Outcome.leave middleSource)
                          targetOutcome
                        at hRun
                      have hFinalRel :=
                        Rel.change_regular_of_nonregular
                          (left := headResult)
                          (right := headResult.append tailResult)
                          (leftRegular := middle)
                          (rightRegular := boundaryRegular)
                          (by simp) hRun
                      exact
                        Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok hFinalRel)
              | halt kind =>
                  cases targetResult with
                  | exhausted label targetMiddle =>
                      exact False.elim hRun
                  | stopped targetOutcome =>
                      change
                        Rel headResult ctx middle source.returns tokens
                          (Structured.Outcome.halt kind middleSource)
                          targetOutcome
                        at hRun
                      have hFinalRel :=
                        Rel.change_regular_of_nonregular
                          (left := headResult)
                          (right := headResult.append tailResult)
                          (leftRegular := middle)
                          (rightRegular := boundaryRegular)
                          (by simp) hRun
                      exact
                        Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok hFinalRel)

end PreservesWithin

def TargetStopped (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word) :
    TypedCfg.Outcome → Prop
  | .jump label state =>
      stopJump result ctx regular returns tokens label state = true
  | .halt _ _ => True
  | .fallthrough _ | .returnDispatch _ | .invalid _ => False

theorem targetStopped_of_rel
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Outcome}
    (hRel : Rel result ctx regular returns tokens source target) :
    TargetStopped result ctx regular returns tokens target := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  rcases source with ⟨sourceState, sourceMode⟩
  cases sourceMode with
  | regular =>
      obtain ⟨targetState, rfl, hState⟩ :=
        TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
          hOutcome
      rcases hFits with ⟨shape, hShape, hSourceFits⟩
      have hFrame :=
        TypedCfgPreservation.ActivationFrameMatches.check_of_stateRel
          hState hSourceFits
      have hReturns : sourceState.returns = returns := by
        simpa [ActivationRestored] using hRestored
      have hFrame' :
          TypedCfgPreservation.activationFrameMatches?
              returns tokens shape targetState = true := by
        simpa [hReturns] using hFrame
      exact
        stopJump_regular ctx regular returns tokens
          shape targetState hShape hFrame'
  | brk =>
      obtain ⟨label, targetState, hLabel, rfl, hState⟩ :=
        TypedCfgPreservation.OutcomeSimulation.Rel.brk_elim
          hOutcome
      rcases hFits with ⟨shape, hShape, hSourceFits⟩
      have hFrame :=
        TypedCfgPreservation.ActivationFrameMatches.check_of_stateRel
          hState hSourceFits
      have hReturns : sourceState.returns = returns := by
        simpa [ActivationRestored] using hRestored
      have hBreakLabel : ctx.breakLabel? = some label := by
        simpa [
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          using hLabel
      have hFrame' :
          TypedCfgPreservation.activationFrameMatches?
              returns tokens shape targetState = true := by
        simpa [hReturns] using hFrame
      simp [
        TargetStopped, stopJump, continuationMatches?,
        hBreakLabel, hShape, hFrame']
  | cont =>
      obtain ⟨label, targetState, hLabel, rfl, hState⟩ :=
        TypedCfgPreservation.OutcomeSimulation.Rel.cont_elim
          hOutcome
      rcases hFits with ⟨shape, hShape, hSourceFits⟩
      have hFrame :=
        TypedCfgPreservation.ActivationFrameMatches.check_of_stateRel
          hState hSourceFits
      have hReturns : sourceState.returns = returns := by
        simpa [ActivationRestored] using hRestored
      have hContinueLabel : ctx.continueLabel? = some label := by
        simpa [
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          using hLabel
      have hFrame' :
          TypedCfgPreservation.activationFrameMatches?
              returns tokens shape targetState = true := by
        simpa [hReturns] using hFrame
      simp [
        TargetStopped, stopJump, continuationMatches?,
        hContinueLabel, hShape, hFrame']
  | leave =>
      obtain ⟨label, targetState, hLabel, rfl, hState⟩ :=
        TypedCfgPreservation.OutcomeSimulation.Rel.leave_elim
          hOutcome
      rcases hFits with ⟨shape, hShape, hSourceFits⟩
      have hFrame :=
        TypedCfgPreservation.ActivationFrameMatches.check_of_stateRel
          hState hSourceFits
      have hReturns : sourceState.returns = returns := by
        simpa [ActivationRestored] using hRestored
      have hLeaveLabel : ctx.leaveLabel? = some label := by
        simpa [
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          using hLabel
      have hFrame' :
          TypedCfgPreservation.activationFrameMatches?
              returns tokens shape targetState = true := by
        simpa [hReturns] using hFrame
      simp [
        TargetStopped, stopJump, continuationMatches?,
        hLeaveLabel, hShape, hFrame']
  | halt kind =>
      obtain ⟨targetState, targetFinal, rfl, _hStep, _hState⟩ :=
        TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim
          hOutcome
      trivial

theorem afterOpenStepResultWithStop_zero_rel
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Outcome}
    (hRel : Rel result ctx regular returns tokens source target) :
    Simulation.Interaction.Rel
      (DoneRel result ctx regular returns tokens)
      (Simulation.Interaction.pure source)
      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
        (stopJump result ctx regular returns tokens) cfg 0 target) := by
  have hStopped := targetStopped_of_rel hRel
  cases target with
  | jump label targetState =>
      change
        stopJump result ctx regular returns tokens
          label targetState = true at hStopped
      simp only [
        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
        hStopped, if_true]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact hRel
  | halt kind targetState =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact hRel
  | fallthrough targetState
  | returnDispatch targetState
  | invalid targetState =>
      exact False.elim hStopped

theorem target_allStopped
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetRun :
      TypedCfg.InteractionSemantics.Program.OpenRunResult}
    (hRel :
      Simulation.Interaction.Rel
        (DoneRel result ctx regular returns tokens)
        sourceRun targetRun) :
    Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.RunResultStopped
      targetRun := by
  apply Simulation.Interaction.Rel.allDone_right hRel
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ =>
      trivial
  | @ok sourceResult targetResult hRun =>
      cases targetResult with
      | exhausted label state =>
          exact False.elim hRun
      | stopped outcome =>
          trivial

/--
Open preservation for one compiled Structured fragment in an ambient CFG.

The target fuel is existential because adjacent compiler fragments contribute
different numbers of CFG blocks. It is proof output, not public compiler
evidence.
-/
def Preserves (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome) : Prop :=
  ∀ target,
    TypedCfgPreservation.StateRel source tokens target →
      ∃ targetFuel,
        Simulation.Interaction.Rel
          (DoneRel result ctx regular source.returns tokens)
          sourceRun
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            (stopJump result ctx regular source.returns tokens)
            cfg targetFuel entry target)

end OpenOutcome

namespace Stmt

/--
One compiled straight-line statement preserves the complete open interaction
tree through the ambient TypedCfg step. Boundary stopping is deliberately left
to the enclosing control theorem.
-/
theorem openStep_code_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {target : EVMState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStateRel :
      TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel
      (OpenOutcome.OutcomeDoneRel
        result ctx regular source.returns tokens)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.code code) source)
      (TypedCfg.InteractionSemantics.Program.openStep
        cfg entry target) := by
  obtain ⟨output, hType, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code
      hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg code
      output := output
      term := .jump regular }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  have hCode :=
    InteractionPreservation.Code.openRun_toCfg
      hType hFits hStateRel
  have hCodeWithReturns :=
    Simulation.Interaction.Rel.strengthen_left hCode
      (InteractionSemantics.Code.openRun_returns code source)
  have hBlock :
      Simulation.Interaction.Rel
        (OpenOutcome.OutcomeDoneRel
          { blocks := [generated]
            next := supply + 1
            calls := []
            fallthrough? := some output }
          ctx regular source.returns tokens)
        (Simulation.Interaction.bind
          (InteractionSemantics.Code.openRun code source)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final)))
        (TypedCfg.InteractionSemantics.Block.openRun
          generated target) := by
    unfold TypedCfg.InteractionSemantics.Block.openRun
    unfold TypedCfg.Control.Block.run
    apply Simulation.Interaction.Rel.bind_custom hCodeWithReturns
    intro sourceDone targetDone hDone
    rcases hDone with ⟨hOriginal, hReturns⟩
    cases sourceDone with
    | error sourceError =>
        cases targetDone with
        | error targetError =>
            apply Simulation.Interaction.Rel.done
            exact Simulation.Interaction.ExceptRel.error trivial
        | ok targetFinal =>
            cases hOriginal
    | ok sourceFinal =>
        cases targetDone with
        | error targetError =>
            cases hOriginal
        | ok targetFinal =>
            cases hOriginal with
            | ok hFinal =>
                rcases targetFinal with
                  ⟨targetState, targetShape⟩
                rcases hFinal with
                  ⟨hTargetShape, hFinalStateRel, hFinalFits⟩
                have hTargetShape' : targetShape = output := by
                  simpa using hTargetShape
                subst targetShape
                have hFinalFitsOutput :
                    TypedCfgCompiler.Shape.SourceFrameFits
                      output sourceFinal.evm.stack.length := by
                  exact hFinalFits
                have hRelated :
                    OpenOutcome.Rel
                      { blocks := [generated]
                        next := supply + 1
                        calls := []
                        fallthrough? := some output }
                      ctx regular source.returns tokens
                      (Structured.Outcome.regular sourceFinal)
                      (.jump regular targetState) := by
                  constructor
                  · exact
                      TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                        ⟨rfl, hFinalStateRel⟩
                  · constructor
                    · exact ⟨output, rfl, hFinalFitsOutput⟩
                    · simpa [OpenOutcome.ActivationRestored] using hReturns
                have hLeaf :
                    Simulation.Interaction.Rel
                      (OpenOutcome.OutcomeDoneRel
                        { blocks := [generated]
                          next := supply + 1
                          calls := []
                          fallthrough? := some output }
                        ctx regular source.returns tokens)
                      (Simulation.Interaction.pure
                        (Structured.Outcome.regular sourceFinal))
                      (Simulation.Interaction.pure
                        (TypedCfg.Outcome.jump regular targetState)) :=
                  Simulation.Interaction.Rel.done
                    (Simulation.Interaction.ExceptRel.ok hRelated)
                simpa [generated, TypedCfg.Block.runTerm] using hLeaf
  simpa [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind] using hBlock

/--
Fixed-fuel straight-line preservation under an arbitrary enclosing boundary
policy. The policy premise is needed only for the statement's regular jump;
the source invariant rules out every other successful control mode.
-/
theorem openRun_code_within_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular boundaryRegular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit : OpenOutcome.RegularExit}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRegularPolicy :
      ∀ {final : RunState} {targetState : EVMState},
        OpenOutcome.Rel result ctx regular source.returns tokens
            (Structured.Outcome.regular final)
            (.jump regular targetState) →
          OpenOutcome.stopJump boundaryResult ctx boundaryRegular
              source.returns tokens regular targetState =
            match regularExit with
            | .stop => true
            | .resume => false) :
    OpenOutcome.PreservesWithin result boundaryResult cfg entry ctx
      regular boundaryRegular regularExit source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.code code) source)
      1 := by
  intro target hStateRel
  rw [show 1 = 0 + 1 by rfl,
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  have hStep :=
    openStep_code_of_compileStmtFuel?
      (sourceProgram := sourceProgram)
      (sourceFuel := sourceFuel)
      hCompile hBlocks hFits hStateRel
  have hStepRegular :=
    Simulation.Interaction.Rel.strengthen_left hStep
      (InteractionSemantics.Stmt.openRun_code_regular
        sourceProgram sourceFuel code source)
  have hLifted :
      Simulation.Interaction.Rel
        (OpenOutcome.SegmentDoneRel result ctx regular
          source.returns tokens regularExit)
        (Simulation.Interaction.bind
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel (.code code) source)
          Simulation.Interaction.pure)
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Program.openStep
            cfg entry target)
          (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
            (OpenOutcome.stopJump boundaryResult ctx boundaryRegular
              source.returns tokens)
            cfg 0)) := by
    apply Simulation.Interaction.Rel.bind_custom hStepRegular
    intro sourceDone targetDone hDone
    rcases hDone with ⟨hOriginal, hRegular⟩
    cases sourceDone with
    | error sourceError =>
        cases targetDone with
        | error targetError =>
            exact
              Simulation.Interaction.Rel.done
                (Simulation.Interaction.ExceptRel.error trivial)
        | ok targetOutcome =>
            cases hOriginal
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError =>
            cases hOriginal
        | ok targetOutcome =>
            cases hOriginal with
            | ok hOutcome =>
                rcases sourceOutcome with
                  ⟨final, sourceMode⟩
                change sourceMode = .regular at hRegular
                cases sourceMode with
                | regular =>
                    obtain ⟨targetState, rfl, _hState⟩ :=
                      TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
                        hOutcome.1
                    have hOutcome' :
                        OpenOutcome.Rel result ctx regular
                          source.returns tokens
                          (Structured.Outcome.regular final)
                          (.jump regular targetState) := by
                      simpa [
                        TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                        using hOutcome
                    have hPolicy := hRegularPolicy hOutcome'
                    cases regularExit with
                    | stop =>
                        simp only [
                          TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext,
                          hPolicy, if_true]
                        exact
                          Simulation.Interaction.Rel.done
                            (Simulation.Interaction.ExceptRel.ok hOutcome')
                    | resume =>
                        simp only [
                          TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext,
                          hPolicy, if_false,
                          TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_zero]
                        exact
                          Simulation.Interaction.Rel.done
                            (Simulation.Interaction.ExceptRel.ok hOutcome')
                | brk | cont | leave | halt kind =>
                    cases hRegular
  simpa [Simulation.Interaction.bind_pure] using hLifted

/--
Straight-line code at an externally visible fragment boundary stops in one
TypedCfg step.
-/
theorem openRun_code_within_stop_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length) :
    OpenOutcome.PreservesWithin result result cfg entry ctx
      regular regular .stop source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.code code) source)
      1 := by
  apply
    openRun_code_within_of_compileStmtFuel?
      hCompile hBlocks hFits
  intro final targetState hRel
  exact OpenOutcome.targetStopped_of_rel hRel

/--
Straight-line code followed by a statement-list tail leaves its generated rest
label as tagged exhaustion under the enclosing fragment's stop policy.
-/
theorem openRun_code_within_resume_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry boundaryRegular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input
            (TypedCfgCompiler.restLabel supply) =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply) :
    OpenOutcome.PreservesWithin result boundaryResult cfg entry ctx
      (TypedCfgCompiler.restLabel supply) boundaryRegular .resume
      source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.code code) source)
      1 := by
  apply
    openRun_code_within_of_compileStmtFuel?
      hCompile hBlocks hFits
  intro final targetState _hRel
  exact
    OpenOutcome.stopJump_restLabel_eq_false
      hBefore source.returns tokens targetState

/--
The existing straight-line statement lowering preserves the complete open
interaction tree and reaches its regular continuation in one CFG block.
-/
theorem openRun_code_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length) :
    OpenOutcome.Preserves result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.code code) source) := by
  intro target hStateRel
  refine ⟨1, ?_⟩
  exact
    openRun_code_within_stop_of_compileStmtFuel?
      hCompile hBlocks hFits target hStateRel

end Stmt

namespace Block

/--
The empty statement list reaches its regular continuation without exposing any
interaction and preserves the input source-frame shape.
-/
theorem openRun_nil_of_compileStmtListFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          [] ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length) :
    OpenOutcome.Preserves result cfg entry ctx regular source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := [] } source) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump regular }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  intro target hStateRel
  refine ⟨1, ?_⟩
  rw [show 1 = 0 + 1 by rfl,
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind]
  have hTargetRun :
      TypedCfg.Control.Block.run
          TypedCfg.InteractionSemantics.Instr.openRunState
          generated target =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump regular target) := by
    change
      Simulation.Interaction.bind
          (Simulation.Interaction.done
            (Except.ok (target, input)))
          (fun result =>
            if result.2 = input then
              Simulation.Interaction.done
                (Except.ok
                  (TypedCfg.Outcome.jump regular result.1))
            else
              Simulation.Interaction.done
                (Except.error
                  (.InvalidInstruction : EVMException))) =
        Simulation.Interaction.done
          (Except.ok
            (TypedCfg.Outcome.jump regular target))
    simp [Simulation.Interaction.bind]
  have hRelated :
      OpenOutcome.Rel
        { blocks := [generated]
          next := supply
          calls := []
          fallthrough? := some input }
        ctx regular source.returns tokens
        (Structured.Outcome.regular source)
        (.jump regular target) := by
    constructor
    · exact
        TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
          ⟨rfl, hStateRel⟩
    · constructor
      · exact ⟨input, rfl, hFits⟩
      · rfl
  have hStopped :=
    OpenOutcome.targetStopped_of_rel hRelated
  have hDone :
      Simulation.Interaction.Rel
        (OpenOutcome.DoneRel
          { blocks := [generated]
            next := supply
            calls := []
            fallthrough? := some input }
          ctx regular source.returns tokens)
        (Simulation.Interaction.pure
          (Structured.Outcome.regular source))
        (Simulation.Interaction.pure
          (TypedCfg.Control.Program.RunResult.stopped
            (TypedCfg.Outcome.jump regular target))) :=
    Simulation.Interaction.Rel.done
      (Simulation.Interaction.ExceptRel.ok hRelated)
  rw [hTargetRun]
  change
    OpenOutcome.stopJump
      { blocks := [generated]
        next := supply
        calls := []
        fallthrough? := some input }
      ctx regular source.returns tokens regular target = true
    at hStopped
  have hTargetContinuation :
      Simulation.Interaction.bind
          (Simulation.Interaction.pure
            (TypedCfg.Outcome.jump regular target))
          (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
            (OpenOutcome.stopJump
              { blocks := [generated]
                next := supply
                calls := []
                fallthrough? := some input }
              ctx regular source.returns tokens)
            cfg 0) =
        Simulation.Interaction.pure
          (TypedCfg.Control.Program.RunResult.stopped
            (TypedCfg.Outcome.jump regular target)) := by
    change
      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
          (OpenOutcome.stopJump
            { blocks := [generated]
              next := supply
              calls := []
              fallthrough? := some input }
            ctx regular source.returns tokens)
          cfg 0 (TypedCfg.Outcome.jump regular target) =
        Simulation.Interaction.pure
          (TypedCfg.Control.Program.RunResult.stopped
            (TypedCfg.Outcome.jump regular target))
    simp [
      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
      hStopped]
    rfl
  rw [hTargetContinuation]
  simpa [
    InteractionSemantics.Block.openRun,
    EffectSemantics.Control.Block.run,
    Simulation.Interaction.pure] using hDone

/--
The first nonempty statement-list composition theorem: straight-line code
followed by an already-preserved tail. Compiler decomposition, ambient block
inheritance, the generated rest label, and target-fuel addition are owned by
the Structured-to-TypedCfg pass.
-/
theorem openRun_code_cons_within_of_compileStmtListFuel?
    {compilerFuel sourceFuel tailTargetFuel : Nat}
    {code : Structured.Code} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (.code code :: rest) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (hTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape} {middleSource : RunState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel (.code code)
            ctx supply entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        middleSource.returns = source.returns →
        OpenOutcome.PreservesWithin tailResult result cfg
          (TypedCfgCompiler.restLabel supply) ctx
          regular regular .stop middleSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
          tailTargetFuel) :
    OpenOutcome.PreservesWithin result result cfg entry ctx
      regular regular .stop source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := .code code :: rest } source)
      (1 + tailTargetFuel) := by
  cases compilerFuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtListFuel?,
        TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      rcases
          TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
            hCompile with
        ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
      · rcases hNoTail with ⟨hFallthrough, _hResult⟩
        obtain ⟨output, _hType, hHeadResult⟩ :=
          TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code
            hHeadCompile
        rw [hHeadResult] at hFallthrough
        cases hFallthrough
      · rcases hWithTail with
          ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
        have hHeadBlocks :=
          TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
        have hTailBlocks :=
          TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
        have hHeadPreserves :
            OpenOutcome.PreservesWithin headResult
              (headResult.append tailResult) cfg entry ctx
              (TypedCfgCompiler.restLabel supply) regular .resume
              source tokens
              (InteractionSemantics.Stmt.openRun
                sourceProgram sourceFuel (.code code) source)
              1 :=
          Stmt.openRun_code_within_resume_of_compileStmtFuel?
            hHeadCompile hHeadBlocks hFits hBefore
        have hComposed :=
          OpenOutcome.PreservesWithin.sequence
            hHeadPreserves
            (fun middleSource hReturns =>
              hTail hHeadCompile hFallthrough hTailCompile
                hTailBlocks hReturns)
        simpa [
          InteractionSemantics.Block.openRun,
          InteractionSemantics.Stmt.openRun,
          EffectSemantics.Control.Block.run] using hComposed

end Block

end InteractionControlPreservation
end Structured
end EvmCompiler
