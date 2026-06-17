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
  | continue
  deriving DecidableEq

def SegmentRunRel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (regularExit : RegularExit)
    (source : Structured.Outcome) :
    TypedCfg.Control.Program.RunResult → Prop :=
  match regularExit, source.mode with
  | .continue, .regular =>
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
        middle boundaryRegular .continue source tokens
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
  intro target hStateRel
  refine ⟨1, ?_⟩
  rw [show 1 = 0 + 1 by rfl,
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind]
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
  have hLifted :
      Simulation.Interaction.Rel
        (OpenOutcome.DoneRel
          { blocks := [generated]
            next := supply + 1
            calls := []
            fallthrough? := some output }
          ctx regular source.returns tokens)
        (Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (InteractionSemantics.Code.openRun code source)
            (fun final =>
              Simulation.Interaction.pure
                (Structured.Outcome.regular final)))
          Simulation.Interaction.pure)
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Block.openRun
            generated target)
          (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
            (OpenOutcome.stopJump
              { blocks := [generated]
                next := supply + 1
                calls := []
                fallthrough? := some output }
              ctx regular source.returns tokens)
            cfg 0)) := by
    apply Simulation.Interaction.Rel.bind hBlock
    intro sourceOutcome targetOutcome hOutcome
    exact
      OpenOutcome.afterOpenStepResultWithStop_zero_rel
        (cfg := cfg) hOutcome
  simpa [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    TypedCfg.InteractionSemantics.Block.openRun,
    Simulation.Interaction.bind_pure,
    generated, TypedCfg.Block.runTerm] using hLifted

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

end Block

end InteractionControlPreservation
end Structured
end EvmCompiler
