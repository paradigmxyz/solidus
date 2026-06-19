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

theorem continuationMatches?_eq_true_iff
    {returns : List ReturnDest} {tokens : List Word}
    {expectedLabel : Option Assembly.Label}
    {expectedShape : Option TypedCfg.Shape}
    {label : Assembly.Label} {state : EVMState} :
    continuationMatches? returns tokens expectedLabel expectedShape
        label state = true ↔
      ∃ shape,
        expectedLabel = some label ∧
          expectedShape = some shape ∧
            TypedCfgPreservation.ActivationFrameMatches
              returns tokens shape state := by
  unfold continuationMatches?
  cases expectedLabel with
  | none =>
      simp
  | some expected =>
      cases expectedShape with
      | none =>
          simp
      | some shape =>
          rw [Bool.and_eq_true]
          rw [
            TypedCfgPreservation.activationFrameMatches?_eq_true_iff]
          constructor
          · rintro ⟨hLabel, hFrame⟩
            have hLabelEq : label = expected := by
              simpa using hLabel
            refine ⟨shape, ?_, rfl, hFrame⟩
            simpa [hLabelEq]
          · rintro ⟨actualShape, hLabel, hShape, hFrame⟩
            have hLabelEq : expected = label :=
              Option.some.inj hLabel
            have hShapeEq : shape = actualShape :=
              Option.some.inj hShape
            subst expected
            subst actualShape
            exact ⟨by simp, hFrame⟩

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

abbrev StopPolicy := Assembly.Label → EVMState → Bool

def pushStopJump (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (outer : StopPolicy) : StopPolicy :=
  fun label state =>
    outer label state ||
      stopJump result ctx regular returns tokens label state

def StopPolicy.FreshAt (policy : StopPolicy)
    (supply : LabelSupply) : Prop :=
  ∀ scope tag state,
    supply ≤ scope →
      policy (.generated scope tag) state = false

def StopPolicy.FreshExceptAt (policy : StopPolicy)
    (regular : Assembly.Label) (supply : LabelSupply) : Prop :=
  ∀ scope tag state,
    supply ≤ scope →
      .generated scope tag ≠ regular →
        policy (.generated scope tag) state = false

namespace StopPolicy.FreshAt

theorem mono
    {policy : StopPolicy} {supply next : LabelSupply}
    (hFresh : StopPolicy.FreshAt policy supply)
    (hSupply : supply ≤ next) :
    StopPolicy.FreshAt policy next := by
  intro scope tag state hScope
  exact hFresh scope tag state (Nat.le_trans hSupply hScope)

theorem except
    {policy : StopPolicy} {regular : Assembly.Label}
    {supply : LabelSupply}
    (hFresh : StopPolicy.FreshAt policy supply) :
    StopPolicy.FreshExceptAt policy regular supply := by
  intro scope tag state hScope _hNe
  exact hFresh scope tag state hScope

end StopPolicy.FreshAt

namespace StopPolicy.FreshExceptAt

theorem mono
    {policy : StopPolicy} {regular : Assembly.Label}
    {supply next : LabelSupply}
    (hFresh : StopPolicy.FreshExceptAt policy regular supply)
    (hSupply : supply ≤ next) :
    StopPolicy.FreshExceptAt policy regular next := by
  intro scope tag state hScope hNe
  exact hFresh scope tag state (Nat.le_trans hSupply hScope) hNe

theorem toFreshAt
    {policy : StopPolicy} {regular : Assembly.Label}
    {supply : LabelSupply}
    (hFresh : StopPolicy.FreshExceptAt policy regular supply)
    (hRegular :
      TypedCfgCompilerFacts.LabelBeforeSupply regular supply) :
    StopPolicy.FreshAt policy supply := by
  intro scope tag state hScope
  exact hFresh scope tag state hScope (hRegular.generated_ne hScope)

theorem at_succ
    {policy : StopPolicy} {regular : Assembly.Label}
    {supply : LabelSupply}
    (hFresh : StopPolicy.FreshExceptAt policy regular supply)
    (hRegular :
      TypedCfgCompilerFacts.RegularAtSupply regular supply) :
    StopPolicy.FreshAt policy (supply + 1) :=
  (hFresh.mono (by simp)).toFreshAt hRegular.before_succ

end StopPolicy.FreshExceptAt

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

theorem stopJump_generated_eq_false
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply scope tag : Nat}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (hScope : supply ≤ scope)
    (returns : List ReturnDest) (tokens : List Word)
    (state : EVMState) :
    stopJump result ctx regular returns tokens
        (.generated scope tag) state = false := by
  have hRegularNe :
      .generated scope tag ≠ regular :=
    hBefore.regular.generated_ne hScope
  have hRegular :
      continuationMatches? returns tokens
          (some regular) result.fallthrough?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected => by
        cases Option.some.inj hExpected
        exact hRegularNe)
  have hBreak :
      continuationMatches? returns tokens
          ctx.breakLabel? ctx.breakShape?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.breakLabel expected hExpected).generated_ne hScope)
  have hContinue :
      continuationMatches? returns tokens
          ctx.continueLabel? ctx.continueShape?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.continueLabel expected hExpected).generated_ne hScope)
  have hLeave :
      continuationMatches? returns tokens
          ctx.leaveLabel? ctx.leaveShape?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.leaveLabel expected hExpected).generated_ne hScope)
  simp [stopJump, hRegular, hBreak, hContinue, hLeave]

theorem stopJump_generated_eq_false_of_regular_ne
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular regular : Assembly.Label}
    {supply scope tag : Nat}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply)
    (hRegularNe : .generated scope tag ≠ regular)
    (hScope : supply ≤ scope)
    (returns : List ReturnDest) (tokens : List Word)
    (state : EVMState) :
    stopJump result ctx regular returns tokens
        (.generated scope tag) state = false := by
  have hRegular :
      continuationMatches? returns tokens
          (some regular) result.fallthrough?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected => by
        cases Option.some.inj hExpected
        exact hRegularNe)
  have hBreak :
      continuationMatches? returns tokens
          ctx.breakLabel? ctx.breakShape?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.breakLabel expected hExpected).generated_ne hScope)
  have hContinue :
      continuationMatches? returns tokens
          ctx.continueLabel? ctx.continueShape?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.continueLabel expected hExpected).generated_ne hScope)
  have hLeave :
      continuationMatches? returns tokens
          ctx.leaveLabel? ctx.leaveShape?
          (.generated scope tag) state = false :=
    continuationMatches?_eq_false_of_ne
      (fun expected hExpected =>
        (hBefore.leaveLabel expected hExpected).generated_ne hScope)
  simp [stopJump, hRegular, hBreak, hContinue, hLeave]

theorem StopPolicy.FreshAt.of_stopJump
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply : LabelSupply}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (returns : List ReturnDest) (tokens : List Word) :
    StopPolicy.FreshAt
      (stopJump result ctx regular returns tokens) supply := by
  intro scope tag state hScope
  exact
    stopJump_generated_eq_false
      hBefore hScope returns tokens state

theorem StopPolicy.FreshAt.push
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply : LabelSupply}
    (hOuter : StopPolicy.FreshAt outer supply)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (returns : List ReturnDest) (tokens : List Word) :
    StopPolicy.FreshAt
      (pushStopJump result ctx regular returns tokens outer) supply := by
  intro scope tag state hScope
  have hOuterFalse := hOuter scope tag state hScope
  have hLocalFalse :
      stopJump result ctx regular returns tokens
          (.generated scope tag) state =
        false :=
    stopJump_generated_eq_false
      (result := result) (tag := tag)
      hBefore hScope returns tokens state
  simp [pushStopJump, hOuterFalse, hLocalFalse]

theorem pushStopJump_generated_eq_false_of_regular_ne
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular regular : Assembly.Label}
    {supply scope tag : Nat}
    (hOuter : StopPolicy.FreshAt outer supply)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply)
    (hRegularNe : .generated scope tag ≠ regular)
    (hScope : supply ≤ scope)
    (returns : List ReturnDest) (tokens : List Word)
    (state : EVMState) :
    pushStopJump result ctx regular returns tokens outer
        (.generated scope tag) state = false := by
  have hOuterFalse := hOuter scope tag state hScope
  have hLocalFalse :
      stopJump result ctx regular returns tokens
          (.generated scope tag) state =
        false :=
    stopJump_generated_eq_false_of_regular_ne
      (result := result)
      hBefore hRegularNe hScope returns tokens state
  simp [pushStopJump, hOuterFalse, hLocalFalse]

theorem StopPolicy.FreshAt.push_rest_succ
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular : Assembly.Label} {supply : LabelSupply}
    (hOuter : StopPolicy.FreshAt outer supply)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply)
    (returns : List ReturnDest) (tokens : List Word) :
    StopPolicy.FreshAt
      (pushStopJump result ctx (TypedCfgCompiler.restLabel supply)
        returns tokens outer)
      (supply + 1) := by
  apply StopPolicy.FreshAt.push
  · exact hOuter.mono (by simp)
  · exact hBefore.rest_succ

theorem StopPolicy.FreshExceptAt.push_rest
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular : Assembly.Label} {supply : LabelSupply}
    (hOuter : StopPolicy.FreshAt outer supply)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply)
    (returns : List ReturnDest) (tokens : List Word) :
    StopPolicy.FreshExceptAt
      (pushStopJump result ctx (TypedCfgCompiler.restLabel supply)
        returns tokens outer)
      (TypedCfgCompiler.restLabel supply) supply := by
  intro scope tag state hScope hNe
  exact
    pushStopJump_generated_eq_false_of_regular_ne
      hOuter hBefore hNe hScope returns tokens state

theorem pushStopJump_rest_current_generated_eq_false
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular : Assembly.Label} {supply tag : Nat}
    (hOuter : StopPolicy.FreshAt outer supply)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply)
    (hTag : tag ≠ 100)
    (returns : List ReturnDest) (tokens : List Word)
    (state : EVMState) :
    pushStopJump result ctx (TypedCfgCompiler.restLabel supply)
        returns tokens outer (.generated supply tag) state =
      false := by
  apply pushStopJump_generated_eq_false_of_regular_ne
    hOuter hBefore
  · simpa [TypedCfgCompiler.restLabel] using hTag
  · exact Nat.le_refl supply

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

def segmentStopJump
    (fragmentResult boundaryResult : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (fragmentRegular boundaryRegular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word) :
    RegularExit → Assembly.Label → EVMState → Bool
  | .stop =>
      stopJump boundaryResult ctx boundaryRegular returns tokens
  | .resume =>
      pushStopJump fragmentResult ctx fragmentRegular returns tokens
        (stopJump boundaryResult ctx boundaryRegular returns tokens)

def SegmentRunRel (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (regularExit : RegularExit)
    (source : Structured.Outcome) :
    TypedCfg.Control.Program.RunResult → Prop :=
  fun
  | .exhausted _ _ => False
  | .stopped _ target =>
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

theorem Rel.change_result_of_fallthrough_eq
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome} {target : TypedCfg.Outcome}
    (hFallthrough :
      left.fallthrough? = right.fallthrough?)
    (hRel : Rel left ctx regular returns tokens source target) :
    Rel right ctx regular returns tokens source target := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  refine ⟨hOutcome, ?_, hRestored⟩
  rcases source with ⟨sourceState, sourceMode⟩
  cases sourceMode with
  | regular =>
      rcases hFits with ⟨shape, hShape, hSourceFits⟩
      exact ⟨shape, hFallthrough ▸ hShape, hSourceFits⟩
  | brk | cont | leave | halt kind =>
      exact hFits

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

theorem Rel.not_regular_of_fallthrough_none
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {final : RunState} {target : TypedCfg.Outcome}
    (hFallthrough : result.fallthrough? = none)
    (hRel :
      Rel result ctx regular returns tokens
        (Structured.Outcome.regular final) target) :
    False := by
  rcases hRel.2.1 with ⟨shape, hShape, _hFits⟩
  rw [hFallthrough] at hShape
  cases hShape

/--
Eliminate a related regular outcome at a compiler-checked join shape.

`requireFallthrough?` permits a fragment with no regular path, but the
existence of this regular relation rules that case out and identifies the
compiler's actual fallthrough shape with `expected`.
-/
theorem Rel.regular_elim_of_required_fallthrough
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {expected : TypedCfg.Shape}
    {source : RunState} {target : TypedCfg.Outcome}
    (hRequire :
      result.requireFallthrough? expected = some ())
    (hRel :
      Rel result ctx regular returns tokens
        (Structured.Outcome.regular source) target) :
    ∃ targetState,
      target = .jump regular targetState ∧
        TypedCfgPreservation.StateRel source tokens targetState ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            expected source.evm.stack.length ∧
            source.returns = returns := by
  obtain ⟨targetState, rfl, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
      hRel.1
  rcases hRel.2.1 with ⟨shape, hShape, hFits⟩
  have hExpected :
      result.fallthrough? = some expected := by
    rcases
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
          hRequire with
      hNone | hSome
    · rw [hNone] at hShape
      cases hShape
    · exact hSome
  have hShapeEq : shape = expected := by
    rw [hExpected] at hShape
    exact Option.some.inj hShape.symm
  subst shape
  have hReturns : source.returns = returns := by
    simpa [ActivationRestored] using hRel.2.2
  exact ⟨targetState, rfl, hStateRel, hFits, hReturns⟩

theorem Rel.mode_ne_regular_of_fallthrough_none
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome} {target : TypedCfg.Outcome}
    (hFallthrough : result.fallthrough? = none)
    (hRel :
      Rel result ctx regular returns tokens source target) :
    source.mode ≠ .regular := by
  intro hMode
  rcases source with ⟨state, mode⟩
  change mode = .regular at hMode
  subst mode
  exact Rel.not_regular_of_fallthrough_none hFallthrough hRel

theorem Rel.change_result_of_required_fallthrough
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome} {target : TypedCfg.Outcome}
    {expected : TypedCfg.Shape}
    (hRequire :
      left.requireFallthrough? expected = some ())
    (hRight :
      right.fallthrough? = some expected)
    (hRel : Rel left ctx regular returns tokens source target) :
    Rel right ctx regular returns tokens source target := by
  by_cases hMode : source.mode = .regular
  · rcases
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
          hRequire with
      hNone | hSome
    · rcases source with ⟨state, mode⟩
      change mode = .regular at hMode
      subst mode
      exact False.elim
        (Rel.not_regular_of_fallthrough_none hNone hRel)
    · exact
        Rel.change_result_of_fallthrough_eq
          (hSome.trans hRight.symm) hRel
  · exact
      Rel.change_regular_of_nonregular
        (left := left) (right := right)
        (leftRegular := regular) (rightRegular := regular)
        hMode hRel

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
  | stopped remaining outcome =>
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

theorem SegmentRunRel.change_result_of_required_fallthrough
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Control.Program.RunResult}
    {regularExit : RegularExit} {expected : TypedCfg.Shape}
    (hRequire :
      left.requireFallthrough? expected = some ())
    (hRight :
      right.fallthrough? = some expected)
    (hRun :
      SegmentRunRel left ctx regular returns tokens regularExit
        source target) :
    SegmentRunRel right ctx regular returns tokens regularExit
      source target := by
  rcases source with ⟨sourceState, sourceMode⟩
  cases regularExit <;> cases sourceMode <;> cases target
  all_goals
    first
    | exact False.elim hRun
    | exact
        Rel.change_result_of_required_fallthrough
          hRequire hRight hRun

theorem SegmentDoneRel.change_result_of_required_fallthrough
    {left right : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Except EVMException Structured.Outcome}
    {target :
      Except EVMException TypedCfg.Control.Program.RunResult}
    {regularExit : RegularExit} {expected : TypedCfg.Shape}
    (hRequire :
      left.requireFallthrough? expected = some ())
    (hRight :
      right.fallthrough? = some expected)
    (hDone :
      SegmentDoneRel left ctx regular returns tokens regularExit
        source target) :
    SegmentDoneRel right ctx regular returns tokens regularExit
      source target := by
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hRun =>
      exact
        Simulation.Interaction.ExceptRel.ok
          (SegmentRunRel.change_result_of_required_fallthrough
            hRequire hRight hRun)

theorem SegmentRunRel.addFuelToRunResult
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Control.Program.RunResult}
    {regularExit : RegularExit}
    (extra : Nat)
    (hRun :
      SegmentRunRel result ctx regular returns tokens regularExit
        source target) :
    SegmentRunRel result ctx regular returns tokens regularExit source
      (TypedCfg.InteractionSemantics.Program.addFuelToRunResult
        extra target) := by
  cases target with
  | exhausted label state =>
      exact False.elim hRun
  | stopped remaining outcome =>
      exact hRun

theorem SegmentDoneRel.addFuelToRunResult
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Except EVMException Structured.Outcome}
    {target :
      Except EVMException TypedCfg.Control.Program.RunResult}
    {regularExit : RegularExit}
    (extra : Nat)
    (hDone :
      SegmentDoneRel result ctx regular returns tokens regularExit
        source target) :
    SegmentDoneRel result ctx regular returns tokens regularExit source
      (target.map
        (TypedCfg.InteractionSemantics.Program.addFuelToRunResult
          extra)) := by
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hRun =>
      exact
        Simulation.Interaction.ExceptRel.ok
          (SegmentRunRel.addFuelToRunResult extra hRun)

def PreservesUnder (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (regularExit : RegularExit)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (targetFuel : Nat) (policy : StopPolicy) : Prop :=
  ∀ target,
    TypedCfgPreservation.StateRel source tokens target →
      Simulation.Interaction.Rel
        (SegmentDoneRel result ctx regular
          source.returns tokens regularExit)
        sourceRun
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg targetFuel entry target)

/--
Successful-execution forward preservation under an active target stop policy.

The theorem quantifies over every concrete source interaction transcript and
derives target fuel from that execution. This is the pass-wide interface for
loops and internal calls, whose successful paths need not share one uniform
target budget. Stronger structural `PreservesUnder` theorems convert to this
interface directly.
-/
def ExecPreservesUnder (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (policy : StopPolicy) : Prop :=
  ∀ target,
    TypedCfgPreservation.StateRel source tokens target →
      ∀ transcript sourceOutcome,
        Simulation.Interaction.Executes
            sourceRun transcript (.ok sourceOutcome) →
          ∃ targetFuel remaining targetOutcome,
            Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                  policy cfg targetFuel entry target)
                transcript
                (.ok
                  (.stopped remaining targetOutcome)) ∧
              Rel result ctx regular source.returns tokens
                sourceOutcome targetOutcome

/--
Execution-oriented preservation at one uniform target budget. This is the
internal bridge between fuel-accounting proofs and the structural open-world
`PreservesUnder` interface.
-/
def UniformExecPreservesUnder (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (targetFuel : Nat) (policy : StopPolicy) : Prop :=
  forall target,
    TypedCfgPreservation.StateRel source tokens target ->
      forall transcript sourceOutcome,
        Simulation.Interaction.Executes
            sourceRun transcript (.ok sourceOutcome) ->
          exists remaining targetOutcome,
            Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                  policy cfg targetFuel entry target)
                transcript
                (.ok (.stopped remaining targetOutcome)) /\
              Rel result ctx regular source.returns tokens
                sourceOutcome targetOutcome

/-- Execution-oriented preservation whose internally selected target budget is
bounded by one source-owned ceiling. -/
def BoundedExecPreservesUnder (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (targetBudget : Nat) (policy : StopPolicy) : Prop :=
  forall target,
    TypedCfgPreservation.StateRel source tokens target ->
      forall transcript sourceOutcome,
        Simulation.Interaction.Executes
            sourceRun transcript (.ok sourceOutcome) ->
          exists targetFuel remaining targetOutcome,
            targetFuel <= targetBudget /\
              Simulation.Interaction.Executes
                  (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                    policy cfg targetFuel entry target)
                  transcript
                  (.ok (.stopped remaining targetOutcome)) /\
                Rel result ctx regular source.returns tokens
                  sourceOutcome targetOutcome

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
  PreservesUnder fragmentResult cfg entry ctx fragmentRegular regularExit
    source tokens sourceRun targetFuel
    (segmentStopJump fragmentResult boundaryResult ctx
      fragmentRegular boundaryRegular source.returns tokens regularExit)

def TargetStoppedBy (policy : StopPolicy) :
    TypedCfg.Outcome → Prop
  | .jump label state =>
      policy label state = true
  | .halt _ _ => True
  | .fallthrough _ | .returnDispatch _ | .invalid _ => False

abbrev TargetStopped (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word) :=
  TargetStoppedBy
    (stopJump result ctx regular returns tokens)

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
        TargetStoppedBy, stopJump, continuationMatches?,
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
        TargetStoppedBy, stopJump, continuationMatches?,
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
        TargetStoppedBy, stopJump, continuationMatches?,
        hLeaveLabel, hShape, hFrame']
  | halt kind =>
      obtain ⟨targetState, targetFinal, rfl, _hStep, _hState⟩ :=
        TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim
          hOutcome
      trivial

theorem targetStoppedBy_pushStopJump_of_rel
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Outcome}
    (outer : StopPolicy)
    (hRel : Rel result ctx regular returns tokens source target) :
    TargetStoppedBy
      (pushStopJump result ctx regular returns tokens outer)
      target := by
  have hStopped := targetStopped_of_rel hRel
  cases target with
  | jump label targetState =>
      change
        stopJump result ctx regular returns tokens
          label targetState = true
        at hStopped
      simp [TargetStoppedBy, pushStopJump, hStopped]
  | halt kind targetState =>
      trivial
  | fallthrough targetState
  | returnDispatch targetState
  | invalid targetState =>
      exact False.elim hStopped

def StopPolicy.StopsNonregular (policy : StopPolicy)
    (ctx : TypedCfgCompiler.Context)
    (returns : List ReturnDest) (tokens : List Word) : Prop :=
  ∀ {result : TypedCfgCompiler.Result} {regular : Assembly.Label}
      {source : Structured.Outcome} {target : TypedCfg.Outcome},
    source.mode ≠ .regular →
      Rel result ctx regular returns tokens source target →
        TargetStoppedBy policy target

theorem StopPolicy.StopsNonregular.push
    {boundaryResult : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    (outer : StopPolicy) :
    StopPolicy.StopsNonregular
      (pushStopJump boundaryResult ctx boundaryRegular
        returns tokens outer)
      ctx returns tokens := by
  intro result regular source target hMode hRel
  have hBoundaryRel :
      Rel boundaryResult ctx boundaryRegular returns tokens
        source target :=
    Rel.change_regular_of_nonregular
      (left := result) (right := boundaryResult)
      (leftRegular := regular) (rightRegular := boundaryRegular)
      hMode hRel
  exact targetStoppedBy_pushStopJump_of_rel outer hBoundaryRel

theorem afterOpenStepResultWithStop_of_targetStopped
    {result boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {ctx : TypedCfgCompiler.Context}
    {regular boundaryRegular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Outcome}
    {regularExit : RegularExit} {fuel : Nat}
    (hRel : Rel result ctx regular returns tokens source target)
    (hStopped :
      TargetStopped boundaryResult ctx boundaryRegular
        returns tokens target) :
    Simulation.Interaction.Rel
      (SegmentDoneRel result ctx regular returns tokens regularExit)
      (Simulation.Interaction.pure source)
      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
        (stopJump boundaryResult ctx boundaryRegular returns tokens)
        cfg fuel target) := by
  cases target with
  | jump label targetState =>
      change
        stopJump boundaryResult ctx boundaryRegular returns tokens
          label targetState = true
        at hStopped
      simp only [
        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
        hStopped, if_true]
      exact
        Simulation.Interaction.Rel.done
          (Simulation.Interaction.ExceptRel.ok hRel)
  | halt kind targetState =>
      exact
        Simulation.Interaction.Rel.done
          (Simulation.Interaction.ExceptRel.ok hRel)
  | fallthrough targetState
  | returnDispatch targetState
  | invalid targetState =>
      exact False.elim hStopped

theorem afterOpenStepResultWithPolicy_of_targetStopped
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Outcome}
    {regularExit : RegularExit} {fuel : Nat}
    {policy : StopPolicy}
    (hRel : Rel result ctx regular returns tokens source target)
    (hStopped : TargetStoppedBy policy target) :
    Simulation.Interaction.Rel
      (SegmentDoneRel result ctx regular returns tokens regularExit)
      (Simulation.Interaction.pure source)
      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
        policy cfg fuel target) := by
  cases target with
  | jump label targetState =>
      change policy label targetState = true at hStopped
      simp only [
        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
        hStopped, if_true]
      exact
        Simulation.Interaction.Rel.done
          (Simulation.Interaction.ExceptRel.ok hRel)
  | halt kind targetState =>
      exact
        Simulation.Interaction.Rel.done
          (Simulation.Interaction.ExceptRel.ok hRel)
  | fallthrough targetState
  | returnDispatch targetState
  | invalid targetState =>
      exact False.elim hStopped

theorem afterOpenStepResultWithPolicy_executes_of_targetStopped
    {cfg : TypedCfg.Program} {policy : StopPolicy}
    {fuel : Nat} {target : TypedCfg.Outcome}
    (hStopped : TargetStoppedBy policy target) :
    Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
        policy cfg fuel target)
      []
      (.ok
        (TypedCfg.Control.Program.RunResult.stopped fuel target)) := by
  cases target with
  | jump label targetState =>
      change policy label targetState = true at hStopped
      simpa [
        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
        hStopped] using
        (Simulation.Interaction.Executes.done
          (.ok
            (TypedCfg.Control.Program.RunResult.stopped fuel
              (TypedCfg.Outcome.jump label targetState))))
  | halt kind targetState =>
      simpa [
        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop] using
        (Simulation.Interaction.Executes.done
          (.ok
            (TypedCfg.Control.Program.RunResult.stopped fuel
              (TypedCfg.Outcome.halt kind targetState))))
  | fallthrough targetState =>
      simp [TargetStoppedBy] at hStopped
  | returnDispatch targetState =>
      simp [TargetStoppedBy] at hStopped
  | invalid targetState =>
      simp [TargetStoppedBy] at hStopped

namespace PreservesUnder

theorem uniformExec
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {regularExit : RegularExit}
    (hPreserves :
      PreservesUnder result cfg entry ctx regular regularExit
        source tokens sourceRun targetFuel policy) :
    UniformExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetFuel policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain ⟨targetDone, hTargetExec, hDone⟩ :=
    Simulation.Interaction.Rel.executes
      (hPreserves target hStateRel) hSourceExec
  cases targetDone with
  | error targetError =>
      cases hDone
  | ok targetResult =>
      cases hDone with
      | ok hRun =>
          cases targetResult with
          | exhausted label targetState =>
              exact False.elim hRun
          | stopped remaining targetOutcome =>
              exact ⟨remaining, targetOutcome, hTargetExec, hRun⟩

theorem boundedExec
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {regularExit : RegularExit}
    (hPreserves :
      PreservesUnder result cfg entry ctx regular regularExit
        source tokens sourceRun targetFuel policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetFuel policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain ⟨remaining, targetOutcome, hTargetExec, hRel⟩ :=
    uniformExec hPreserves target hStateRel transcript sourceOutcome hSourceExec
  exact ⟨targetFuel, remaining, targetOutcome, Nat.le_refl _,
    hTargetExec, hRel⟩

theorem exec
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {regularExit : RegularExit}
    (hPreserves :
      PreservesUnder result cfg entry ctx regular regularExit
        source tokens sourceRun targetFuel policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      sourceRun policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain ⟨targetDone, hTargetExec, hDone⟩ :=
    Simulation.Interaction.Rel.executes
      (hPreserves target hStateRel) hSourceExec
  cases targetDone with
  | error targetError =>
      cases hDone
  | ok targetResult =>
      cases hDone with
      | ok hRun =>
          cases targetResult with
          | exhausted label targetState =>
              exact False.elim hRun
          | stopped remaining targetOutcome =>
              exact
                ⟨targetFuel, remaining, targetOutcome,
                  hTargetExec, hRun⟩

theorem change_result_of_required_fallthrough
    {left right : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {regularExit : RegularExit} {expected : TypedCfg.Shape}
    (hRequire :
      left.requireFallthrough? expected = some ())
    (hRight :
      right.fallthrough? = some expected)
    (hPreserves :
      PreservesUnder left cfg entry ctx regular regularExit
        source tokens sourceRun targetFuel policy) :
    PreservesUnder right cfg entry ctx regular regularExit
      source tokens sourceRun targetFuel policy := by
  intro target hStateRel
  apply Simulation.Interaction.Rel.mono
    (hPreserves target hStateRel)
  intro sourceDone targetDone hDone
  exact
    SegmentDoneRel.change_result_of_required_fallthrough
      hRequire hRight hDone

theorem pad
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {regularExit : RegularExit}
    (hPreserves :
      PreservesUnder result cfg entry ctx regular regularExit
        source tokens sourceRun targetFuel policy)
    (extra : Nat) :
    PreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun (targetFuel + extra) policy := by
  intro target hStateRel
  have hRel := hPreserves target hStateRel
  have hStopped :
      Simulation.Interaction.AllDone
        TypedCfg.InteractionSemantics.Program.RunResultStopped
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg targetFuel entry target) := by
    apply Simulation.Interaction.Rel.allDone_right hRel
    intro sourceDone targetDone hDone
    cases hDone with
    | error _ =>
        trivial
    | @ok sourceResult targetResult hRun =>
        cases targetResult with
        | exhausted label state =>
            exact False.elim hRun
        | stopped remaining outcome =>
            trivial
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_add_eq_map_addFuel_of_allStopped
      (stopJump := policy)
      (program := cfg) (fuel := targetFuel) (extra := extra)
      (label := entry) (state := target) hStopped]
  have hMapped :
      Simulation.Interaction.Rel
        (SegmentDoneRel result ctx regular
          source.returns tokens regularExit)
        (Simulation.Interaction.bind
          sourceRun Simulation.Interaction.pure)
        (Simulation.Interaction.map
          (TypedCfg.InteractionSemantics.Program.addFuelToRunResult extra)
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            policy cfg targetFuel entry target)) := by
    apply Simulation.Interaction.Rel.bind_custom hRel
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
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError =>
            cases hDone
        | ok targetResult =>
            exact
              Simulation.Interaction.Rel.done
                (SegmentDoneRel.addFuelToRunResult
                  extra hDone)
  simpa [
    Simulation.Interaction.bind_pure,
    Simulation.Interaction.map] using hMapped

theorem prepend_closed_jump
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry next regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source nextSource : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {regularExit : RegularExit} {targetFuel : Nat}
    {policy : StopPolicy}
    (hStep :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          ∃ targetAfter,
            TypedCfg.InteractionSemantics.Program.openStep
                cfg entry target =
              .done (.ok (.jump next targetAfter)) ∧
            TypedCfgPreservation.StateRel
              nextSource tokens targetAfter)
    (hReturns :
      nextSource.returns = source.returns)
    (hNoStop :
      ∀ targetAfter,
        TypedCfgPreservation.StateRel
            nextSource tokens targetAfter →
          policy next targetAfter = false)
    (hTail :
      PreservesUnder result cfg next ctx regular regularExit
        nextSource tokens sourceRun targetFuel policy) :
    PreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun (targetFuel + 1) policy := by
  intro target hStateRel
  obtain ⟨targetAfter, hTargetStep, hAfterRel⟩ :=
    hStep target hStateRel
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind,
    hTargetStep]
  simp only [Simulation.Interaction.bind_done_ok]
  have hContinue := hNoStop targetAfter hAfterRel
  simp only [
    TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
    hContinue, if_false]
  simpa [hReturns] using hTail targetAfter hAfterRel

theorem of_openStep
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {regularExit : RegularExit} {policy : StopPolicy}
    (hStep :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          Simulation.Interaction.Rel
            (OutcomeDoneRel result ctx regular
              source.returns tokens)
            sourceRun
            (TypedCfg.InteractionSemantics.Program.openStep
              cfg entry target))
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          TargetStoppedBy policy targetOutcome) :
    PreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun 1 policy := by
  intro target hStateRel
  rw [show 1 = 0 + 1 by rfl,
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  have hLifted :
      Simulation.Interaction.Rel
        (SegmentDoneRel result ctx regular
          source.returns tokens regularExit)
        (Simulation.Interaction.bind sourceRun
          Simulation.Interaction.pure)
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Program.openStep
            cfg entry target)
          (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
            policy cfg 0)) := by
    apply Simulation.Interaction.Rel.bind_custom
      (hStep target hStateRel)
    intro sourceDone targetDone hDone
    cases sourceDone with
    | error sourceError =>
        cases targetDone with
        | error targetError =>
            exact
              Simulation.Interaction.Rel.done
                (Simulation.Interaction.ExceptRel.error trivial)
        | ok targetOutcome =>
            cases hDone
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError =>
            cases hDone
        | ok targetOutcome =>
            cases hDone with
            | ok hOutcome =>
                exact
                  afterOpenStepResultWithPolicy_of_targetStopped
                    hOutcome (hStops hOutcome)
  simpa [Simulation.Interaction.bind_pure] using hLifted

theorem of_openStep_no_fallthrough
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {regularExit : RegularExit} {policy : StopPolicy}
    (hFallthrough : result.fallthrough? = none)
    (hStep :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          Simulation.Interaction.Rel
            (OutcomeDoneRel result ctx regular
              source.returns tokens)
            sourceRun
            (TypedCfg.InteractionSemantics.Program.openStep
              cfg entry target))
    (hNonregularStops :
      StopPolicy.StopsNonregular
        policy ctx source.returns tokens) :
    PreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun 1 policy := by
  apply of_openStep hStep
  intro sourceOutcome targetOutcome hRel
  exact
    hNonregularStops
      (Rel.mode_ne_regular_of_fallthrough_none
        hFallthrough hRel)
      hRel

theorem sequence
    {headResult tailResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry middle regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState →
        Simulation.Interaction EVMException Structured.Outcome}
    {headFuel tailFuel : Nat} {policy : StopPolicy}
    (hHead :
      PreservesUnder headResult cfg entry ctx middle .resume
        source tokens headRun headFuel
        (pushStopJump headResult ctx middle
          source.returns tokens policy))
    (hMiddleNoStop :
      ∀ targetMiddle,
        policy middle targetMiddle = false)
    (hNonregularStops :
      ∀ {middleSource : RunState} {headMode : Structured.Mode}
          {targetOutcome : TypedCfg.Outcome},
        headMode ≠ .regular →
          Rel headResult ctx middle source.returns tokens
              { state := middleSource, mode := headMode }
              targetOutcome →
            TargetStoppedBy policy targetOutcome)
    (hTail :
      ∀ middleSource,
        middleSource.returns = source.returns →
          PreservesUnder tailResult cfg middle ctx regular .stop
            middleSource tokens (tailRun middleSource) tailFuel policy) :
    PreservesUnder (headResult.append tailResult)
      cfg entry ctx regular .stop source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      (headFuel + tailFuel) policy := by
  intro target hStateRel
  have hRefines :
      ∀ next nextState,
        policy next nextState = true →
          pushStopJump headResult ctx middle
              source.returns tokens policy next nextState =
            true := by
    intro next nextState hOuter
    simp [pushStopJump, hOuter]
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
      policy
      (pushStopJump headResult ctx middle
        source.returns tokens policy)
      cfg headFuel tailFuel entry target hRefines]
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
              have hNonregular
                  (hMode : headMode ≠ .regular) :
                  Simulation.Interaction.Rel
                    (SegmentDoneRel
                      (headResult.append tailResult)
                      ctx regular source.returns tokens .stop)
                    (Simulation.Interaction.pure
                      { state := middleSource, mode := headMode })
                    (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                      policy cfg tailFuel targetResult) := by
                cases targetResult with
                | exhausted label targetMiddle =>
                    exact False.elim hRun
                | stopped remaining targetOutcome =>
                    change
                      Rel headResult ctx middle source.returns tokens
                        { state := middleSource, mode := headMode }
                        targetOutcome
                      at hRun
                    have hOutputRel :
                        Rel (headResult.append tailResult) ctx
                          regular source.returns tokens
                          { state := middleSource, mode := headMode }
                          targetOutcome :=
                      Rel.change_regular_of_nonregular
                        (left := headResult)
                        (right := headResult.append tailResult)
                        (leftRegular := middle)
                        (rightRegular := regular)
                        hMode hRun
                    have hFinal :=
                      afterOpenStepResultWithPolicy_of_targetStopped
                        (cfg := cfg)
                        (regularExit := .stop)
                        (fuel := remaining + tailFuel)
                        hOutputRel (hNonregularStops hMode hRun)
                    simpa [
                      TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop] using
                      hFinal
              cases headMode with
              | regular =>
                  cases targetResult with
                  | exhausted label targetMiddle =>
                      exact False.elim hRun
                  | stopped remaining targetOutcome =>
                      change
                        Rel headResult ctx middle source.returns tokens
                          (Structured.Outcome.regular middleSource)
                          targetOutcome
                        at hRun
                      obtain ⟨targetMiddle, rfl, hMiddleStateRel⟩ :=
                        TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
                          hRun.1
                      have hReturns :
                          middleSource.returns = source.returns := by
                        simpa [ActivationRestored] using hRun.2.2
                      have hTailPadded :=
                        PreservesUnder.pad
                          (hTail middleSource hReturns) remaining
                      have hTailRel :=
                        hTailPadded targetMiddle hMiddleStateRel
                      have hAppended :=
                        Simulation.Interaction.Rel.mono hTailRel
                          (fun sourceFinal targetFinal hFinal =>
                            SegmentDoneRel.append_right_stop
                              (left := headResult) hFinal)
                      have hTailRel' :
                          Simulation.Interaction.Rel
                            (SegmentDoneRel
                              (headResult.append tailResult)
                              ctx regular source.returns tokens .stop)
                            (tailRun middleSource)
                            (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                              policy cfg (remaining + tailFuel)
                              middle targetMiddle) := by
                        simpa [hReturns, Nat.add_comm] using hAppended
                      simpa [
                        TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop,
                        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                        TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext,
                        hMiddleNoStop targetMiddle] using hTailRel'
              | brk =>
                  exact hNonregular (by simp)
              | cont =>
                  exact hNonregular (by simp)
              | leave =>
                  exact hNonregular (by simp)
              | halt kind =>
                  exact hNonregular (by simp)

theorem ignore_tail_of_no_fallthrough
    {headResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry headRegular resultRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState →
        Simulation.Interaction EVMException Structured.Outcome}
    {headFuel : Nat} {policy : StopPolicy}
    {regularExit : RegularExit}
    (hFallthrough : headResult.fallthrough? = none)
    (hHead :
      PreservesUnder headResult cfg entry ctx headRegular regularExit
        source tokens headRun headFuel policy) :
    PreservesUnder headResult cfg entry ctx resultRegular regularExit
      source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      headFuel policy := by
  intro target hStateRel
  have hHeadRel := hHead target hStateRel
  have hLifted :
      Simulation.Interaction.Rel
        (SegmentDoneRel headResult ctx resultRegular
          source.returns tokens regularExit)
        (Simulation.Interaction.bind headRun
          (fun outcome =>
            match outcome.mode with
            | .regular => tailRun outcome.state
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure outcome))
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            policy cfg headFuel entry target)
          Simulation.Interaction.pure) := by
    apply Simulation.Interaction.Rel.bind_custom hHeadRel
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
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError =>
            cases hDone
        | ok targetResult =>
            cases hDone with
            | ok hRun =>
                rcases sourceOutcome with ⟨middleSource, sourceMode⟩
                cases sourceMode with
                | regular =>
                    cases targetResult with
                    | exhausted label targetMiddle =>
                        exact False.elim hRun
                    | stopped _remaining targetOutcome =>
                        exact False.elim
                          (Rel.not_regular_of_fallthrough_none
                            hFallthrough hRun)
                | brk | cont | leave | halt kind =>
                    cases targetResult with
                    | exhausted label targetMiddle =>
                        exact False.elim hRun
                    | stopped _remaining targetOutcome =>
                        change
                          Rel headResult ctx headRegular
                            source.returns tokens
                            _ targetOutcome
                          at hRun
                        have hFinalRel :=
                          Rel.change_regular_of_nonregular
                            (left := headResult)
                            (right := headResult)
                            (leftRegular := headRegular)
                            (rightRegular := resultRegular)
                            (by simp) hRun
                        exact
                          Simulation.Interaction.Rel.done
                            (Simulation.Interaction.ExceptRel.ok hFinalRel)
  simpa [Simulation.Interaction.bind_pure] using hLifted

end PreservesUnder

namespace BoundedExecPreservesUnder

/-- Forget the source-owned ceiling while retaining the execution witness. -/
theorem exec
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetBudget : Nat} {policy : StopPolicy}
    (hPreserves :
      BoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget policy) :
    ExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, remaining, targetOutcome, _hFuel,
        hTargetExec, hRel⟩ :=
    hPreserves target hStateRel transcript sourceOutcome hSourceExec
  exact ⟨targetFuel, remaining, targetOutcome, hTargetExec, hRel⟩

/-- The numeric execution ceiling is independent of compiler-result metadata. -/
theorem change_result_of_fallthrough_eq
    {left right : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetBudget : Nat} {policy : StopPolicy}
    (hFallthrough : left.fallthrough? = right.fallthrough?)
    (hPreserves :
      BoundedExecPreservesUnder left cfg entry ctx regular
        source tokens sourceRun targetBudget policy) :
    BoundedExecPreservesUnder right cfg entry ctx regular
      source tokens sourceRun targetBudget policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, remaining, targetOutcome, hFuel,
        hTargetExec, hRel⟩ :=
    hPreserves target hStateRel transcript sourceOutcome hSourceExec
  exact
    ⟨targetFuel, remaining, targetOutcome, hFuel, hTargetExec,
      Rel.change_result_of_fallthrough_eq hFallthrough hRel⟩

theorem mono_budget
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {smaller larger : Nat} {policy : StopPolicy}
    (hPreserves :
      BoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun smaller policy)
    (hLe : smaller <= larger) :
    BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun larger policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, remaining, targetOutcome, hFuel,
        hTargetExec, hRel⟩ :=
    hPreserves target hStateRel transcript sourceOutcome hSourceExec
  exact ⟨targetFuel, remaining, targetOutcome,
    Nat.le_trans hFuel hLe, hTargetExec, hRel⟩

theorem close_refined_under
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetBudget : Nat} {outer inner : StopPolicy}
    (hPreserves :
      BoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget inner)
    (hRefines :
      forall label state,
        outer label state = true -> inner label state = true)
    (hStops :
      forall {sourceOutcome targetOutcome},
        Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome ->
          TargetStoppedBy outer targetOutcome) :
    BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetBudget outer := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, remaining, targetOutcome, hFuel,
        hTargetExec, hRel⟩ :=
    hPreserves target hStateRel transcript sourceOutcome hSourceExec
  have hContinuation :=
    afterOpenStepResultWithPolicy_executes_of_targetStopped
      (cfg := cfg) (fuel := remaining) (hStops hRel)
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok
      (next :=
        TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
          outer cfg 0)
      hTargetExec hContinuation
  have hClosed :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          outer cfg targetFuel entry target)
        transcript (.ok (.stopped remaining targetOutcome)) := by
    have hClosedWithZero :
        Simulation.Interaction.Executes
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            outer cfg (targetFuel + 0) entry target)
          transcript (.ok (.stopped remaining targetOutcome)) := by
      rw [
        TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
          outer inner cfg targetFuel 0 entry target hRefines]
      simpa using hCombined
    simpa using hClosedWithZero
  exact
    ⟨targetFuel, remaining, targetOutcome, hFuel, hClosed, hRel⟩

theorem change_result_of_required_fallthrough
    {left right : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetBudget : Nat} {policy : StopPolicy} {expected : TypedCfg.Shape}
    (hRequire : left.requireFallthrough? expected = some ())
    (hRight : right.fallthrough? = some expected)
    (hPreserves :
      BoundedExecPreservesUnder left cfg entry ctx regular
        source tokens sourceRun targetBudget policy) :
    BoundedExecPreservesUnder right cfg entry ctx regular
      source tokens sourceRun targetBudget policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, remaining, targetOutcome, hFuel,
        hTargetExec, hRel⟩ :=
    hPreserves target hStateRel transcript sourceOutcome hSourceExec
  exact
    ⟨targetFuel, remaining, targetOutcome, hFuel, hTargetExec,
      Rel.change_result_of_required_fallthrough hRequire hRight hRel⟩

theorem prepend_closed_jump
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry next regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source nextSource : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailBudget : Nat} {policy : StopPolicy}
    (hStep :
      forall target,
        TypedCfgPreservation.StateRel source tokens target ->
          exists targetAfter,
            TypedCfg.InteractionSemantics.Program.openStep
                cfg entry target =
              .done (.ok (.jump next targetAfter)) /\
            TypedCfgPreservation.StateRel nextSource tokens targetAfter)
    (hReturns : nextSource.returns = source.returns)
    (hNoStop :
      forall targetAfter,
        TypedCfgPreservation.StateRel nextSource tokens targetAfter ->
          policy next targetAfter = false)
    (hTail :
      BoundedExecPreservesUnder result cfg next ctx regular
        nextSource tokens sourceRun tailBudget policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      sourceRun (tailBudget + 1) policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain ⟨targetAfter, hTargetStep, hAfterRel⟩ :=
    hStep target hStateRel
  obtain
      ⟨tailFuel, remaining, targetOutcome, hTailFuel,
        hTargetTailExec, hTailRel⟩ :=
    hTail targetAfter hAfterRel transcript sourceOutcome hSourceExec
  have hTargetHeadExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        [] (.ok (.jump next targetAfter)) := by
    rw [hTargetStep]
    exact Simulation.Interaction.Executes.done _
  have hContinuationExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
          policy cfg tailFuel (.jump next targetAfter))
        transcript (.ok (.stopped remaining targetOutcome)) := by
    simpa [
      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
      hNoStop targetAfter hAfterRel] using hTargetTailExec
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok
      hTargetHeadExec hContinuationExec
  have hTargetExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg (tailFuel + 1) entry target)
        transcript (.ok (.stopped remaining targetOutcome)) := by
    rw [
      TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
    simpa using hCombined
  exact
    ⟨tailFuel + 1, remaining, targetOutcome, by omega, hTargetExec,
      by simpa [hReturns] using hTailRel⟩

theorem sequence
    {headResult tailResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry middle regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState -> Simulation.Interaction EVMException Structured.Outcome}
    {headBudget tailBudget : Nat} {policy : StopPolicy}
    (hHead :
      BoundedExecPreservesUnder headResult cfg entry ctx middle
        source tokens headRun headBudget
        (pushStopJump headResult ctx middle
          source.returns tokens policy))
    (hMiddleNoStop :
      forall {middleSource : RunState} {targetMiddle : EVMState},
        Rel headResult ctx middle source.returns tokens
            (.regular middleSource) (.jump middle targetMiddle) ->
          policy middle targetMiddle = false)
    (hNonregularStops :
      forall {middleSource : RunState} {headMode : Structured.Mode}
          {targetOutcome : TypedCfg.Outcome},
        (headMode = .regular -> False) ->
          Rel headResult ctx middle source.returns tokens
              { state := middleSource, mode := headMode }
              targetOutcome ->
            TargetStoppedBy policy targetOutcome)
    (hTail :
      forall middleSource,
        middleSource.returns = source.returns ->
          FrameFits headResult ctx
            (Structured.Outcome.regular middleSource) ->
          BoundedExecPreservesUnder tailResult cfg middle ctx regular
            middleSource tokens (tailRun middleSource) tailBudget policy) :
    BoundedExecPreservesUnder (headResult.append tailResult)
      cfg entry ctx regular source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      (headBudget + tailBudget) policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    hSourceError |
      ⟨headOutcome, headTranscript, restTranscript,
        hTranscript, hHeadExec, hRestExec⟩
  · rcases hSourceError with ⟨err, hOutcome, _hHeadError⟩
    cases hOutcome
  · subst transcript
    obtain
        ⟨headFuel, headRemaining, targetHead, hHeadFuel,
          hTargetHeadExec, hHeadRel⟩ :=
      hHead target hStateRel headTranscript headOutcome hHeadExec
    rcases headOutcome with ⟨middleSource, headMode⟩
    have hRefines :
        forall next nextState,
          policy next nextState = true ->
            pushStopJump headResult ctx middle
                source.returns tokens policy next nextState = true := by
      intro next nextState hOuter
      simp [pushStopJump, hOuter]
    have finishNonregular
        (hMode : headMode = .regular -> False)
        (hRest :
          Simulation.Interaction.Executes
            (Simulation.Interaction.pure (Error := EVMException)
              { state := middleSource, mode := headMode })
            restTranscript (.ok sourceOutcome)) :
        exists targetFuel remaining targetOutcome,
          targetFuel <= headBudget + tailBudget /\
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg targetFuel entry target)
              (headTranscript ++ restTranscript)
              (.ok (.stopped remaining targetOutcome)) /\
              Rel (headResult.append tailResult) ctx regular
                source.returns tokens sourceOutcome targetOutcome := by
      cases hRest
      have hStopped := hNonregularStops hMode hHeadRel
      have hContinuation :=
        afterOpenStepResultWithPolicy_executes_of_targetStopped
          (cfg := cfg) (fuel := headRemaining) hStopped
      have hCombined :=
        Simulation.Interaction.Executes.bind_ok
          (next :=
            TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
              policy cfg 0)
          hTargetHeadExec hContinuation
      have hTargetExec :
          Simulation.Interaction.Executes
            (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
              policy cfg headFuel entry target)
            headTranscript (.ok (.stopped headRemaining targetHead)) := by
        have hWithZero :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg (headFuel + 0) entry target)
              headTranscript (.ok (.stopped headRemaining targetHead)) := by
          rw [
            TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
              policy
              (pushStopJump headResult ctx middle
                source.returns tokens policy)
              cfg headFuel 0 entry target hRefines]
          simpa using hCombined
        simpa using hWithZero
      exact
        ⟨headFuel, headRemaining, targetHead, by omega,
          by simpa using hTargetExec,
          Rel.change_regular_of_nonregular
            (left := headResult)
            (right := headResult.append tailResult)
            (leftRegular := middle) (rightRegular := regular)
            hMode hHeadRel⟩
    cases headMode with
    | regular =>
        obtain ⟨targetMiddle, rfl, hMiddleStateRel⟩ :=
          TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim hHeadRel.1
        have hReturns : middleSource.returns = source.returns := by
          simpa [ActivationRestored] using hHeadRel.2.2
        obtain
            ⟨tailFuel, tailRemaining, targetFinal, hTailFuel,
              hTargetTailExec, hTailRel⟩ :=
          hTail middleSource hReturns hHeadRel.2.1
            targetMiddle hMiddleStateRel
            restTranscript sourceOutcome hRestExec
        have hTargetTailPadded :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg (headRemaining + tailFuel) middle targetMiddle)
              restTranscript
              (.ok (.stopped
                (tailRemaining + headRemaining) targetFinal)) := by
          rw [show headRemaining + tailFuel =
            tailFuel + headRemaining by omega]
          rw [
            TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_add]
          have hTailContinuation :
              Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithStop
                  policy cfg headRemaining
                  (.stopped tailRemaining targetFinal))
                []
                (.ok (.stopped
                  (tailRemaining + headRemaining) targetFinal)) := by
            exact Simulation.Interaction.Executes.done _
          simpa using
            Simulation.Interaction.Executes.bind_ok
              hTargetTailExec hTailContinuation
        have hContinuationExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                policy cfg tailFuel
                (.stopped headRemaining (.jump middle targetMiddle)))
              restTranscript
              (.ok (.stopped
                (tailRemaining + headRemaining) targetFinal)) := by
          simpa [
            TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop,
            TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
            hMiddleNoStop hHeadRel] using hTargetTailPadded
        have hCombined :=
          Simulation.Interaction.Executes.bind_ok
            (next :=
              TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                policy cfg tailFuel)
            hTargetHeadExec hContinuationExec
        have hTargetExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg (headFuel + tailFuel) entry target)
              (headTranscript ++ restTranscript)
              (.ok (.stopped
                (tailRemaining + headRemaining) targetFinal)) := by
          rw [
            TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
              policy
              (pushStopJump headResult ctx middle
                source.returns tokens policy)
              cfg headFuel tailFuel entry target hRefines]
          exact hCombined
        exact
          ⟨headFuel + tailFuel,
            tailRemaining + headRemaining, targetFinal, by omega,
            hTargetExec,
            by
              simpa [hReturns] using
                (Rel.append_right (left := headResult) hTailRel)⟩
    | brk => exact finishNonregular (by simp) hRestExec
    | cont => exact finishNonregular (by simp) hRestExec
    | leave => exact finishNonregular (by simp) hRestExec
    | halt kind => exact finishNonregular (by simp) hRestExec

theorem ignore_tail_of_no_fallthrough
    {headResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry headRegular resultRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState -> Simulation.Interaction EVMException Structured.Outcome}
    {headBudget : Nat} {policy : StopPolicy}
    (hFallthrough : headResult.fallthrough? = none)
    (hHead :
      BoundedExecPreservesUnder headResult cfg entry ctx headRegular
        source tokens headRun headBudget policy) :
    BoundedExecPreservesUnder headResult cfg entry ctx resultRegular
      source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      headBudget policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    hSourceError |
      ⟨headOutcome, headTranscript, restTranscript,
        hTranscript, hHeadExec, hRestExec⟩
  · rcases hSourceError with ⟨err, hOutcome, _hHeadError⟩
    cases hOutcome
  · subst transcript
    obtain
        ⟨targetFuel, remaining, targetOutcome, hFuel,
          hTargetExec, hHeadRel⟩ :=
      hHead target hStateRel headTranscript headOutcome hHeadExec
    rcases headOutcome with ⟨middleSource, headMode⟩
    have finishNonregular
        (hMode : headMode = .regular -> False)
        (hRest :
          Simulation.Interaction.Executes
            (Simulation.Interaction.pure (Error := EVMException)
              { state := middleSource, mode := headMode })
            restTranscript (.ok sourceOutcome)) :
        exists used remaining targetOutcome,
          used <= headBudget /\
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg used entry target)
              (headTranscript ++ restTranscript)
              (.ok (.stopped remaining targetOutcome)) /\
              Rel headResult ctx resultRegular source.returns tokens
                sourceOutcome targetOutcome := by
      cases hRest
      exact
        ⟨targetFuel, remaining, targetOutcome, hFuel,
          by simpa using hTargetExec,
          Rel.change_regular_of_nonregular
            (left := headResult) (right := headResult)
            (leftRegular := headRegular) (rightRegular := resultRegular)
            hMode hHeadRel⟩
    cases headMode with
    | regular =>
        exact False.elim
          (Rel.not_regular_of_fallthrough_none hFallthrough hHeadRel)
    | brk => exact finishNonregular (by simp) hRestExec
    | cont => exact finishNonregular (by simp) hRestExec
    | leave => exact finishNonregular (by simp) hRestExec
    | halt kind => exact finishNonregular (by simp) hRestExec

/-- Pad every branch-specific target execution to its common source-owned
ceiling. The active stop policy makes the extra fuel observationally inert. -/
theorem uniform
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetBudget : Nat} {policy : StopPolicy}
    (hBounded :
      BoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget policy)
    (hStops :
      forall {sourceOutcome targetOutcome},
        Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome ->
          TargetStoppedBy policy targetOutcome) :
    UniformExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetBudget policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, remaining, targetOutcome, hFuel,
        hTargetExec, hRel⟩ :=
    hBounded target hStateRel transcript sourceOutcome hSourceExec
  let extra := targetBudget - targetFuel
  have hFuelEq : targetFuel + extra = targetBudget := by
    omega
  have hContinue :=
    afterOpenStepResultWithPolicy_executes_of_targetStopped
      (cfg := cfg) (fuel := remaining + extra) (hStops hRel)
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok
      (next :=
        TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
          policy cfg extra)
      hTargetExec hContinue
  have hRefines :
      forall next nextState,
        policy next nextState = true -> policy next nextState = true := by
    intro next nextState hStop
    exact hStop
  have hPadded :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg (targetFuel + extra) entry target)
        transcript
        (.ok (.stopped (remaining + extra) targetOutcome)) := by
    rw [
      TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
        policy policy cfg targetFuel extra entry target hRefines]
    simpa using hCombined
  exact ⟨remaining + extra, targetOutcome, by simpa [hFuelEq] using hPadded,
    hRel⟩

end BoundedExecPreservesUnder

namespace UniformExecPreservesUnder

/-- Universal source success upgrades uniform branch preservation to the
structural open-world relation used by adjacent compiler boundaries. -/
theorem preserves
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {regularExit : RegularExit}
    (hExec :
      UniformExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetFuel policy)
    (hSuccessful : Simulation.Interaction.Successful sourceRun) :
    PreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun targetFuel policy := by
  intro target hStateRel
  apply Simulation.Interaction.Rel.of_successful_executes hSuccessful
  intro transcript sourceOutcome hSourceExec
  obtain ⟨remaining, targetOutcome, hTargetExec, hRel⟩ :=
    hExec target hStateRel transcript sourceOutcome hSourceExec
  exact
    ⟨.ok (.stopped remaining targetOutcome), hTargetExec,
      Simulation.Interaction.ExceptRel.ok hRel⟩

/-- Forget uniformity while retaining the existing execution-indexed API. -/
theorem exec
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    (hExec :
      UniformExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetFuel policy) :
    ExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain ⟨remaining, targetOutcome, hTargetExec, hRel⟩ :=
    hExec target hStateRel transcript sourceOutcome hSourceExec
  exact ⟨targetFuel, remaining, targetOutcome, hTargetExec, hRel⟩

end UniformExecPreservesUnder

namespace ExecPreservesUnder

private theorem continue_refined_zero_executes_of_stopped
    {policy : StopPolicy} {cfg : TypedCfg.Program}
    {remaining : Nat} {target : TypedCfg.Outcome}
    (hStopped : TargetStoppedBy policy target) :
    Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
        policy cfg 0 (.stopped remaining target))
      []
      (.ok (.stopped remaining target)) := by
  cases target with
  | jump label state =>
      change policy label state = true at hStopped
      simpa [
        TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop,
        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
        hStopped] using
        (Simulation.Interaction.Executes.done
          (.ok
            (TypedCfg.Control.Program.RunResult.stopped remaining
              (TypedCfg.Outcome.jump label state))))
  | halt kind state =>
      simpa [
        TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop,
        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop] using
        (Simulation.Interaction.Executes.done
          (.ok
            (TypedCfg.Control.Program.RunResult.stopped remaining
              (TypedCfg.Outcome.halt kind state))))
  | fallthrough state =>
      simp [TargetStoppedBy] at hStopped
  | returnDispatch state =>
      simp [TargetStoppedBy] at hStopped
  | invalid state =>
      simp [TargetStoppedBy] at hStopped

/--
Close an execution stopped by a refined compiler-boundary policy when its
target outcome is also a genuine boundary of the enclosing policy.
-/
theorem close_refined
    {outer inner : StopPolicy} {cfg : TypedCfg.Program}
    {headFuel headRemaining : Nat}
    {entry : Assembly.Label} {target : EVMState}
    {targetOutcome : TypedCfg.Outcome}
    {transcript : Simulation.Interaction.Transcript}
    (hRefines :
      ∀ next nextState,
        outer next nextState = true →
          inner next nextState = true)
    (hHead :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          inner cfg headFuel entry target)
        transcript
        (.ok (.stopped headRemaining targetOutcome)))
    (hStopped : TargetStoppedBy outer targetOutcome) :
    Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
        outer cfg headFuel entry target)
      transcript
      (.ok (.stopped headRemaining targetOutcome)) := by
  have hContinuation :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
          outer cfg 0 (.stopped headRemaining targetOutcome))
        []
        (.ok (.stopped headRemaining targetOutcome)) :=
    continue_refined_zero_executes_of_stopped hStopped
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok hHead hContinuation
  rw [
    ← TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
      outer inner cfg headFuel 0 entry target hRefines] at hCombined
  simpa using hCombined

/--
Forget a fragment-local stop refinement once every related source outcome is a
genuine boundary of the enclosing policy.
-/
theorem close_refined_under
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {outer inner : StopPolicy}
    (hPreserves :
      ExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun inner)
    (hRefines :
      ∀ label state,
        outer label state = true →
          inner label state = true)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          TargetStoppedBy outer targetOutcome) :
    ExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun outer := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, targetRemaining, targetOutcome,
        hTargetExec, hOutcomeRel⟩ :=
    hPreserves target hStateRel transcript sourceOutcome hSourceExec
  exact
    ⟨targetFuel, targetRemaining, targetOutcome,
      close_refined hRefines hTargetExec (hStops hOutcomeRel),
      hOutcomeRel⟩

/--
Resume a refined execution at an internal jump and splice in a successful run
under the enclosing stop policy. Residual fuel from the first segment remains
available after the tail stops.
-/
theorem splice_refined_jump
    {outer inner : StopPolicy} {cfg : TypedCfg.Program}
    {headFuel headRemaining tailFuel tailRemaining : Nat}
    {entry next : Assembly.Label}
    {target nextTarget : EVMState}
    {targetFinal : TypedCfg.Outcome}
    {headTranscript tailTranscript :
      Simulation.Interaction.Transcript}
    (hRefines :
      ∀ label state,
        outer label state = true →
          inner label state = true)
    (hHead :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          inner cfg headFuel entry target)
        headTranscript
        (.ok
          (.stopped headRemaining
            (.jump next nextTarget))))
    (hNoStop : outer next nextTarget = false)
    (hTail :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          outer cfg tailFuel next nextTarget)
        tailTranscript
        (.ok (.stopped tailRemaining targetFinal))) :
    Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
        outer cfg (headFuel + tailFuel) entry target)
      (headTranscript ++ tailTranscript)
      (.ok
        (.stopped (tailRemaining + headRemaining) targetFinal)) := by
  have hTailContinuation :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithStop
          outer cfg headRemaining
          (.stopped tailRemaining targetFinal))
        []
        (.ok
          (.stopped (tailRemaining + headRemaining) targetFinal)) := by
    exact
      Simulation.Interaction.Executes.done
        (.ok
          (TypedCfg.Control.Program.RunResult.stopped
            (tailRemaining + headRemaining) targetFinal))
  have hTailPadded :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          outer cfg (headRemaining + tailFuel) next nextTarget)
        tailTranscript
        (.ok
          (.stopped (tailRemaining + headRemaining) targetFinal)) := by
    rw [show headRemaining + tailFuel =
      tailFuel + headRemaining by omega]
    rw [
      TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_add]
    simpa using
      Simulation.Interaction.Executes.bind_ok hTail hTailContinuation
  have hContinuation :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
          outer cfg tailFuel
          (.stopped headRemaining (.jump next nextTarget)))
        tailTranscript
        (.ok
          (.stopped (tailRemaining + headRemaining) targetFinal)) := by
    simpa [
      TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop,
      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
      hNoStop] using hTailPadded
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok hHead hContinuation
  rw [
    ← TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
      outer inner cfg headFuel tailFuel entry target hRefines] at hCombined
  exact hCombined

/--
Prepend one target step that reaches a non-stopping jump before a successful
execution under the same policy. The head step may carry an open interaction
prefix, as loop conditions and switch scrutinees do.
-/
theorem prepend_step_jump
    {policy : StopPolicy} {cfg : TypedCfg.Program}
    {tailFuel tailRemaining : Nat}
    {entry next : Assembly.Label}
    {target nextTarget : EVMState}
    {targetFinal : TypedCfg.Outcome}
    {headTranscript tailTranscript :
      Simulation.Interaction.Transcript}
    (hHead :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg entry target)
        headTranscript
        (.ok (.jump next nextTarget)))
    (hNoStop : policy next nextTarget = false)
    (hTail :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg tailFuel next nextTarget)
        tailTranscript
        (.ok (.stopped tailRemaining targetFinal))) :
    Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
        policy cfg (tailFuel + 1) entry target)
      (headTranscript ++ tailTranscript)
      (.ok (.stopped tailRemaining targetFinal)) := by
  have hContinuation :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
          policy cfg tailFuel (.jump next nextTarget))
        tailTranscript
        (.ok (.stopped tailRemaining targetFinal)) := by
    simpa [
      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
      hNoStop] using hTail
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  exact
    Simulation.Interaction.Executes.bind_ok hHead hContinuation

theorem change_result_of_required_fallthrough
    {left right : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {policy : StopPolicy} {expected : TypedCfg.Shape}
    (hRequire :
      left.requireFallthrough? expected = some ())
    (hRight :
      right.fallthrough? = some expected)
    (hPreserves :
      ExecPreservesUnder left cfg entry ctx regular
        source tokens sourceRun policy) :
    ExecPreservesUnder right cfg entry ctx regular
      source tokens sourceRun policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨targetFuel, remaining, targetOutcome,
        hTargetExec, hRel⟩ :=
    hPreserves target hStateRel transcript sourceOutcome hSourceExec
  exact
    ⟨targetFuel, remaining, targetOutcome, hTargetExec,
      Rel.change_result_of_required_fallthrough
        hRequire hRight hRel⟩

theorem prepend_closed_jump
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry next regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source nextSource : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {policy : StopPolicy}
    (hStep :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          ∃ targetAfter,
            TypedCfg.InteractionSemantics.Program.openStep
                cfg entry target =
              .done (.ok (.jump next targetAfter)) ∧
            TypedCfgPreservation.StateRel
              nextSource tokens targetAfter)
    (hReturns :
      nextSource.returns = source.returns)
    (hNoStop :
      ∀ targetAfter,
        TypedCfgPreservation.StateRel
            nextSource tokens targetAfter →
          policy next targetAfter = false)
    (hTail :
      ExecPreservesUnder result cfg next ctx regular nextSource tokens
        sourceRun policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      sourceRun policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain ⟨targetAfter, hTargetStep, hAfterRel⟩ :=
    hStep target hStateRel
  obtain
      ⟨tailFuel, remaining, targetOutcome,
        hTargetTailExec, hTailRel⟩ :=
    hTail targetAfter hAfterRel transcript sourceOutcome hSourceExec
  have hTargetHeadExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg entry target)
        []
        (.ok (.jump next targetAfter)) := by
    rw [hTargetStep]
    exact
      Simulation.Interaction.Executes.done
        (.ok (TypedCfg.Outcome.jump next targetAfter))
  have hContinue :=
    hNoStop targetAfter hAfterRel
  have hContinuationExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
          policy cfg tailFuel (.jump next targetAfter))
        transcript
        (.ok
          (TypedCfg.Control.Program.RunResult.stopped
            remaining targetOutcome)) := by
    simpa [
      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
      hContinue] using hTargetTailExec
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok
      hTargetHeadExec hContinuationExec
  have hTargetExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg (tailFuel + 1) entry target)
        ([] ++ transcript)
        (.ok
          (TypedCfg.Control.Program.RunResult.stopped
            remaining targetOutcome)) := by
    rw [
      TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
    exact hCombined
  exact
    ⟨tailFuel + 1, remaining, targetOutcome,
      by simpa using hTargetExec,
      by simpa [hReturns] using hTailRel⟩

theorem sequence
    {headResult tailResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry middle regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState →
        Simulation.Interaction EVMException Structured.Outcome}
    {policy : StopPolicy}
    (hHead :
      ExecPreservesUnder headResult cfg entry ctx middle
        source tokens headRun
        (pushStopJump headResult ctx middle
          source.returns tokens policy))
    (hMiddleNoStop :
      ∀ {middleSource : RunState} {targetMiddle : EVMState},
        Rel headResult ctx middle source.returns tokens
            (.regular middleSource) (.jump middle targetMiddle) →
          policy middle targetMiddle = false)
    (hNonregularStops :
      ∀ {middleSource : RunState} {headMode : Structured.Mode}
          {targetOutcome : TypedCfg.Outcome},
        headMode ≠ .regular →
          Rel headResult ctx middle source.returns tokens
              { state := middleSource, mode := headMode }
              targetOutcome →
            TargetStoppedBy policy targetOutcome)
    (hTail :
      ∀ middleSource,
        middleSource.returns = source.returns →
          FrameFits headResult ctx
            (Structured.Outcome.regular middleSource) →
          ExecPreservesUnder tailResult cfg middle ctx regular
            middleSource tokens (tailRun middleSource) policy) :
    ExecPreservesUnder (headResult.append tailResult)
      cfg entry ctx regular source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  rcases
      Simulation.Interaction.Executes.bind_cases hSourceExec with
    hSourceError |
      ⟨headOutcome, headTranscript, restTranscript,
        hTranscript, hHeadExec, hRestExec⟩
  · rcases hSourceError with ⟨err, hOutcome, _hHeadError⟩
    cases hOutcome
  · subst transcript
    obtain
        ⟨headFuel, headRemaining, targetHead,
          hTargetHeadExec, hHeadRel⟩ :=
      hHead target hStateRel headTranscript headOutcome hHeadExec
    rcases headOutcome with ⟨middleSource, headMode⟩
    have hRefines :
        ∀ next nextState,
          policy next nextState = true →
            pushStopJump headResult ctx middle
                source.returns tokens policy next nextState =
              true := by
      intro next nextState hOuter
      simp [pushStopJump, hOuter]
    cases headMode with
    | regular =>
        obtain ⟨targetMiddle, rfl, hMiddleStateRel⟩ :=
          TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
            hHeadRel.1
        have hReturns :
            middleSource.returns = source.returns := by
          simpa [ActivationRestored] using hHeadRel.2.2
        obtain
            ⟨tailFuel, tailRemaining, targetFinal,
              hTargetTailExec, hTailRel⟩ :=
          hTail middleSource hReturns hHeadRel.2.1
            targetMiddle hMiddleStateRel
            restTranscript sourceOutcome hRestExec
        have hTargetTailPadded :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg (headRemaining + tailFuel)
                middle targetMiddle)
              restTranscript
              (.ok
                (.stopped
                  (tailRemaining + headRemaining) targetFinal)) := by
          rw [show headRemaining + tailFuel =
            tailFuel + headRemaining by omega]
          rw [
            TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_add]
          have hTailContinuation :
              Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithStop
                  policy cfg headRemaining
                  (.stopped tailRemaining targetFinal))
                []
                (.ok
                  (.stopped
                    (tailRemaining + headRemaining) targetFinal)) := by
            exact
              Simulation.Interaction.Executes.done
                (.ok
                  (TypedCfg.Control.Program.RunResult.stopped
                    (tailRemaining + headRemaining) targetFinal))
          simpa using
            Simulation.Interaction.Executes.bind_ok
              hTargetTailExec hTailContinuation
        have hContinuationExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                policy cfg tailFuel
                (.stopped headRemaining
                  (.jump middle targetMiddle)))
              restTranscript
              (.ok
                (.stopped
                  (tailRemaining + headRemaining) targetFinal)) := by
          simpa [
            TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop,
            TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
            hMiddleNoStop hHeadRel] using hTargetTailPadded
        have hCombined :
            Simulation.Interaction.Executes
              (Simulation.Interaction.bind
                (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                  (pushStopJump headResult ctx middle
                    source.returns tokens policy)
                  cfg headFuel entry target)
                (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                  policy cfg tailFuel))
              (headTranscript ++ restTranscript)
              (.ok
                (.stopped
                  (tailRemaining + headRemaining) targetFinal)) :=
          Simulation.Interaction.Executes.bind_ok
            hTargetHeadExec hContinuationExec
        have hTargetExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg (headFuel + tailFuel) entry target)
              (headTranscript ++ restTranscript)
              (.ok
                (.stopped
                  (tailRemaining + headRemaining) targetFinal)) := by
          rw [
            TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
              policy
              (pushStopJump headResult ctx middle
                source.returns tokens policy)
              cfg headFuel tailFuel entry target hRefines]
          exact hCombined
        exact
          ⟨headFuel + tailFuel,
            tailRemaining + headRemaining, targetFinal,
            hTargetExec,
            by
              simpa [hReturns] using
                (Rel.append_right
                  (left := headResult) hTailRel)⟩
    | brk =>
        cases hRestExec
        have hStopped :=
          hNonregularStops (by simp) hHeadRel
        have hContinuationExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                policy cfg 0
                (.stopped headRemaining targetHead))
              []
              (.ok (.stopped headRemaining targetHead)) :=
          continue_refined_zero_executes_of_stopped hStopped
        have hCombined :=
          Simulation.Interaction.Executes.bind_ok
            hTargetHeadExec hContinuationExec
        rw [
          ← TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
            policy
            (pushStopJump headResult ctx middle
              source.returns tokens policy)
            cfg headFuel 0 entry target hRefines] at hCombined
        exact
          ⟨headFuel, headRemaining, targetHead,
            by simpa using hCombined,
            Rel.change_regular_of_nonregular
              (left := headResult)
              (right := headResult.append tailResult)
              (leftRegular := middle) (rightRegular := regular)
              (by simp) hHeadRel⟩
    | cont =>
        cases hRestExec
        have hStopped :=
          hNonregularStops (by simp) hHeadRel
        have hContinuationExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                policy cfg 0
                (.stopped headRemaining targetHead))
              []
              (.ok (.stopped headRemaining targetHead)) :=
          continue_refined_zero_executes_of_stopped hStopped
        have hCombined :=
          Simulation.Interaction.Executes.bind_ok
            hTargetHeadExec hContinuationExec
        rw [
          ← TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
            policy
            (pushStopJump headResult ctx middle
              source.returns tokens policy)
            cfg headFuel 0 entry target hRefines] at hCombined
        exact
          ⟨headFuel, headRemaining, targetHead,
            by simpa using hCombined,
            Rel.change_regular_of_nonregular
              (left := headResult)
              (right := headResult.append tailResult)
              (leftRegular := middle) (rightRegular := regular)
              (by simp) hHeadRel⟩
    | leave =>
        cases hRestExec
        have hStopped :=
          hNonregularStops (by simp) hHeadRel
        have hContinuationExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                policy cfg 0
                (.stopped headRemaining targetHead))
              []
              (.ok (.stopped headRemaining targetHead)) :=
          continue_refined_zero_executes_of_stopped hStopped
        have hCombined :=
          Simulation.Interaction.Executes.bind_ok
            hTargetHeadExec hContinuationExec
        rw [
          ← TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
            policy
            (pushStopJump headResult ctx middle
              source.returns tokens policy)
            cfg headFuel 0 entry target hRefines] at hCombined
        exact
          ⟨headFuel, headRemaining, targetHead,
            by simpa using hCombined,
            Rel.change_regular_of_nonregular
              (left := headResult)
              (right := headResult.append tailResult)
              (leftRegular := middle) (rightRegular := regular)
              (by simp) hHeadRel⟩
    | halt kind =>
        cases hRestExec
        have hStopped :=
          hNonregularStops (by simp) hHeadRel
        have hContinuationExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
                policy cfg 0
                (.stopped headRemaining targetHead))
              []
              (.ok (.stopped headRemaining targetHead)) :=
          continue_refined_zero_executes_of_stopped hStopped
        have hCombined :=
          Simulation.Interaction.Executes.bind_ok
            hTargetHeadExec hContinuationExec
        rw [
          ← TypedCfg.InteractionSemantics.Program.openRunNResultWithRefinedStop_add
            policy
            (pushStopJump headResult ctx middle
              source.returns tokens policy)
            cfg headFuel 0 entry target hRefines] at hCombined
        exact
          ⟨headFuel, headRemaining, targetHead,
            by simpa using hCombined,
            Rel.change_regular_of_nonregular
              (left := headResult)
              (right := headResult.append tailResult)
              (leftRegular := middle) (rightRegular := regular)
              (by simp) hHeadRel⟩

theorem ignore_tail_of_no_fallthrough
    {headResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry headRegular resultRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState →
        Simulation.Interaction EVMException Structured.Outcome}
    {policy : StopPolicy}
    (hFallthrough : headResult.fallthrough? = none)
    (hHead :
      ExecPreservesUnder headResult cfg entry ctx headRegular
        source tokens headRun policy) :
    ExecPreservesUnder headResult cfg entry ctx resultRegular
      source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  rcases
      Simulation.Interaction.Executes.bind_cases hSourceExec with
    hSourceError |
      ⟨headOutcome, headTranscript, restTranscript,
        hTranscript, hHeadExec, hRestExec⟩
  · rcases hSourceError with ⟨err, hOutcome, _hHeadError⟩
    cases hOutcome
  · subst transcript
    obtain
        ⟨targetFuel, remaining, targetOutcome,
          hTargetExec, hHeadRel⟩ :=
      hHead target hStateRel headTranscript headOutcome hHeadExec
    rcases headOutcome with ⟨middleSource, headMode⟩
    cases headMode with
    | regular =>
        exact False.elim
          (Rel.not_regular_of_fallthrough_none
            hFallthrough hHeadRel)
    | brk =>
        cases hRestExec
        exact
          ⟨targetFuel, remaining, targetOutcome,
            by simpa using hTargetExec,
            Rel.change_regular_of_nonregular
              (left := headResult) (right := headResult)
              (leftRegular := headRegular)
              (rightRegular := resultRegular)
              (by simp) hHeadRel⟩
    | cont =>
        cases hRestExec
        exact
          ⟨targetFuel, remaining, targetOutcome,
            by simpa using hTargetExec,
            Rel.change_regular_of_nonregular
              (left := headResult) (right := headResult)
              (leftRegular := headRegular)
              (rightRegular := resultRegular)
              (by simp) hHeadRel⟩
    | leave =>
        cases hRestExec
        exact
          ⟨targetFuel, remaining, targetOutcome,
            by simpa using hTargetExec,
            Rel.change_regular_of_nonregular
              (left := headResult) (right := headResult)
              (leftRegular := headRegular)
              (rightRegular := resultRegular)
              (by simp) hHeadRel⟩
    | halt kind =>
        cases hRestExec
        exact
          ⟨targetFuel, remaining, targetOutcome,
            by simpa using hTargetExec,
            Rel.change_regular_of_nonregular
              (left := headResult) (right := headResult)
              (leftRegular := headRegular)
              (rightRegular := resultRegular)
              (by simp) hHeadRel⟩

end ExecPreservesUnder

namespace PreservesWithin

/--
Retarget a preserved fragment to an enclosing compiler result that has the
same required source fallthrough shape. This changes only the outcome-indexed
relation; the target runner and enclosing stop policy remain unchanged.
-/
theorem change_result_of_required_fallthrough
    {left right boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry fragmentRegular boundaryRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat}
    {expected : TypedCfg.Shape}
    (hRequire :
      left.requireFallthrough? expected = some ())
    (hRight :
      right.fallthrough? = some expected)
    (hPreserves :
      PreservesWithin left boundaryResult cfg entry ctx
        fragmentRegular boundaryRegular .stop source tokens
        sourceRun targetFuel) :
    PreservesWithin right boundaryResult cfg entry ctx
      fragmentRegular boundaryRegular .stop source tokens
      sourceRun targetFuel := by
  intro target hStateRel
  apply Simulation.Interaction.Rel.mono
    (hPreserves target hStateRel)
  intro sourceDone targetDone hDone
  exact
    SegmentDoneRel.change_result_of_required_fallthrough
      hRequire hRight hDone

/--
Once a fragment has stopped at the enclosing semantic boundary, extra target
fuel cannot expose another block or interaction.
-/
theorem pad_stop
    {fragmentResult boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry fragmentRegular boundaryRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat}
    (hPreserves :
      PreservesWithin fragmentResult boundaryResult cfg entry ctx
        fragmentRegular boundaryRegular .stop source tokens
        sourceRun targetFuel)
    (extra : Nat) :
    PreservesWithin fragmentResult boundaryResult cfg entry ctx
      fragmentRegular boundaryRegular .stop source tokens
      sourceRun (targetFuel + extra) := by
  intro target hStateRel
  have hRel := hPreserves target hStateRel
  have hStopped :
      Simulation.Interaction.AllDone
        TypedCfg.InteractionSemantics.Program.RunResultStopped
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          (segmentStopJump fragmentResult boundaryResult ctx
            fragmentRegular boundaryRegular source.returns tokens .stop)
          cfg targetFuel entry target) := by
    apply Simulation.Interaction.Rel.allDone_right hRel
    intro sourceDone targetDone hDone
    cases hDone with
    | error _ =>
        trivial
    | @ok sourceResult targetResult hRun =>
        cases targetResult with
        | exhausted label state =>
            exact False.elim hRun
        | stopped remaining outcome =>
            trivial
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_add_eq_map_addFuel_of_allStopped
      (stopJump :=
        segmentStopJump fragmentResult boundaryResult ctx
          fragmentRegular boundaryRegular source.returns tokens .stop)
      (program := cfg) (fuel := targetFuel) (extra := extra)
      (label := entry) (state := target) hStopped]
  have hMapped :
      Simulation.Interaction.Rel
        (SegmentDoneRel fragmentResult ctx fragmentRegular
          source.returns tokens .stop)
        (Simulation.Interaction.bind
          sourceRun Simulation.Interaction.pure)
        (Simulation.Interaction.map
          (TypedCfg.InteractionSemantics.Program.addFuelToRunResult extra)
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            (segmentStopJump fragmentResult boundaryResult ctx
              fragmentRegular boundaryRegular source.returns tokens .stop)
            cfg targetFuel entry target)) := by
    apply Simulation.Interaction.Rel.bind_custom hRel
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
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError =>
            cases hDone
        | ok targetResult =>
            exact
              Simulation.Interaction.Rel.done
                (SegmentDoneRel.addFuelToRunResult
                  extra hDone)
  simpa [
    Simulation.Interaction.bind_pure,
    Simulation.Interaction.map] using hMapped

/--
Compose two adjacent Structured fragments under one enclosing stop policy.

The head runner stops at either the enclosing boundary or its generated middle
label. The refined-stop splice resumes only the middle-label branch, carrying
the head's residual fuel into the tail. Every nonregular head outcome remains
stopped and bypasses the tail.
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
    (hMiddleNoStop :
      ∀ targetMiddle,
        stopJump boundaryResult ctx boundaryRegular
            source.returns tokens middle targetMiddle =
          false)
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
  apply
    PreservesUnder.sequence
      (policy :=
        stopJump boundaryResult ctx boundaryRegular
          source.returns tokens)
      hHead hMiddleNoStop
  · intro middleSource headMode targetOutcome hMode hRel
    have hBoundaryRel :
        Rel boundaryResult ctx boundaryRegular
          source.returns tokens
          { state := middleSource, mode := headMode }
          targetOutcome :=
      Rel.change_regular_of_nonregular
        (left := headResult)
        (right := boundaryResult)
        (leftRegular := middle)
        (rightRegular := boundaryRegular)
        hMode hRel
    exact targetStopped_of_rel hBoundaryRel
  · intro middleSource hReturns
    simpa [PreservesWithin, segmentStopJump, hReturns] using
      hTail middleSource hReturns

/--
A compiler fragment with no fallthrough cannot produce a regular source
outcome. Consequently an enclosing statement-list tail is unreachable, and
binding that tail onto the source interaction leaves preservation unchanged.
-/
theorem ignore_tail_of_no_fallthrough
    {headResult boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry headRegular boundaryRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {headRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {tailRun :
      RunState →
        Simulation.Interaction EVMException Structured.Outcome}
    {headFuel : Nat}
    (hFallthrough : headResult.fallthrough? = none)
    (hHead :
      PreservesWithin headResult boundaryResult cfg entry ctx
        headRegular boundaryRegular .stop source tokens
        headRun headFuel) :
    PreservesWithin headResult boundaryResult cfg entry ctx
      boundaryRegular boundaryRegular .stop source tokens
      (Simulation.Interaction.bind headRun
        (fun outcome =>
          match outcome.mode with
          | .regular => tailRun outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome))
      headFuel := by
  intro target hStateRel
  have hHeadRel := hHead target hStateRel
  have hLifted :
      Simulation.Interaction.Rel
        (SegmentDoneRel headResult ctx boundaryRegular
          source.returns tokens .stop)
        (Simulation.Interaction.bind headRun
          (fun outcome =>
            match outcome.mode with
            | .regular => tailRun outcome.state
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure outcome))
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            (stopJump boundaryResult ctx boundaryRegular
              source.returns tokens)
            cfg headFuel entry target)
          Simulation.Interaction.pure) := by
    apply Simulation.Interaction.Rel.bind_custom hHeadRel
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
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError =>
            cases hDone
        | ok targetResult =>
            cases hDone with
            | ok hRun =>
                rcases sourceOutcome with ⟨middleSource, sourceMode⟩
                cases sourceMode with
                | regular =>
                    cases targetResult with
                    | exhausted label targetMiddle =>
                        exact False.elim hRun
                    | stopped _remaining targetOutcome =>
                        exact False.elim
                          (Rel.not_regular_of_fallthrough_none
                            hFallthrough hRun)
                | brk | cont | leave | halt kind =>
                    cases targetResult with
                    | exhausted label targetMiddle =>
                        exact False.elim hRun
                    | stopped _remaining targetOutcome =>
                        change
                          Rel headResult ctx headRegular
                            source.returns tokens
                            _ targetOutcome
                          at hRun
                        have hFinalRel :=
                          Rel.change_regular_of_nonregular
                            (left := headResult)
                            (right := headResult)
                            (leftRegular := headRegular)
                            (rightRegular := boundaryRegular)
                            (by simp) hRun
                        exact
                          Simulation.Interaction.Rel.done
                            (Simulation.Interaction.ExceptRel.ok hFinalRel)
  simpa [Simulation.Interaction.bind_pure] using hLifted

end PreservesWithin

theorem afterOpenStepResultWithStop_rel
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {ctx : TypedCfgCompiler.Context} {regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : Structured.Outcome}
    {target : TypedCfg.Outcome}
    {fuel : Nat}
    (hRel : Rel result ctx regular returns tokens source target) :
    Simulation.Interaction.Rel
      (DoneRel result ctx regular returns tokens)
      (Simulation.Interaction.pure source)
      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
        (stopJump result ctx regular returns tokens) cfg fuel target) := by
  exact
    afterOpenStepResultWithStop_of_targetStopped hRel
      (targetStopped_of_rel hRel)

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
        (stopJump result ctx regular returns tokens) cfg 0 target) :=
  afterOpenStepResultWithStop_rel hRel

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
      | stopped remaining outcome =>
          trivial

namespace PreservesWithin

/--
Monotone form of `pad_stop`, convenient when branch proofs provide only a
common upper bound.
-/
theorem pad_stop_to
    {fragmentResult boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry fragmentRegular boundaryRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel largerFuel : Nat}
    (hPreserves :
      PreservesWithin fragmentResult boundaryResult cfg entry ctx
        fragmentRegular boundaryRegular .stop source tokens
        sourceRun targetFuel)
    (hFuel : targetFuel ≤ largerFuel) :
    PreservesWithin fragmentResult boundaryResult cfg entry ctx
      fragmentRegular boundaryRegular .stop source tokens
      sourceRun largerFuel := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  exact pad_stop hPreserves extra

/--
Prepend one compiler-generated closed jump to an already-preserved fragment.
The jump may update the source-visible state, but it must preserve the active
return frame and must not itself satisfy the enclosing stop policy.
-/
theorem prepend_closed_jump
    {fragmentResult boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry next fragmentRegular boundaryRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source nextSource : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {regularExit : RegularExit} {targetFuel : Nat}
    (hStep :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          ∃ targetAfter,
            TypedCfg.InteractionSemantics.Program.openStep
                cfg entry target =
              .done (.ok (.jump next targetAfter)) ∧
            TypedCfgPreservation.StateRel
              nextSource tokens targetAfter)
    (hReturns :
      nextSource.returns = source.returns)
    (hNoStop :
      ∀ targetAfter,
        TypedCfgPreservation.StateRel
            nextSource tokens targetAfter →
          segmentStopJump fragmentResult boundaryResult ctx
              fragmentRegular boundaryRegular source.returns tokens
              regularExit next targetAfter =
            false)
    (hTail :
      PreservesWithin fragmentResult boundaryResult cfg next ctx
        fragmentRegular boundaryRegular regularExit nextSource tokens
        sourceRun targetFuel) :
    PreservesWithin fragmentResult boundaryResult cfg entry ctx
      fragmentRegular boundaryRegular regularExit source tokens
      sourceRun (targetFuel + 1) := by
  intro target hStateRel
  obtain ⟨targetAfter, hTargetStep, hAfterRel⟩ :=
    hStep target hStateRel
  rw [
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind,
    hTargetStep]
  simp only [Simulation.Interaction.bind_done_ok]
  have hContinue := hNoStop targetAfter hAfterRel
  simp only [
    TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
    hContinue, if_false]
  simpa [hReturns] using hTail targetAfter hAfterRel

/--
Lift one pass-owned TypedCfg step into the canonical boundary-aware runner.

Only regular exits need a caller-supplied policy: every nonregular outcome can
be retargeted to the enclosing continuation relation because its frame shape
is owned by the compiler context rather than the fragment fallthrough.
-/
theorem of_openStep
    {fragmentResult boundaryResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry fragmentRegular boundaryRegular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {regularExit : RegularExit}
    (hStep :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          Simulation.Interaction.Rel
            (OutcomeDoneRel fragmentResult ctx fragmentRegular
              source.returns tokens)
            sourceRun
            (TypedCfg.InteractionSemantics.Program.openStep
              cfg entry target))
    (hRegularPolicy :
      ∀ {final : RunState} {targetState : EVMState},
        Rel fragmentResult ctx fragmentRegular
            source.returns tokens
            (Structured.Outcome.regular final)
            (.jump fragmentRegular targetState) →
          stopJump boundaryResult ctx boundaryRegular
              source.returns tokens fragmentRegular targetState =
            match regularExit with
            | .stop => true
            | .resume => false) :
    PreservesWithin fragmentResult boundaryResult cfg entry ctx
      fragmentRegular boundaryRegular regularExit source tokens
      sourceRun 1 := by
  intro target hStateRel
  rw [show 1 = 0 + 1 by rfl,
    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
  have hLifted :
      Simulation.Interaction.Rel
        (SegmentDoneRel fragmentResult ctx fragmentRegular
          source.returns tokens regularExit)
        (Simulation.Interaction.bind sourceRun
          Simulation.Interaction.pure)
        (Simulation.Interaction.bind
          (TypedCfg.InteractionSemantics.Program.openStep
            cfg entry target)
          (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
            (segmentStopJump fragmentResult boundaryResult ctx
              fragmentRegular boundaryRegular source.returns tokens
              regularExit)
            cfg 0)) := by
    apply Simulation.Interaction.Rel.bind_custom
      (hStep target hStateRel)
    intro sourceDone targetDone hDone
    cases sourceDone with
    | error sourceError =>
        cases targetDone with
        | error targetError =>
            exact
              Simulation.Interaction.Rel.done
                (Simulation.Interaction.ExceptRel.error trivial)
        | ok targetOutcome =>
            cases hDone
    | ok sourceOutcome =>
        cases targetDone with
        | error targetError =>
            cases hDone
        | ok targetOutcome =>
            cases hDone with
            | ok hOutcome =>
                rcases sourceOutcome with ⟨final, sourceMode⟩
                have hNonregular
                    (hMode : sourceMode ≠ .regular) :
                    Simulation.Interaction.Rel
                      (SegmentDoneRel fragmentResult ctx fragmentRegular
                        source.returns tokens regularExit)
                      (Simulation.Interaction.pure
                        { state := final, mode := sourceMode })
                      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
                        (segmentStopJump fragmentResult boundaryResult ctx
                          fragmentRegular boundaryRegular source.returns tokens
                          regularExit)
                        cfg 0 targetOutcome) := by
                  have hBoundary :
                      Rel boundaryResult ctx boundaryRegular
                        source.returns tokens
                        { state := final, mode := sourceMode }
                        targetOutcome :=
                    Rel.change_regular_of_nonregular
                      (left := fragmentResult)
                      (right := boundaryResult)
                      (leftRegular := fragmentRegular)
                      (rightRegular := boundaryRegular)
                      hMode hOutcome
                  have hStopped := targetStopped_of_rel hBoundary
                  cases targetOutcome with
                  | jump label targetState =>
                      change
                        stopJump boundaryResult ctx boundaryRegular
                          source.returns tokens label targetState = true
                        at hStopped
                      have hSegmentStop :
                          segmentStopJump fragmentResult boundaryResult ctx
                              fragmentRegular boundaryRegular
                              source.returns tokens regularExit
                              label targetState =
                            true := by
                        cases regularExit <;>
                          simp [segmentStopJump, pushStopJump, hStopped]
                      have hSegment :
                          SegmentRunRel fragmentResult ctx fragmentRegular
                            source.returns tokens regularExit
                            { state := final, mode := sourceMode }
                            (.stopped 0 (.jump label targetState)) := by
                        simpa [SegmentRunRel] using hOutcome
                      simp only [
                        TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                        hSegmentStop, if_true]
                      exact
                        Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok hSegment)
                  | halt kind targetState =>
                      have hSegment :
                          SegmentRunRel fragmentResult ctx fragmentRegular
                            source.returns tokens regularExit
                            { state := final, mode := sourceMode }
                            (.stopped 0 (.halt kind targetState)) := by
                        simpa [SegmentRunRel] using hOutcome
                      exact
                        Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok hSegment)
                  | fallthrough targetState
                  | returnDispatch targetState
                  | invalid targetState =>
                      exact False.elim hStopped
                cases sourceMode with
                | regular =>
                    obtain ⟨targetState, rfl, _hState⟩ :=
                      TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
                        hOutcome.1
                    have hOutcome' :
                        Rel fragmentResult ctx fragmentRegular
                          source.returns tokens
                          (Structured.Outcome.regular final)
                          (.jump fragmentRegular targetState) := by
                      simpa [
                        TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                        using hOutcome
                    have hPolicy := hRegularPolicy hOutcome'
                    have hFragmentStopped :=
                      targetStopped_of_rel hOutcome'
                    change
                      stopJump fragmentResult ctx fragmentRegular
                        source.returns tokens fragmentRegular targetState =
                          true
                      at hFragmentStopped
                    have hSegmentStop :
                        segmentStopJump fragmentResult boundaryResult ctx
                            fragmentRegular boundaryRegular
                            source.returns tokens regularExit
                            fragmentRegular targetState =
                          true := by
                      cases regularExit with
                      | stop =>
                          simpa [segmentStopJump] using hPolicy
                      | resume =>
                          simp [
                            segmentStopJump, pushStopJump,
                            hPolicy, hFragmentStopped]
                    have hSegment :
                        SegmentRunRel fragmentResult ctx fragmentRegular
                          source.returns tokens regularExit
                          (Structured.Outcome.regular final)
                          (.stopped 0
                            (.jump fragmentRegular targetState)) := by
                      simpa [SegmentRunRel] using hOutcome'
                    simp only [
                      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext,
                      hSegmentStop, if_true]
                    exact
                      Simulation.Interaction.Rel.done
                        (Simulation.Interaction.ExceptRel.ok hSegment)
                | brk | cont | leave | halt kind =>
                    exact hNonregular (by simp)
  simpa [Simulation.Interaction.bind_pure] using hLifted

end PreservesWithin

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
theorem openRun_code_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit : OpenOutcome.RegularExit}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        OpenOutcome.Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          OpenOutcome.TargetStoppedBy policy targetOutcome) :
    OpenOutcome.PreservesUnder result cfg entry ctx regular regularExit
      source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceFuel (.code code) source)
      1 policy := by
  apply OpenOutcome.PreservesUnder.of_openStep
  · intro target hStateRel
    exact
      openStep_code_of_compileStmtFuel?
        (sourceProgram := sourceProgram)
        (sourceFuel := sourceFuel)
        hCompile hBlocks hFits hStateRel
  · exact hStops

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
  apply OpenOutcome.PreservesWithin.of_openStep
  · intro target hStateRel
    exact
      openStep_code_of_compileStmtFuel?
        (sourceProgram := sourceProgram)
        (sourceFuel := sourceFuel)
        hCompile hBlocks hFits hStateRel
  · exact hRegularPolicy

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
An empty compiled statement list preserves under any active policy that accepts
its related regular jump.
-/
theorem openRun_nil_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {regularExit : OpenOutcome.RegularExit}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          [] ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        OpenOutcome.Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          OpenOutcome.TargetStoppedBy policy targetOutcome) :
    OpenOutcome.PreservesUnder result cfg entry ctx regular regularExit
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := [] } source)
      1 policy := by
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
  apply OpenOutcome.PreservesUnder.of_openStep
  · intro target hStateRel
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
    rw [hTargetRun]
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
    have hDone :
        Simulation.Interaction.Rel
          (OpenOutcome.OutcomeDoneRel
            { blocks := [generated]
              next := supply
              calls := []
              fallthrough? := some input }
            ctx regular source.returns tokens)
          (Simulation.Interaction.pure
            (Structured.Outcome.regular source))
          (Simulation.Interaction.pure
            (TypedCfg.Outcome.jump regular target)) :=
      Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.ok hRelated)
    simpa [
      InteractionSemantics.Block.openRun,
      EffectSemantics.Control.Block.run,
      Simulation.Interaction.pure] using hDone
  · exact hStops

theorem openRun_nil_exec_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          [] ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        OpenOutcome.Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          OpenOutcome.TargetStoppedBy policy targetOutcome) :
    OpenOutcome.ExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := [] } source)
      policy :=
  OpenOutcome.PreservesUnder.exec
    (openRun_nil_under_of_compileStmtListFuel?
      (regularExit := .stop)
      hCompile hBlocks hFits hStops)

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
          (TypedCfg.Control.Program.RunResult.stopped 0
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
          (TypedCfg.Control.Program.RunResult.stopped 0
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
          (TypedCfg.Control.Program.RunResult.stopped 0
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
Statement-form-independent nonempty list composition under an arbitrary active
policy. The head alone receives the generated middle boundary; the tail keeps
the original policy.
-/
theorem openRun_cons_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel headTargetFuel tailTargetFuel : Nat}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {policy : OpenOutcome.StopPolicy}
    {regularExit : OpenOutcome.RegularExit}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hMiddleNoStop :
      ∀ targetMiddle,
        policy (TypedCfgCompiler.restLabel supply) targetMiddle =
          false)
    (hNonregularStops :
      OpenOutcome.StopPolicy.StopsNonregular
        policy ctx source.returns tokens)
    (hHeadNoTail :
      ∀ {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        headResult.fallthrough? = none →
        OpenOutcome.PreservesUnder headResult cfg entry ctx
          (TypedCfgCompiler.restLabel supply) regularExit
          source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          headTargetFuel policy)
    (hHeadWithTail :
      ∀ {headResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        headResult.fallthrough? = some tailInput →
        OpenOutcome.PreservesUnder headResult cfg entry ctx
          (TypedCfgCompiler.restLabel supply) .resume
          source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          headTargetFuel
          (OpenOutcome.pushStopJump headResult ctx
            (TypedCfgCompiler.restLabel supply)
            source.returns tokens policy))
    (hTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape} {middleSource : RunState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        middleSource.returns = source.returns →
        OpenOutcome.PreservesUnder tailResult cfg
          (TypedCfgCompiler.restLabel supply) ctx regular regularExit
          middleSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
          tailTargetFuel policy) :
    OpenOutcome.PreservesUnder result cfg entry ctx regular regularExit
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := stmt :: rest } source)
      (headTargetFuel + tailTargetFuel) policy := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    have hHead :=
      hHeadNoTail hHeadCompile hBlocks hFallthrough
    have hIgnored :=
      OpenOutcome.PreservesUnder.ignore_tail_of_no_fallthrough
        (resultRegular := regular)
        (tailRun := fun middleSource =>
          InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
        hFallthrough hHead
    have hPadded :=
      OpenOutcome.PreservesUnder.pad
        hIgnored tailTargetFuel
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hPadded
  · rcases hWithTail with
      ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    have hHead :=
      hHeadWithTail hHeadCompile hHeadBlocks hFallthrough
    have hComposed :=
      OpenOutcome.PreservesUnder.sequence hHead hMiddleNoStop
        (fun hMode hRel => hNonregularStops hMode hRel)
        (fun middleSource hReturns =>
          hTail hHeadCompile hFallthrough hTailCompile
            hTailBlocks hReturns)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hComposed

/--
Execution-indexed nonempty list composition.

The compiler owner decomposes the generated head/tail artifacts exactly once.
Recursive statement and tail owners derive target fuel only from the successful
source branch being preserved.
-/
theorem openRun_cons_exec_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel : Nat}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hMiddleNoStop :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape}
          {middleSource : RunState} {targetMiddle : EVMState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        OpenOutcome.Rel headResult ctx
            (TypedCfgCompiler.restLabel supply)
            source.returns tokens
            (.regular middleSource)
            (.jump (TypedCfgCompiler.restLabel supply) targetMiddle) →
          policy (TypedCfgCompiler.restLabel supply) targetMiddle =
            false)
    (hNonregularStops :
      OpenOutcome.StopPolicy.StopsNonregular
        policy ctx source.returns tokens)
    (hHeadNoTail :
      ∀ {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        TypedCfgPreservation.CallsInProgram headResult generatedCalls →
        headResult.fallthrough? = none →
        OpenOutcome.ExecPreservesUnder headResult cfg entry ctx
          (TypedCfgCompiler.restLabel supply) source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          policy)
    (hHeadWithTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        TypedCfgPreservation.CallsInProgram headResult generatedCalls →
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        result = headResult.append tailResult →
        OpenOutcome.ExecPreservesUnder headResult cfg entry ctx
          (TypedCfgCompiler.restLabel supply) source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          (OpenOutcome.pushStopJump headResult ctx
            (TypedCfgCompiler.restLabel supply)
            source.returns tokens policy))
    (hTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape} {middleSource : RunState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        TypedCfgPreservation.CallsInProgram tailResult generatedCalls →
        middleSource.returns = source.returns →
        OpenOutcome.FrameFits headResult ctx
          (Structured.Outcome.regular middleSource) →
        result = headResult.append tailResult →
        OpenOutcome.ExecPreservesUnder tailResult cfg
          (TypedCfgCompiler.restLabel supply) ctx regular
          middleSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
          policy) :
    OpenOutcome.ExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := stmt :: rest } source)
      policy := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    have hHead :=
      hHeadNoTail hHeadCompile hBlocks hResultCalls hFallthrough
    have hIgnored :=
      OpenOutcome.ExecPreservesUnder.ignore_tail_of_no_fallthrough
        (resultRegular := regular)
        (tailRun := fun middleSource =>
          InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
        hFallthrough hHead
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hIgnored
  · rcases hWithTail with
      ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    have hHeadCalls :=
      TypedCfgPreservation.CallsInProgram.left_of_append hResultCalls
    have hTailCalls :=
      TypedCfgPreservation.CallsInProgram.right_of_append hResultCalls
    have hHead :=
      hHeadWithTail hHeadCompile hHeadBlocks hHeadCalls hFallthrough
        hTailCompile hTailBlocks rfl
    have hComposed :=
      OpenOutcome.ExecPreservesUnder.sequence hHead
        (fun hRel =>
          hMiddleNoStop hHeadCompile hFallthrough
            hTailCompile hTailBlocks hRel)
        (fun hMode hRel => hNonregularStops hMode hRel)
        (fun middleSource hReturns hFits =>
          hTail hHeadCompile hFallthrough hTailCompile
            hTailBlocks hTailCalls hReturns hFits rfl)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hComposed

/--
Statement-form-independent nonempty list composition.

The head callbacks own the adjacent statement pass theorem; the tail callback
owns recursive list preservation. This theorem alone decomposes the compiler
result, inherits ambient blocks, erases unreachable tails, and adds target
fuel under one outer boundary policy.
-/
theorem openRun_cons_within_of_compileStmtListFuel?
    {compilerFuel sourceFuel headTargetFuel tailTargetFuel : Nat}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (hHeadNoTail :
      ∀ {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        headResult.fallthrough? = none →
        OpenOutcome.PreservesWithin headResult result cfg entry ctx
          (TypedCfgCompiler.restLabel supply) regular .stop
          source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          headTargetFuel)
    (hHeadWithTail :
      ∀ {headResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        headResult.fallthrough? = some tailInput →
        OpenOutcome.PreservesWithin headResult result cfg entry ctx
          (TypedCfgCompiler.restLabel supply) regular .resume
          source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          headTargetFuel)
    (hTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape} {middleSource : RunState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
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
        { stmts := stmt :: rest } source)
      (headTargetFuel + tailTargetFuel) := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    have hHead :=
      hHeadNoTail hHeadCompile hBlocks hFallthrough
    have hIgnored :=
      OpenOutcome.PreservesWithin.ignore_tail_of_no_fallthrough
        (tailRun := fun middleSource =>
          InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
        hFallthrough hHead
    have hPadded :=
      OpenOutcome.PreservesWithin.pad_stop
        hIgnored tailTargetFuel
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hPadded
  · rcases hWithTail with
      ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    have hHead :=
      hHeadWithTail hHeadCompile hHeadBlocks hFallthrough
    have hComposed :=
      OpenOutcome.PreservesWithin.sequence hHead
        (fun targetMiddle =>
          OpenOutcome.stopJump_restLabel_eq_false
            hBefore source.returns tokens targetMiddle)
        (fun middleSource hReturns =>
          hTail hHeadCompile hFallthrough hTailCompile
            hTailBlocks hReturns)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hComposed

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
      apply
        openRun_cons_within_of_compileStmtListFuel?
          hCompile hBlocks hBefore
      · intro headResult hHeadCompile _hHeadBlocks hFallthrough
        obtain ⟨output, _hType, hHeadResult⟩ :=
          TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code
            hHeadCompile
        rw [hHeadResult] at hFallthrough
        cases hFallthrough
      · intro headResult tailInput hHeadCompile hHeadBlocks _hFallthrough
        exact
          Stmt.openRun_code_within_resume_of_compileStmtFuel?
            hHeadCompile hHeadBlocks hFits hBefore
      · exact hTail

end Block

end InteractionControlPreservation
end Structured
end EvmCompiler
