import EvmCompiler.Structured.ObserverActivationBoundary

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace OutcomeSimulation

abbrev Continuations :=
  TypedCfgPreservation.OutcomeSimulation.Continuations

/--
A target outcome has reached one of the Structured fragment's semantic
continuations or has halted.
-/
def TargetBoundary (continuations : Continuations) :
    TypedCfg.Outcome → Prop
  | .jump label _ =>
      label = continuations.regular ∨
        continuations.breakLabel? = some label ∨
        continuations.continueLabel? = some label ∨
        continuations.leaveLabel? = some label
  | .halt _ _ => True
  | .fallthrough _ | .returnDispatch _ | .invalid _ => False

/--
An enclosing observer boundary cannot accept any label allocated at or after
`supply`.
-/
def GeneratedFresh
    (accept : TypedCfg.Outcome → Prop) (supply : LabelSupply) : Prop :=
  ∀ scope tag target,
    supply ≤ scope →
    ¬ accept (.jump (.generated scope tag) target)

/--
A statement boundary may additionally accept its one regular continuation.
Every other label allocated at or after `supply` remains internal.
-/
def GeneratedFreshExcept
    (accept : TypedCfg.Outcome → Prop) (supply : LabelSupply)
    (regular : Assembly.Label) : Prop :=
  ∀ scope tag target,
    supply ≤ scope →
    .generated scope tag ≠ regular →
    ¬ accept (.jump (.generated scope tag) target)

/--
The label was allocated before `supply`, or is a stable named label.
-/
def LabelBeforeSupply
    (label : Assembly.Label) (supply : LabelSupply) : Prop :=
  match label with
  | .named _ => True
  | .generated scope _ => scope < supply

namespace LabelBeforeSupply

theorem generated_ne
    {label : Assembly.Label} {supply scope tag : Nat}
    (hBefore : LabelBeforeSupply label supply)
    (hScope : supply ≤ scope) :
    .generated scope tag ≠ label := by
  cases label with
  | named name =>
      simp
  | generated prior priorTag =>
      simp only [LabelBeforeSupply] at hBefore
      intro hEq
      cases hEq
      omega

end LabelBeforeSupply

/--
Every semantic continuation was allocated before the current compiler supply.
-/
structure ContinuationsBeforeSupply
    (continuations :
      TypedCfgPreservation.OutcomeSimulation.Continuations)
    (supply : LabelSupply) : Prop where
  regular :
    LabelBeforeSupply continuations.regular supply
  breakLabel :
    ∀ label, continuations.breakLabel? = some label →
      LabelBeforeSupply label supply
  continueLabel :
    ∀ label, continuations.continueLabel? = some label →
      LabelBeforeSupply label supply
  leaveLabel :
    ∀ label, continuations.leaveLabel? = some label →
      LabelBeforeSupply label supply

/--
At a statement boundary the regular continuation is either inherited from an
older compiler generation or is the current statement-list tail label.
-/
def RegularAtSupply
    (regular : Assembly.Label) (supply : LabelSupply) : Prop :=
  LabelBeforeSupply regular supply ∨
    regular = TypedCfgCompiler.restLabel supply

namespace RegularAtSupply

theorem before_succ
    {regular : Assembly.Label} {supply : LabelSupply}
    (hRegular : RegularAtSupply regular supply) :
    LabelBeforeSupply regular (supply + 1) := by
  rcases hRegular with hBefore | rfl
  · cases regular with
    | named name =>
        trivial
    | generated scope tag =>
        simp only [LabelBeforeSupply] at hBefore ⊢
        omega
  · simp [LabelBeforeSupply, TypedCfgCompiler.restLabel]

theorem current_generated_ne
    {regular : Assembly.Label} {supply tag : Nat}
    (hRegular : RegularAtSupply regular supply)
    (hTag : tag ≠ 100) :
    .generated supply tag ≠ regular := by
  rcases hRegular with hBefore | rfl
  · exact hBefore.generated_ne (Nat.le_refl supply)
  · simpa [TypedCfgCompiler.restLabel] using hTag

end RegularAtSupply

namespace GeneratedFresh

theorem mono
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    (hFresh : GeneratedFresh accept supply)
    (hSupply : supply ≤ next) :
    GeneratedFresh accept next := by
  intro scope tag target hNext
  exact hFresh scope tag target (Nat.le_trans hSupply hNext)

theorem except
    {accept : TypedCfg.Outcome → Prop} {supply : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFresh accept supply) :
    GeneratedFreshExcept accept supply regular := by
  intro scope tag target hScope _hNe
  exact hFresh scope tag target hScope

theorem jumpAt
    {transcript : Trace}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {next : Assembly.Label}
    {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop} {supply : LabelSupply}
    (hFresh : GeneratedFresh accept supply) :
    GeneratedFreshExcept
      (JumpAt source tokens next shape accept) supply next := by
  intro scope tag target hScope hNe
  simp only [JumpAt]
  push_neg
  exact
    ⟨fun hEq => (hNe hEq).elim,
      hFresh scope tag target hScope⟩

end GeneratedFresh

theorem targetBoundary_generatedFresh
    {continuations : Continuations} {supply : LabelSupply}
    (hBefore :
      ContinuationsBeforeSupply continuations supply) :
    GeneratedFresh (TargetBoundary continuations) supply := by
  intro scope tag target hScope hAccepted
  rcases hAccepted with
    hRegular | hBreak | hContinue | hLeave
  · exact hBefore.regular.generated_ne hScope hRegular
  · exact
      (hBefore.breakLabel _ hBreak).generated_ne hScope rfl
  · exact
      (hBefore.continueLabel _ hContinue).generated_ne hScope rfl
  · exact
      (hBefore.leaveLabel _ hLeave).generated_ne hScope rfl

namespace GeneratedFreshExcept

theorem mono
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hSupply : supply ≤ next) :
    GeneratedFreshExcept accept next regular := by
  intro scope tag target hNext hNe
  exact
    hFresh scope tag target
      (Nat.le_trans hSupply hNext) hNe

theorem reject
    {accept : TypedCfg.Outcome → Prop} {supply scope tag : Nat}
    {regular : Assembly.Label} {target : EVMState}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular) :
    ¬ accept (.jump (.generated scope tag) target) :=
  hFresh scope tag target hScope hNe

theorem toFresh
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hSupply : supply ≤ next)
    (hRegularBefore :
      ∀ scope tag, next ≤ scope →
        .generated scope tag ≠ regular) :
    GeneratedFresh accept next := by
  intro scope tag target hScope
  exact
    hFresh scope tag target
      (Nat.le_trans hSupply hScope)
      (hRegularBefore scope tag hScope)

theorem toFresh_of_regularBefore
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hSupply : supply ≤ next)
    (hRegularBefore : LabelBeforeSupply regular next) :
    GeneratedFresh accept next :=
  toFresh hFresh hSupply
    (fun scope tag hScope =>
      hRegularBefore.generated_ne hScope)

end GeneratedFreshExcept

end OutcomeSimulation
end ObserverAdequacy
end Structured
end EvmCompiler
