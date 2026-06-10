import Mathlib.Data.List.Basic

namespace EvmCompiler
namespace Simulation

/-!
Shared outcome-indexed simulation vocabulary.

Compiler passes use different outcome and state types, but preservation proofs
repeat the same operation: inspect source and target modes, then select the
state relation and cleanup contract owned by that mode. `OutcomeView` separates
that common operation from each layer's concrete outcome representation, while
`OutcomeContract` keeps mode-specific policy at the pass boundary.
-/

structure OutcomeView (Outcome State Mode : Type) where
  state : Outcome → State
  mode : Outcome → Mode

structure OutcomeContract
    (SourceMode TargetMode SourceState TargetState : Type) where
  relate :
    SourceMode → TargetMode → SourceState → TargetState → Prop

structure OutcomePackage (Mode : Type) (Obligation : Mode → Prop) : Prop where
  sound : ∀ mode, Obligation mode

namespace OutcomePackage

def project {Mode : Type} {Obligation : Mode → Prop}
    (package : OutcomePackage Mode Obligation) (mode : Mode) :
    Obligation mode :=
  package.sound mode

def map {Mode : Type} {left right : Mode → Prop}
    (hMap : ∀ mode, left mode → right mode)
    (package : OutcomePackage Mode left) :
    OutcomePackage Mode right where
  sound mode := hMap mode (package.sound mode)

end OutcomePackage

def OutcomeRel
    {SourceOutcome TargetOutcome SourceState TargetState
      SourceMode TargetMode : Type}
    (sourceView : OutcomeView SourceOutcome SourceState SourceMode)
    (targetView : OutcomeView TargetOutcome TargetState TargetMode)
    (contract :
      OutcomeContract SourceMode TargetMode SourceState TargetState)
    (source : SourceOutcome) (target : TargetOutcome) : Prop :=
  contract.relate
    (sourceView.mode source) (targetView.mode target)
    (sourceView.state source) (targetView.state target)

namespace OutcomeRel

theorem intro
    {SourceOutcome TargetOutcome SourceState TargetState
      SourceMode TargetMode : Type}
    {sourceView : OutcomeView SourceOutcome SourceState SourceMode}
    {targetView : OutcomeView TargetOutcome TargetState TargetMode}
    {contract :
      OutcomeContract SourceMode TargetMode SourceState TargetState}
    {source : SourceOutcome} {target : TargetOutcome}
    (hRel :
      contract.relate
        (sourceView.mode source) (targetView.mode target)
        (sourceView.state source) (targetView.state target)) :
    OutcomeRel sourceView targetView contract source target :=
  hRel

theorem elim
    {SourceOutcome TargetOutcome SourceState TargetState
      SourceMode TargetMode : Type}
    {sourceView : OutcomeView SourceOutcome SourceState SourceMode}
    {targetView : OutcomeView TargetOutcome TargetState TargetMode}
    {contract :
      OutcomeContract SourceMode TargetMode SourceState TargetState}
    {source : SourceOutcome} {target : TargetOutcome}
    (hRel : OutcomeRel sourceView targetView contract source target) :
    contract.relate
      (sourceView.mode source) (targetView.mode target)
      (sourceView.state source) (targetView.state target) :=
  hRel

theorem mono
    {SourceOutcome TargetOutcome SourceState TargetState
      SourceMode TargetMode : Type}
    {sourceView : OutcomeView SourceOutcome SourceState SourceMode}
    {targetView : OutcomeView TargetOutcome TargetState TargetMode}
    {left right :
      OutcomeContract SourceMode TargetMode SourceState TargetState}
    (hMono :
      ∀ sourceMode targetMode sourceState targetState,
        left.relate sourceMode targetMode sourceState targetState →
          right.relate sourceMode targetMode sourceState targetState)
    {source : SourceOutcome} {target : TargetOutcome}
    (hRel : OutcomeRel sourceView targetView left source target) :
    OutcomeRel sourceView targetView right source target :=
  hMono _ _ _ _ hRel

end OutcomeRel

end Simulation
end EvmCompiler
