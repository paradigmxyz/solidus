import EvmCompiler.Simulation.Outcome

namespace EvmCompiler
namespace Simulation
namespace ObserverPass

/-!
Stable contracts for one adjacent observer-aware compiler pass.

The compiler equality is the only artifact premise. Initial-state and outcome
relations are source-facing semantic contracts; no generated layout, replay,
call, or emitted-code witness appears in either interface.
-/

structure Interface
    (Source Target SourceInput TargetInput SourceOutcome TargetOutcome : Type)
    where
  lower? : Source → Option Target
  InputRel : SourceInput → TargetInput → Prop
  SourceRuns : Source → SourceInput → SourceOutcome → Prop
  TargetRuns : Target → TargetInput → TargetOutcome → Prop
  OutcomeRel : SourceOutcome → TargetOutcome → Prop

def ForwardPreservation
    {Source Target SourceInput TargetInput SourceOutcome TargetOutcome : Type}
    (pass :
      Interface Source Target SourceInput TargetInput SourceOutcome
        TargetOutcome) : Prop :=
  ∀ {source target sourceInput targetInput sourceOutcome},
    pass.lower? source = some target →
    pass.InputRel sourceInput targetInput →
    pass.SourceRuns source sourceInput sourceOutcome →
    ∃ targetOutcome,
      pass.TargetRuns target targetInput targetOutcome ∧
        pass.OutcomeRel sourceOutcome targetOutcome

def BackwardAdequacy
    {Source Target SourceInput TargetInput SourceOutcome TargetOutcome : Type}
    (pass :
      Interface Source Target SourceInput TargetInput SourceOutcome
        TargetOutcome) : Prop :=
  ∀ {source target sourceInput targetInput targetOutcome},
    pass.lower? source = some target →
    pass.InputRel sourceInput targetInput →
    pass.TargetRuns target targetInput targetOutcome →
    ∃ sourceOutcome,
      pass.SourceRuns source sourceInput sourceOutcome ∧
        pass.OutcomeRel sourceOutcome targetOutcome

structure Verified
    {Source Target SourceInput TargetInput SourceOutcome TargetOutcome : Type}
    (pass :
      Interface Source Target SourceInput TargetInput SourceOutcome
        TargetOutcome) : Prop where
  forward : ForwardPreservation pass
  backward : BackwardAdequacy pass

end ObserverPass
end Simulation
end EvmCompiler
