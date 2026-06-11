import EvmCompiler.Assembly.Observer
import EvmCompiler.PublicVerification

namespace EvmCompiler
namespace Public
namespace Observer

/-!
Observer-aware facts owned by the checked public artifact boundary.

This module contains target execution and artifact safety only. Imported Yul
replay belongs to `Yul.ObserverSemantics`.
-/

abbrev Trace := Assembly.ResourceTrace

def NoExternalEffects (artifact : Public.Artifact) : Prop :=
  artifact.metadata.certificate.cfg.safety.noCallCreate = true

def noExternalEffects? (artifact : Public.Artifact) : Bool :=
  artifact.metadata.certificate.cfg.safety.noCallCreate

theorem noExternalEffects_of_check
    {artifact : Public.Artifact}
    (hCheck : noExternalEffects? artifact = true) :
    NoExternalEffects artifact :=
  hCheck

def TerminalRun (artifact : Public.Artifact) (fuel : Nat)
    (initial : Assembly.EVMState) (result : Assembly.StepResult)
    (trace : Trace) : Prop :=
  Assembly.Target.runNResultWithObservers artifact.target fuel initial =
      .ok (result, trace) ∧
    result.IsTerminal

def ExactReplay (artifact : Public.Artifact) (fuel : Nat)
    (initial : Assembly.EVMState) (result : Assembly.StepResult)
    (trace : Trace) : Prop :=
  Assembly.Target.runNResultWithObservers artifact.target fuel initial =
      .ok (result, trace) ∧
    Assembly.Target.runNResultWithOracle artifact.target fuel initial trace =
      .ok (result, [])

theorem exactReplay_of_run
    {artifact : Public.Artifact} {fuel : Nat}
    {initial : Assembly.EVMState} {result : Assembly.StepResult}
    {trace : Trace}
    (hRun :
      Assembly.Target.runNResultWithObservers artifact.target fuel initial =
        .ok (result, trace)) :
    ExactReplay artifact fuel initial result trace := by
  refine ⟨hRun, ?_⟩
  simpa using
    (Assembly.Target.runNResultWithOracle_of_withObservers
      (rest := []) hRun)

theorem TerminalRun.exactReplay
    {artifact : Public.Artifact} {fuel : Nat}
    {initial : Assembly.EVMState} {result : Assembly.StepResult}
    {trace : Trace}
    (hRun : TerminalRun artifact fuel initial result trace) :
    ExactReplay artifact fuel initial result trace :=
  exactReplay_of_run hRun.1

theorem compileResourceArtifactWithPolicy?_verifiedRun
    {policy : Public.BackendPolicy} {source : Public.Source}
    {artifact : Public.Artifact} {initial : Assembly.EVMState}
    {fuel : Nat} {result : Assembly.StepResult} {trace : Trace}
    (hCompile :
      Public.compileArtifactWithPolicy? policy
        .resourceObservers source = some artifact)
    (hRun :
      Assembly.Target.runNResultWithObservers artifact.target fuel initial =
        .ok (result, trace)) :
    artifact.EntrySimulation initial ∧
      ExactReplay artifact fuel initial result trace := by
  exact
    ⟨Public.compileArtifactWithPolicy?_entrySimulation hCompile,
      exactReplay_of_run hRun⟩

end Observer
end Public
end EvmCompiler
