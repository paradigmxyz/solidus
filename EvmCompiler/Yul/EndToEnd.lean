import EvmCompiler.Public.Observer
import EvmCompiler.Yul.FunctionsObserverPreservation
import EvmCompiler.Yul.ObserverSemantics
import EvmCompiler.Yul.StateRelation

namespace EvmCompiler
namespace Yul
namespace EndToEnd

/-!
The public statement boundary for resource-observing Yul compilation.

The first theorem is deliberately restricted to checked artifacts without
external calls or creates and to target runs that reach an explicit EVM halt.
Ordinary Yul fallthrough needs a separate completion boundary because the
current generated CFG represents program end with an invalid terminator.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev SourceResult := ObserverSemantics.SourceReplay.Result

namespace State

def Rel (codeRel : StateRelation.CodeRel)
    (source : EvmYul.Yul.State) (target : Assembly.EVMState) : Prop :=
  ∃ shared vars,
    source = .Ok shared vars ∧
      StateRelation.Shared.Rel codeRel shared target.toSharedState

def InitialRel (codeRel : StateRelation.CodeRel)
    (program : Yul.Program) (source : EvmYul.Yul.State)
    (target : Assembly.EVMState) : Prop :=
  Rel codeRel
    (ObserverSemantics.SourceReplay.Program.installContract program
      (transcript := ([] : Trace)) { source := source }).source
    target

def TerminalRel (codeRel : StateRelation.CodeRel)
    (source : EvmYul.Yul.State) (target : Assembly.EVMState) : Prop :=
  ∃ shared vars,
    source = .Ok shared vars ∧
      StateRelation.TerminalShared.Rel codeRel
        shared target.toSharedState

end State

namespace Result

def IsSuccessfulHalt : Assembly.Halt → Prop
  | { kind := .stop, .. } => True
  | { kind := .return, .. } => True
  | { kind := .selfdestruct, .. } => True
  | { kind := .revert, .. } => False

def Rel {transcript : Trace} (codeRel : StateRelation.CodeRel) :
    SourceResult transcript → Assembly.StepResult → Prop
  | .regular _, _ => False
  | .yulHalt source _value, .running _ => False
  | .yulHalt source _value, .halted halt =>
      IsSuccessfulHalt halt ∧
        State.TerminalRel codeRel source.source halt.state ∧
        halt.output =
          source.source.sharedState.toMachineState.H_return
  | .revert source, .running _ => False
  | .revert source, .halted halt =>
      halt.kind = .revert ∧
        State.TerminalRel codeRel source.source halt.state ∧
        halt.output =
          source.source.sharedState.toMachineState.H_return

theorem target_terminal {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {source : SourceResult transcript} {target : Assembly.StepResult}
    (hRel : Rel codeRel source target) :
    target.IsTerminal := by
  cases source <;> cases target <;>
    simp_all [Rel, Assembly.StepResult.IsTerminal]

end Result

structure ClosedArtifact (policy : Public.BackendPolicy)
    (program : Yul.Program) (artifact : Public.Artifact) : Prop where
  accepted :
    Public.SourceAccepted .resourceObservers (.yul program)
  compiled :
    Public.compileArtifactWithPolicy? policy
      .resourceObservers (.yul program) = some artifact
  noExternalEffects :
    Public.Observer.NoExternalEffects artifact

theorem ClosedArtifact.valid
    {policy : Public.BackendPolicy} {program : Yul.Program}
    {artifact : Public.Artifact}
    (hArtifact : ClosedArtifact policy program artifact) :
    Public.ArtifactValid policy .resourceObservers
      (.yul program) artifact :=
  Public.compileArtifactWithPolicy?_valid hArtifact.compiled

theorem ClosedArtifact.observerReplay
    {policy : Public.BackendPolicy} {program : Yul.Program}
    {artifact : Public.Artifact} {fuel : Nat}
    {initial : Assembly.EVMState} {target : Assembly.StepResult}
    {transcript : Trace}
    (hArtifact : ClosedArtifact policy program artifact)
    (hRun :
      Public.Observer.TerminalRun artifact fuel
        initial target transcript) :
    Public.Observer.ExactReplay artifact fuel initial
      target transcript :=
  hRun.exactReplay

/--
The exact proposition that the first end-to-end proof must establish.

It is target-to-source backward adequacy: a concrete terminal target run
constructs an exact source replay over the target's complete ordered resource
transcript and relates the terminal source and target outcomes.
-/
def ClosedResourceCorrect : Prop :=
  ∀ (policy : Public.BackendPolicy) (program : Yul.Program)
    (artifact : Public.Artifact) (codeRel : StateRelation.CodeRel)
    (source : EvmYul.Yul.State) (initial : Assembly.EVMState)
    (fuel : Nat) (target : Assembly.StepResult) (transcript : Trace),
    ClosedArtifact policy program artifact →
    State.InitialRel codeRel program source initial →
    Public.Observer.TerminalRun artifact fuel
      initial target transcript →
    ∃ sourceResult : SourceResult transcript,
      ObserverSemantics.SourceReplay.Program.ExactTerminates
        program source transcript sourceResult ∧
      Result.Rel codeRel sourceResult target

end EndToEnd
end Yul
end EvmCompiler
