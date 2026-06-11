import EvmCompiler.Simulation.ResourceReplay
import EvmCompiler.Structured.EffectSemantics

namespace EvmCompiler
namespace Structured
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace
abbrev Observer := Assembly.ResourceObserver
abbrev State :=
  Simulation.ResourceReplay.State Structured.RunState
abbrev Outcome {transcript : Trace} :=
  Structured.OutcomeT (State transcript)

def basicOpObserver? (op : Structured.BasicOp) : Option Observer :=
  Assembly.ResourceObserver.ofPrimOp? op.toPrimOp

def stateModel (transcript : Trace) :
    Structured.EffectSemantics.StateModel (State transcript) where
  source state := state.source
  withSource := Simulation.ResourceReplay.State.withSource
  pushReturn state callerStack retc :=
    state.withSource (state.source.pushReturn callerStack retc)
  popReturn? state :=
    match state.source.popReturn? with
    | none => none
    | some (frame, source) => some (frame, state.withSource source)

def handler (transcript : Trace) :
    Structured.EffectSemantics.Handler (State transcript) where
  afterInstr instr state :=
    match instr with
    | .op op =>
        match basicOpObserver? op with
        | none => .ok state
        | some kind =>
            match Simulation.ResourceReplay.consume? kind state with
            | none => Structured.invalid
            | some (value, consumed) =>
                match
                    Assembly.ResourceObserver.overwriteTop
                      value consumed.source.evm
                with
                | .error err => .error err
                | .ok evm =>
                    .ok
                      (consumed.withSource
                        (consumed.source.withEVM evm))
    | .push _ | .bindLocals _ _ | .bindScratch _ _ _ =>
        .ok state

namespace Outcome

def ConsumedExactly {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Prop :=
  outcome.state.ConsumedExactly

def observed {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Trace :=
  outcome.state.observed

def remaining {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Trace :=
  outcome.state.remaining

theorem observed_eq_transcript_of_consumedExactly
    {transcript : Trace} {outcome : Outcome (transcript := transcript)}
    (hConsumed : outcome.ConsumedExactly) :
    outcome.observed = transcript :=
  Simulation.ResourceReplay.State.observed_eq_transcript_of_consumedExactly
    hConsumed

theorem remaining_eq_nil_of_consumedExactly
    {transcript : Trace} {outcome : Outcome (transcript := transcript)}
    (hConsumed : outcome.ConsumedExactly) :
    outcome.remaining = [] :=
  Simulation.ResourceReplay.State.remaining_eq_nil_of_consumedExactly
    hConsumed

end Outcome

namespace Code

def run {transcript : Trace} (code : Structured.Code)
    (state : State transcript) :
    Except EVMException (State transcript) :=
  Structured.EffectSemantics.Code.run
    (stateModel transcript) (handler transcript) code state

def runCondition {transcript : Trace} (code : Structured.Code)
    (state : State transcript) :
    Except EVMException (State transcript × Bool) :=
  Structured.EffectSemantics.Code.runCondition
    (stateModel transcript) (handler transcript) code state

end Code

namespace Program

def initialState (initial : Structured.RunState) (transcript : Trace) :
    State transcript :=
  { source := initial }

def runState (fuel : Nat) (program : Structured.Program)
    {transcript : Trace} (state : State transcript) :
    Except EVMException (Outcome (transcript := transcript)) :=
  Structured.EffectSemantics.Program.runState
    (stateModel transcript) (handler transcript)
    fuel program state

def run (fuel : Nat) (program : Structured.Program)
    (initial : Structured.RunState) (transcript : Trace) :
    Except EVMException (Outcome (transcript := transcript)) :=
  runState fuel program (initialState initial transcript)

def ExactReplay (fuel : Nat) (program : Structured.Program)
    (initial : Structured.RunState) (transcript : Trace)
    (outcome : Outcome (transcript := transcript)) : Prop :=
  run fuel program initial transcript = .ok outcome ∧
    outcome.ConsumedExactly

theorem ExactReplay.observed_eq_transcript
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    outcome.observed = transcript :=
  Outcome.observed_eq_transcript_of_consumedExactly hReplay.2

theorem ExactReplay.remaining_eq_nil
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    outcome.remaining = [] :=
  Outcome.remaining_eq_nil_of_consumedExactly hReplay.2

end Program

@[simp] theorem basicOpObserver?_gas :
    basicOpObserver? .gas = some .gas := rfl

@[simp] theorem basicOpObserver?_msize :
    basicOpObserver? .msize = some .msize := rfl

end ObserverSemantics
end Structured
end EvmCompiler
