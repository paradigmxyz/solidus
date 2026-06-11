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

def applyObserver {transcript : Trace} (kind : Observer)
    (state : State transcript) :
    Except EVMException (State transcript) :=
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

@[simp] theorem stateModel_source
    {transcript : Trace} (state : State transcript) :
    (stateModel transcript).source state = state.source := rfl

@[simp] theorem stateModel_evm
    {transcript : Trace} (state : State transcript) :
    (stateModel transcript).evm state = state.source.evm := rfl

@[simp] theorem stateModel_returns
    {transcript : Trace} (state : State transcript) :
    (stateModel transcript).returns state = state.source.returns := rfl

@[simp] theorem stateModel_withEVM
    {transcript : Trace} (state : State transcript) (evm : EVMState) :
    (stateModel transcript).withEVM state evm =
      state.withSource (state.source.withEVM evm) := rfl

def handler (transcript : Trace) :
    Structured.EffectSemantics.Handler (State transcript) where
  afterInstr instr state :=
    match instr with
    | .op op =>
        match basicOpObserver? op with
        | none => .ok state
        | some kind => applyObserver kind state
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

def withHidden {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) : State transcript :=
  state.withSource
    (state.source.withEVM
      { state.source.evm with
        stack := state.source.evm.stack ++ hidden })

def FrameSafe (code : Structured.Code) : Prop :=
  ∀ (transcript : Trace) (state final : State transcript)
      (hidden : EvmYul.Stack Word),
    run code state = .ok final →
      run code (withHidden state hidden) =
        .ok (withHidden final hidden)

@[simp] theorem withHidden_source
    {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) :
    (withHidden state hidden).source =
      state.source.withEVM
        { state.source.evm with
          stack := state.source.evm.stack ++ hidden } := rfl

@[simp] theorem withHidden_cursor
    {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) :
    (withHidden state hidden).cursor = state.cursor := rfl

@[simp] theorem withHidden_remaining
    {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) :
    (withHidden state hidden).remaining = state.remaining := rfl

def runCondition {transcript : Trace} (code : Structured.Code)
    (state : State transcript) :
    Except EVMException (State transcript × Bool) :=
  Structured.EffectSemantics.Code.runCondition
    (stateModel transcript) (handler transcript) code state

theorem run_cons_eq_run_single_bind
    {transcript : Trace} (instr : Structured.BasicInstr)
    (rest : Structured.Code) (state : State transcript) :
    run (instr :: rest) state =
      (run [instr] state).bind (run rest) :=
  Structured.EffectSemantics.Code.run_cons_eq_run_single_bind
    (stateModel transcript) (handler transcript) instr rest state

theorem run_returns_eq
    {transcript : Trace} {code : Structured.Code}
    {state final : State transcript}
    (hRun : run code state = .ok final) :
    final.source.returns = state.source.returns := by
  induction code generalizing state final with
  | nil =>
      simp [run, Structured.EffectSemantics.Code.run] at hRun
      cases hRun
      rfl
  | cons instr rest ih =>
      unfold run Structured.EffectSemantics.Code.run at hRun
      simp only [stateModel_evm, stateModel_withEVM] at hRun
      cases hStep : instr.step state.source.evm with
      | error err =>
          simp [hStep, Bind.bind, Except.bind] at hRun
      | ok evm =>
          simp only [hStep, Bind.bind, Except.bind] at hRun
          cases hAfter :
              (handler transcript).afterInstr instr
                (state.withSource (state.source.withEVM evm)) with
          | error err =>
              rw [hAfter] at hRun
              contradiction
          | ok middle =>
              rw [hAfter] at hRun
              have hMiddle :
                  middle.source.returns = state.source.returns := by
                cases instr with
                | push value | bindLocals value names
                | bindScratch value name slot =>
                    simp [handler] at hAfter
                    cases hAfter
                    rfl
                | op op =>
                    cases hObserver : basicOpObserver? op with
                    | none =>
                        simp [handler, hObserver] at hAfter
                        cases hAfter
                        rfl
                    | some kind =>
                        simp only [handler, hObserver] at hAfter
                        unfold applyObserver at hAfter
                        cases hConsume :
                            Simulation.ResourceReplay.consume? kind
                              (state.withSource
                                (state.source.withEVM evm)) with
                        | none =>
                            simp [hConsume, Structured.invalid] at hAfter
                        | some consumed =>
                            rcases consumed with ⟨value, consumed⟩
                            simp [hConsume] at hAfter
                            cases hOverwrite :
                                Assembly.ResourceObserver.overwriteTop
                                  value consumed.source.evm with
                            | error err =>
                                simp [hOverwrite] at hAfter
                            | ok observed =>
                                simp [hOverwrite] at hAfter
                                cases hAfter
                                rw [
                                  Simulation.ResourceReplay.consume?_source
                                    hConsume]
                                rfl
              exact (ih hRun).trans hMiddle

end Code

namespace Block

abbrev Eval {transcript : Trace} :=
  Structured.EffectSemantics.Block.Eval
    (stateModel transcript) (handler transcript)

end Block

namespace Stmt

abbrev Eval {transcript : Trace} :=
  Structured.EffectSemantics.Stmt.Eval
    (stateModel transcript) (handler transcript)

end Stmt

namespace For

abbrev Eval {transcript : Trace} :=
  Structured.EffectSemantics.For.Eval
    (stateModel transcript) (handler transcript)

end For

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

theorem eval_of_runState
    {fuel : Nat} {program : Structured.Program}
    {transcript : Trace} {state : State transcript}
    {outcome : Outcome (transcript := transcript)}
    (hRun : runState fuel program state = .ok outcome) :
    Block.Eval program fuel program.body state outcome :=
  Structured.EffectSemantics.Program.eval_of_runState hRun

theorem eval_of_run
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hRun : run fuel program initial transcript = .ok outcome) :
    Block.Eval program fuel program.body
      (initialState initial transcript) outcome :=
  eval_of_runState hRun

theorem ExactReplay.eval
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    Block.Eval program fuel program.body
      (initialState initial transcript) outcome :=
  eval_of_run hReplay.1

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
