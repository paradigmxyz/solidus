import EvmCompiler.Locals.EffectSemantics
import EvmCompiler.Simulation.ResourceReplay

namespace EvmCompiler
namespace Locals
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace
abbrev Observer := Assembly.ResourceObserver
abbrev Word := Assembly.Word

def basicOpObserver? (op : Structured.BasicOp) : Option Observer :=
  Assembly.ResourceObserver.ofPrimOp? op.toPrimOp

abbrev State :=
  Simulation.ResourceReplay.State Locals.Source.State

def stateModel (transcript : Trace) :
    Locals.Source.Effectful.StateModel (State transcript) where
  source := fun state => state.source
  withSource := Simulation.ResourceReplay.State.withSource

def primitiveSemantics (transcript : Trace) :
    Locals.Source.Effectful.PrimitiveSemantics (State transcript) where
  eval op state values :=
    match basicOpObserver? op with
    | some kind =>
        match values with
        | [] =>
            match Simulation.ResourceReplay.consume? kind state with
            | some (value, state') => .ok (state', [value])
            | none => Structured.invalid
        | _ :: _ => Structured.invalid
    | none =>
        match
            Locals.Source.PrimitiveSemantics.structured.eval op
              state.source.shared values with
        | .ok (shared, results) =>
            .ok
              ({ state with source := state.source.withShared shared },
                results)
        | .error err => .error err
  terminal kind state values :=
    match
        Locals.Source.PrimitiveSemantics.structured.terminal kind
          state.source.shared values with
    | .ok shared =>
        .ok { state with source := state.source.withShared shared }
    | .error err => .error err

abbrev Outcome {transcript : Trace} :=
  Locals.Source.Effectful.Outcome (State transcript)

namespace Outcome

def ConsumedExactly {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Prop :=
  Simulation.ResourceReplay.State.ConsumedExactly outcome.state

def observed {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Trace :=
  Simulation.ResourceReplay.State.observed outcome.state

def remaining {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Trace :=
  Simulation.ResourceReplay.State.remaining outcome.state

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

namespace Program

def initialState (initial : Assembly.EVMState) (transcript : Trace) :
    State transcript :=
  { source := Locals.Source.Program.initialState initial.toSharedState }

def run (fuel : Nat) (program : Locals.Program)
    (initial : Assembly.EVMState) (transcript : Trace) :
    Except EVMException (Outcome (transcript := transcript)) :=
  Locals.Source.Effectful.Program.runState
    (stateModel transcript) (primitiveSemantics transcript)
    fuel program (initialState initial transcript)

def ExactReplay (fuel : Nat) (program : Locals.Program)
    (initial : Assembly.EVMState) (transcript : Trace)
    (outcome : Outcome (transcript := transcript)) : Prop :=
  run fuel program initial transcript = .ok outcome ∧
    outcome.ConsumedExactly

theorem ExactReplay.observed_eq_transcript
    {fuel : Nat} {program : Locals.Program}
    {initial : Assembly.EVMState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    outcome.observed = transcript :=
  Outcome.observed_eq_transcript_of_consumedExactly hReplay.2

theorem ExactReplay.remaining_eq_nil
    {fuel : Nat} {program : Locals.Program}
    {initial : Assembly.EVMState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    outcome.remaining = [] :=
  Outcome.remaining_eq_nil_of_consumedExactly hReplay.2

end Program

@[simp] theorem eval_gas_cons
    (source : Locals.Source.State) (value : Word) (rest : Trace) :
    Locals.Source.Effectful.Expr.eval
        (stateModel ({ kind := .gas, value := value } :: rest))
        (primitiveSemantics ({ kind := .gas, value := value } :: rest))
        (.prim .gas .nil : Locals.Expr 1)
        { source := source } =
      .ok ({ source := source, cursor := 1 }, [value]) := by
  simp [Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval, primitiveSemantics,
    basicOpObserver?, Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Simulation.ResourceReplay.consume?]

@[simp] theorem eval_msize_cons
    (source : Locals.Source.State) (value : Word) (rest : Trace) :
    Locals.Source.Effectful.Expr.eval
        (stateModel ({ kind := .msize, value := value } :: rest))
        (primitiveSemantics ({ kind := .msize, value := value } :: rest))
        (.prim .msize .nil : Locals.Expr 1)
        { source := source } =
      .ok ({ source := source, cursor := 1 }, [value]) := by
  simp [Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval, primitiveSemantics,
    basicOpObserver?, Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Simulation.ResourceReplay.consume?]

end ObserverSemantics
end Locals
end EvmCompiler
