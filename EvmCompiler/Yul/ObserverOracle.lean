import EvmCompiler.Assembly.Observer
import EvmCompiler.PublicVerification
import EvmCompiler.Simulation.ResourceReplay
import EvmCompiler.Yul.EffectSemantics

namespace EvmCompiler
namespace Yul
namespace ObserverOracle

/-!
Resource-observer support over the common compiler architecture.

The imported-Yul replay is a primitive-handler specialization of
`Yul.Source.Effectful`; it does not define a second control evaluator. Target
observation and oracle replay use the shared Assembly observer semantics, and
public resource-mode artifacts use the same entry simulation relation as the
ordinary compiler mode.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Observation := Assembly.ResourceObservation
abbrev Observer := Assembly.ResourceObserver

def basicOpObserver? : Structured.BasicOp → Option Observer
  | .gas => some .gas
  | .msize => some .msize
  | _ => none

def yulPrimObserver? (prim : EvmYul.Operation .Yul) : Option Observer :=
  (Prim.toUncheckedBasicOp? prim).bind basicOpObserver?

@[simp] theorem basicOpObserver?_gas :
    basicOpObserver? .gas = some .gas := rfl

@[simp] theorem basicOpObserver?_msize :
    basicOpObserver? .msize = some .msize := rfl

@[simp] theorem yulPrimObserver?_gas :
    yulPrimObserver?
        ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) =
      some .gas := rfl

@[simp] theorem yulPrimObserver?_msize :
    yulPrimObserver?
        ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) =
      some .msize := rfl

@[simp] theorem uncheckedBasicOp?_gas_observer :
    Prim.toUncheckedBasicOp?
        ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) =
      some .gas ∧
    basicOpObserver? .gas =
      yulPrimObserver?
        ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) := by
  simp [Prim.toUncheckedBasicOp?]

@[simp] theorem uncheckedBasicOp?_msize_observer :
    Prim.toUncheckedBasicOp?
        ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) =
      some .msize ∧
    basicOpObserver? .msize =
      yulPrimObserver?
        ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) := by
  simp [Prim.toUncheckedBasicOp?]

@[simp] theorem basicOp_toPrimOp_observer
    (op : Structured.BasicOp) :
    Assembly.ResourceObserver.ofPrimOp? op.toPrimOp =
      basicOpObserver? op := by
  cases op <;> rfl

@[simp] theorem typedCfgEffects_gas :
    (TypedCfg.Effects.ofPrim .gas).observesResources = true := by
  native_decide

@[simp] theorem typedCfgEffects_msize :
    (TypedCfg.Effects.ofPrim .msize).observesResources = true := by
  native_decide

@[simp] theorem typedCfgEffects_gas_noExternal :
    (TypedCfg.Effects.ofPrim .gas).callsOrCreates = false := by
  native_decide

@[simp] theorem typedCfgEffects_msize_noExternal :
    (TypedCfg.Effects.ofPrim .msize).callsOrCreates = false := by
  native_decide

namespace SourceReplay

abbrev State :=
  Simulation.ResourceReplay.State EvmYul.Yul.State

namespace State

def withSource {transcript : Trace} (state : State transcript)
    (source : EvmYul.Yul.State) : State transcript :=
  Simulation.ResourceReplay.State.withSource state source

def afterException {transcript : Trace} (state : State transcript) :
    EvmYul.Yul.Exception → State transcript
  | .YulHalt source _value => state.withSource source
  | .Revert source => state.withSource source
  | _ => state

def observed {transcript : Trace} (state : State transcript) : Trace :=
  Simulation.ResourceReplay.State.observed state

def remaining {transcript : Trace} (state : State transcript) : Trace :=
  Simulation.ResourceReplay.State.remaining state

def ConsumedExactly {transcript : Trace} (state : State transcript) : Prop :=
  Simulation.ResourceReplay.State.ConsumedExactly state

@[simp] theorem withSource_source {transcript : Trace}
    (state : State transcript)
    (source : EvmYul.Yul.State) :
    (state.withSource source).source = source := rfl

@[simp] theorem withSource_cursor {transcript : Trace}
    (state : State transcript)
    (source : EvmYul.Yul.State) :
    (state.withSource source).cursor = state.cursor := rfl

@[simp] theorem withSource_observed {transcript : Trace}
    (state : State transcript)
    (source : EvmYul.Yul.State) :
    (state.withSource source).observed = state.observed := rfl

@[simp] theorem withSource_remaining {transcript : Trace}
    (state : State transcript)
    (source : EvmYul.Yul.State) :
    (state.withSource source).remaining = state.remaining := rfl

theorem observed_eq_transcript_of_consumedExactly
    {transcript : Trace} {state : State transcript}
    (hConsumed : state.ConsumedExactly) :
    state.observed = transcript :=
  Simulation.ResourceReplay.State.observed_eq_transcript_of_consumedExactly
    hConsumed

theorem remaining_eq_nil_of_consumedExactly
    {transcript : Trace} {state : State transcript}
    (hConsumed : state.ConsumedExactly) :
    state.remaining = [] :=
  Simulation.ResourceReplay.State.remaining_eq_nil_of_consumedExactly
    hConsumed

end State

def primCall {transcript : Trace} (fuel : Nat) (state : State transcript)
    (prim : EvmYul.Operation .Yul) (args : List Word) :
    Yul.Source.Effectful.Result (State transcript)
      (State transcript × List Word) :=
  match fuel with
  | 0 => Yul.Source.Effectful.fail state .OutOfFuel
  | fuel' + 1 =>
      match yulPrimObserver? prim with
      | some kind =>
          match args with
          | [] =>
              match Simulation.ResourceReplay.consume? kind state with
              | some (value, state') => .ok (state', [value])
              | none =>
                  Yul.Source.Effectful.fail state .InvalidInstruction
          | _ :: _ => Yul.Source.Effectful.fail state .InvalidArguments
      | none =>
          match EvmYul.Yul.primCall fuel' state.source prim args with
          | .ok (source', values) =>
              .ok ({ state with source := source' }, values)
          | .error err =>
              Yul.Source.Effectful.fail (state.afterException err) err

def stateModel (transcript : Trace) :
    Yul.Source.Effectful.StateModel (State transcript) where
  source := fun state => state.source
  withSource := State.withSource

def primitiveSemantics (transcript : Trace) :
    Yul.Source.Effectful.PrimitiveSemantics (State transcript) where
  eval := primCall

abbrev evalArgs {transcript : Trace} :=
  Yul.Source.Effectful.evalArgs (stateModel transcript)
    (primitiveSemantics transcript)

abbrev evalValues {transcript : Trace} :=
  Yul.Source.Effectful.evalValues (stateModel transcript)
    (primitiveSemantics transcript)

abbrev eval {transcript : Trace} :=
  Yul.Source.Effectful.eval (stateModel transcript)
    (primitiveSemantics transcript)

abbrev call {transcript : Trace} :=
  Yul.Source.Effectful.call (stateModel transcript)
    (primitiveSemantics transcript)

abbrev callDispatcher {transcript : Trace} :=
  Yul.Source.Effectful.callDispatcher (stateModel transcript)
    (primitiveSemantics transcript)

abbrev execSeq {transcript : Trace} :=
  Yul.Source.Effectful.execSeq (stateModel transcript)
    (primitiveSemantics transcript)

abbrev exec {transcript : Trace} :=
  Yul.Source.Effectful.exec (stateModel transcript)
    (primitiveSemantics transcript)

abbrev loop {transcript : Trace} :=
  Yul.Source.Effectful.loop (stateModel transcript)
    (primitiveSemantics transcript)

@[simp] theorem primCall_gas_cons (fuel : Nat)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    primCall fuel.succ
        (transcript := { kind := .gas, value := value } :: trace)
        { source := source }
        (.StackMemFlow .GAS) [] =
      .ok
        ({ source := source, cursor := 1 },
        [value]) := by
  simp [primCall, Simulation.ResourceReplay.consume?]

@[simp] theorem primCall_msize_cons (fuel : Nat)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    primCall fuel.succ
        (transcript := { kind := .msize, value := value } :: trace)
        { source := source }
        (.StackMemFlow .MSIZE) [] =
      .ok
        ({ source := source, cursor := 1 },
        [value]) := by
  simp [primCall, Simulation.ResourceReplay.consume?]

theorem primCall_nonObserver_preserves_trace
    {transcript : Trace} {fuel : Nat}
    {state state' : State transcript}
    {prim : EvmYul.Operation .Yul} {args values : List Word}
    (hObserver : yulPrimObserver? prim = none)
    (hRun : primCall fuel.succ state prim args = .ok (state', values)) :
    EvmYul.Yul.primCall fuel state.source prim args =
        .ok (state'.source, values) ∧
      state'.cursor = state.cursor := by
  unfold primCall at hRun
  simp [hObserver] at hRun
  generalize hPrim :
      EvmYul.Yul.primCall fuel state.source prim args = result at hRun ⊢
  cases result with
  | error err =>
      simp [Yul.Source.Effectful.fail] at hRun
  | ok result =>
      rcases result with ⟨source', values'⟩
      simp at hRun
      rcases hRun with ⟨hState, hValues⟩
      cases hValues
      have hSource :
          state'.source = source' := by
        simpa using
          congrArg (fun replay : State transcript => replay.source) hState.symm
      have hCursor :
          state'.cursor = state.cursor := by
        simpa using
          congrArg (fun replay : State transcript => replay.cursor) hState.symm
      exact ⟨by simpa [hSource] using hPrim, hCursor⟩

@[simp] theorem evalValues_gas_cons (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    evalValues fuel.succ.succ
        (.Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])
        codeOverride
        (transcript := { kind := .gas, value := value } :: trace)
        { source := source } =
      .ok
        ({ source := source, cursor := 1 },
        [value]) := by
  simp [evalValues, primitiveSemantics,
    Yul.Source.Effectful.evalValues, Yul.Source.Effectful.evalArgs,
    primCall, Simulation.ResourceReplay.consume?]

@[simp] theorem evalValues_msize_cons (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    evalValues fuel.succ.succ
        (.Call (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])
        codeOverride
        (transcript := { kind := .msize, value := value } :: trace)
        { source := source } =
      .ok
        ({ source := source, cursor := 1 },
        [value]) := by
  simp [evalValues, primitiveSemantics,
    Yul.Source.Effectful.evalValues, Yul.Source.Effectful.evalArgs,
    primCall, Simulation.ResourceReplay.consume?]

@[simp] theorem exec_let_gas_cons (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : EvmYul.Yul.State) (name : EvmYul.Identifier)
    (value : Word) (trace : Trace)
    (hDecl : EvmYul.Yul.checkDeclaration source [name] = .ok ()) :
    exec fuel.succ.succ.succ
        (.Let [name]
          (some
            (.Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])))
        codeOverride
        (transcript := { kind := .gas, value := value } :: trace)
        { source := source } =
      .ok
        { source := source.multifill [name] [value], cursor := 1 } := by
  simp [exec, hDecl, primitiveSemantics, stateModel, State.withSource,
    Simulation.ResourceReplay.State.withSource,
    Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
    Yul.Source.Effectful.StateModel.multifill, primCall,
    Simulation.ResourceReplay.consume?]

@[simp] theorem exec_let_msize_cons (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : EvmYul.Yul.State) (name : EvmYul.Identifier)
    (value : Word) (trace : Trace)
    (hDecl : EvmYul.Yul.checkDeclaration source [name] = .ok ()) :
    exec fuel.succ.succ.succ
        (.Let [name]
          (some
            (.Call (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])))
        codeOverride
        (transcript := { kind := .msize, value := value } :: trace)
        { source := source } =
      .ok
        { source := source.multifill [name] [value], cursor := 1 } := by
  simp [exec, hDecl, primitiveSemantics, stateModel, State.withSource,
    Simulation.ResourceReplay.State.withSource,
    Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
    Yul.Source.Effectful.StateModel.multifill, primCall,
    Simulation.ResourceReplay.consume?]

inductive Result (transcript : Trace) where
  | regular (state : State transcript)
  | yulHalt (state : State transcript) (value : Word)
  | revert (stateBeforeRevert : State transcript)

namespace Result

def state {transcript : Trace} :
    Result transcript → State transcript
  | .regular state
  | .yulHalt state _
  | .revert state => state

def ConsumedExactly {transcript : Trace} (result : Result transcript) : Prop :=
  result.state.ConsumedExactly

def observed {transcript : Trace} (result : Result transcript) : Trace :=
  result.state.observed

def remaining {transcript : Trace} (result : Result transcript) : Trace :=
  result.state.remaining

theorem observed_eq_transcript_of_consumedExactly
    {transcript : Trace} {result : Result transcript}
    (hConsumed : result.ConsumedExactly) :
    result.observed = transcript :=
  State.observed_eq_transcript_of_consumedExactly hConsumed

theorem remaining_eq_nil_of_consumedExactly
    {transcript : Trace} {result : Result transcript}
    (hConsumed : result.ConsumedExactly) :
    result.remaining = [] :=
  State.remaining_eq_nil_of_consumedExactly hConsumed

end Result

namespace Program

def installContract {transcript : Trace} (program : Yul.Program)
    (state : State transcript) : State transcript :=
  state.withSource
    (match state.source with
    | .Ok shared store =>
        .Ok
          { shared with
            executionEnv :=
              { shared.executionEnv with code := program.contract } }
          store
    | .OutOfFuel => .OutOfFuel
    | .Checkpoint jump => .Checkpoint jump)

@[simp] theorem installContract_cursor
    {transcript : Trace} (program : Yul.Program)
    (state : State transcript) :
    (installContract program state).cursor = state.cursor := rfl

@[simp] theorem installContract_observed
    {transcript : Trace} (program : Yul.Program)
    (state : State transcript) :
    (installContract program state).observed = state.observed := rfl

@[simp] theorem installContract_remaining
    {transcript : Trace} (program : Yul.Program)
    (state : State transcript) :
    (installContract program state).remaining = state.remaining := rfl

def run (fuel : Nat) (program : Yul.Program)
    (source : EvmYul.Yul.State) (trace : Trace) :
    Except EvmYul.Yul.Exception (Result trace) :=
  match
      callDispatcher fuel (some program.contract)
        (installContract program { source := source }) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error failure =>
      match failure.exception with
      | .YulHalt source' value =>
          .ok (.yulHalt (failure.state.withSource source') value)
      | .Revert sourceBeforeRevert =>
          .ok (.revert (failure.state.withSource sourceBeforeRevert))
      | err => .error err

def ExactReplay (fuel : Nat) (program : Yul.Program)
    (source : EvmYul.Yul.State) (transcript : Trace)
    (result : Result transcript) : Prop :=
  run fuel program source transcript = .ok result ∧
    result.ConsumedExactly

def ExactTerminates (program : Yul.Program)
    (source : EvmYul.Yul.State) (transcript : Trace)
    (result : Result transcript) : Prop :=
  ∃ fuel, ExactReplay fuel program source transcript result

theorem ExactReplay.exactTerminates
    {fuel : Nat} {program : Yul.Program}
    {source : EvmYul.Yul.State} {transcript : Trace}
    {result : Result transcript}
    (hReplay : ExactReplay fuel program source transcript result) :
    ExactTerminates program source transcript result :=
  ⟨fuel, hReplay⟩

theorem ExactReplay.observed_eq_transcript
    {fuel : Nat} {program : Yul.Program}
    {source : EvmYul.Yul.State} {transcript : Trace}
    {result : Result transcript}
    (hReplay : ExactReplay fuel program source transcript result) :
    result.observed = transcript :=
  Result.observed_eq_transcript_of_consumedExactly hReplay.2

theorem ExactReplay.remaining_eq_nil
    {fuel : Nat} {program : Yul.Program}
    {source : EvmYul.Yul.State} {transcript : Trace}
    {result : Result transcript}
    (hReplay : ExactReplay fuel program source transcript result) :
    result.remaining = [] :=
  Result.remaining_eq_nil_of_consumedExactly hReplay.2

theorem ExactTerminates.observed_eq_transcript
    {program : Yul.Program}
    {source : EvmYul.Yul.State} {transcript : Trace}
    {result : Result transcript}
    (hTerminates : ExactTerminates program source transcript result) :
    result.observed = transcript := by
  rcases hTerminates with ⟨fuel, hReplay⟩
  exact ExactReplay.observed_eq_transcript hReplay

theorem ExactTerminates.remaining_eq_nil
    {program : Yul.Program}
    {source : EvmYul.Yul.State} {transcript : Trace}
    {result : Result transcript}
    (hTerminates : ExactTerminates program source transcript result) :
    result.remaining = [] := by
  rcases hTerminates with ⟨fuel, hReplay⟩
  exact ExactReplay.remaining_eq_nil hReplay

end Program
end SourceReplay

namespace PublicArtifact

def NoExternalEffects (artifact : Public.Artifact) : Prop :=
  artifact.metadata.certificate.cfg.safety.noCallCreate = true

def noExternalEffects? (artifact : Public.Artifact) : Bool :=
  artifact.metadata.certificate.cfg.safety.noCallCreate

theorem noExternalEffects_of_check
    {artifact : Public.Artifact}
    (hCheck : noExternalEffects? artifact = true) :
    NoExternalEffects artifact :=
  hCheck

def TerminalObserverRun (artifact : Public.Artifact) (fuel : Nat)
    (initial : Assembly.EVMState) (result : Assembly.StepResult)
    (trace : Trace) : Prop :=
  Assembly.Target.runNResultWithObservers artifact.target fuel initial =
      .ok (result, trace) ∧
    result.IsTerminal

def ObserverReplay (artifact : Public.Artifact) (fuel : Nat)
    (initial : Assembly.EVMState) (result : Assembly.StepResult)
    (trace : Trace) : Prop :=
  Assembly.Target.runNResultWithObservers artifact.target fuel initial =
      .ok (result, trace) ∧
    Assembly.Target.runNResultWithOracle artifact.target fuel initial trace =
      .ok (result, [])

theorem observerReplay_of_run
    {artifact : Public.Artifact} {fuel : Nat}
    {initial : Assembly.EVMState} {result : Assembly.StepResult}
    {trace : Trace}
    (hRun :
      Assembly.Target.runNResultWithObservers artifact.target fuel initial =
        .ok (result, trace)) :
    ObserverReplay artifact fuel initial result trace := by
  refine ⟨hRun, ?_⟩
  simpa using
    (Assembly.Target.runNResultWithOracle_of_withObservers
      (rest := []) hRun)

theorem terminalObserverRun_observerReplay
    {artifact : Public.Artifact} {fuel : Nat}
    {initial : Assembly.EVMState} {result : Assembly.StepResult}
    {trace : Trace}
    (hRun : TerminalObserverRun artifact fuel initial result trace) :
    ObserverReplay artifact fuel initial result trace :=
  observerReplay_of_run hRun.1

end PublicArtifact

theorem compileResourceArtifactWithPolicy?_verifiedObserverRun
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
      PublicArtifact.ObserverReplay artifact fuel initial result trace := by
  exact
    ⟨Public.compileArtifactWithPolicy?_entrySimulation hCompile,
      PublicArtifact.observerReplay_of_run hRun⟩

end ObserverOracle
end Yul
end EvmCompiler
