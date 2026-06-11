import EvmCompiler.Assembly.Observer
import EvmCompiler.PublicVerification
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

namespace SourceReplay

structure State where
  source : EvmYul.Yul.State
  trace : Trace

namespace State

def withSource (state : State) (source : EvmYul.Yul.State) : State :=
  { state with source := source }

@[simp] theorem withSource_source (state : State)
    (source : EvmYul.Yul.State) :
    (state.withSource source).source = source := rfl

@[simp] theorem withSource_trace (state : State)
    (source : EvmYul.Yul.State) :
    (state.withSource source).trace = state.trace := rfl

end State

def consume (kind : Observer) : Trace →
    Except EvmYul.Yul.Exception (Word × Trace)
  | [] => .error .InvalidInstruction
  | observation :: rest =>
      if observation.kind = kind then
        .ok (observation.value, rest)
      else
        .error .InvalidInstruction

def primCall (fuel : Nat) (state : State)
    (prim : EvmYul.Operation .Yul) (args : List Word) :
    Except EvmYul.Yul.Exception (State × List Word) :=
  match fuel with
  | 0 => .error .OutOfFuel
  | fuel' + 1 =>
      match yulPrimObserver? prim with
      | some kind =>
          match args with
          | [] =>
              match consume kind state.trace with
              | .ok (value, trace') =>
                  .ok ({ state with trace := trace' }, [value])
              | .error err => .error err
          | _ :: _ => .error .InvalidArguments
      | none =>
          match EvmYul.Yul.primCall fuel' state.source prim args with
          | .ok (source', values) =>
              .ok ({ state with source := source' }, values)
          | .error err => .error err

def stateModel : Yul.Source.Effectful.StateModel State where
  source := State.source
  withSource := State.withSource

def primitiveSemantics : Yul.Source.Effectful.PrimitiveSemantics State where
  eval := primCall

abbrev evalArgs :=
  Yul.Source.Effectful.evalArgs stateModel primitiveSemantics

abbrev evalValues :=
  Yul.Source.Effectful.evalValues stateModel primitiveSemantics

abbrev eval :=
  Yul.Source.Effectful.eval stateModel primitiveSemantics

abbrev call :=
  Yul.Source.Effectful.call stateModel primitiveSemantics

abbrev callDispatcher :=
  Yul.Source.Effectful.callDispatcher stateModel primitiveSemantics

abbrev execSeq :=
  Yul.Source.Effectful.execSeq stateModel primitiveSemantics

abbrev exec :=
  Yul.Source.Effectful.exec stateModel primitiveSemantics

abbrev loop :=
  Yul.Source.Effectful.loop stateModel primitiveSemantics

@[simp] theorem primCall_gas_cons (fuel : Nat)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    primCall fuel.succ
        { source := source,
          trace := { kind := .gas, value := value } :: trace }
        (.StackMemFlow .GAS) [] =
      .ok ({ source := source, trace := trace }, [value]) := by
  simp [primCall, consume]

@[simp] theorem primCall_msize_cons (fuel : Nat)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    primCall fuel.succ
        { source := source,
          trace := { kind := .msize, value := value } :: trace }
        (.StackMemFlow .MSIZE) [] =
      .ok ({ source := source, trace := trace }, [value]) := by
  simp [primCall, consume]

theorem primCall_nonObserver_preserves_trace
    {fuel : Nat} {state state' : State}
    {prim : EvmYul.Operation .Yul} {args values : List Word}
    (hObserver : yulPrimObserver? prim = none)
    (hRun : primCall fuel.succ state prim args = .ok (state', values)) :
    EvmYul.Yul.primCall fuel state.source prim args =
        .ok (state'.source, values) ∧
      state'.trace = state.trace := by
  unfold primCall at hRun
  simp [hObserver] at hRun
  generalize hPrim :
      EvmYul.Yul.primCall fuel state.source prim args = result at hRun ⊢
  cases result with
  | error err =>
      simp at hRun
  | ok result =>
      rcases result with ⟨source', values'⟩
      simp at hRun
      rcases hRun with ⟨hState, hValues⟩
      cases hValues
      have hSource :
          state'.source = source' := by
        simpa using congrArg State.source hState.symm
      have hTrace :
          state'.trace = state.trace := by
        simpa using congrArg State.trace hState.symm
      exact ⟨by simpa [hSource] using hPrim, hTrace⟩

@[simp] theorem evalValues_gas_cons (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    evalValues fuel.succ.succ
        (.Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])
        codeOverride
        { source := source,
          trace := { kind := .gas, value := value } :: trace } =
      .ok ({ source := source, trace := trace }, [value]) := by
  simp [evalValues, primitiveSemantics,
    Yul.Source.Effectful.evalValues, Yul.Source.Effectful.evalArgs,
    primCall, consume]

@[simp] theorem evalValues_msize_cons (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (source : EvmYul.Yul.State) (value : Word) (trace : Trace) :
    evalValues fuel.succ.succ
        (.Call (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])
        codeOverride
        { source := source,
          trace := { kind := .msize, value := value } :: trace } =
      .ok ({ source := source, trace := trace }, [value]) := by
  simp [evalValues, primitiveSemantics,
    Yul.Source.Effectful.evalValues, Yul.Source.Effectful.evalArgs,
    primCall, consume]

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
        { source := source,
          trace := { kind := .gas, value := value } :: trace } =
      .ok ({ source := source.multifill [name] [value], trace := trace }) := by
  simp [exec, hDecl, primitiveSemantics, stateModel, State.withSource,
    Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
    Yul.Source.Effectful.StateModel.multifill, primCall, consume]

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
        { source := source,
          trace := { kind := .msize, value := value } :: trace } =
      .ok ({ source := source.multifill [name] [value], trace := trace }) := by
  simp [exec, hDecl, primitiveSemantics, stateModel, State.withSource,
    Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
    Yul.Source.Effectful.StateModel.multifill, primCall, consume]

inductive Result where
  | regular (state : State)
  | yulHalt (source : EvmYul.Yul.State) (value : Word)
  | revert (sourceBeforeRevert : EvmYul.Yul.State)

namespace Program

def installContract (program : Yul.Program) (state : State) : State :=
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

@[simp] theorem installContract_trace
    (program : Yul.Program) (state : State) :
    (installContract program state).trace = state.trace := rfl

def run (fuel : Nat) (program : Yul.Program)
    (source : EvmYul.Yul.State) (trace : Trace) :
    Except EvmYul.Yul.Exception Result :=
  match
      callDispatcher fuel (some program.contract)
        (installContract program { source := source, trace := trace }) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error (.YulHalt source' value) => .ok (.yulHalt source' value)
  | .error (.Revert sourceBeforeRevert) =>
      .ok (.revert sourceBeforeRevert)
  | .error err => .error err

end Program
end SourceReplay

namespace PublicArtifact

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
