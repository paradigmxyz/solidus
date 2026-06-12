import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Assembly

/--
Resource observers whose source value is allowed to be supplied by a replay
oracle instead of by the ordinary source state.

`gas` and `msize` are the two current nullary EVM/Yul observers whose exact
values can be changed by compiler-inserted code or private scratch allocation.
-/
inductive ResourceObserver where
  | gas
  | msize
  deriving DecidableEq, Repr

structure ResourceObservation where
  kind : ResourceObserver
  value : Word
  deriving DecidableEq, Repr

abbrev ResourceTrace := List ResourceObservation

namespace ResourceObserver

def ofPrimOp? : PrimOp → Option ResourceObserver
  | .gas => some .gas
  | .msize => some .msize
  | _ => none

def ofTargetInstr? : TargetInstr → Option ResourceObserver
  | .prim op => ofPrimOp? op
  | .push32 _ | .jump | .jumpi | .jumpdest => none

def ofInstr? : Instr → Option ResourceObserver
  | .prim op => ofPrimOp? op
  | .label _ | .push _ | .jump _ | .jumpi _ => none

def recordFromPostState (kind : ResourceObserver) (state : EVMState) :
    ResourceTrace :=
  match state.stack with
  | value :: _ => [{ kind := kind, value := value }]
  | [] => []

def consume (kind : ResourceObserver) : ResourceTrace →
    Except EVMException (Word × ResourceTrace)
  | [] => .error .InvalidInstruction
  | observation :: rest =>
      if observation.kind = kind then
        .ok (observation.value, rest)
      else
        .error .InvalidInstruction

def overwriteTop (value : Word) (state : EVMState) :
    Except EVMException EVMState :=
  match state.stack with
  | _ :: rest => .ok { state with stack := value :: rest }
  | [] => .error .StackUnderflow

theorem overwriteTop_pc
    {value : Word} {state state' : EVMState}
    (hOverwrite : overwriteTop value state = .ok state') :
    state'.pc = state.pc := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil =>
          simp [overwriteTop] at hOverwrite
      | cons top rest =>
          simp [overwriteTop] at hOverwrite
          cases hOverwrite
          rfl

theorem overwriteTop_stack_length
    {value : Word} {state state' : EVMState}
    (hOverwrite : overwriteTop value state = .ok state') :
    state'.stack.length = state.stack.length := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil =>
          simp [overwriteTop] at hOverwrite
      | cons top rest =>
          simp [overwriteTop] at hOverwrite
          cases hOverwrite
          rfl

def applyOracleFromPostState (kind : ResourceObserver) (state : EVMState)
    (trace : ResourceTrace) :
    Except EVMException (EVMState × ResourceTrace) := do
  let (value, rest) ← consume kind trace
  let state' ← overwriteTop value state
  .ok (state', rest)

theorem applyOracleFromPostState_pc
    {kind : ResourceObserver} {state state' : EVMState}
    {trace trace' : ResourceTrace}
    (hApply :
      applyOracleFromPostState kind state trace = .ok (state', trace')) :
    state'.pc = state.pc := by
  unfold applyOracleFromPostState at hApply
  cases hConsume : consume kind trace with
  | error err =>
      simp [hConsume, Bind.bind, Except.bind] at hApply
  | ok consumed =>
      rcases consumed with ⟨value, rest⟩
      simp [hConsume, Bind.bind, Except.bind] at hApply
      cases hOverwrite : overwriteTop value state with
      | error err =>
          simp [hOverwrite] at hApply
      | ok stateMid =>
          simp [hOverwrite] at hApply
          rcases hApply with ⟨hState, _hTrace⟩
          subst state'
          exact overwriteTop_pc hOverwrite

theorem applyOracleFromPostState_stack_length
    {kind : ResourceObserver} {state state' : EVMState}
    {trace trace' : ResourceTrace}
    (hApply :
      applyOracleFromPostState kind state trace = .ok (state', trace')) :
    state'.stack.length = state.stack.length := by
  unfold applyOracleFromPostState at hApply
  cases hConsume : consume kind trace with
  | error err =>
      simp [hConsume, Bind.bind, Except.bind] at hApply
  | ok consumed =>
      rcases consumed with ⟨value, rest⟩
      simp [hConsume, Bind.bind, Except.bind] at hApply
      cases hOverwrite : overwriteTop value state with
      | error err =>
          simp [hOverwrite] at hApply
      | ok stateMid =>
          simp [hOverwrite] at hApply
          rcases hApply with ⟨hState, _hTrace⟩
          subst state'
          exact overwriteTop_stack_length hOverwrite

def eraseRuntimeStateTrace
    (result : EVMState × ResourceTrace) :
    EVMState × ResourceTrace :=
  (eraseRuntimeControl result.1, result.2)

theorem applyOracleFromPostState_map_eraseRuntimeControl
    {kind : ResourceObserver} {target source : EVMState}
    {trace : ResourceTrace}
    (hRel : SameRuntimeData target source) :
    (applyOracleFromPostState kind target trace).map
        eraseRuntimeStateTrace =
      (applyOracleFromPostState kind source trace).map
        eraseRuntimeStateTrace := by
  cases target with
  | mk targetShared targetPc targetStack targetExec =>
      cases source with
      | mk sourceShared sourcePc sourceStack sourceExec =>
          simp [SameRuntimeData, eraseRuntimeControl] at hRel
          rcases hRel with ⟨rfl, rfl⟩
          cases trace with
          | nil =>
              simp [applyOracleFromPostState, consume,
                eraseRuntimeStateTrace, Bind.bind, Except.bind, Except.map]
          | cons observation rest =>
              rcases observation with ⟨observedKind, value⟩
              by_cases hKind : observedKind = kind
              · subst observedKind
                cases targetStack with
                | nil =>
                    simp [applyOracleFromPostState, consume, overwriteTop,
                      eraseRuntimeStateTrace, Bind.bind, Except.bind,
                      Except.map]
                | cons head tail =>
                    simp [applyOracleFromPostState, consume, overwriteTop,
                      eraseRuntimeStateTrace, eraseRuntimeControl,
                      Bind.bind, Except.bind, Except.map]
              · simp [applyOracleFromPostState, consume, hKind,
                  eraseRuntimeStateTrace, Bind.bind, Except.bind, Except.map]

theorem applyOracleFromPostState_recordFromPostState_append
    {kind : ResourceObserver} {state : EVMState}
    {rest : ResourceTrace} {value : Word} {stack : EvmYul.Stack Word}
    (hStack : state.stack = value :: stack) :
    applyOracleFromPostState kind state
        (recordFromPostState kind state ++ rest) =
      .ok (state, rest) := by
  cases state with
  | mk shared pc stateStack execLength =>
      change stateStack = value :: stack at hStack
      rw [hStack]
      simp [recordFromPostState, applyOracleFromPostState, consume,
        overwriteTop, Bind.bind, Except.bind]

end ResourceObserver

namespace StepResult

def state : StepResult → EVMState
  | .running state => state
  | .halted halt => halt.state

def withState : StepResult → EVMState → StepResult
  | .running _, state => .running state
  | .halted halt, state =>
      .halted { halt with state := state, output := halt.kind.output state }

end StepResult

namespace Target

def stepInstrResultWithObservers (instr : TargetInstr) (state : EVMState) :
    Except EVMException (StepResult × ResourceTrace) :=
  match stepInstrResult instr state with
  | .error err => .error err
  | .ok result =>
      let trace :=
        match ResourceObserver.ofTargetInstr? instr with
        | some kind => ResourceObserver.recordFromPostState kind result.state
        | none => []
      .ok (result, trace)

def stepInstrResultWithOracle (instr : TargetInstr) (state : EVMState)
    (trace : ResourceTrace) :
    Except EVMException (StepResult × ResourceTrace) :=
  match stepInstrResult instr state with
  | .error err => .error err
  | .ok result =>
      match ResourceObserver.ofTargetInstr? instr with
      | some kind =>
          match ResourceObserver.applyOracleFromPostState kind result.state trace with
          | .ok (state', trace') => .ok (result.withState state', trace')
          | .error err => .error err
      | none => .ok (result, trace)

def runListResultWithObservers :
    List TargetInstr → EVMState →
      Except EVMException (StepResult × ResourceTrace)
  | [], state => .ok (.running state, [])
  | instr :: rest, state =>
      match stepInstrResultWithObservers instr state with
      | .error err => .error err
      | .ok (result, headTrace) =>
          match result with
          | .running state' =>
              match runListResultWithObservers rest state' with
              | .error err => .error err
              | .ok (tailResult, tailTrace) =>
                  .ok (tailResult, headTrace ++ tailTrace)
          | .halted halt =>
              .ok (.halted halt, headTrace)

def runListResultWithOracle :
    List TargetInstr → EVMState → ResourceTrace →
      Except EVMException (StepResult × ResourceTrace)
  | [], state, trace => .ok (.running state, trace)
  | instr :: rest, state, trace =>
      match stepInstrResultWithOracle instr state trace with
      | .error err => .error err
      | .ok (result, trace') =>
          match result with
          | .running state' =>
              runListResultWithOracle rest state' trace'
          | .halted halt =>
              .ok (.halted halt, trace')

def runNResultWithObservers (target : TargetProgram) :
    Nat → EVMState → Except EVMException (StepResult × ResourceTrace)
  | 0, state => .ok (.running state, [])
  | fuel + 1, state =>
      match target.fetch state.pc.toNat with
      | none => .error .InvalidInstruction
      | some instr =>
          match stepInstrResultWithObservers instr state with
          | .error err => .error err
          | .ok (result, headTrace) =>
              match result with
              | .running state' =>
                  match runNResultWithObservers target fuel state' with
                  | .error err => .error err
                  | .ok (tailResult, tailTrace) =>
                      .ok (tailResult, headTrace ++ tailTrace)
              | .halted halt =>
                  .ok (.halted halt, headTrace)

def runNResultWithOracle (target : TargetProgram) :
    Nat → EVMState → ResourceTrace →
      Except EVMException (StepResult × ResourceTrace)
  | 0, state, trace => .ok (.running state, trace)
  | fuel + 1, state, trace =>
      match target.fetch state.pc.toNat with
      | none => .error .InvalidInstruction
      | some instr =>
          match stepInstrResultWithOracle instr state trace with
          | .error err => .error err
          | .ok (result, trace') =>
              match result with
              | .running state' =>
                  runNResultWithOracle target fuel state' trace'
              | .halted halt =>
                  .ok (.halted halt, trace')

theorem stepInstrResultWithObservers_sound
    {instr : TargetInstr} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      stepInstrResultWithObservers instr state = .ok (result, trace)) :
    stepInstrResult instr state = .ok result := by
  unfold stepInstrResultWithObservers at hRun
  cases hStep : stepInstrResult instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
      | ok stepResult =>
          rw [hStep] at hRun
          cases hRun
          rfl

theorem runListResultWithObservers_sound
    {code : List TargetInstr} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      runListResultWithObservers code state = .ok (result, trace)) :
    runListResult code state = .ok result := by
  induction code generalizing state result trace with
  | nil =>
      simp [runListResultWithObservers] at hRun
      rcases hRun with ⟨hResult, _hTrace⟩
      simp [runListResult, hResult.symm]
  | cons instr rest ih =>
      unfold runListResultWithObservers at hRun
      cases hStep : stepInstrResultWithObservers instr state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, headTrace⟩
          rw [hStep] at hRun
          have hPlainStep :
              stepInstrResult instr state = .ok stepResult :=
            stepInstrResultWithObservers_sound hStep
          unfold runListResult
          rw [hPlainStep]
          cases stepResult with
          | running state' =>
              cases hTail :
                  runListResultWithObservers rest state' with
              | error err =>
                  simp [hTail] at hRun
              | ok tailPair =>
                  rcases tailPair with ⟨tailResult, tailTrace⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨hResult, _hTrace⟩
                  cases hResult
                  exact ih hTail
          | halted halt =>
              cases hRun
              rfl

theorem runNResultWithObservers_sound
    {target : TargetProgram} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      runNResultWithObservers target fuel state = .ok (result, trace)) :
    runNResult target fuel state = .ok result := by
  induction fuel generalizing state result trace with
  | zero =>
      simp [runNResultWithObservers] at hRun
      rcases hRun with ⟨hResult, _hTrace⟩
      simp [runNResult, hResult.symm]
  | succ fuel ih =>
      unfold runNResultWithObservers at hRun
      cases hFetch : target.fetch state.pc.toNat with
      | none =>
          simp [hFetch] at hRun
      | some instr =>
          simp [hFetch] at hRun
          cases hStep : stepInstrResultWithObservers instr state with
          | error err =>
              rw [hStep] at hRun
              cases hRun
          | ok stepPair =>
              rcases stepPair with ⟨stepResult, headTrace⟩
              rw [hStep] at hRun
              have hPlainStep :
                  stepInstrResult instr state = .ok stepResult :=
                stepInstrResultWithObservers_sound hStep
              cases stepResult with
              | running state' =>
                  cases hTail :
                      runNResultWithObservers target fuel state' with
                  | error err =>
                      simp [hTail] at hRun
                  | ok tailPair =>
                      rcases tailPair with ⟨tailResult, tailTrace⟩
                      simp [hTail] at hRun
                      rcases hRun with ⟨hResult, _hTrace⟩
                      cases hResult
                      simpa [runNResult, Target.stepResult, hFetch, hPlainStep]
                        using ih hTail
              | halted halt =>
                  cases hRun
                  have hTargetStep :
                      Target.stepResult target state =
                        .ok (StepResult.halted halt) := by
                    simp [Target.stepResult, hFetch, hPlainStep]
                  unfold runNResult
                  rw [hTargetStep]
                  rfl

theorem stepInstrResult_observer_running_stack
    {instr : TargetInstr} {state : EVMState} {result : StepResult}
    {kind : ResourceObserver}
    (hObserver : ResourceObserver.ofTargetInstr? instr = some kind)
    (hStep : stepInstrResult instr state = .ok result) :
    ∃ post value stack,
      result = .running post ∧ post.stack = value :: stack := by
  cases instr with
  | push32 _value =>
      simp [ResourceObserver.ofTargetInstr?] at hObserver
  | jump =>
      simp [ResourceObserver.ofTargetInstr?] at hObserver
  | jumpi =>
      simp [ResourceObserver.ofTargetInstr?] at hObserver
  | jumpdest =>
      simp [ResourceObserver.ofTargetInstr?] at hObserver
  | prim op =>
      cases op <;>
        simp [ResourceObserver.ofTargetInstr?, ResourceObserver.ofPrimOp?]
          at hObserver
      · unfold stepInstrResult at hStep
        change
          (do
            let state' ←
              EvmYul.EVM.machineStateOp EvmYul.MachineState.msize state
            match (TargetInstr.prim PrimOp.msize).haltKind? with
            | some kind =>
                Except.ok
                  (StepResult.halted
                    { kind := kind, state := state',
                      output := kind.output state' })
            | none => Except.ok (StepResult.running state')) =
            .ok result at hStep
        simp [EvmYul.EVM.machineStateOp, Id.run,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hStep
        cases hStep
        exact
          ⟨state.replaceStackAndIncrPC
              (state.stack.push (EvmYul.MachineState.msize state.toMachineState)),
            EvmYul.MachineState.msize state.toMachineState, state.stack,
            rfl, rfl⟩
      · unfold stepInstrResult at hStep
        change
          (do
            let state' ←
              EvmYul.EVM.machineStateOp EvmYul.MachineState.gas state
            match (TargetInstr.prim PrimOp.gas).haltKind? with
            | some kind =>
                Except.ok
                  (StepResult.halted
                    { kind := kind, state := state',
                      output := kind.output state' })
            | none => Except.ok (StepResult.running state')) =
            .ok result at hStep
        simp [EvmYul.EVM.machineStateOp, Id.run,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          EvmYul.MachineState.gas] at hStep
        cases hStep
        exact
          ⟨state.replaceStackAndIncrPC
              (state.stack.push (EvmYul.MachineState.gas state.toMachineState)),
            EvmYul.MachineState.gas state.toMachineState, state.stack,
            rfl, rfl⟩

theorem stepInstrResultWithOracle_of_withObservers
    {instr : TargetInstr} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun :
      stepInstrResultWithObservers instr state = .ok (result, trace)) :
    stepInstrResultWithOracle instr state (trace ++ rest) =
      .ok (result, rest) := by
  unfold stepInstrResultWithObservers at hRun
  unfold stepInstrResultWithOracle
  cases hStep : stepInstrResult instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
  | ok plainResult =>
      simp [hStep] at hRun ⊢
      cases hObserver : ResourceObserver.ofTargetInstr? instr with
      | none =>
          simp [hObserver] at hRun ⊢
          rcases hRun with ⟨hResult, hTrace⟩
          cases hResult
          cases hTrace
          exact ⟨rfl, rfl⟩
      | some kind =>
          simp [hObserver] at hRun ⊢
          rcases hRun with ⟨hResult, hTrace⟩
          cases hResult
          cases hTrace
          rcases stepInstrResult_observer_running_stack hObserver hStep with
            ⟨post, value, stack, hPlain, hStack⟩
          cases hPlain
          change
            (match
              ResourceObserver.applyOracleFromPostState kind post
                (ResourceObserver.recordFromPostState kind post ++ rest) with
            | Except.ok (state', trace') =>
                Except.ok (StepResult.withState (.running post) state', trace')
            | Except.error err => Except.error err) =
              Except.ok (.running post, rest)
          rw [ResourceObserver.applyOracleFromPostState_recordFromPostState_append
            (kind := kind) (state := post) (rest := rest)
            (value := value) (stack := stack) hStack]
          rfl

theorem runListResultWithOracle_of_withObservers
    {code : List TargetInstr} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun :
      runListResultWithObservers code state = .ok (result, trace)) :
    runListResultWithOracle code state (trace ++ rest) =
      .ok (result, rest) := by
  induction code generalizing state result trace rest with
  | nil =>
      simp [runListResultWithObservers] at hRun
      rcases hRun with ⟨hResult, hTrace⟩
      cases hResult
      cases hTrace
      simp [runListResultWithOracle]
  | cons instr code ih =>
      unfold runListResultWithObservers at hRun
      cases hStep :
          stepInstrResultWithObservers instr state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, headTrace⟩
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              cases hTail :
                  runListResultWithObservers code mid with
              | error err =>
                  simp [hTail] at hRun
              | ok tailPair =>
                  rcases tailPair with ⟨tailResult, tailTrace⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨hResult, hTrace⟩
                  cases hResult
                  cases hTrace
                  have hStepOracle :=
                    stepInstrResultWithOracle_of_withObservers
                      (rest := tailTrace ++ rest) hStep
                  unfold runListResultWithOracle
                  rw [show headTrace ++ tailTrace ++ rest =
                      headTrace ++ (tailTrace ++ rest) by
                    simp [List.append_assoc]]
                  rw [hStepOracle]
                  exact ih hTail
          | halted halt =>
              cases hRun
              have hStepOracle :=
                stepInstrResultWithOracle_of_withObservers
                  (rest := rest) hStep
              unfold runListResultWithOracle
              rw [hStepOracle]

theorem runNResultWithOracle_of_withObservers
    {target : TargetProgram} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun :
      runNResultWithObservers target fuel state = .ok (result, trace)) :
    runNResultWithOracle target fuel state (trace ++ rest) =
      .ok (result, rest) := by
  induction fuel generalizing state result trace rest with
  | zero =>
      simp [runNResultWithObservers] at hRun
      rcases hRun with ⟨hResult, hTrace⟩
      cases hResult
      cases hTrace
      simp [runNResultWithOracle]
  | succ fuel ih =>
      unfold runNResultWithObservers at hRun
      cases hFetch : target.fetch state.pc.toNat with
      | none =>
          simp [hFetch] at hRun
      | some instr =>
          simp [hFetch] at hRun
          cases hStep :
              stepInstrResultWithObservers instr state with
          | error err =>
              rw [hStep] at hRun
              cases hRun
          | ok stepPair =>
              rcases stepPair with ⟨stepResult, headTrace⟩
              rw [hStep] at hRun
              cases stepResult with
              | running mid =>
                  cases hTail :
                      runNResultWithObservers target fuel mid with
                  | error err =>
                      simp [hTail] at hRun
                  | ok tailPair =>
                      rcases tailPair with ⟨tailResult, tailTrace⟩
                      simp [hTail] at hRun
                      rcases hRun with ⟨hResult, hTrace⟩
                      cases hResult
                      cases hTrace
                      have hStepOracle :=
                        stepInstrResultWithOracle_of_withObservers
                          (rest := tailTrace ++ rest) hStep
                      unfold runNResultWithOracle
                      simp [hFetch]
                      rw [hStepOracle]
                      exact ih hTail
              | halted halt =>
                  cases hRun
                  have hStepOracle :=
                    stepInstrResultWithOracle_of_withObservers
                      (rest := rest) hStep
                  unfold runNResultWithOracle
                  simp [hFetch]
                  rw [hStepOracle]

theorem runNResultWithOracle_running_bind
    {target : TargetProgram} {fuel₁ fuel₂ : Nat}
    {state mid : EVMState} {trace traceMid traceOut : ResourceTrace}
    {result : StepResult}
    (hHead :
      runNResultWithOracle target fuel₁ state trace =
        .ok (.running mid, traceMid))
    (hTail :
      runNResultWithOracle target fuel₂ mid traceMid =
        .ok (result, traceOut)) :
    runNResultWithOracle target (fuel₁ + fuel₂) state trace =
      .ok (result, traceOut) := by
  induction fuel₁ generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hHead
      rcases hHead with ⟨hMid, hTraceMid⟩
      subst mid
      subst traceMid
      simpa using hTail
  | succ fuel ih =>
      unfold runNResultWithOracle at hHead
      have hFuel :
          fuel + 1 + fuel₂ = (fuel + fuel₂) + 1 := by
        omega
      rw [hFuel]
      unfold runNResultWithOracle
      cases hFetch : target.fetch state.pc.toNat with
      | none =>
          simp [hFetch] at hHead
      | some instr =>
          simp [hFetch] at hHead ⊢
          cases hStep : stepInstrResultWithOracle instr state trace with
          | error err =>
              simp [hStep] at hHead
          | ok stepPair =>
              rcases stepPair with ⟨stepResult, traceAfterHead⟩
              simp [hStep] at hHead ⊢
              cases stepResult with
              | running stateAfterHead =>
                  exact ih hHead
              | halted halt =>
                  cases hHead

theorem runNResultWithOracle_halted_add
    {target : TargetProgram} {fuel extra : Nat}
    {state : EVMState} {trace traceOut : ResourceTrace}
    {halt : Halt}
    (hRun :
      runNResultWithOracle target fuel state trace =
        .ok (.halted halt, traceOut)) :
    runNResultWithOracle target (fuel + extra) state trace =
      .ok (.halted halt, traceOut) := by
  induction fuel generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hRun
  | succ fuel ih =>
      unfold runNResultWithOracle at hRun
      have hFuel :
          fuel + 1 + extra = (fuel + extra) + 1 := by
        omega
      rw [hFuel]
      unfold runNResultWithOracle
      cases hFetch : target.fetch state.pc.toNat with
      | none =>
          simp [hFetch] at hRun
      | some instr =>
          simp [hFetch] at hRun ⊢
          cases hStep : stepInstrResultWithOracle instr state trace with
          | error err =>
              simp [hStep] at hRun
          | ok stepPair =>
              rcases stepPair with ⟨stepResult, traceAfterHead⟩
              simp [hStep] at hRun ⊢
              cases stepResult with
              | running stateAfterHead =>
                  exact ih hRun
              | halted halt' =>
                  cases hRun
                  rfl

theorem runNResultWithOracle_add_of_running
    {target : TargetProgram} {first second : Nat}
    {state mid : EVMState} {trace traceMid : ResourceTrace}
    (hRun :
      runNResultWithOracle target first state trace =
        .ok (.running mid, traceMid)) :
    runNResultWithOracle target (first + second) state trace =
      runNResultWithOracle target second mid traceMid := by
  induction first generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hRun
      rcases hRun with ⟨hMid, hTrace⟩
      subst mid
      subst traceMid
      simp
  | succ first ih =>
      unfold runNResultWithOracle at hRun
      have hFuel :
          first + 1 + second = (first + second) + 1 := by
        omega
      rw [hFuel]
      rw [runNResultWithOracle]
      cases hFetch : target.fetch state.pc.toNat with
      | none =>
          simp [hFetch] at hRun
      | some instr =>
          simp [hFetch] at hRun ⊢
          cases hStep : stepInstrResultWithOracle instr state trace with
          | error err =>
              simp [hStep] at hRun
          | ok stepPair =>
              rcases stepPair with ⟨stepResult, traceAfterHead⟩
              simp [hStep] at hRun ⊢
              cases stepResult with
              | running stateAfterHead =>
                  exact ih hRun
              | halted halt =>
                  cases hRun

theorem runNResultWithOracle_add_of_error
    {target : TargetProgram} {first second : Nat}
    {state : EVMState} {trace : ResourceTrace} {err : EVMException}
    (hRun :
      runNResultWithOracle target first state trace = .error err) :
    runNResultWithOracle target (first + second) state trace =
      .error err := by
  induction first generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hRun
  | succ first ih =>
      unfold runNResultWithOracle at hRun
      have hFuel :
          first + 1 + second = (first + second) + 1 := by
        omega
      rw [hFuel]
      rw [runNResultWithOracle]
      cases hFetch : target.fetch state.pc.toNat with
      | none =>
          simp [hFetch] at hRun ⊢
          exact hRun
      | some instr =>
          simp [hFetch] at hRun ⊢
          cases hStep : stepInstrResultWithOracle instr state trace with
          | error stepErr =>
              simp [hStep] at hRun ⊢
              exact hRun
          | ok stepPair =>
              rcases stepPair with ⟨stepResult, traceAfterHead⟩
              simp [hStep] at hRun ⊢
              cases stepResult with
              | running stateAfterHead =>
                  exact ih hRun
              | halted halt =>
                  cases hRun

theorem runNResultWithOracle_add
    (target : TargetProgram) (first second : Nat)
    (state : EVMState) (trace : ResourceTrace) :
    runNResultWithOracle target (first + second) state trace =
      match runNResultWithOracle target first state trace with
      | .error err => .error err
      | .ok (.running mid, traceMid) =>
          runNResultWithOracle target second mid traceMid
      | .ok (.halted halt, traceOut) =>
          .ok (.halted halt, traceOut) := by
  cases hFirst : runNResultWithOracle target first state trace with
  | error err =>
      rw [runNResultWithOracle_add_of_error hFirst]
  | ok firstPair =>
      rcases firstPair with ⟨firstResult, traceAfterFirst⟩
      cases firstResult with
      | running mid =>
          rw [runNResultWithOracle_add_of_running hFirst]
      | halted halt =>
          rw [runNResultWithOracle_halted_add hFirst]

end Target

namespace Source

def stepAtResultWithObservers (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) : Except EVMException (StepResult × ResourceTrace) :=
  match stepAtResult program pc instr state with
  | .error err => .error err
  | .ok result =>
      let trace :=
        match ResourceObserver.ofInstr? instr with
        | some kind => ResourceObserver.recordFromPostState kind result.state
        | none => []
      .ok (result, trace)

def stepResultWithObservers (program : Program) (state : EVMState) :
    Except EVMException (StepResult × ResourceTrace) :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => stepAtResultWithObservers program pc instr state
  | none => .error .InvalidInstruction

def runNResultWithObservers (program : Program) :
    Nat → EVMState → Except EVMException (StepResult × ResourceTrace)
  | 0, state => .ok (.running state, [])
  | fuel + 1, state =>
      match stepResultWithObservers program state with
      | .error err => .error err
      | .ok (result, headTrace) =>
          match result with
          | .running state' =>
              match runNResultWithObservers program fuel state' with
              | .error err => .error err
              | .ok (tailResult, tailTrace) =>
                  .ok (tailResult, headTrace ++ tailTrace)
          | .halted halt =>
              .ok (.halted halt, headTrace)

def stepAtResultWithOracle (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) (trace : ResourceTrace) :
    Except EVMException (StepResult × ResourceTrace) :=
  match stepAtResult program pc instr state with
  | .error err => .error err
  | .ok result =>
      match ResourceObserver.ofInstr? instr with
      | some kind =>
          match ResourceObserver.applyOracleFromPostState kind result.state trace with
          | .ok (state', trace') => .ok (result.withState state', trace')
          | .error err => .error err
      | none => .ok (result, trace)

def stepResultWithOracle (program : Program) (state : EVMState)
    (trace : ResourceTrace) :
    Except EVMException (StepResult × ResourceTrace) :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => stepAtResultWithOracle program pc instr state trace
  | none => .error .InvalidInstruction

def runNResultWithOracle (program : Program) :
    Nat → EVMState → ResourceTrace →
      Except EVMException (StepResult × ResourceTrace)
  | 0, state, trace => .ok (.running state, trace)
  | fuel + 1, state, trace =>
      match stepResultWithOracle program state trace with
      | .error err => .error err
      | .ok (result, trace') =>
          match result with
          | .running state' =>
              runNResultWithOracle program fuel state' trace'
          | .halted halt =>
              .ok (.halted halt, trace')

theorem stepAtResultWithOracle_of_observer_none
    {program : Program} {pc : Nat} {instr : Instr}
    {state : EVMState} {trace : ResourceTrace}
    (hObserver : ResourceObserver.ofInstr? instr = none) :
    stepAtResultWithOracle program pc instr state trace =
      (stepAtResult program pc instr state).map
        (fun result => (result, trace)) := by
  unfold stepAtResultWithOracle
  rw [hObserver]
  cases stepAtResult program pc instr state <;> rfl

theorem stepResultWithOracle_at_boundary
    {pre post : Program} {instr : Instr}
    {state : EVMState} {trace : ResourceTrace}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    stepResultWithOracle (pre ++ instr :: post) state trace =
      stepAtResultWithOracle (pre ++ instr :: post)
        pre.byteLength instr state trace := by
  unfold stepResultWithOracle
  have hAt :
      Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  rw [hAt]

theorem runNResultWithOracle_one_at_boundary
    {pre post : Program} {instr : Instr}
    {state : EVMState} {trace : ResourceTrace}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    runNResultWithOracle (pre ++ instr :: post) 1 state trace =
      stepAtResultWithOracle (pre ++ instr :: post)
        pre.byteLength instr state trace := by
  unfold runNResultWithOracle
  rw [stepResultWithOracle_at_boundary hFits hPc]
  cases hStep :
      stepAtResultWithOracle (pre ++ instr :: post)
        pre.byteLength instr state trace with
  | error err =>
      simp only [Bind.bind, Except.bind]
  | ok pair =>
      rcases pair with ⟨result, trace'⟩
      cases result <;>
        simp only [Bind.bind, Except.bind, runNResultWithOracle]

theorem runNResultWithOracle_one_at_boundary_append
    {pre post : Program} {instr : Instr}
    {state : EVMState} {trace : ResourceTrace}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    runNResultWithOracle (pre ++ ([instr] ++ post)) 1 state trace =
      stepAtResultWithOracle (pre ++ ([instr] ++ post))
        pre.byteLength instr state trace := by
  simpa [List.append_assoc] using
    runNResultWithOracle_one_at_boundary
      (pre := pre) (post := post) (instr := instr)
      (state := state) (trace := trace) hFits hPc

theorem stepAtResultWithOracle_running_plain_pc
    {program : Program} {pc : Nat} {instr : Instr}
    {state final : EVMState} {trace trace' : ResourceTrace}
    (hRun :
      stepAtResultWithOracle program pc instr state trace =
        .ok (.running final, trace')) :
    ∃ plain,
      stepAtResult program pc instr state = .ok (.running plain) ∧
        final.pc = plain.pc := by
  unfold stepAtResultWithOracle at hRun
  cases hPlain : stepAtResult program pc instr state with
  | error err =>
      simp [hPlain] at hRun
  | ok plainResult =>
      simp [hPlain] at hRun
      cases plainResult with
      | halted halt =>
          cases hObserver : ResourceObserver.ofInstr? instr with
          | none =>
              simp [hObserver] at hRun
          | some kind =>
              simp [hObserver] at hRun
              simp only [StepResult.state, StepResult.withState] at hRun
              cases hApply :
                  ResourceObserver.applyOracleFromPostState kind halt.state
                    trace with
              | error err =>
                  rw [hApply] at hRun
                  cases hRun
              | ok pair =>
                  rcases pair with ⟨oracleState, oracleTrace⟩
                  rw [hApply] at hRun
                  cases hRun
      | running plain =>
          cases hObserver : ResourceObserver.ofInstr? instr with
          | none =>
              simp [hObserver] at hRun
              rcases hRun with ⟨hFinal, _hTrace⟩
              subst final
              exact ⟨plain, by simpa only using hPlain, rfl⟩
          | some kind =>
              simp [hObserver] at hRun
              simp only [StepResult.state, StepResult.withState] at hRun
              cases hApply :
                  ResourceObserver.applyOracleFromPostState kind plain trace with
              | error err =>
                  rw [hApply] at hRun
                  cases hRun
              | ok pair =>
                  rcases pair with ⟨oracleState, oracleTrace⟩
                  rw [hApply] at hRun
                  cases hRun
                  exact
                    ⟨plain, by simpa only using hPlain,
                      ResourceObserver.applyOracleFromPostState_pc hApply⟩

theorem stepResultWithOracle_of_stepResult_observer_none
    {program : Program} {state : EVMState} {result : StepResult}
    {trace : ResourceTrace}
    (hStep : stepResult program state = .ok result)
    (hObserver :
      ∀ {pc : Nat} {instr : Instr},
        Program.instrAtPc program state.pc.toNat = some (pc, instr) →
          ResourceObserver.ofInstr? instr = none) :
    stepResultWithOracle program state trace = .ok (result, trace) := by
  unfold stepResult at hStep
  unfold stepResultWithOracle
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp [hAt] at hStep ⊢
      unfold stepAtResultWithOracle
      rw [hStep]
      simp [hObserver hAt]

theorem runNResultWithOracle_running_bind
    {program : Program} {fuel₁ fuel₂ : Nat}
    {state mid : EVMState} {trace traceMid traceOut : ResourceTrace}
    {result : StepResult}
    (hHead :
      runNResultWithOracle program fuel₁ state trace =
        .ok (.running mid, traceMid))
    (hTail :
      runNResultWithOracle program fuel₂ mid traceMid =
        .ok (result, traceOut)) :
    runNResultWithOracle program (fuel₁ + fuel₂) state trace =
      .ok (result, traceOut) := by
  induction fuel₁ generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hHead
      rcases hHead with ⟨hMid, hTraceMid⟩
      subst mid
      subst traceMid
      simpa using hTail
  | succ fuel ih =>
      unfold runNResultWithOracle at hHead
      have hFuel :
          fuel + 1 + fuel₂ = (fuel + fuel₂) + 1 := by
        omega
      rw [hFuel]
      unfold runNResultWithOracle
      cases hStep : stepResultWithOracle program state trace with
      | error err =>
          simp [hStep] at hHead
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, traceAfterHead⟩
          simp [hStep] at hHead ⊢
          cases stepResult with
          | running stateAfterHead =>
              exact ih hHead
          | halted halt =>
              cases hHead

theorem runNResultWithOracle_halted_add
    {program : Program} {fuel extra : Nat}
    {state : EVMState} {trace traceOut : ResourceTrace}
    {halt : Halt}
    (hRun :
      runNResultWithOracle program fuel state trace =
        .ok (.halted halt, traceOut)) :
    runNResultWithOracle program (fuel + extra) state trace =
      .ok (.halted halt, traceOut) := by
  induction fuel generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hRun
  | succ fuel ih =>
      unfold runNResultWithOracle at hRun
      have hFuel :
          fuel + 1 + extra = (fuel + extra) + 1 := by
        omega
      rw [hFuel]
      unfold runNResultWithOracle
      cases hStep : stepResultWithOracle program state trace with
      | error err =>
          simp [hStep] at hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, traceAfterHead⟩
          simp [hStep] at hRun ⊢
          cases stepResult with
          | running stateAfterHead =>
              exact ih hRun
          | halted halt' =>
              cases hRun
              rfl

theorem runNResultWithOracle_add_of_running
    {program : Program} {first second : Nat}
    {state mid : EVMState} {trace traceMid : ResourceTrace}
    (hRun :
      runNResultWithOracle program first state trace =
        .ok (.running mid, traceMid)) :
    runNResultWithOracle program (first + second) state trace =
      runNResultWithOracle program second mid traceMid := by
  induction first generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hRun
      rcases hRun with ⟨hMid, hTrace⟩
      subst mid
      subst traceMid
      simp
  | succ first ih =>
      unfold runNResultWithOracle at hRun
      have hFuel :
          first + 1 + second = (first + second) + 1 := by
        omega
      rw [hFuel]
      rw [runNResultWithOracle]
      cases hStep : stepResultWithOracle program state trace with
      | error err =>
          simp [hStep] at hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, traceAfterHead⟩
          simp [hStep] at hRun ⊢
          cases stepResult with
          | running stateAfterHead =>
              exact ih hRun
          | halted halt =>
              cases hRun

theorem runNResultWithOracle_add_of_error
    {program : Program} {first second : Nat}
    {state : EVMState} {trace : ResourceTrace} {err : EVMException}
    (hRun :
      runNResultWithOracle program first state trace = .error err) :
    runNResultWithOracle program (first + second) state trace =
      .error err := by
  induction first generalizing state trace with
  | zero =>
      simp [runNResultWithOracle] at hRun
  | succ first ih =>
      unfold runNResultWithOracle at hRun
      have hFuel :
          first + 1 + second = (first + second) + 1 := by
        omega
      rw [hFuel]
      rw [runNResultWithOracle]
      cases hStep : stepResultWithOracle program state trace with
      | error stepErr =>
          simp [hStep] at hRun ⊢
          exact hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, traceAfterHead⟩
          simp [hStep] at hRun ⊢
          cases stepResult with
          | running stateAfterHead =>
              exact ih hRun
          | halted halt =>
              cases hRun

theorem runNResultWithOracle_add
    (program : Program) (first second : Nat)
    (state : EVMState) (trace : ResourceTrace) :
    runNResultWithOracle program (first + second) state trace =
      match runNResultWithOracle program first state trace with
      | .error err => .error err
      | .ok (.running mid, traceMid) =>
          runNResultWithOracle program second mid traceMid
      | .ok (.halted halt, traceOut) =>
          .ok (.halted halt, traceOut) := by
  cases hFirst :
      runNResultWithOracle program first state trace with
  | error err =>
      rw [runNResultWithOracle_add_of_error hFirst]
  | ok firstPair =>
      rcases firstPair with ⟨firstResult, traceAfterFirst⟩
      cases firstResult with
      | running mid =>
          rw [runNResultWithOracle_add_of_running hFirst]
      | halted halt =>
          rw [runNResultWithOracle_halted_add hFirst]

abbrev OracleExecutionOutcome :=
  Except EVMException (StepResult × ResourceTrace)

theorem runNResultWithOracle_compare_halted
    {program : Program} {state : EVMState}
    {trace traceOut : ResourceTrace}
    {halt : Halt} {fullFuel prefixFuel : Nat}
    {prefixOutcome : OracleExecutionOutcome}
    (hFull :
      runNResultWithOracle program fullFuel state trace =
        .ok (.halted halt, traceOut))
    (hPrefix :
      runNResultWithOracle program prefixFuel state trace =
        prefixOutcome) :
    match prefixOutcome with
    | .error _ => False
    | .ok (.running _, _) => prefixFuel < fullFuel
    | .ok (.halted prefixHalt, prefixTrace) =>
        prefixHalt = halt ∧ prefixTrace = traceOut := by
  rcases Nat.le_total prefixFuel fullFuel with hLe | hLe
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hLe
    rw [runNResultWithOracle_add, hPrefix] at hFull
    cases prefixOutcome with
    | error err =>
        cases hFull
    | ok pair =>
        rcases pair with ⟨result, prefixTrace⟩
        cases result with
        | running mid =>
            by_cases hExtra : extra = 0
            · subst extra
              simp [runNResultWithOracle] at hFull
            · omega
        | halted prefixHalt =>
            simp at hFull
            exact ⟨hFull.1, hFull.2⟩
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hLe
    have hLong :=
      runNResultWithOracle_halted_add
        (extra := extra) hFull
    rw [hPrefix] at hLong
    cases prefixOutcome with
    | error err =>
        cases hLong
    | ok pair =>
        rcases pair with ⟨result, prefixTrace⟩
        cases result with
        | running mid =>
            cases hLong
        | halted prefixHalt =>
            cases hLong
            exact ⟨rfl, rfl⟩

def EventuallyWithOracle (program : Program) (state : EVMState)
    (trace : ResourceTrace)
    (post : OracleExecutionOutcome → Prop) : Prop :=
  ∃ fuel outcome,
    runNResultWithOracle program fuel state trace = outcome ∧
      post outcome

namespace EventuallyWithOracle

theorem pure {program : Program} {state : EVMState}
    {trace : ResourceTrace} {post : OracleExecutionOutcome → Prop}
    (hPost : post (.ok (.running state, trace))) :
    EventuallyWithOracle program state trace post := by
  exact
    ⟨0, .ok (.running state, trace),
      by simp [runNResultWithOracle], hPost⟩

theorem bind_running
    {program : Program} {state : EVMState}
    {trace : ResourceTrace}
    {middle : EVMState → ResourceTrace → Prop}
    {post : OracleExecutionOutcome → Prop}
    (hRun :
      EventuallyWithOracle program state trace
        (fun outcome =>
          match outcome with
          | .ok (.running mid, traceMid) => middle mid traceMid
          | _ => False))
    (hNext :
      ∀ mid traceMid, middle mid traceMid →
        EventuallyWithOracle program mid traceMid post) :
    EventuallyWithOracle program state trace post := by
  rcases hRun with ⟨firstFuel, firstOutcome, hFirst, hMiddle⟩
  cases firstOutcome with
  | error err =>
      cases hMiddle
  | ok pair =>
      rcases pair with ⟨result, traceMid⟩
      cases result with
      | halted halt =>
          cases hMiddle
      | running mid =>
          rcases hNext mid traceMid hMiddle with
            ⟨secondFuel, outcome, hSecond, hPost⟩
          exact
            ⟨firstFuel + secondFuel, outcome,
              (runNResultWithOracle_add_of_running hFirst).trans hSecond,
              hPost⟩

theorem mono {program : Program} {state : EVMState}
    {trace : ResourceTrace}
    {post₁ post₂ : OracleExecutionOutcome → Prop}
    (hRun : EventuallyWithOracle program state trace post₁)
    (hPost : ∀ outcome, post₁ outcome → post₂ outcome) :
    EventuallyWithOracle program state trace post₂ := by
  rcases hRun with ⟨fuel, outcome, hRun, hOutcome⟩
  exact ⟨fuel, outcome, hRun, hPost outcome hOutcome⟩

end EventuallyWithOracle

theorem stepAtResultWithObservers_sound
    {program : Program} {pc : Nat} {instr : Instr} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      stepAtResultWithObservers program pc instr state = .ok (result, trace)) :
    stepAtResult program pc instr state = .ok result := by
  unfold stepAtResultWithObservers at hRun
  cases hStep : stepAtResult program pc instr state with
  | error err =>
      simp [hStep] at hRun
  | ok stepResult =>
      simp [hStep] at hRun
      rcases hRun with ⟨hResult, _hTrace⟩
      cases hResult
      rfl

theorem stepResultWithObservers_sound
    {program : Program} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      stepResultWithObservers program state = .ok (result, trace)) :
    stepResult program state = .ok result := by
  unfold stepResultWithObservers at hRun
  unfold Source.stepResult
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hRun
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp [hAt] at hRun ⊢
      exact stepAtResultWithObservers_sound hRun

theorem runNResultWithObservers_sound
    {program : Program} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      runNResultWithObservers program fuel state = .ok (result, trace)) :
    runNResult program fuel state = .ok result := by
  induction fuel generalizing state result trace with
  | zero =>
      simp [runNResultWithObservers] at hRun
      rcases hRun with ⟨hResult, _hTrace⟩
      simp [runNResult, hResult.symm]
  | succ fuel ih =>
      unfold runNResultWithObservers at hRun
      cases hStep : stepResultWithObservers program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult', headTrace⟩
          rw [hStep] at hRun
          have hPlainStep :
              stepResult program state = .ok stepResult' :=
            stepResultWithObservers_sound hStep
          unfold runNResult
          rw [hPlainStep]
          cases stepResult' with
          | running state' =>
              cases hTail : runNResultWithObservers program fuel state' with
              | error err =>
                  simp [hTail] at hRun
              | ok tailPair =>
                  rcases tailPair with ⟨tailResult, tailTrace⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨hResult, _hTrace⟩
                  cases hResult
                  exact ih hTail
          | halted halt =>
              cases hRun
              rfl

theorem stepAtResult_observer_running_stack
    {program : Program} {pc : Nat} {instr : Instr} {state : EVMState}
    {result : StepResult} {kind : ResourceObserver}
    (hObserver : ResourceObserver.ofInstr? instr = some kind)
    (hStep : stepAtResult program pc instr state = .ok result) :
    ∃ post value stack,
      result = .running post ∧ post.stack = value :: stack := by
  cases instr with
  | label _ =>
      simp [ResourceObserver.ofInstr?] at hObserver
  | prim op =>
      have hTargetObserver :
          ResourceObserver.ofTargetInstr? (TargetInstr.prim op) = some kind := by
        simpa [ResourceObserver.ofInstr?, ResourceObserver.ofTargetInstr?]
          using hObserver
      have hTargetStep :
          Target.stepInstrResult (TargetInstr.prim op) state = .ok result := by
        simpa [stepAtResult, stepAt, Target.stepInstrResult,
          Instr.haltKind?, TargetInstr.haltKind?] using hStep
      exact
        Target.stepInstrResult_observer_running_stack
          hTargetObserver hTargetStep
  | push _ =>
      simp [ResourceObserver.ofInstr?] at hObserver
  | jump _ =>
      simp [ResourceObserver.ofInstr?] at hObserver
  | jumpi _ =>
      simp [ResourceObserver.ofInstr?] at hObserver

theorem stepAtResultWithOracle_of_withObservers
    {program : Program} {pc : Nat} {instr : Instr} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun :
      stepAtResultWithObservers program pc instr state =
        .ok (result, trace)) :
    stepAtResultWithOracle program pc instr state (trace ++ rest) =
      .ok (result, rest) := by
  unfold stepAtResultWithObservers at hRun
  unfold stepAtResultWithOracle
  cases hStep : stepAtResult program pc instr state with
  | error err =>
      simp [hStep] at hRun
  | ok plainResult =>
      simp [hStep] at hRun ⊢
      cases hObserver : ResourceObserver.ofInstr? instr with
      | none =>
          simp [hObserver] at hRun ⊢
          rcases hRun with ⟨hResult, hTrace⟩
          cases hResult
          cases hTrace
          exact ⟨rfl, rfl⟩
      | some kind =>
          simp [hObserver] at hRun ⊢
          rcases hRun with ⟨hResult, hTrace⟩
          cases hResult
          cases hTrace
          rcases stepAtResult_observer_running_stack hObserver hStep with
            ⟨post, value, stack, hPlain, hStack⟩
          cases hPlain
          change
            (match
              ResourceObserver.applyOracleFromPostState kind post
                (ResourceObserver.recordFromPostState kind post ++ rest) with
            | Except.ok (state', trace') =>
                Except.ok (StepResult.withState (.running post) state', trace')
            | Except.error err => Except.error err) =
              Except.ok (.running post, rest)
          rw [ResourceObserver.applyOracleFromPostState_recordFromPostState_append
            (kind := kind) (state := post) (rest := rest)
            (value := value) (stack := stack) hStack]
          rfl

theorem stepResultWithOracle_of_withObservers
    {program : Program} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun :
      stepResultWithObservers program state = .ok (result, trace)) :
    stepResultWithOracle program state (trace ++ rest) =
      .ok (result, rest) := by
  unfold stepResultWithObservers at hRun
  unfold stepResultWithOracle
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hRun
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp [hAt] at hRun ⊢
      exact stepAtResultWithOracle_of_withObservers hRun

theorem runNResultWithOracle_of_withObservers
    {program : Program} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun : runNResultWithObservers program fuel state = .ok (result, trace)) :
    runNResultWithOracle program fuel state (trace ++ rest) =
      .ok (result, rest) := by
  induction fuel generalizing state result trace rest with
  | zero =>
      simp [runNResultWithObservers] at hRun
      rcases hRun with ⟨hResult, hTrace⟩
      cases hResult
      cases hTrace
      simp [runNResultWithOracle]
  | succ fuel ih =>
      unfold runNResultWithObservers at hRun
      cases hStep : stepResultWithObservers program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult', headTrace⟩
          rw [hStep] at hRun
          cases stepResult' with
          | running mid =>
              cases hTail : runNResultWithObservers program fuel mid with
              | error err =>
                  simp [hTail] at hRun
              | ok tailPair =>
                  rcases tailPair with ⟨tailResult, tailTrace⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨hResult, hTrace⟩
                  cases hResult
                  cases hTrace
                  have hStepOracle :=
                    stepResultWithOracle_of_withObservers
                      (rest := tailTrace ++ rest) hStep
                  unfold runNResultWithOracle
                  rw [show headTrace ++ tailTrace ++ rest =
                      headTrace ++ (tailTrace ++ rest) by
                    simp [List.append_assoc]]
                  rw [hStepOracle]
                  exact ih hTail
          | halted halt =>
              cases hRun
              have hStepOracle :=
                stepResultWithOracle_of_withObservers
                  (rest := rest) hStep
              unfold runNResultWithOracle
              rw [hStepOracle]

end Source

namespace Compiled

def stepResultWithObservers (program : Program) (state : EVMState) :
    Except EVMException (StepResult × ResourceTrace) :=
  match emitCurrent? program state with
  | some code => Target.runListResultWithObservers code state
  | none => .error .InvalidInstruction

def runNResultWithObservers (program : Program) :
    Nat → EVMState → Except EVMException (StepResult × ResourceTrace)
  | 0, state => .ok (.running state, [])
  | fuel + 1, state =>
      match stepResultWithObservers program state with
      | .error err => .error err
      | .ok (result, headTrace) =>
          match result with
          | .running state' =>
              match runNResultWithObservers program fuel state' with
              | .error err => .error err
              | .ok (tailResult, tailTrace) =>
                  .ok (tailResult, headTrace ++ tailTrace)
          | .halted halt =>
              .ok (.halted halt, headTrace)

def stepResultWithOracle (program : Program) (state : EVMState)
    (trace : ResourceTrace) :
    Except EVMException (StepResult × ResourceTrace) :=
  match emitCurrent? program state with
  | some code => Target.runListResultWithOracle code state trace
  | none => .error .InvalidInstruction

def runNResultWithOracle (program : Program) :
    Nat → EVMState → ResourceTrace →
      Except EVMException (StepResult × ResourceTrace)
  | 0, state, trace => .ok (.running state, trace)
  | fuel + 1, state, trace =>
      match stepResultWithOracle program state trace with
      | .error err => .error err
      | .ok (result, trace') =>
          match result with
          | .running state' =>
              runNResultWithOracle program fuel state' trace'
          | .halted halt =>
              .ok (.halted halt, trace')

theorem stepResultWithObservers_sound
    {program : Program} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun : stepResultWithObservers program state = .ok (result, trace)) :
    stepResult program state = .ok result := by
  unfold stepResultWithObservers at hRun
  unfold Compiled.stepResult
  cases hEmit : emitCurrent? program state with
  | none =>
      simp [hEmit] at hRun
  | some code =>
      simp [hEmit] at hRun ⊢
      exact Target.runListResultWithObservers_sound hRun

theorem runNResultWithObservers_sound
    {program : Program} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      runNResultWithObservers program fuel state = .ok (result, trace)) :
    runNResult program fuel state = .ok result := by
  induction fuel generalizing state result trace with
  | zero =>
      simp [runNResultWithObservers] at hRun
      rcases hRun with ⟨hResult, _hTrace⟩
      simp [runNResult, hResult.symm]
  | succ fuel ih =>
      unfold runNResultWithObservers at hRun
      cases hStep : stepResultWithObservers program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult', headTrace⟩
          rw [hStep] at hRun
          have hPlainStep :
              Compiled.stepResult program state = .ok stepResult' :=
            stepResultWithObservers_sound hStep
          unfold runNResult
          rw [hPlainStep]
          cases stepResult' with
          | running state' =>
              cases hTail : runNResultWithObservers program fuel state' with
              | error err =>
                  simp [hTail] at hRun
              | ok tailPair =>
                  rcases tailPair with ⟨tailResult, tailTrace⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨hResult, _hTrace⟩
                  cases hResult
                  exact ih hTail
          | halted halt =>
              cases hRun
              rfl

theorem stepResultWithOracle_of_withObservers
    {program : Program} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun : stepResultWithObservers program state = .ok (result, trace)) :
    stepResultWithOracle program state (trace ++ rest) =
      .ok (result, rest) := by
  unfold stepResultWithObservers at hRun
  unfold stepResultWithOracle
  cases hEmit : emitCurrent? program state with
  | none =>
      simp [hEmit] at hRun
  | some code =>
      simp [hEmit] at hRun ⊢
      exact Target.runListResultWithOracle_of_withObservers hRun

theorem runNResultWithOracle_of_withObservers
    {program : Program} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun : runNResultWithObservers program fuel state = .ok (result, trace)) :
    runNResultWithOracle program fuel state (trace ++ rest) =
      .ok (result, rest) := by
  induction fuel generalizing state result trace rest with
  | zero =>
      simp [runNResultWithObservers] at hRun
      rcases hRun with ⟨hResult, hTrace⟩
      cases hResult
      cases hTrace
      simp [runNResultWithOracle]
  | succ fuel ih =>
      unfold runNResultWithObservers at hRun
      cases hStep : stepResultWithObservers program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, headTrace⟩
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              cases hTail :
                  runNResultWithObservers program fuel mid with
              | error err =>
                  simp [hTail] at hRun
              | ok tailPair =>
                  rcases tailPair with ⟨tailResult, tailTrace⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨hResult, hTrace⟩
                  cases hResult
                  cases hTrace
                  have hStepOracle :=
                    stepResultWithOracle_of_withObservers
                      (rest := tailTrace ++ rest) hStep
                  unfold runNResultWithOracle
                  rw [show headTrace ++ tailTrace ++ rest =
                      headTrace ++ (tailTrace ++ rest) by
                    simp [List.append_assoc]]
                  rw [hStepOracle]
                  exact ih hTail
          | halted halt =>
              cases hRun
              have hStepOracle :=
                stepResultWithOracle_of_withObservers
                  (rest := rest) hStep
              unfold runNResultWithOracle
              rw [hStepOracle]

end Compiled

namespace Preservation

theorem run_push_jump_result_withObservers (dest : Nat) (state : EVMState) :
    Target.runListResultWithObservers
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .ok (.running (Source.jumpPc dest state), []) := by
  rfl

theorem run_push_jumpi_result_withObservers (dest : Nat) (state : EVMState) :
    Target.runListResultWithObservers
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      match state.stack.pop with
      | some (stack, cond) =>
          .ok
            (.running
              { state with
                pc :=
                  if cond != EvmYul.UInt256.ofNat 0 then
                    EvmYul.UInt256.ofNat dest
                  else
                    Source.jumpiFallthroughPc state
                stack := stack
              }, [])
      | none =>
          .error .StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
  cases stack with
  | nil => rfl
  | cons _ _ => rfl

theorem run_push_jump_result_withOracle
    (dest : Nat) (state : EVMState) (trace : ResourceTrace) :
    Target.runListResultWithOracle
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state trace =
      .ok (.running (Source.jumpPc dest state), trace) := by
  rfl

theorem run_push_jumpi_result_withOracle
    (dest : Nat) (state : EVMState) (trace : ResourceTrace) :
    Target.runListResultWithOracle
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state trace =
      match state.stack.pop with
      | some (stack, cond) =>
          .ok
            (.running
              { state with
                pc :=
                  if cond != EvmYul.UInt256.ofNat 0 then
                    EvmYul.UInt256.ofNat dest
                  else
                    Source.jumpiFallthroughPc state
                stack := stack
              }, trace)
      | none =>
          .error .StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
  cases stack with
  | nil => rfl
  | cons _ _ => rfl

theorem replaceStackAndIncrPC_pc_toNat_of_no_overflow
    {state : EVMState} {stack : EvmYul.Stack Word} {pcΔ : Nat}
    (hNoOverflow : state.pc.toNat + pcΔ < EvmYul.UInt256.size) :
    (state.replaceStackAndIncrPC stack (pcΔ := pcΔ)).pc.toNat =
      state.pc.toNat + pcΔ := by
  cases state with
  | mk shared pc oldStack execLength =>
      cases pc with
      | mk pcVal =>
          have hNoOverflow' : pcVal.val + pcΔ < EvmYul.UInt256.size := by
            simpa [EvmYul.UInt256.toNat] using hNoOverflow
          have hDeltaLt : pcΔ < EvmYul.UInt256.size :=
            Nat.lt_of_le_of_lt (Nat.le_add_left pcΔ pcVal.val)
              hNoOverflow'
          have hDeltaVal :
              (EvmYul.UInt256.ofNat pcΔ).val.val = pcΔ := by
            simpa [EvmYul.UInt256.toNat] using
              EvmYul.UInt256.toNat_ofNat_of_lt hDeltaLt
          unfold EvmYul.EVM.State.replaceStackAndIncrPC
            EvmYul.EVM.State.incrPC
          change
            (EvmYul.UInt256.add { val := pcVal }
                (EvmYul.UInt256.ofNat pcΔ)).toNat =
              pcVal.val + pcΔ
          unfold EvmYul.UInt256.add EvmYul.UInt256.toNat
          simpa [Fin.val_add, hDeltaVal,
            Nat.mod_eq_of_lt hNoOverflow']

theorem add_ofNat_toNat_of_no_overflow
    {value : Word} {delta : Nat}
    (hNoOverflow : value.toNat + delta < EvmYul.UInt256.size) :
    (value + EvmYul.UInt256.ofNat delta).toNat =
      value.toNat + delta := by
  let state : EVMState :=
    { toSharedState := default,
      pc := value,
      stack := [],
      execLength := 0 }
  have hReplace :=
    replaceStackAndIncrPC_pc_toNat_of_no_overflow
      (state := state) (stack := []) (pcΔ := delta) hNoOverflow
  simpa [state, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] using hReplace

theorem primOp_step_pc_of_nonterminal_success
    {op : PrimOp} {state final : EVMState}
    (hHalt : op.haltKind? = none)
    (hRun : op.step state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases op <;>
    try exact PrimOp.step_pc_of_stackArity (by rfl) hRun
  all_goals simp [PrimOp.haltKind?] at hHalt
  simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run] at hRun

theorem runListResultWithObservers_single
    (instr : TargetInstr) (state : EVMState) :
    Target.runListResultWithObservers [instr] state =
      Target.stepInstrResultWithObservers instr state := by
  cases h : Target.stepInstrResultWithObservers instr state with
  | error e =>
      unfold Target.runListResultWithObservers
      rw [h]
  | ok result =>
      rcases result with ⟨stepResult, trace⟩
      unfold Target.runListResultWithObservers
      rw [h]
      cases stepResult <;> simp [Target.runListResultWithObservers]

theorem runListResultWithOracle_single
    (instr : TargetInstr) (state : EVMState) (trace : ResourceTrace) :
    Target.runListResultWithOracle [instr] state trace =
      Target.stepInstrResultWithOracle instr state trace := by
  cases h : Target.stepInstrResultWithOracle instr state trace with
  | error e =>
      unfold Target.runListResultWithOracle
      rw [h]
  | ok result =>
      rcases result with ⟨stepResult, trace'⟩
      unfold Target.runListResultWithOracle
      rw [h]
      cases stepResult <;> simp [Target.runListResultWithOracle]

theorem target_runNResultWithOracle_single_of_fetch
    {target : TargetProgram} {state : EVMState}
    {instr : TargetInstr} {trace : ResourceTrace}
    (hFetch : TargetProgram.fetch target state.pc.toNat = some instr) :
    Target.runNResultWithOracle target 1 state trace =
      Target.runListResultWithOracle [instr] state trace := by
  rw [runListResultWithOracle_single]
  unfold Target.runNResultWithOracle
  rw [hFetch]
  cases hStep : Target.stepInstrResultWithOracle instr state trace with
  | error err =>
      simp [hStep]
  | ok pair =>
      rcases pair with ⟨stepResult, trace'⟩
      simp [hStep]
      cases stepResult <;> simp [Target.runNResultWithOracle]

theorem target_runNResultWithOracle_push_jump_of_fetch
    {target : TargetProgram} {state : EVMState}
    {dest : Nat} {trace : ResourceTrace}
    (hFetchPush :
      TargetProgram.fetch target state.pc.toNat =
        some (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)))
    (hFetchJump :
      TargetProgram.fetch target (state.pc.toNat + Instr.push32Size) =
        some TargetInstr.jump)
    (hNoOverflow :
      state.pc.toNat + Instr.push32Size < EvmYul.UInt256.size) :
    Target.runNResultWithOracle target 2 state trace =
      Target.runListResultWithOracle
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state trace := by
  unfold Target.runNResultWithOracle
  rw [hFetchPush]
  simp [Target.stepInstrResultWithOracle, Target.stepInstrResult,
    Target.stepInstr, TargetInstr.haltKind?,
    ResourceObserver.ofTargetInstr?, Bind.bind, Except.bind]
  have hPostPc :
      (state.replaceStackAndIncrPC
          (state.stack.push (EvmYul.UInt256.ofNat dest))
          (pcΔ := 33)).pc.toNat =
        state.pc.toNat + 33 :=
    replaceStackAndIncrPC_pc_toNat_of_no_overflow
      (state := state)
      (stack := state.stack.push (EvmYul.UInt256.ofNat dest))
      (pcΔ := 33) (by simpa [Instr.push32Size] using hNoOverflow)
  have hFetchJump' :
      TargetProgram.fetch target
          ((state.replaceStackAndIncrPC
            (state.stack.push (EvmYul.UInt256.ofNat dest))
            (pcΔ := 33)).pc.toNat) =
        some TargetInstr.jump := by
    rw [hPostPc]
    simpa [Instr.push32Size] using hFetchJump
  rw [target_runNResultWithOracle_single_of_fetch hFetchJump']
  simp [Target.stepInstrResultWithOracle, Target.stepInstrResult,
    Target.stepInstr, TargetInstr.haltKind?,
    ResourceObserver.ofTargetInstr?, Bind.bind, Except.bind,
    Target.runListResultWithOracle, Source.jumpPc]

theorem target_runNResultWithOracle_push_jumpi_of_fetch
    {target : TargetProgram} {state : EVMState}
    {dest : Nat} {trace : ResourceTrace}
    (hFetchPush :
      TargetProgram.fetch target state.pc.toNat =
        some (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)))
    (hFetchJumpi :
      TargetProgram.fetch target (state.pc.toNat + Instr.push32Size) =
        some TargetInstr.jumpi)
    (hNoOverflow :
      state.pc.toNat + Instr.push32Size < EvmYul.UInt256.size) :
    Target.runNResultWithOracle target 2 state trace =
      Target.runListResultWithOracle
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state trace := by
  unfold Target.runNResultWithOracle
  rw [hFetchPush]
  simp [Target.stepInstrResultWithOracle, Target.stepInstrResult,
    Target.stepInstr, TargetInstr.haltKind?,
    ResourceObserver.ofTargetInstr?, Bind.bind, Except.bind]
  have hPostPc :
      (state.replaceStackAndIncrPC
          (state.stack.push (EvmYul.UInt256.ofNat dest))
          (pcΔ := 33)).pc.toNat =
        state.pc.toNat + 33 :=
    replaceStackAndIncrPC_pc_toNat_of_no_overflow
      (state := state)
      (stack := state.stack.push (EvmYul.UInt256.ofNat dest))
      (pcΔ := 33) (by simpa [Instr.push32Size] using hNoOverflow)
  have hFetchJumpi' :
      TargetProgram.fetch target
          ((state.replaceStackAndIncrPC
            (state.stack.push (EvmYul.UInt256.ofNat dest))
            (pcΔ := 33)).pc.toNat) =
        some TargetInstr.jumpi := by
    rw [hPostPc]
    simpa [Instr.push32Size] using hFetchJumpi
  rw [target_runNResultWithOracle_single_of_fetch hFetchJumpi']
  simp [Target.stepInstrResultWithOracle, Target.stepInstrResult,
    Target.stepInstr, TargetInstr.haltKind?,
    ResourceObserver.ofTargetInstr?, Bind.bind, Except.bind,
    Target.runListResultWithOracle, Source.jumpiFallthroughPc]

def TargetBlockPcSafe (instr : Instr) (state : EVMState) : Prop :=
  match instr with
  | .jump _ | .jumpi _ =>
      state.pc.toNat + Instr.push32Size < EvmYul.UInt256.size
  | .label _ | .prim _ | .push _ => True

theorem targetBlockPcSafe_of_instrAtPc_of_byteLength_lt
    {program : Program} {state : EVMState} {pc : Nat} {instr : Instr}
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    TargetBlockPcSafe instr state := by
  cases instr with
  | label name =>
      simp [TargetBlockPcSafe]
  | prim op =>
      simp [TargetBlockPcSafe]
  | push value =>
      simp [TargetBlockPcSafe]
  | jump targetLabel =>
      have hPcEq : pc = state.pc.toNat :=
        Program.instrAtPc_pc_eq hAt
      have hEnd :
          pc + (Instr.jump targetLabel).byteSize ≤
            Program.byteLength program :=
        Program.instrAtPc_end_le_byteLength hAt
      have hEnd' :
          pc + (Instr.push32Size + 1) ≤
            Program.byteLength program := by
        simpa [Instr.byteSize, Instr.jumpSize] using hEnd
      simp [TargetBlockPcSafe]
      omega
  | jumpi targetLabel =>
      have hPcEq : pc = state.pc.toNat :=
        Program.instrAtPc_pc_eq hAt
      have hEnd :
          pc + (Instr.jumpi targetLabel).byteSize ≤
            Program.byteLength program :=
        Program.instrAtPc_end_le_byteLength hAt
      have hEnd' :
          pc + (Instr.push32Size + 1) ≤
            Program.byteLength program := by
        simpa [Instr.byteSize, Instr.jumpSize] using hEnd
      simp [TargetBlockPcSafe]
      omega

theorem target_runNResultWithOracle_eq_runList_of_emitInstr?
    {program : Program} {target : TargetProgram}
    {state : EVMState} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget} {trace : ResourceTrace}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hSafe : TargetBlockPcSafe instr state) :
    Target.runNResultWithOracle target emitted.length state trace =
      Target.runListResultWithOracle
        (emitted.map LocatedTarget.instr) state trace := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .label name)
            (emitted := [{ pc := pc, instr := TargetInstr.jumpdest }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_runNResultWithOracle_single_of_fetch hFetch
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .prim op)
            (emitted := [{ pc := pc, instr := TargetInstr.prim op }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_runNResultWithOracle_single_of_fetch hFetch
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .push value)
            (emitted := [{ pc := pc, instr := TargetInstr.push32 value }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_runNResultWithOracle_single_of_fetch hFetch
  | jump targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          rcases
              assemble?_fetch_first_of_instrAtPc
                (program := program) (target := target)
                (query := state.pc.toNat) (pc := pc)
                (instr := .jump targetLabel)
                (emitted :=
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) }
                  , { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jump }
                  ])
                hAsm hAt (by simp [emitInstr?, hDest]) with
            ⟨targetInstr, restEmitted, hFirst, hFetchPush⟩
          cases hFirst
          have hFetchJump :
              TargetProgram.fetch target
                  (state.pc.toNat + Instr.push32Size) =
                some TargetInstr.jump :=
            assemble?_fetch_jump_second_of_instrAtPc
              (program := program) (targetProgram := target)
              (query := state.pc.toNat) (pc := state.pc.toNat)
              (target := targetLabel)
              (emitted :=
                [ { pc := state.pc.toNat,
                    instr := TargetInstr.push32
                      (EvmYul.UInt256.ofNat dest) }
                , { pc := state.pc.toNat + Instr.push32Size,
                    instr := TargetInstr.jump }
                ])
              hAsm hAt (by simp [emitInstr?, hDest])
          have hNoOverflow :
              state.pc.toNat + Instr.push32Size <
                EvmYul.UInt256.size := by
            simpa [TargetBlockPcSafe] using hSafe
          exact
            target_runNResultWithOracle_push_jump_of_fetch
              hFetchPush hFetchJump hNoOverflow
  | jumpi targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          rcases
              assemble?_fetch_first_of_instrAtPc
                (program := program) (target := target)
                (query := state.pc.toNat) (pc := pc)
                (instr := .jumpi targetLabel)
                (emitted :=
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) }
                  , { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jumpi }
                  ])
                hAsm hAt (by simp [emitInstr?, hDest]) with
            ⟨targetInstr, restEmitted, hFirst, hFetchPush⟩
          cases hFirst
          have hFetchJumpi :
              TargetProgram.fetch target
                  (state.pc.toNat + Instr.push32Size) =
                some TargetInstr.jumpi :=
            assemble?_fetch_jumpi_second_of_instrAtPc
              (program := program) (targetProgram := target)
              (query := state.pc.toNat) (pc := state.pc.toNat)
              (target := targetLabel)
              (emitted :=
                [ { pc := state.pc.toNat,
                    instr := TargetInstr.push32
                      (EvmYul.UInt256.ofNat dest) }
                , { pc := state.pc.toNat + Instr.push32Size,
                    instr := TargetInstr.jumpi }
                ])
              hAsm hAt (by simp [emitInstr?, hDest])
          have hNoOverflow :
              state.pc.toNat + Instr.push32Size <
                EvmYul.UInt256.size := by
            simpa [TargetBlockPcSafe] using hSafe
          exact
            target_runNResultWithOracle_push_jumpi_of_fetch
              hFetchPush hFetchJumpi hNoOverflow

theorem target_runNResultWithOracle_of_emitInstr?_runList
    {program : Program} {target : TargetProgram}
    {state : EVMState} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget}
    {result : StepResult} {trace trace' : ResourceTrace}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hSafe : TargetBlockPcSafe instr state)
    (hRun :
      Target.runListResultWithOracle (emitted.map LocatedTarget.instr)
        state trace =
        .ok (result, trace')) :
    Target.runNResultWithOracle target emitted.length state trace =
      .ok (result, trace') := by
  rw [target_runNResultWithOracle_eq_runList_of_emitInstr?
    hAsm hAt hEmit hSafe]
  exact hRun

theorem stepAt_emit_result_withObservers_sound
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep :
      Source.stepAtResultWithObservers program pc instr state =
        .ok (result, trace)) :
    Target.runListResultWithObservers (located.map LocatedTarget.instr)
        state =
      .ok (result, trace) := by
  unfold Source.stepAtResultWithObservers at hStep
  cases hPlain : Source.stepAtResult program pc instr state with
  | error err =>
      simp [hPlain] at hStep
  | ok plainResult =>
      simp [hPlain] at hStep
      rcases hStep with ⟨hResult, hTrace⟩
      cases hResult
      cases instr with
      | label name =>
          simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hPlain
          subst located
          cases hTrace
          have hTargetPlain :
              Target.stepInstrResult TargetInstr.jumpdest state = .ok result := by
            simpa [Source.stepAtResult, Source.stepAt] using hPlain
          change
            Target.runListResultWithObservers [TargetInstr.jumpdest] state =
              .ok (result, [])
          rw [runListResultWithObservers_single]
          unfold Target.stepInstrResultWithObservers
          rw [hTargetPlain]
          rfl
      | prim op =>
          simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hPlain
          subst located
          cases hTrace
          have hTargetPlain :
              Target.stepInstrResult (TargetInstr.prim op) state =
                .ok result := by
            simpa [Source.stepAtResult, Source.stepAt] using hPlain
          change
            Target.runListResultWithObservers [TargetInstr.prim op] state =
              .ok
                (result,
                  match ResourceObserver.ofPrimOp? op with
                  | some kind => kind.recordFromPostState result.state
                  | none => [])
          rw [runListResultWithObservers_single]
          unfold Target.stepInstrResultWithObservers
          rw [hTargetPlain]
          rfl
      | push value =>
          simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hPlain
          subst located
          cases hTrace
          have hTargetPlain :
              Target.stepInstrResult (TargetInstr.push32 value) state =
                .ok result := by
            simpa [Source.stepAtResult, Source.stepAt] using hPlain
          change
            Target.runListResultWithObservers [TargetInstr.push32 value]
                state =
              .ok (result, [])
          rw [runListResultWithObservers_single]
          unfold Target.stepInstrResultWithObservers
          rw [hTargetPlain]
          rfl
      | jump target =>
          cases hDest : Program.labelPc program target with
          | none =>
              simp [emitInstr?, hDest] at hEmit
          | some dest =>
              simp [emitInstr?, hDest, Source.stepAtResult, Source.stepAt,
                Source.jumpPc, Instr.haltKind?] at hEmit hPlain
              subst located
              cases hTrace
              cases hPlain
              change
                Target.runListResultWithObservers
                    [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                      TargetInstr.jump] state =
                  .ok
                    (.running
                      { state with
                        pc := EvmYul.UInt256.ofNat dest }, [])
              rw [run_push_jump_result_withObservers dest state]
              rfl
      | jumpi target =>
          cases hDest : Program.labelPc program target with
          | none =>
              simp [emitInstr?, hDest] at hEmit
          | some dest =>
              simp [emitInstr?, hDest, Source.stepAtResult, Source.stepAt,
                Instr.haltKind?] at hEmit hPlain
              subst located
              cases hTrace
              change
                Target.runListResultWithObservers
                    [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                      TargetInstr.jumpi] state =
                  .ok (result, [])
              rw [run_push_jumpi_result_withObservers dest state]
              cases hPop : state.stack.pop with
              | none =>
                  simp [hPop] at hPlain
                  cases hPlain
              | some pair =>
                  cases pair with
                  | mk stack cond =>
                      simp [hPop] at hPlain
                      cases hPlain
                      rfl

theorem stepAt_emit_result_withOracle_sound
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    {result : StepResult} {trace trace' : ResourceTrace}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep :
      Source.stepAtResultWithOracle program pc instr state trace =
        .ok (result, trace')) :
    Target.runListResultWithOracle (located.map LocatedTarget.instr)
        state trace =
      .ok (result, trace') := by
  unfold Source.stepAtResultWithOracle at hStep
  cases hPlain : Source.stepAtResult program pc instr state with
  | error err =>
      simp [hPlain] at hStep
  | ok plainResult =>
      simp [hPlain] at hStep
      cases instr with
      | label name =>
          simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hPlain
          subst located
          have hTargetPlain :
              Target.stepInstrResult TargetInstr.jumpdest state =
                .ok plainResult := by
            simpa [Source.stepAtResult, Source.stepAt] using hPlain
          change
            Target.runListResultWithOracle [TargetInstr.jumpdest]
                state trace =
              .ok (result, trace')
          rw [runListResultWithOracle_single]
          unfold Target.stepInstrResultWithOracle
          rw [hTargetPlain]
          simpa [ResourceObserver.ofInstr?, ResourceObserver.ofTargetInstr?]
            using hStep
      | prim op =>
          simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hPlain
          subst located
          have hTargetPlain :
              Target.stepInstrResult (TargetInstr.prim op) state =
                .ok plainResult := by
            simpa [Source.stepAtResult, Source.stepAt] using hPlain
          change
            Target.runListResultWithOracle [TargetInstr.prim op]
                state trace =
              .ok (result, trace')
          rw [runListResultWithOracle_single]
          unfold Target.stepInstrResultWithOracle
          rw [hTargetPlain]
          simpa [ResourceObserver.ofInstr?, ResourceObserver.ofTargetInstr?]
            using hStep
      | push value =>
          simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hPlain
          subst located
          have hTargetPlain :
              Target.stepInstrResult (TargetInstr.push32 value) state =
                .ok plainResult := by
            simpa [Source.stepAtResult, Source.stepAt] using hPlain
          change
            Target.runListResultWithOracle [TargetInstr.push32 value]
                state trace =
              .ok (result, trace')
          rw [runListResultWithOracle_single]
          unfold Target.stepInstrResultWithOracle
          rw [hTargetPlain]
          simpa [ResourceObserver.ofInstr?, ResourceObserver.ofTargetInstr?]
            using hStep
      | jump target =>
          cases hDest : Program.labelPc program target with
          | none =>
              simp [emitInstr?, hDest] at hEmit
          | some dest =>
              simp [emitInstr?, hDest, Source.stepAtResult, Source.stepAt,
                Source.jumpPc, Instr.haltKind?] at hEmit hPlain
              subst located
              cases hPlain
              simp [ResourceObserver.ofInstr?] at hStep
              rcases hStep with ⟨hResult, hTrace⟩
              cases hResult
              cases hTrace
              change
                Target.runListResultWithOracle
                    [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                      TargetInstr.jump] state trace =
                  .ok
                    (.running
                      { state with
                        pc := EvmYul.UInt256.ofNat dest }, trace)
              rw [run_push_jump_result_withOracle dest state trace]
              rfl
      | jumpi target =>
          cases hDest : Program.labelPc program target with
          | none =>
              simp [emitInstr?, hDest] at hEmit
          | some dest =>
              simp [emitInstr?, hDest, Source.stepAtResult, Source.stepAt,
                Instr.haltKind?] at hEmit hPlain
              subst located
              simp [ResourceObserver.ofInstr?] at hStep
              rcases hStep with ⟨hResult, hTrace⟩
              cases hResult
              cases hTrace
              change
                Target.runListResultWithOracle
                    [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                      TargetInstr.jumpi] state trace =
                  .ok (result, trace)
              rw [run_push_jumpi_result_withOracle dest state trace]
              cases hPop : state.stack.pop with
              | none =>
                  simp [hPop] at hPlain
                  cases hPlain
              | some pair =>
                  cases pair with
                  | mk stack cond =>
                      simp [hPop] at hPlain
                      cases hPlain
                      rfl

/--
Executing the complete target block emitted for one labeled Assembly
instruction is exactly the source Assembly oracle step, including errors.

Unlike the forward-only preservation theorem above, this equality can be used
to invert successful target execution at source-instruction boundaries.
-/
theorem stepAt_emit_result_withOracle_eq
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    {trace : ResourceTrace}
    (hEmit : emitInstr? program pc instr = some located) :
    Target.runListResultWithOracle (located.map LocatedTarget.instr)
        state trace =
      Source.stepAtResultWithOracle program pc instr state trace := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst located
      simp [runListResultWithOracle_single,
        Target.stepInstrResultWithOracle,
        Target.stepInstrResult, TargetInstr.haltKind?, Instr.haltKind?,
        Source.stepAtResultWithOracle, Source.stepAtResult, Source.stepAt,
        ResourceObserver.ofInstr?, ResourceObserver.ofTargetInstr?]
  | prim op =>
      simp [emitInstr?] at hEmit
      subst located
      simp [runListResultWithOracle_single,
        Target.stepInstrResultWithOracle,
        Target.stepInstrResult, TargetInstr.haltKind?, Instr.haltKind?,
        Source.stepAtResultWithOracle, Source.stepAtResult, Source.stepAt,
        ResourceObserver.ofInstr?, ResourceObserver.ofTargetInstr?]
  | push value =>
      simp [emitInstr?] at hEmit
      subst located
      simp [runListResultWithOracle_single,
        Target.stepInstrResultWithOracle,
        Target.stepInstrResult, TargetInstr.haltKind?, Instr.haltKind?,
        Source.stepAtResultWithOracle, Source.stepAtResult, Source.stepAt,
        ResourceObserver.ofInstr?, ResourceObserver.ofTargetInstr?]
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            Target.runListResultWithOracle
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jump] state trace =
              Source.stepAtResultWithOracle program pc
                (.jump target) state trace
          rw [run_push_jump_result_withOracle]
          simp [Source.stepAtResultWithOracle, Source.stepAtResult,
            Source.stepAt, hDest, Source.jumpPc, Instr.haltKind?,
            ResourceObserver.ofInstr?]
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            Target.runListResultWithOracle
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jumpi] state trace =
              Source.stepAtResultWithOracle program pc
                (.jumpi target) state trace
          rw [run_push_jumpi_result_withOracle]
          cases hPop : state.stack.pop with
          | none =>
              have hPure :
                  (pure dest : Except EVMException Nat) = .ok dest := rfl
              simp [Source.stepAtResultWithOracle, Source.stepAtResult,
                Source.stepAt, hDest, hPop, Instr.haltKind?,
                ResourceObserver.ofInstr?, Bind.bind, Except.bind,
                hPure]
          | some pair =>
              rcases pair with ⟨stack, cond⟩
              simp [Source.stepAtResultWithOracle, Source.stepAtResult,
                Source.stepAt, hDest, hPop, Instr.haltKind?,
                ResourceObserver.ofInstr?]

/--
A successful running Assembly oracle step preserves the source instruction
boundary invariant. Sequential instructions either land on the next source
instruction or exactly at program end; jumps land on their resolved label
instruction.
-/
theorem source_stepAtResultWithOracle_running_boundary
    {program : Program} {pc : Nat} {instr : Instr}
    {state final : EVMState} {trace trace' : ResourceTrace}
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hLen : Program.byteLength program < EvmYul.UInt256.size)
    (hStep :
      Source.stepAtResultWithOracle program pc instr state trace =
        .ok (.running final, trace')) :
    final.pc.toNat = Program.byteLength program ∨
      ∃ nextPc nextInstr,
        Program.instrAtPc program final.pc.toNat =
          some (nextPc, nextInstr) := by
  rcases Source.stepAtResultWithOracle_running_plain_pc hStep with
    ⟨plain, hPlain, hOraclePc⟩
  have hPc : pc = state.pc.toNat :=
    Program.instrAtPc_pc_eq hAt
  have hEndLe :
      pc + instr.byteSize ≤ Program.byteLength program :=
    Program.instrAtPc_end_le_byteLength hAt
  have hStateEndLe :
      state.pc.toNat + instr.byteSize ≤ Program.byteLength program := by
    simpa [hPc] using hEndLe
  have hNext := Program.instrAtPc_next_or_end hAt
  cases instr with
  | label name =>
      have hPlainPc :
          plain.pc =
            state.pc + EvmYul.UInt256.ofNat
              (Instr.label name).byteSize := by
        simp [Source.stepAtResult, Source.stepAt, Target.stepInstr,
          Instr.haltKind?, TargetInstr.haltKind?] at hPlain
        cases hPlain
        rfl
      have hNoOverflow :
          state.pc.toNat + (Instr.label name).byteSize <
            EvmYul.UInt256.size := by
        simp [Instr.byteSize] at hStateEndLe
        omega
      have hFinalPc :
          final.pc.toNat =
            pc + (Instr.label name).byteSize := by
        rw [hOraclePc, hPlainPc,
          add_ofNat_toNat_of_no_overflow hNoOverflow]
        omega
      rw [hFinalPc]
      exact hNext
  | prim op =>
      cases hOp : op.step state with
      | error err =>
          simp [Source.stepAtResult, Source.stepAt, Target.stepInstr,
            hOp, Bind.bind, Except.bind] at hPlain
      | ok stepped =>
          cases hHalt : op.haltKind? with
          | some kind =>
              simp [Source.stepAtResult, Source.stepAt, Target.stepInstr,
                Instr.haltKind?, TargetInstr.haltKind?, hOp, hHalt]
                at hPlain
              cases hPlain
          | none =>
              simp [Source.stepAtResult, Source.stepAt, Target.stepInstr,
                Instr.haltKind?, TargetInstr.haltKind?, hOp, hHalt]
                at hPlain
              cases hPlain
              have hPlainPc :
                  plain.pc =
                    state.pc + EvmYul.UInt256.ofNat
                      (Instr.prim op).byteSize := by
                simpa [Instr.byteSize] using
                  primOp_step_pc_of_nonterminal_success hHalt hOp
              have hNoOverflow :
                  state.pc.toNat + (Instr.prim op).byteSize <
                    EvmYul.UInt256.size := by
                simp [Instr.byteSize] at hStateEndLe
                omega
              have hFinalPc :
                  final.pc.toNat =
                    pc + (Instr.prim op).byteSize := by
                rw [hOraclePc, hPlainPc,
                  add_ofNat_toNat_of_no_overflow hNoOverflow]
                omega
              rw [hFinalPc]
              exact hNext
  | push value =>
      have hPlainPc :
          plain.pc =
            state.pc + EvmYul.UInt256.ofNat
              (Instr.push value).byteSize := by
        simp [Source.stepAtResult, Source.stepAt, Target.stepInstr,
          Instr.haltKind?, TargetInstr.haltKind?] at hPlain
        cases hPlain
        rfl
      have hNoOverflow :
          state.pc.toNat + (Instr.push value).byteSize <
            EvmYul.UInt256.size := by
        simp [Instr.byteSize, Instr.push32Size] at hStateEndLe
        omega
      have hFinalPc :
          final.pc.toNat =
            pc + (Instr.push value).byteSize := by
        rw [hOraclePc, hPlainPc,
          add_ofNat_toNat_of_no_overflow hNoOverflow]
        omega
      rw [hFinalPc]
      exact hNext
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [Source.stepAtResult, Source.stepAt, hDest,
            Source.invalid, Bind.bind, Except.bind] at hPlain
      | some dest =>
          simp [Source.stepAtResult, Source.stepAt, hDest,
            Instr.haltKind?, Source.jumpPc] at hPlain
          cases hPlain
          have hDestAt :
              Program.instrAtPc program dest =
                some (dest, .label target) :=
            Program.instrAtPc_of_labelPc hDest
          have hDestEnd :
              dest + (Instr.label target).byteSize ≤
                Program.byteLength program :=
            Program.instrAtPc_end_le_byteLength hDestAt
          have hDestLt : dest < EvmYul.UInt256.size := by
            have hLabelPos := Instr.byteSize_pos (.label target)
            omega
          have hDestWord :
              (EvmYul.UInt256.ofNat dest).toNat = dest :=
            EvmYul.UInt256.toNat_ofNat_of_lt hDestLt
          right
          refine ⟨dest, .label target, ?_⟩
          rw [hOraclePc]
          simpa [Source.jumpPc, hDestWord] using hDestAt
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [Source.stepAtResult, Source.stepAt, hDest,
            Source.invalid, Bind.bind, Except.bind] at hPlain
      | some dest =>
          cases hPop : state.stack.pop with
          | none =>
              have hPure :
                  (pure dest : Except EVMException Nat) = .ok dest := rfl
              simp [Source.stepAtResult, Source.stepAt, hDest, hPop,
                hPure, Bind.bind, Except.bind] at hPlain
          | some pair =>
              rcases pair with ⟨stack, cond⟩
              cases hCond :
                  cond != EvmYul.UInt256.ofNat 0 with
              | false =>
                  simp [Source.stepAtResult, Source.stepAt, hDest, hPop,
                    hCond, Instr.haltKind?] at hPlain
                  cases hPlain
                  have hNoOverflow :
                      state.pc.toNat + (Instr.jumpi target).byteSize <
                        EvmYul.UInt256.size := by
                    simp [Instr.byteSize, Instr.jumpSize,
                      Instr.push32Size] at hStateEndLe
                    omega
                  have hFallthrough :
                      Source.jumpiFallthroughPc state =
                        state.pc + EvmYul.UInt256.ofNat
                          (Instr.jumpi target).byteSize := by
                    unfold Source.jumpiFallthroughPc
                    change
                      (state.pc + EvmYul.UInt256.ofNat 33) +
                          EvmYul.UInt256.ofNat 1 =
                        state.pc + EvmYul.UInt256.ofNat 34
                    calc
                      (state.pc + EvmYul.UInt256.ofNat 33) +
                            EvmYul.UInt256.ofNat 1 =
                          state.pc +
                            (EvmYul.UInt256.ofNat 33 +
                              EvmYul.UInt256.ofNat 1) :=
                        UInt256_add_assoc _ _ _
                      _ = state.pc + EvmYul.UInt256.ofNat (33 + 1) := by
                        rw [UInt256_ofNat_add]
                      _ = state.pc + EvmYul.UInt256.ofNat 34 := by
                        rfl
                  have hFinalPc :
                      final.pc.toNat =
                        pc + (Instr.jumpi target).byteSize := by
                    rw [hOraclePc, hFallthrough,
                      add_ofNat_toNat_of_no_overflow hNoOverflow]
                    omega
                  rw [hFinalPc]
                  exact hNext
              | true =>
                  simp [Source.stepAtResult, Source.stepAt, hDest, hPop,
                    hCond, Instr.haltKind?] at hPlain
                  cases hPlain
                  have hDestAt :
                      Program.instrAtPc program dest =
                        some (dest, .label target) :=
                    Program.instrAtPc_of_labelPc hDest
                  have hDestEnd :
                      dest + (Instr.label target).byteSize ≤
                        Program.byteLength program :=
                    Program.instrAtPc_end_le_byteLength hDestAt
                  have hDestLt : dest < EvmYul.UInt256.size := by
                    have hLabelPos := Instr.byteSize_pos (.label target)
                    omega
                  have hDestWord :
                      (EvmYul.UInt256.ofNat dest).toNat = dest :=
                    EvmYul.UInt256.toNat_ofNat_of_lt hDestLt
                  right
                  refine ⟨dest, .label target, ?_⟩
                  rw [hOraclePc]
                  simpa [hDestWord] using hDestAt

/--
Exact adjacent adequacy for one labeled Assembly instruction.

At every source instruction boundary, the assembled target executes a positive
number of target instructions and produces exactly the same oracle result,
including the remaining transcript and all error cases.
-/
theorem assemble_target_runNResultWithOracle_source_step_exact
    {program : Program} {target : TargetProgram}
    {state : EVMState} {trace : ResourceTrace}
    {pc : Nat} {instr : Instr}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    ∃ targetFuel,
      0 < targetFuel ∧
        Target.runNResultWithOracle target targetFuel state trace =
          Source.stepResultWithOracle program state trace := by
  rcases assemble_covers_current_pc hAsm hAt with
    ⟨before, emitted, after, hTargetBlock, hEmit⟩
  obtain ⟨targetInstr, rest, hEmitted⟩ := emitInstr?_first hEmit
  have hSafe : TargetBlockPcSafe instr state :=
    targetBlockPcSafe_of_instrAtPc_of_byteLength_lt hAt hLen
  refine ⟨emitted.length, ?_, ?_⟩
  · rw [hEmitted]
    simp
  · rw [target_runNResultWithOracle_eq_runList_of_emitInstr?
      hAsm hAt hEmit hSafe]
    rw [stepAt_emit_result_withOracle_eq hEmit]
    unfold Source.stepResultWithOracle
    rw [hAt]

theorem compile_target_runNResultWithOracle_source_step_exact
    {program : Program} {target : TargetProgram}
    {state : EVMState} {trace : ResourceTrace}
    {pc : Nat} {instr : Instr}
    (hCompile : compile? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    ∃ targetFuel,
      0 < targetFuel ∧
        Target.runNResultWithOracle target targetFuel state trace =
          Source.stepResultWithOracle program state trace :=
  assemble_target_runNResultWithOracle_source_step_exact
    (compile?_some_assemble hCompile) hAt hLen

theorem emitted_length_le_of_terminal_target_run
    {program : Program} {target : TargetProgram}
    {state : EVMState} {trace traceOut : ResourceTrace}
    {pc : Nat} {instr : Instr} {emitted : List LocatedTarget}
    {fuel : Nat} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hRun :
      Target.runNResultWithOracle target fuel state trace =
        .ok (result, traceOut))
    (hTerminal : result.IsTerminal) :
    emitted.length ≤ fuel := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      cases fuel with
      | zero =>
          simp [Target.runNResultWithOracle] at hRun
          rcases hRun with ⟨hResult, _hTrace⟩
          subst result
          simp [StepResult.IsTerminal] at hTerminal
      | succ fuel =>
          simp
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      cases fuel with
      | zero =>
          simp [Target.runNResultWithOracle] at hRun
          rcases hRun with ⟨hResult, _hTrace⟩
          subst result
          simp [StepResult.IsTerminal] at hTerminal
      | succ fuel =>
          simp
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      cases fuel with
      | zero =>
          simp [Target.runNResultWithOracle] at hRun
          rcases hRun with ⟨hResult, _hTrace⟩
          subst result
          simp [StepResult.IsTerminal] at hTerminal
      | succ fuel =>
          simp
  | jump targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          cases fuel with
          | zero =>
              simp [Target.runNResultWithOracle] at hRun
              rcases hRun with ⟨hResult, _hTrace⟩
              subst result
              simp [StepResult.IsTerminal] at hTerminal
          | succ fuel =>
              cases fuel with
              | zero =>
                  rcases
                      assemble?_fetch_first_of_instrAtPc
                        (program := program) (target := target)
                        (query := state.pc.toNat) (pc := pc)
                        (instr := .jump targetLabel)
                        (emitted :=
                          [ { pc := pc,
                              instr := TargetInstr.push32
                                (EvmYul.UInt256.ofNat dest) }
                          , { pc := pc + Instr.push32Size,
                              instr := TargetInstr.jump }
                          ])
                        hAsm hAt (by simp [emitInstr?, hDest]) with
                    ⟨targetInstr, restEmitted, hFirst, hFetch⟩
                  cases hFirst
                  rw [target_runNResultWithOracle_single_of_fetch hFetch]
                    at hRun
                  simp [Target.runListResultWithOracle,
                    Target.stepInstrResultWithOracle,
                    Target.stepInstrResult, Target.stepInstr,
                    TargetInstr.haltKind?,
                    ResourceObserver.ofTargetInstr?, Bind.bind,
                    Except.bind] at hRun
                  rw [← hRun.1] at hTerminal
                  simp [StepResult.IsTerminal] at hTerminal
              | succ fuel =>
                  simp
  | jumpi targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          cases fuel with
          | zero =>
              simp [Target.runNResultWithOracle] at hRun
              rcases hRun with ⟨hResult, _hTrace⟩
              subst result
              simp [StepResult.IsTerminal] at hTerminal
          | succ fuel =>
              cases fuel with
              | zero =>
                  rcases
                      assemble?_fetch_first_of_instrAtPc
                        (program := program) (target := target)
                        (query := state.pc.toNat) (pc := pc)
                        (instr := .jumpi targetLabel)
                        (emitted :=
                          [ { pc := pc,
                              instr := TargetInstr.push32
                                (EvmYul.UInt256.ofNat dest) }
                          , { pc := pc + Instr.push32Size,
                              instr := TargetInstr.jumpi }
                          ])
                        hAsm hAt (by simp [emitInstr?, hDest]) with
                    ⟨targetInstr, restEmitted, hFirst, hFetch⟩
                  cases hFirst
                  rw [target_runNResultWithOracle_single_of_fetch hFetch]
                    at hRun
                  simp [Target.runListResultWithOracle,
                    Target.stepInstrResultWithOracle,
                    Target.stepInstrResult, Target.stepInstr,
                    TargetInstr.haltKind?,
                    ResourceObserver.ofTargetInstr?, Bind.bind,
                    Except.bind] at hRun
                  rw [← hRun.1] at hTerminal
                  simp [StepResult.IsTerminal] at hTerminal
              | succ fuel =>
                  simp

/--
Backward adequacy for arbitrary terminal assembled-target oracle runs.

Starting at a source instruction boundary, every terminal target run can be
partitioned into complete emitted source blocks and reconstructed as a finite
source Assembly oracle run with the identical halt and remaining transcript.
-/
theorem assemble_terminal_target_run_source_exists
    {program : Program} {target : TargetProgram}
    {state : EVMState} {trace traceOut : ResourceTrace}
    {fuel : Nat} {halt : Halt} {pc : Nat} {instr : Instr}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hLen : Program.byteLength program < EvmYul.UInt256.size)
    (hRun :
      Target.runNResultWithOracle target fuel state trace =
        .ok (.halted halt, traceOut)) :
    ∃ sourceFuel,
      Source.runNResultWithOracle program sourceFuel state trace =
        .ok (.halted halt, traceOut) := by
  induction fuel using Nat.strong_induction_on generalizing state trace pc instr with
  | h fuel ih =>
      rcases assemble_covers_current_pc hAsm hAt with
        ⟨before, emitted, after, hTargetBlock, hEmit⟩
      obtain ⟨firstInstr, restEmitted, hEmitted⟩ :=
        emitInstr?_first hEmit
      have hEmittedPos : 0 < emitted.length := by
        rw [hEmitted]
        simp
      have hBlockLe : emitted.length ≤ fuel :=
        emitted_length_le_of_terminal_target_run
          hAsm hAt hEmit hRun (by simp [StepResult.IsTerminal])
      have hSafe : TargetBlockPcSafe instr state :=
        targetBlockPcSafe_of_instrAtPc_of_byteLength_lt hAt hLen
      have hHead :
          Target.runNResultWithOracle target emitted.length state trace =
            Source.stepResultWithOracle program state trace := by
        rw [target_runNResultWithOracle_eq_runList_of_emitInstr?
          hAsm hAt hEmit hSafe]
        rw [stepAt_emit_result_withOracle_eq hEmit]
        unfold Source.stepResultWithOracle
        rw [hAt]
      let restFuel := fuel - emitted.length
      have hFuelEq : emitted.length + restFuel = fuel := by
        exact Nat.add_sub_of_le hBlockLe
      cases hSource :
          Source.stepResultWithOracle program state trace with
      | error err =>
          have hTargetHead :
              Target.runNResultWithOracle target emitted.length state trace =
                .error err := by
            rw [hHead, hSource]
          rw [← hFuelEq] at hRun
          rw [Target.runNResultWithOracle_add, hTargetHead] at hRun
          cases hRun
      | ok sourcePair =>
          rcases sourcePair with ⟨sourceResult, traceMid⟩
          have hTargetHead :
              Target.runNResultWithOracle target emitted.length state trace =
                .ok (sourceResult, traceMid) := by
            rw [hHead, hSource]
          cases sourceResult with
          | halted sourceHalt =>
              rw [← hFuelEq] at hRun
              rw [Target.runNResultWithOracle_add, hTargetHead] at hRun
              cases hRun
              refine ⟨1, ?_⟩
              simp [Source.runNResultWithOracle, hSource]
          | running mid =>
              rw [← hFuelEq] at hRun
              rw [Target.runNResultWithOracle_add, hTargetHead] at hRun
              change
                Target.runNResultWithOracle target restFuel mid traceMid =
                  .ok (.halted halt, traceOut) at hRun
              have hRestLt : restFuel < fuel := by
                omega
              have hStepAt :
                  Source.stepAtResultWithOracle program pc instr state trace =
                    .ok (.running mid, traceMid) := by
                unfold Source.stepResultWithOracle at hSource
                rw [hAt] at hSource
                exact hSource
              rcases
                  source_stepAtResultWithOracle_running_boundary
                    hAt hLen hStepAt with
                hEnd | ⟨nextPc, nextInstr, hNextAt⟩
              · cases hRest : restFuel with
                | zero =>
                    rw [hRest] at hRun
                    simp [Target.runNResultWithOracle] at hRun
                | succ tailFuel =>
                    rw [hRest] at hRun
                    unfold Target.runNResultWithOracle at hRun
                    rw [hEnd,
                      Bytecode.assemble_fetch_byteLength_none hAsm] at hRun
                    cases hRun
              · rcases
                    ih restFuel hRestLt hNextAt hRun with
                  ⟨sourceTailFuel, hSourceTail⟩
                have hSourceHead :
                    Source.runNResultWithOracle program 1 state trace =
                      .ok (.running mid, traceMid) := by
                  simp [Source.runNResultWithOracle, hSource]
                exact
                  ⟨1 + sourceTailFuel,
                    Source.runNResultWithOracle_running_bind
                      hSourceHead hSourceTail⟩

theorem compile_terminal_target_run_source_exists
    {program : Program} {target : TargetProgram}
    {state : EVMState} {trace traceOut : ResourceTrace}
    {fuel : Nat} {halt : Halt} {pc : Nat} {instr : Instr}
    (hCompile : compile? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hLen : Program.byteLength program < EvmYul.UInt256.size)
    (hRun :
      Target.runNResultWithOracle target fuel state trace =
        .ok (.halted halt, traceOut)) :
    ∃ sourceFuel,
      Source.runNResultWithOracle program sourceFuel state trace =
        .ok (.halted halt, traceOut) :=
  assemble_terminal_target_run_source_exists
    (compile?_some_assemble hCompile) hAt hLen hRun

theorem source_step_current_emit_result_withObservers_sound
    {program : Program} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    {code : List TargetInstr}
    (hEmit : emitCurrent? program state = some code)
    (hStep :
      Source.stepResultWithObservers program state = .ok (result, trace)) :
    Target.runListResultWithObservers code state = .ok (result, trace) := by
  unfold emitCurrent? at hEmit
  unfold Source.stepResultWithObservers at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hEmit
    | some current =>
        rcases current with ⟨pc, instr⟩
        simp [hAt] at hEmit hStep
        cases hEmitInstr : emitInstr? program pc instr with
        | none =>
            simp [hEmitInstr] at hEmit
        | some located =>
            simp [hEmitInstr] at hEmit
            subst code
            exact stepAt_emit_result_withObservers_sound hEmitInstr hStep

theorem source_step_current_emit_result_withOracle_sound
    {program : Program} {state : EVMState}
    {result : StepResult} {trace trace' : ResourceTrace}
    {code : List TargetInstr}
    (hEmit : emitCurrent? program state = some code)
    (hStep :
      Source.stepResultWithOracle program state trace = .ok (result, trace')) :
    Target.runListResultWithOracle code state trace = .ok (result, trace') := by
  unfold emitCurrent? at hEmit
  unfold Source.stepResultWithOracle at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hEmit
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp [hAt] at hEmit hStep
      cases hEmitInstr : emitInstr? program pc instr with
      | none =>
          simp [hEmitInstr] at hEmit
      | some located =>
          simp [hEmitInstr] at hEmit
          subst code
          exact stepAt_emit_result_withOracle_sound hEmitInstr hStep

theorem source_compiled_step_result_withObservers_sound
    {program : Program} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hStep :
      Source.stepResultWithObservers program state = .ok (result, trace)) :
    Compiled.stepResultWithObservers program state = .ok (result, trace) := by
  unfold Compiled.stepResultWithObservers
  cases hEmit : emitCurrent? program state with
  | none =>
      have hPlain :
          Source.stepResult program state = .ok result :=
        Source.stepResultWithObservers_sound hStep
      unfold emitCurrent? at hEmit
      unfold Source.stepResult at hPlain
      cases hAt : Program.instrAtPc program state.pc.toNat with
      | none =>
          simp [hAt] at hPlain
      | some current =>
          rcases current with ⟨pc, instr⟩
          simp [hAt] at hEmit hPlain
          cases instr with
          | label name =>
              simp [emitInstr?] at hEmit
          | prim op =>
              simp [emitInstr?] at hEmit
          | push value =>
              simp [emitInstr?] at hEmit
          | jump target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [emitInstr?, hDest] at hEmit
                  unfold Source.stepAtResult Source.stepAt Source.invalid at hPlain
                  simp [hDest, Instr.haltKind?] at hPlain
                  cases hPlain
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
          | jumpi target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [emitInstr?, hDest] at hEmit
                  unfold Source.stepAtResult Source.stepAt Source.invalid at hPlain
                  simp [hDest, Instr.haltKind?] at hPlain
                  cases hPlain
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
  | some code =>
      exact source_step_current_emit_result_withObservers_sound hEmit hStep

theorem source_compiled_step_result_withOracle_sound
    {program : Program} {state : EVMState}
    {result : StepResult} {trace trace' : ResourceTrace}
    (hStep :
      Source.stepResultWithOracle program state trace = .ok (result, trace')) :
    Compiled.stepResultWithOracle program state trace = .ok (result, trace') := by
  unfold Compiled.stepResultWithOracle
  cases hEmit : emitCurrent? program state with
  | none =>
      unfold emitCurrent? at hEmit
      unfold Source.stepResultWithOracle at hStep
      cases hAt : Program.instrAtPc program state.pc.toNat with
      | none =>
          simp [hAt] at hStep
      | some current =>
          rcases current with ⟨pc, instr⟩
          simp [hAt] at hEmit hStep
          cases instr with
          | label name =>
              simp [emitInstr?] at hEmit
          | prim op =>
              simp [emitInstr?] at hEmit
          | push value =>
              simp [emitInstr?] at hEmit
          | jump target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [emitInstr?, hDest] at hEmit
                  unfold Source.stepAtResultWithOracle Source.stepAtResult
                    Source.stepAt Source.invalid at hStep
                  simp [hDest, Bind.bind, Except.bind] at hStep
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
          | jumpi target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [emitInstr?, hDest] at hEmit
                  unfold Source.stepAtResultWithOracle Source.stepAtResult
                    Source.stepAt Source.invalid at hStep
                  simp [hDest, Bind.bind, Except.bind] at hStep
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
  | some code =>
      exact source_step_current_emit_result_withOracle_sound hEmit hStep

theorem source_compiled_runN_result_withObservers_sound
    {program : Program} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace : ResourceTrace}
    (hRun :
      Source.runNResultWithObservers program fuel state =
        .ok (result, trace)) :
    Compiled.runNResultWithObservers program fuel state =
      .ok (result, trace) := by
  induction fuel generalizing state result trace with
  | zero =>
      simp [Source.runNResultWithObservers] at hRun
      simpa [Compiled.runNResultWithObservers] using hRun
  | succ fuel ih =>
      unfold Source.runNResultWithObservers at hRun
      cases hStep : Source.stepResultWithObservers program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, headTrace⟩
          rw [hStep] at hRun
          unfold Compiled.runNResultWithObservers
          rw [source_compiled_step_result_withObservers_sound hStep]
          cases stepResult with
          | running mid =>
              cases hTail :
                  Source.runNResultWithObservers program fuel mid with
              | error err =>
                  simp [hTail] at hRun
              | ok tailPair =>
                  rcases tailPair with ⟨tailResult, tailTrace⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨hResult, hTrace⟩
                  cases hResult
                  have hCompiledTail := ih hTail
                  simp [hCompiledTail, hTrace]
          | halted halt =>
              cases hRun
              rfl

theorem source_compiled_runN_result_withOracle_sound
    {program : Program} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace rest : ResourceTrace}
    (hRun :
      Source.runNResultWithObservers program fuel state =
        .ok (result, trace)) :
    Compiled.runNResultWithOracle program fuel state (trace ++ rest) =
      .ok (result, rest) := by
  exact
    Compiled.runNResultWithOracle_of_withObservers
      (source_compiled_runN_result_withObservers_sound hRun)

inductive BlockTraceResultWithOracle
    (program : Program) (target : TargetProgram) :
    Nat → EVMState → ResourceTrace → ResourceTrace → StepResult → Prop where
  | done (state : EVMState) (trace : ResourceTrace) :
      BlockTraceResultWithOracle program target 0 state trace trace
        (.running state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {trace traceAfterHead traceOut : ResourceTrace}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResultWithOracle
          (emitted.map LocatedTarget.instr) state trace =
          .ok (.running mid, traceAfterHead))
      (hRest :
        BlockTraceResultWithOracle program target fuel mid traceAfterHead
          traceOut result) :
      BlockTraceResultWithOracle program target (fuel + 1) state trace
        traceOut result
  | stepHalted {fuel : Nat} {state : EVMState}
      {trace traceOut : ResourceTrace} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResultWithOracle
          (emitted.map LocatedTarget.instr) state trace =
          .ok (.halted halt, traceOut)) :
      BlockTraceResultWithOracle program target (fuel + 1) state trace
        traceOut (.halted halt)

namespace BlockTraceResultWithOracle

inductive TargetPcSafe {program : Program} {target : TargetProgram} :
    {fuel : Nat} → {state : EVMState} →
      {trace traceOut : ResourceTrace} → {result : StepResult} →
      BlockTraceResultWithOracle program target fuel state trace traceOut
        result → Prop where
  | done (state : EVMState) (trace : ResourceTrace) :
      TargetPcSafe (.done state trace)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {trace traceAfterHead traceOut : ResourceTrace}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr)}
      {hEmit : emitInstr? program pc instr = some emitted}
      {hTargetBlock : target.code = before ++ emitted ++ after}
      {hRun :
        Target.runListResultWithOracle
          (emitted.map LocatedTarget.instr) state trace =
          .ok (.running mid, traceAfterHead)}
      {hRest :
        BlockTraceResultWithOracle program target fuel mid traceAfterHead
          traceOut result}
      (hHeadSafe : TargetBlockPcSafe instr state)
      (hRestSafe : TargetPcSafe hRest) :
      TargetPcSafe
        (.stepRunning hAt hEmit hTargetBlock hRun hRest)
  | stepHalted {fuel : Nat} {state : EVMState}
      {trace traceOut : ResourceTrace} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr)}
      {hEmit : emitInstr? program pc instr = some emitted}
      {hTargetBlock : target.code = before ++ emitted ++ after}
      {hRun :
        Target.runListResultWithOracle
          (emitted.map LocatedTarget.instr) state trace =
          .ok (.halted halt, traceOut)}
      (hHeadSafe : TargetBlockPcSafe instr state) :
      TargetPcSafe (.stepHalted hAt hEmit hTargetBlock hRun)

theorem targetPcSafe_of_byteLength_lt
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {trace traceOut : ResourceTrace}
    {result : StepResult}
    (hTrace :
      BlockTraceResultWithOracle program target fuel state trace traceOut
        result)
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    TargetPcSafe hTrace := by
  induction hTrace with
  | done state trace =>
      exact TargetPcSafe.done state trace
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel' state' mid' trace' traceAfterHead' traceOut' result'
        pc instr emitted before after
      exact
        TargetPcSafe.stepRunning
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          (hAt := hAt) (hEmit := hEmit) (hTargetBlock := hTargetBlock)
          (hRun := hRun) (hRest := hRest)
          (hHeadSafe :=
            targetBlockPcSafe_of_instrAtPc_of_byteLength_lt hAt hLen)
          (hRestSafe := ih)
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel' state' trace' traceOut' halt pc instr emitted before
        after
      exact
        TargetPcSafe.stepHalted
          (fuel := fuel') (pc := pc) (instr := instr)
          (emitted := emitted) (before := before) (after := after)
          (hAt := hAt) (hEmit := hEmit) (hTargetBlock := hTargetBlock)
          (hRun := hRun)
          (hHeadSafe :=
            targetBlockPcSafe_of_instrAtPc_of_byteLength_lt hAt hLen)

theorem target_runNResultWithOracle_exists
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {trace traceOut : ResourceTrace}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    {hTrace :
      BlockTraceResultWithOracle program target fuel state trace traceOut
        result}
    (hSafe : TargetPcSafe hTrace) :
    ∃ targetFuel,
      Target.runNResultWithOracle target targetFuel state trace =
        .ok (result, traceOut) := by
  induction hSafe with
  | done state trace =>
      exact ⟨0, by simp [Target.runNResultWithOracle]⟩
  | stepRunning hHeadSafe hRestSafe ih =>
      rename_i fuel state mid trace traceAfterHead traceOut result pc instr
        emitted before after hAt hEmit hTargetBlock hRun hRest
      have hHead :
          Target.runNResultWithOracle target
              (emitted.length) state trace =
            .ok (.running mid, traceAfterHead) :=
        target_runNResultWithOracle_of_emitInstr?_runList
          hAsm hAt hEmit hHeadSafe hRun
      rcases ih with ⟨targetTailFuel, hTail⟩
      exact
        ⟨emitted.length + targetTailFuel,
          Target.runNResultWithOracle_running_bind hHead hTail⟩
  | stepHalted hHeadSafe =>
      rename_i fuel state trace traceOut halt pc instr emitted before after
        hAt hEmit hTargetBlock hRun
      exact
        ⟨emitted.length,
          target_runNResultWithOracle_of_emitInstr?_runList
            hAsm hAt hEmit hHeadSafe hRun⟩

theorem target_runNResultWithOracle_exists_of_byteLength_lt
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {trace traceOut : ResourceTrace}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hTrace :
      BlockTraceResultWithOracle program target fuel state trace traceOut
        result)
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    ∃ targetFuel,
      Target.runNResultWithOracle target targetFuel state trace =
        .ok (result, traceOut) :=
  target_runNResultWithOracle_exists hAsm
    (targetPcSafe_of_byteLength_lt hTrace hLen)

end BlockTraceResultWithOracle

theorem assemble_source_step_current_result_withOracle_sound
    {program : Program} {target : TargetProgram}
    {state : EVMState} {result : StepResult}
    {trace trace' : ResourceTrace}
    (hAsm : assemble? program = some target)
    (hStep :
      Source.stepResultWithOracle program state trace =
        .ok (result, trace')) :
    ∃ pc instr emitted before after,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        Target.runListResultWithOracle
          (emitted.map LocatedTarget.instr) state trace =
          .ok (result, trace') := by
  unfold Source.stepResultWithOracle at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp [hAt] at hStep
      rcases assemble_covers_current_pc hAsm hAt with
        ⟨before, emitted, after, hTargetBlock, hEmit⟩
      exact
        ⟨pc, instr, emitted, before, after, rfl, hEmit, hTargetBlock,
          stepAt_emit_result_withOracle_sound hEmit hStep⟩

theorem assemble_runN_result_block_trace_withOracle_sound
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {trace trace' : ResourceTrace}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hRun :
      Source.runNResultWithOracle program fuel state trace =
        .ok (result, trace')) :
    BlockTraceResultWithOracle program target fuel state trace trace'
      result := by
  induction fuel generalizing state trace trace' result with
  | zero =>
      simp [Source.runNResultWithOracle] at hRun
      rcases hRun with ⟨hResult, hTrace⟩
      cases hResult
      cases hTrace
      exact BlockTraceResultWithOracle.done state trace
  | succ fuel ih =>
      unfold Source.runNResultWithOracle at hRun
      cases hStep :
          Source.stepResultWithOracle program state trace with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, traceAfterHead⟩
          rw [hStep] at hRun
          rcases
              assemble_source_step_current_result_withOracle_sound
                hAsm hStep with
            ⟨pc, instr, emitted, before, after, hAt, hEmit, hTargetBlock,
              hTargetRun⟩
          cases stepResult with
          | running mid =>
              exact
                BlockTraceResultWithOracle.stepRunning hAt hEmit
                  hTargetBlock hTargetRun (ih hRun)
          | halted halt =>
              cases hRun
              exact
                BlockTraceResultWithOracle.stepHalted hAt hEmit
                  hTargetBlock hTargetRun

theorem compile_runN_result_block_trace_withOracle_sound
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {trace trace' : ResourceTrace}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hRun :
      Source.runNResultWithOracle program fuel state trace =
        .ok (result, trace')) :
    Accepted program ∧
      BlockTraceResultWithOracle program target fuel state trace trace'
        result := by
  exact
    ⟨compile?_some_accepted hCompile,
      assemble_runN_result_block_trace_withOracle_sound
        (compile?_some_assemble hCompile) hRun⟩

theorem source_compiled_runN_result_withOracle_sound_of_sourceOracle
    {program : Program} {fuel : Nat} {state : EVMState}
    {result : StepResult} {trace trace' : ResourceTrace}
    (hRun :
      Source.runNResultWithOracle program fuel state trace =
        .ok (result, trace')) :
    Compiled.runNResultWithOracle program fuel state trace =
      .ok (result, trace') := by
  induction fuel generalizing state result trace trace' with
  | zero =>
      simp [Source.runNResultWithOracle] at hRun
      simpa [Compiled.runNResultWithOracle] using hRun
  | succ fuel ih =>
      unfold Source.runNResultWithOracle at hRun
      cases hStep : Source.stepResultWithOracle program state trace with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, headTrace⟩
          rw [hStep] at hRun
          unfold Compiled.runNResultWithOracle
          rw [source_compiled_step_result_withOracle_sound hStep]
          cases stepResult with
          | running mid =>
              exact ih hRun
          | halted halt =>
              cases hRun
              rfl

end Preservation

end Assembly
end EvmCompiler
