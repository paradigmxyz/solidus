import EvmCompiler.Assembly.Preservation

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
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      cases hEmit
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .label name)
            (emitted := [{ pc := pc, instr := TargetInstr.jumpdest }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      change Target.runNResultWithOracle target 1 state trace =
        .ok (result, trace')
      rw [target_runNResultWithOracle_single_of_fetch hFetch]
      simpa using hRun
  | prim op =>
      simp [emitInstr?] at hEmit
      cases hEmit
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .prim op)
            (emitted := [{ pc := pc, instr := TargetInstr.prim op }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      change Target.runNResultWithOracle target 1 state trace =
        .ok (result, trace')
      rw [target_runNResultWithOracle_single_of_fetch hFetch]
      simpa using hRun
  | push value =>
      simp [emitInstr?] at hEmit
      cases hEmit
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .push value)
            (emitted := [{ pc := pc, instr := TargetInstr.push32 value }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      change Target.runNResultWithOracle target 1 state trace =
        .ok (result, trace')
      rw [target_runNResultWithOracle_single_of_fetch hFetch]
      simpa using hRun
  | jump targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          cases hEmit
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
          change Target.runNResultWithOracle target 2 state trace =
            .ok (result, trace')
          rw [target_runNResultWithOracle_push_jump_of_fetch
            hFetchPush hFetchJump hNoOverflow]
          simpa using hRun
  | jumpi targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          cases hEmit
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
          change Target.runNResultWithOracle target 2 state trace =
            .ok (result, trace')
          rw [target_runNResultWithOracle_push_jumpi_of_fetch
            hFetchPush hFetchJumpi hNoOverflow]
          simpa using hRun

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
