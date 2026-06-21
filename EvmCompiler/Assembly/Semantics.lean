import EvmCompiler.Assembly.PrimSemantics
import EvmYul.Semantics
import EvmYul.EVM.State
import EvmYul.EVM.StateOps

namespace EvmCompiler
namespace Assembly

abbrev EVMException := EvmYul.EVM.ExecutionException

@[simp] theorem pure_except {α : Type} (value : α) :
    (pure value : Except EVMException α) = .ok value := rfl

@[simp] theorem throw_except {α : Type} (err : EVMException) :
    (throw err : Except EVMException α) = .error err := rfl

@[simp] theorem bind_except_error {α β : Type}
    (err : EVMException) (next : α → Except EVMException β) :
    ((.error err : Except EVMException α) >>= next) = .error err := rfl

@[simp] theorem bind_except_ok {α β : Type}
    (value : α) (next : α → Except EVMException β) :
    ((.ok value : Except EVMException α) >>= next) = next value := rfl

structure Halt where
  kind : HaltKind
  state : EVMState
  output : ByteArray

inductive StepResult where
  | running (state : EVMState)
  | halted (halt : Halt)

inductive FlowStep where
  | next (state : EVMState)
  | exit (result : StepResult)

namespace FlowStep

def result : FlowStep → StepResult
  | .next state => .running state
  | .exit result => result

end FlowStep

namespace StepResult

def IsTerminal : StepResult → Prop
  | .running _ => False
  | .halted _ => True

@[simp] theorem running_not_terminal (state : EVMState) :
    ¬ (StepResult.running state).IsTerminal := by
  simp [IsTerminal]

@[simp] theorem halted_terminal (halt : Halt) :
    (StepResult.halted halt).IsTerminal := by
  simp [IsTerminal]

theorem terminal_iff_exists_halt {result : StepResult} :
    result.IsTerminal ↔ ∃ halt, result = .halted halt := by
  cases result with
  | running state =>
      simp [IsTerminal]
  | halted halt =>
      simp [IsTerminal]

end StepResult

namespace HaltKind

def output (kind : HaltKind) (state : EVMState) : ByteArray :=
  match kind with
  | .stop | .selfdestruct => .empty
  | .return | .revert => state.toMachineState.H_return

end HaltKind

namespace PrimOp

def haltKind? : PrimOp → Option HaltKind
  | .stop => some .stop
  | .return => some .return
  | .revert => some .revert
  | .selfdestruct => some .selfdestruct
  | _ => none

end PrimOp

namespace TargetInstr

def haltKind? : TargetInstr → Option HaltKind
  | .prim op => op.haltKind?
  | _ => none

end TargetInstr

namespace Instr

def haltKind? : Instr → Option HaltKind
  | .prim op => op.haltKind?
  | _ => none

/--
Classify whether a successful Assembly instruction remains in the current
control region or transfers control out of it.

An untaken conditional jump falls through to the next Assembly instruction.
For a taken jump, `continueTransfer` decides whether the edge is internal to
the caller-owned control region. Halts always leave the region.
-/
def classifyFlowWith (continueTransfer : Instr → Bool)
    (instr : Instr) (before : EVMState) :
    StepResult → FlowStep
  | .halted halt => .exit (.halted halt)
  | .running after =>
      match instr with
      | .jump _ =>
          if continueTransfer instr then
            .next after
          else
            .exit (.running after)
      | .jumpi _ =>
          match before.stack.pop with
          | none => .exit (.running after)
          | some (_, cond) =>
              if cond = EvmYul.UInt256.ofNat 0 then
                .next after
              else if continueTransfer instr then
                .next after
              else
                .exit (.running after)
      | _ => .next after

/--
The basic-block policy: every taken jump leaves the current region.
-/
def classifyFlow (instr : Instr) (before : EVMState) :
    StepResult → FlowStep :=
  classifyFlowWith (fun _ => false) instr before

theorem classifyFlowWith_false
    (instr : Instr) (before : EVMState) (result : StepResult) :
    classifyFlowWith (fun _ => false) instr before result =
      classifyFlow instr before result := rfl

end Instr

namespace Control

def runNWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (step : EVMState → M EVMState) : Nat → EVMState → M EVMState
  | 0, state => pure state
  | fuel + 1, state => do
      let state' ← step state
      runNWith step fuel state'

def runNResultWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (step : EVMState → M StepResult) : Nat → EVMState → M StepResult
  | 0, state => pure (.running state)
  | fuel + 1, state => do
      let result ← step state
      match result with
      | .running state' => runNResultWith step fuel state'
      | .halted halt => pure (.halted halt)

def runUntilTransferWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (step : EVMState → M FlowStep) :
    Nat → EVMState → M StepResult
  | 0, state => pure (.running state)
  | fuel + 1, state => do
      let flow ← step state
      match flow with
      | .next state' =>
          runUntilTransferWith step fuel state'
      | .exit result =>
          pure result

end Control

namespace Target

abbrev stepPushWith {Result : Type}
    (pureState : EVMState -> Result)
    (width : Nat) (value : Word) (state : EVMState) : Result :=
  pureState <| state.replaceStackAndIncrPC
    (state.stack.push value) (pcΔ := width + 1)

abbrev stepInstrWith {Result : Type}
    (pureState : EVMState → Result)
    (throwState : EVMException → Result)
    (primStep : PrimOp → EVMState → Result)
    (instr : TargetInstr) (state : EVMState) : Result :=
  match instr with
  | .push32 value =>
      stepPushWith pureState 32 value state
  | .jump =>
    match state.stack.pop with
    | some (stack, dest) =>
        pureState { state with pc := dest, stack := stack }
    | none =>
        throwState .StackUnderflow
  | .jumpi =>
    match state.stack.pop2 with
    | some (stack, dest, cond) =>
        let pc' :=
          if cond != EvmYul.UInt256.ofNat 0 then
            dest
          else
            state.pc + EvmYul.UInt256.ofNat 1
        pureState { state with pc := pc', stack := stack }
    | none =>
        throwState .StackUnderflow
  | .jumpdest =>
      pureState state.incrPC
  | .prim op =>
      primStep op state

@[simp] theorem stepInstrWith_prim {Result : Type}
    (pureState : EVMState → Result)
    (throwState : EVMException → Result)
    (primStep : PrimOp → EVMState → Result)
    (op : PrimOp) (state : EVMState) :
    stepInstrWith pureState throwState primStep (.prim op) state =
      primStep op state := rfl

def stepInstr (instr : TargetInstr) (state : EVMState) :
    Except EVMException EVMState :=
  match instr with
  | .push32 value =>
      stepInstrWith Except.ok Except.error PrimOp.step (.push32 value) state
  | .jump =>
      stepInstrWith Except.ok Except.error PrimOp.step .jump state
  | .jumpi =>
      stepInstrWith Except.ok Except.error PrimOp.step .jumpi state
  | .jumpdest =>
      stepInstrWith Except.ok Except.error PrimOp.step .jumpdest state
  | .prim op =>
      stepInstrWith Except.ok Except.error PrimOp.step (.prim op) state

@[simp] theorem stepInstr_prim (op : PrimOp) (state : EVMState) :
    stepInstr (.prim op) state = op.step state := rfl

def stepInstrResultWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : TargetInstr → EVMState → M EVMState)
    (instr : TargetInstr) (state : EVMState) : M StepResult := do
  let state' ← instrStep instr state
  match instr.haltKind? with
  | some kind =>
      pure (.halted { kind := kind, state := state', output := kind.output state' })
  | none =>
      pure (.running state')

def stepInstrResult (instr : TargetInstr) (state : EVMState) :
    Except EVMException StepResult := do
  let state' ← stepInstr instr state
  match instr.haltKind? with
  | some kind =>
      .ok (.halted { kind := kind, state := state', output := kind.output state' })
  | none =>
      .ok (.running state')

def runListWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : TargetInstr → EVMState → M EVMState) :
    List TargetInstr → EVMState → M EVMState
  | [], state => pure state
  | instr :: rest, state => do
      let state' ← instrStep instr state
      runListWith instrStep rest state'

def runListResultWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : TargetInstr → EVMState → M StepResult) :
    List TargetInstr → EVMState → M StepResult
  | [], state => pure (.running state)
  | instr :: rest, state => do
      let result ← instrStep instr state
      match result with
      | .running state' => runListResultWith instrStep rest state'
      | .halted halt => pure (.halted halt)

def stepWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : TargetInstr → EVMState → M EVMState)
    (target : TargetProgram) (state : EVMState) : M EVMState :=
  match target.fetch state.pc.toNat with
  | some instr => instrStep instr state
  | none => throw .InvalidInstruction

def stepResultWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : TargetInstr → EVMState → M StepResult)
    (target : TargetProgram) (state : EVMState) : M StepResult :=
  match target.fetch state.pc.toNat with
  | some instr => instrStep instr state
  | none => throw .InvalidInstruction

abbrev runNWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : TargetInstr → EVMState → M EVMState)
    (target : TargetProgram) (fuel : Nat) (state : EVMState) : M EVMState :=
  Control.runNWith (stepWith instrStep target) fuel state

abbrev runNResultWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : TargetInstr → EVMState → M StepResult)
    (target : TargetProgram) (fuel : Nat) (state : EVMState) : M StepResult :=
  Control.runNResultWith (stepResultWith instrStep target) fuel state

abbrev runList (code : List TargetInstr) (state : EVMState) :
    Except EVMException EVMState :=
  runListWith stepInstr code state

abbrev runListResult (code : List TargetInstr) (state : EVMState) :
    Except EVMException StepResult :=
  runListResultWith stepInstrResult code state

abbrev step (target : TargetProgram) (state : EVMState) :
    Except EVMException EVMState :=
  stepWith stepInstr target state

abbrev stepResult (target : TargetProgram) (state : EVMState) :
    Except EVMException StepResult :=
  stepResultWith stepInstrResult target state

abbrev runN (target : TargetProgram) (fuel : Nat) (state : EVMState) :
    Except EVMException EVMState :=
  runNWith stepInstr target fuel state

abbrev runNResult (target : TargetProgram) (fuel : Nat) (state : EVMState) :
    Except EVMException StepResult :=
  runNResultWith stepInstrResult target fuel state

end Target

namespace Source

def invalid {α : Type} : Except EVMException α :=
  .error .InvalidInstruction

def jumpPc (dest : Nat) (state : EVMState) : EVMState :=
  { state with pc := EvmYul.UInt256.ofNat dest }

def jumpiFallthroughPc (state : EVMState) : Word :=
  state.pc + EvmYul.UInt256.ofNat Instr.push32Size + EvmYul.UInt256.ofNat 1

def stepAt (program : Program) (_pc : Nat) (instr : Instr)
    (state : EVMState) : Except EVMException EVMState :=
  match instr with
  | .label _ =>
      Target.stepInstr TargetInstr.jumpdest state
  | .prim op =>
      Target.stepInstr (TargetInstr.prim op) state
  | .push value =>
      Target.stepInstr (TargetInstr.push32 value) state
  | .jump target => do
      let dest ← (Program.labelPc program target).elim invalid pure
      pure (jumpPc dest state)
  | .jumpi target => do
      let dest ← (Program.labelPc program target).elim invalid pure
      match state.stack.pop with
      | some (stack, cond) =>
          let pc' :=
            if cond != EvmYul.UInt256.ofNat 0 then
              EvmYul.UInt256.ofNat dest
            else
              jumpiFallthroughPc state
          pure { state with pc := pc', stack := stack }
      | none =>
          .error .StackUnderflow

def stepAtResult (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) : Except EVMException StepResult := do
  let state' ← stepAt program pc instr state
  match instr.haltKind? with
  | some kind =>
      .ok (.halted { kind := kind, state := state', output := kind.output state' })
  | none =>
      .ok (.running state')

def stepWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : Nat → Instr → EVMState → M EVMState)
    (program : Program) (state : EVMState) : M EVMState :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => instrStep pc instr state
  | none => throw .InvalidInstruction

def stepResultWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (instrStep : Nat → Instr → EVMState → M StepResult)
    (program : Program) (state : EVMState) : M StepResult :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => instrStep pc instr state
  | none => throw .InvalidInstruction

def flowStepWithPolicy {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (continueTransfer : Instr → Bool)
    (step : EVMState → M StepResult)
    (program : Program) (state : EVMState) : M FlowStep :=
  match Program.instrAtPc program state.pc.toNat with
  | some (_, instr) => do
      let result ← step state
      pure (instr.classifyFlowWith continueTransfer state result)
  | none => throw .InvalidInstruction

abbrev flowStepWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (step : EVMState → M StepResult)
    (program : Program) (state : EVMState) : M FlowStep :=
  flowStepWithPolicy (fun _ => false) step program state

def runUntilTransferWithPolicy {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (continueTransfer : Instr → Bool)
    (step : EVMState → M StepResult)
    (program : Program) (fuel : Nat)
    (state : EVMState) : M StepResult :=
  Control.runUntilTransferWith
    (flowStepWithPolicy continueTransfer step program) fuel state

abbrev runUntilTransferWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (step : EVMState → M StepResult)
    (program : Program) (fuel : Nat)
    (state : EVMState) : M StepResult :=
  runUntilTransferWithPolicy (fun _ => false)
    step program fuel state

abbrev step (program : Program) (state : EVMState) :
    Except EVMException EVMState :=
  stepWith (stepAt program) program state

abbrev stepResult (program : Program) (state : EVMState) :
    Except EVMException StepResult :=
  stepResultWith (stepAtResult program) program state

abbrev runN (program : Program) (fuel : Nat) (state : EVMState) :
    Except EVMException EVMState :=
  Control.runNWith (step program) fuel state

theorem runN_add (program : Program) (first second : Nat)
    (state : EVMState) :
    runN program (first + second) state =
      (do
        let state' ← runN program first state
        runN program second state') := by
  induction first generalizing state with
  | zero =>
      simp [runN, Control.runNWith]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [runN, Control.runNWith]
      cases hStep : step program state with
      | error err =>
          simp only [hStep, Bind.bind, Except.bind]
      | ok state' =>
          simp only [hStep, Bind.bind, Except.bind]
          exact ih state'

abbrev runNResult (program : Program) (fuel : Nat) (state : EVMState) :
    Except EVMException StepResult :=
  Control.runNResultWith (stepResult program) fuel state

abbrev runUntilTransfer (program : Program) (fuel : Nat)
    (state : EVMState) : Except EVMException StepResult :=
  runUntilTransferWith (stepResult program) program fuel state

abbrev ExecutionOutcome := Except EVMException StepResult

/--
An execution segment ending in any observable Assembly outcome.

Unlike the historical preservation helper, this contract retains target errors
as outcomes. That is necessary for source layers such as `TypedCfg`, whose
single `invalid` result intentionally abstracts over several concrete EVM
exceptions.
-/
def Eventually (program : Program) (state : EVMState)
    (post : ExecutionOutcome → Prop) : Prop :=
  ∃ fuel outcome,
    runNResult program fuel state = outcome ∧ post outcome

theorem runNResult_add (program : Program) (first second : Nat)
    (state : EVMState) :
    runNResult program (first + second) state =
      (do
        let result ← runNResult program first state
        match result with
        | .running mid => runNResult program second mid
        | .halted halt => .ok (.halted halt)) := by
  induction first generalizing state with
  | zero =>
      simp [runNResult, Control.runNResultWith]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [runNResult, Control.runNResultWith]
      cases hStep : stepResult program state with
      | error err =>
          simp only [hStep, Bind.bind, Except.bind]
      | ok result =>
          simp only [hStep, Bind.bind, Except.bind]
          cases result with
          | halted halt =>
              rfl
          | running state' =>
              exact ih state'

theorem runNResult_add_of_running
    (program : Program) (first second : Nat)
    {state mid : EVMState}
    (hFirst :
      runNResult program first state = .ok (.running mid)) :
    runNResult program (first + second) state =
      runNResult program second mid := by
  rw [runNResult_add]
  rw [hFirst]
  rfl

namespace Eventually

theorem pure {program : Program} {state : EVMState}
    {post : ExecutionOutcome → Prop}
    (hPost : post (.ok (.running state))) :
    Eventually program state post := by
  exact
    ⟨0, .ok (.running state),
      by simp [runNResult, Control.runNResultWith], hPost⟩

theorem bind_running {program : Program} {state : EVMState}
    {middle : EVMState → Prop} {post : ExecutionOutcome → Prop}
    (hRun :
      Eventually program state
        (fun outcome =>
          match outcome with
          | .ok (.running mid) => middle mid
          | _ => False))
    (hNext : ∀ mid, middle mid → Eventually program mid post) :
    Eventually program state post := by
  rcases hRun with ⟨firstFuel, firstOutcome, hFirst, hMiddle⟩
  cases firstOutcome with
  | error err =>
      cases hMiddle
  | ok result =>
      cases result with
      | halted halt =>
          cases hMiddle
      | running mid =>
          rcases hNext mid hMiddle with
            ⟨secondFuel, outcome, hSecond, hPost⟩
          exact
            ⟨firstFuel + secondFuel, outcome,
              (runNResult_add_of_running program firstFuel secondFuel
                hFirst).trans hSecond,
              hPost⟩

theorem mono {program : Program} {state : EVMState}
    {post₁ post₂ : ExecutionOutcome → Prop}
    (hRun : Eventually program state post₁)
    (hPost : ∀ outcome, post₁ outcome → post₂ outcome) :
    Eventually program state post₂ := by
  rcases hRun with ⟨fuel, outcome, hRun, hOutcome⟩
  exact ⟨fuel, outcome, hRun, hPost outcome hOutcome⟩

end Eventually

end Source

def emitCurrent? (program : Program) (state : EVMState) : Option (List TargetInstr) := do
  let (pc, instr) ← Program.instrAtPc program state.pc.toNat
  let located ← emitInstr? program pc instr
  some (located.map LocatedTarget.instr)

namespace Compiled

def stepWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runBlock : List TargetInstr → EVMState → M EVMState)
    (program : Program) (state : EVMState) : M EVMState :=
  match emitCurrent? program state with
  | some code => runBlock code state
  | none => throw .InvalidInstruction

def stepResultWith {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runBlock : List TargetInstr → EVMState → M StepResult)
    (program : Program) (state : EVMState) : M StepResult :=
  match emitCurrent? program state with
  | some code => runBlock code state
  | none => throw .InvalidInstruction

abbrev step (program : Program) (state : EVMState) :
    Except EVMException EVMState :=
  stepWith Target.runList program state

abbrev stepResult (program : Program) (state : EVMState) :
    Except EVMException StepResult :=
  stepResultWith Target.runListResult program state

abbrev runN (program : Program) (fuel : Nat) (state : EVMState) :
    Except EVMException EVMState :=
  Control.runNWith (step program) fuel state

abbrev runNResult (program : Program) (fuel : Nat) (state : EVMState) :
    Except EVMException StepResult :=
  Control.runNResultWith (stepResult program) fuel state

end Compiled

theorem SameData.jumpPc (dest : Nat) (state : EVMState) :
    SameData (Source.jumpPc dest state) state := by
  simp [SameData, Source.jumpPc, eraseControl_with_pc]

theorem SameRuntimeData.jumpPc (dest : Nat) (state : EVMState) :
    SameRuntimeData (Source.jumpPc dest state) state := by
  exact SameRuntimeData.with_pc_left _ (SameRuntimeData.refl state)

end Assembly
end EvmCompiler
