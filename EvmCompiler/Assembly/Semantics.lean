import EvmCompiler.Assembly.PrimSemantics
import EvmYul.Semantics
import EvmYul.EVM.State
import EvmYul.EVM.StateOps

namespace EvmCompiler
namespace Assembly

abbrev EVMState := EvmYul.EVM.State
abbrev EVMException := EvmYul.EVM.ExecutionException

structure Halt where
  kind : HaltKind
  state : EVMState
  output : ByteArray

inductive StepResult where
  | running (state : EVMState)
  | halted (halt : Halt)

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

end Instr

namespace Target

def stepInstr (instr : TargetInstr) (state : EVMState) : Except EVMException EVMState :=
  match instr with
  | .push32 value =>
      .ok <| state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33)
  | .jump =>
    match state.stack.pop with
    | some (stack, dest) =>
        .ok { state with pc := dest, stack := stack }
    | none =>
        .error .StackUnderflow
  | .jumpi =>
    match state.stack.pop2 with
    | some (stack, dest, cond) =>
        let pc' :=
          if cond != EvmYul.UInt256.ofNat 0 then
            dest
          else
            state.pc + EvmYul.UInt256.ofNat 1
        .ok { state with pc := pc', stack := stack }
    | none =>
        .error .StackUnderflow
  | .jumpdest =>
      .ok state.incrPC
  | .prim op =>
      op.step state

def stepInstrResult (instr : TargetInstr) (state : EVMState) :
    Except EVMException StepResult := do
  let state' ← stepInstr instr state
  match instr.haltKind? with
  | some kind =>
      .ok (.halted { kind := kind, state := state', output := kind.output state' })
  | none =>
      .ok (.running state')

def runList : List TargetInstr → EVMState → Except EVMException EVMState
  | [], state => .ok state
  | instr :: rest, state => do
      let state' ← stepInstr instr state
      runList rest state'

def runListResult : List TargetInstr → EVMState → Except EVMException StepResult
  | [], state => .ok (.running state)
  | instr :: rest, state => do
      let result ← stepInstrResult instr state
      match result with
      | .running state' => runListResult rest state'
      | .halted halt => .ok (.halted halt)

def step (target : TargetProgram) (state : EVMState) : Except EVMException EVMState :=
  match target.fetch state.pc.toNat with
  | some instr => stepInstr instr state
  | none => .error .InvalidInstruction

def stepResult (target : TargetProgram) (state : EVMState) :
    Except EVMException StepResult :=
  match target.fetch state.pc.toNat with
  | some instr => stepInstrResult instr state
  | none => .error .InvalidInstruction

def runN (target : TargetProgram) : Nat → EVMState → Except EVMException EVMState
  | 0, state => .ok state
  | fuel + 1, state => do
      let state' ← step target state
      runN target fuel state'

def runNResult (target : TargetProgram) : Nat → EVMState → Except EVMException StepResult
  | 0, state => .ok (.running state)
  | fuel + 1, state => do
      let result ← stepResult target state
      match result with
      | .running state' => runNResult target fuel state'
      | .halted halt => .ok (.halted halt)

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

def step (program : Program) (state : EVMState) : Except EVMException EVMState :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => stepAt program pc instr state
  | none => .error .InvalidInstruction

def stepResult (program : Program) (state : EVMState) :
    Except EVMException StepResult :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => stepAtResult program pc instr state
  | none => .error .InvalidInstruction

def runN (program : Program) : Nat → EVMState → Except EVMException EVMState
  | 0, state => .ok state
  | fuel + 1, state => do
      let state' ← step program state
      runN program fuel state'

theorem runN_add (program : Program) (first second : Nat)
    (state : EVMState) :
    runN program (first + second) state =
      (do
        let state' ← runN program first state
        runN program second state') := by
  induction first generalizing state with
  | zero =>
      simp only [Nat.zero_add, runN.eq_1, Bind.bind, Except.bind]
  | succ first ih =>
      rw [Nat.succ_add, runN.eq_2, runN.eq_2]
      cases hStep : step program state with
      | error err =>
          simp only [hStep, Bind.bind, Except.bind]
      | ok state' =>
          simp only [hStep, Bind.bind, Except.bind]
          exact ih state'

def runNResult (program : Program) : Nat → EVMState → Except EVMException StepResult
  | 0, state => .ok (.running state)
  | fuel + 1, state => do
      let result ← stepResult program state
      match result with
      | .running state' => runNResult program fuel state'
      | .halted halt => .ok (.halted halt)

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
      simp only [Nat.zero_add, runNResult, Bind.bind, Except.bind]
  | succ first ih =>
      rw [Nat.succ_add, runNResult, runNResult]
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
  exact ⟨0, .ok (.running state), by simp [runNResult], hPost⟩

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

def step (program : Program) (state : EVMState) : Except EVMException EVMState :=
  match emitCurrent? program state with
  | some code => Target.runList code state
  | none => .error .InvalidInstruction

def stepResult (program : Program) (state : EVMState) :
    Except EVMException StepResult :=
  match emitCurrent? program state with
  | some code => Target.runListResult code state
  | none => .error .InvalidInstruction

def runN (program : Program) : Nat → EVMState → Except EVMException EVMState
  | 0, state => .ok state
  | fuel + 1, state => do
      let state' ← step program state
      runN program fuel state'

def runNResult (program : Program) : Nat → EVMState → Except EVMException StepResult
  | 0, state => .ok (.running state)
  | fuel + 1, state => do
      let result ← stepResult program state
      match result with
      | .running state' => runNResult program fuel state'
      | .halted halt => .ok (.halted halt)

end Compiled

/--
The observable state relation for the gasless layer.

The first verified slice actually proves exact equality against the gasless
target semantics. This projection names the intended claim boundary for the
later full-EVM theorem, where EVM gas accounting and execution counters will be
erased before comparison.
-/
def eraseGas (state : EVMState) : EVMState :=
  { state with
    gasAvailable := EvmYul.UInt256.ofNat 0
    execLength := 0
  }

/--
Erase lowering-only control position and accounting fields while retaining the
ordinary EVM data observed by adjacent compiler IRs.

Structured and TypedCfg control transfers are atomic, while their Assembly
lowerings may execute labels, stack shuffles, and dispatch tests. Those hidden
instructions legitimately change `pc` and `execLength`.
-/
def eraseControl (state : EVMState) : EVMState :=
  { eraseGas state with pc := EvmYul.UInt256.ofNat 0 }

def SameData (target source : EVMState) : Prop :=
  eraseControl target = eraseControl source

theorem eraseControl_with_pc (state : EVMState) (pc : Word) :
    eraseControl { state with pc := pc } = eraseControl state := by
  cases state
  rfl

theorem eraseControl_with_stack (state : EVMState)
    (stack : EvmYul.Stack Word) :
    eraseControl { state with stack := stack } =
      { eraseControl state with stack := stack } := by
  cases state
  rfl

theorem eraseControl_with_stack_congr {left right : EVMState}
    {stack : EvmYul.Stack Word}
    (hEq : eraseControl left = eraseControl right) :
    eraseControl { left with stack := stack } =
      eraseControl { right with stack := stack } := by
  cases left
  cases right
  simp [eraseControl, eraseGas] at hEq ⊢
  exact hEq.1

theorem eraseControl_replaceStackAndIncrPC_of_eq
    {left right : EVMState}
    {leftStack rightStack : EvmYul.Stack Word} {pcΔ : Nat}
    (hEq : eraseControl left = eraseControl right)
    (hStack : leftStack = rightStack) :
    eraseControl
        (left.replaceStackAndIncrPC leftStack (pcΔ := pcΔ)) =
      eraseControl
        (right.replaceStackAndIncrPC rightStack (pcΔ := pcΔ)) := by
  cases left
  cases right
  simp [eraseControl, eraseGas] at hEq ⊢
  exact ⟨hEq.1, hStack⟩

theorem SameData.refl (state : EVMState) :
    SameData state state := rfl

theorem SameData.trans {first second third : EVMState}
    (hFirst : SameData first second)
    (hSecond : SameData second third) :
    SameData first third :=
  Eq.trans hFirst hSecond

theorem SameData.jumpPc (dest : Nat) (state : EVMState) :
    SameData (Source.jumpPc dest state) state := by
  simp [SameData, Source.jumpPc, eraseControl_with_pc]

end Assembly
end EvmCompiler
