import EvmCompiler.Assembly.Semantics
import EvmCompiler.Simulation.Interaction

namespace EvmCompiler
namespace Assembly
namespace InteractionSemantics

abbrev OpenStep :=
  Simulation.Interaction EVMException EVMState

abbrev OpenStepResult :=
  Simulation.Interaction EVMException StepResult

namespace Control

theorem openRunNResultWith_add
    (step : EVMState → OpenStepResult)
    (first second : Nat) (state : EVMState) :
    Assembly.Control.runNResultWith step (first + second) state =
      (do
        let result ←
          Assembly.Control.runNResultWith step first state
        match result with
        | .running mid =>
            Assembly.Control.runNResultWith step second mid
        | .halted halt =>
            pure (.halted halt)) := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      simp only [Assembly.Control.runNResultWith]
      change
        Assembly.Control.runNResultWith step second state =
          Simulation.Interaction.bind
            (Simulation.Interaction.pure
              (Error := EVMException) (StepResult.running state))
            (fun result =>
              match result with
              | StepResult.running mid =>
                  Assembly.Control.runNResultWith step second mid
              | StepResult.halted halt =>
                  Simulation.Interaction.pure (StepResult.halted halt))
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [Assembly.Control.runNResultWith]
      change
        Simulation.Interaction.bind (step state)
            (fun result =>
              match result with
              | .running state' =>
                  Assembly.Control.runNResultWith
                    step (first + second) state'
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind (step state)
              (fun result =>
                match result with
                | .running state' =>
                    Assembly.Control.runNResultWith step first state'
                | .halted halt =>
                    Simulation.Interaction.pure (.halted halt)))
            (fun result =>
              match result with
              | .running mid =>
                  Assembly.Control.runNResultWith step second mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt))
      rw [Simulation.Interaction.bind_assoc]
      congr
      funext result
      cases result with
      | running mid =>
          exact ih mid
      | halted halt =>
          rfl

end Control

namespace EVMState

def installWorld (state : EVMState) (world : Simulation.OpenWorld) :
    EVMState :=
  { state with
    toSharedState :=
      Simulation.OpenWorld.installEVMShared state.toSharedState world }

def finishCall (state : EVMState) (rest : EvmYul.Stack Word)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse) : EVMState :=
  let withWorld := installWorld state response.postWorld
  let machine :=
    callLocal.finishMachine state.toMachineState response.returnData
  EvmYul.EVM.State.incrPC
    { withWorld with
      toMachineState := machine
      stack := response.statusWord :: rest }

def finishCreate (state : EVMState) (rest : EvmYul.Stack Word)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse) : EVMState :=
  let withWorld := installWorld state response.postWorld
  let machine :=
    createLocal.finishMachine state.toMachineState response.returnData
  EvmYul.EVM.State.incrPC
    { withWorld with
      toMachineState := machine
      stack := response.address :: rest }

end EVMState

namespace PrimOp

def resourceStep (kind : Simulation.ResourceQuery)
    (state : EVMState) : OpenStep :=
  .request (.resource kind) fun value =>
    .done
      (.ok
        (state.replaceStackAndIncrPC (state.stack.push value)))

def callStep (kind : Simulation.CallKind)
    (state : EVMState) : OpenStep :=
  match kind.evmOperands? state.stack with
  | none => .done (.error .StackUnderflow)
  | some (rest, operands) =>
      let frame := Simulation.ExternalFrame.ofShared state.toSharedState
      if kind.allowedIn frame operands then
        let callLocal := operands.callLocal
        let request := frame.callRequest kind operands
        let world := Simulation.OpenWorld.ofEVMShared state.toSharedState
        .request (.external world (.call request)) fun response =>
          .done
            (.ok
              (EVMState.finishCall state rest callLocal response))
      else
        .done (.error .StaticModeViolation)

def createStep (kind : Simulation.CreateKind)
    (state : EVMState) : OpenStep :=
  match kind.evmOperands? state.stack with
  | none => .done (.error .StackUnderflow)
  | some (rest, operands) =>
      let frame := Simulation.ExternalFrame.ofShared state.toSharedState
      if frame.permission then
        let createLocal := operands.createLocal
        let request := frame.createRequest kind operands
        let world := Simulation.OpenWorld.ofEVMShared state.toSharedState
        .request (.external world (.create request)) fun response =>
          .done
            (.ok
              (EVMState.finishCreate state rest createLocal response))
      else
        .done (.error .StaticModeViolation)

/--
Open primitive semantics for the Assembly owner.

Ordinary primitives embed their existing semantics. `gas` and `msize` suspend
at resource queries, while every CALL/CREATE-family primitive suspends at the
one shared open-world protocol.
-/
def openStep (op : Assembly.PrimOp) (state : EVMState) : OpenStep :=
  match Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some (.call kind) => callStep kind state
  | some (.create kind) => createStep kind state
  | none =>
      match op with
      | .gas => resourceStep .gas state
      | .msize => resourceStep .msize state
      | _ => .done (op.step state)

theorem openStep_closed
    {op : Assembly.PrimOp} {state : EVMState}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize) :
    openStep op state = .done (op.step state) := by
  cases op <;>
    simp [openStep, hExternal] at hGas hMsize ⊢

@[simp] theorem openStep_gas (state : EVMState) :
    openStep .gas state = resourceStep .gas state := rfl

@[simp] theorem openStep_msize (state : EVMState) :
    openStep .msize state = resourceStep .msize state := rfl

@[simp] theorem openStep_call (state : EVMState) :
    openStep .call state = callStep .call state := rfl

@[simp] theorem openStep_callcode (state : EVMState) :
    openStep .callcode state = callStep .callcode state := rfl

@[simp] theorem openStep_delegatecall (state : EVMState) :
    openStep .delegatecall state = callStep .delegatecall state := rfl

@[simp] theorem openStep_staticcall (state : EVMState) :
    openStep .staticcall state = callStep .staticcall state := rfl

@[simp] theorem openStep_create (state : EVMState) :
    openStep .create state = createStep .create state := rfl

@[simp] theorem openStep_create2 (state : EVMState) :
    openStep .create2 state = createStep .create2 state := rfl

end PrimOp

namespace Target

def openStepInstr (instr : TargetInstr) (state : EVMState) : OpenStep :=
  Assembly.Target.stepInstrWith
    (fun next => .done (.ok next))
    (fun err => .done (.error err))
    PrimOp.openStep instr state

def openStepInstrResult (instr : TargetInstr) (state : EVMState) :
    OpenStepResult :=
  Assembly.Target.stepInstrResultWith openStepInstr instr state

def openRunList (code : List TargetInstr) (state : EVMState) : OpenStep :=
  Assembly.Target.runListWith openStepInstr code state

def openRunListResult (code : List TargetInstr) (state : EVMState) :
    OpenStepResult :=
  Assembly.Target.runListResultWith openStepInstrResult code state

def openStep (target : TargetProgram) (state : EVMState) : OpenStep :=
  Assembly.Target.stepWith openStepInstr target state

def openStepResult (target : TargetProgram) (state : EVMState) :
    OpenStepResult :=
  Assembly.Target.stepResultWith openStepInstrResult target state

def openRunN (target : TargetProgram) (fuel : Nat) (state : EVMState) :
    OpenStep :=
  Assembly.Target.runNWith openStepInstr target fuel state

def openRunNResult (target : TargetProgram) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Target.runNResultWith openStepInstrResult target fuel state

theorem openRunNResult_add
    (target : TargetProgram) (first second : Nat)
    (state : EVMState) :
    openRunNResult target (first + second) state =
      (do
        let result ← openRunNResult target first state
        match result with
        | .running mid =>
            openRunNResult target second mid
        | .halted halt =>
            pure (.halted halt)) := by
  exact
    Control.openRunNResultWith_add
      (Assembly.Target.stepResultWith openStepInstrResult target)
      first second state

end Target

namespace Source

def openStepAt (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) : OpenStep :=
  match instr with
  | .prim op => PrimOp.openStep op state
  | _ => .done (Assembly.Source.stepAt program pc instr state)

def openStepAtResult (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) : OpenStepResult := do
  let state' ← openStepAt program pc instr state
  match instr.haltKind? with
  | some kind =>
      pure (.halted { kind := kind, state := state', output := kind.output state' })
  | none =>
      pure (.running state')

def openStep (program : Program) (state : EVMState) : OpenStep :=
  Assembly.Source.stepWith (openStepAt program) program state

def openStepResult (program : Program) (state : EVMState) :
    OpenStepResult :=
  Assembly.Source.stepResultWith (openStepAtResult program) program state

def openRunN (program : Program) (fuel : Nat) (state : EVMState) :
    OpenStep :=
  Assembly.Control.runNWith (openStep program) fuel state

def openRunNResult (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Control.runNResultWith (openStepResult program) fuel state

theorem openRunNResult_add
    (program : Program) (first second : Nat)
    (state : EVMState) :
    openRunNResult program (first + second) state =
      (do
        let result ← openRunNResult program first state
        match result with
        | .running mid =>
            openRunNResult program second mid
        | .halted halt =>
            pure (.halted halt)) := by
  exact
    Control.openRunNResultWith_add
      (Assembly.Source.stepResultWith (openStepAtResult program) program)
      first second state

/--
The primitive case of the Assembly-to-resolved-instruction boundary is exact:
both sides expose the same query and use the same continuation for every
answer. This is the seed used by the pass-owned recursive composition proof.
-/
theorem prim_openStep_rel
    (program : Program) (pc : Nat) (op : Assembly.PrimOp)
    (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (openStepAt program pc (.prim op) state)
      (Target.openStepInstr (.prim op) state) := by
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

end Source

namespace Compiled

def openStep (program : Program) (state : EVMState) : OpenStep :=
  Assembly.Compiled.stepWith Target.openRunList program state

def openStepResult (program : Program) (state : EVMState) :
    OpenStepResult :=
  Assembly.Compiled.stepResultWith Target.openRunListResult program state

def openRunN (program : Program) (fuel : Nat) (state : EVMState) :
    OpenStep :=
  Assembly.Control.runNWith (openStep program) fuel state

def openRunNResult (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Control.runNResultWith (openStepResult program) fuel state

end Compiled

end InteractionSemantics
end Assembly
end EvmCompiler
