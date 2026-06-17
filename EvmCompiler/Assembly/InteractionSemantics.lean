import EvmCompiler.Assembly.Semantics
import EvmCompiler.Simulation.Interaction

namespace EvmCompiler
namespace Assembly
namespace InteractionSemantics

abbrev OpenStep :=
  Simulation.Interaction EVMException EVMState

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
  match instr with
  | .prim op => PrimOp.openStep op state
  | _ => .done (Assembly.Target.stepInstr instr state)

end Target

namespace Source

def openStepAt (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) : OpenStep :=
  match instr with
  | .prim op => PrimOp.openStep op state
  | _ => .done (Assembly.Source.stepAt program pc instr state)

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

end InteractionSemantics
end Assembly
end EvmCompiler
