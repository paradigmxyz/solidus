import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.TypedCfg.Control

namespace EvmCompiler
namespace TypedCfg
namespace InteractionSemantics

abbrev OpenStep :=
  Simulation.Interaction EVMException EVMState

abbrev OpenOutcome :=
  Simulation.Interaction EVMException TypedCfg.Outcome

namespace Instr

/--
The TypedCfg instruction specialization of the shared open semantics.

Every primitive delegates to the Assembly-owned primitive semantics. All
TypedCfg-only bookkeeping instructions embed their ordinary authoritative
semantics.
-/
def openRunState (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) : OpenStep :=
  match instr with
  | .prim op =>
      Assembly.InteractionSemantics.PrimOp.openStep op state
  | _ =>
      .done (TypedCfg.Instr.runState instr shape state)

def openRunAt (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) :
    Simulation.Interaction EVMException (EVMState × Shape) :=
  Control.Instr.runAt openRunState instr shape state

@[simp] theorem openRunState_gas (shape : Shape) (state : EVMState) :
    openRunState (.prim .gas) shape state =
      Assembly.InteractionSemantics.PrimOp.resourceStep
        .gas state := rfl

@[simp] theorem openRunState_msize (shape : Shape) (state : EVMState) :
    openRunState (.prim .msize) shape state =
      Assembly.InteractionSemantics.PrimOp.resourceStep
        .msize state := rfl

@[simp] theorem openRunState_call (shape : Shape) (state : EVMState) :
    openRunState (.prim .call) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .call state := rfl

@[simp] theorem openRunState_callcode
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .callcode) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .callcode state := rfl

@[simp] theorem openRunState_delegatecall
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .delegatecall) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .delegatecall state := rfl

@[simp] theorem openRunState_staticcall
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .staticcall) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .staticcall state := rfl

@[simp] theorem openRunState_create
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .create) shape state =
      Assembly.InteractionSemantics.PrimOp.createStep
        .create state := rfl

@[simp] theorem openRunState_create2
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .create2) shape state =
      Assembly.InteractionSemantics.PrimOp.createStep
        .create2 state := rfl

end Instr

namespace Block

def openRunBody (body : List TypedCfg.Instr) (shape : Shape)
    (state : EVMState) :
    Simulation.Interaction EVMException (EVMState × Shape) :=
  Control.Block.runBody Instr.openRunState body shape state

def openRun (block : TypedCfg.Block) (state : EVMState) :
    OpenOutcome :=
  Control.Block.run Instr.openRunState block state

end Block

namespace Program

def openStep (program : TypedCfg.Program) (label : Label)
    (state : EVMState) : OpenOutcome :=
  Control.Program.step Instr.openRunState program label state

def openRunN (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState) : OpenOutcome :=
  Control.Program.runN
    Instr.openRunState program fuel label state

@[simp] theorem openRunN_zero (program : TypedCfg.Program)
    (label : Label) (state : EVMState) :
    openRunN program 0 label state =
      .done (.ok (.jump label state)) := rfl

theorem openRunN_succ (program : TypedCfg.Program)
    (fuel : Nat) (label : Label) (state : EVMState) :
    openRunN program (fuel + 1) label state =
      (do
        let outcome ← openStep program label state
        match outcome with
        | .jump next state' =>
            openRunN program fuel next state'
        | .fallthrough state' => pure (.fallthrough state')
        | .returnDispatch state' => pure (.returnDispatch state')
        | .halt kind state' => pure (.halt kind state')
        | .invalid state' => pure (.invalid state')) := rfl

end Program

end InteractionSemantics
end TypedCfg
end EvmCompiler
