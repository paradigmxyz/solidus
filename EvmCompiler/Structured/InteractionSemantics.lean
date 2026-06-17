import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Structured.EffectSemantics

namespace EvmCompiler
namespace Structured
namespace InteractionSemantics

abbrev Open (α : Type) :=
  Simulation.Interaction EVMException α

namespace BasicInstr

/--
The EVM-state effect owned by one Structured instruction.

Primitive operations delegate to their Assembly owner. Structured-only
bookkeeping instructions embed their ordinary semantics.
-/
def openStepEVM (instr : Structured.BasicInstr)
    (state : EVMState) : Open EVMState :=
  match instr with
  | .op op =>
      Assembly.InteractionSemantics.PrimOp.openStep
        op.toPrimOp state
  | _ =>
      .done (instr.step state)

def openStep (instr : Structured.BasicInstr)
    (state : RunState) : Open RunState :=
  Simulation.Interaction.map state.withEVM
    (openStepEVM instr state.evm)

@[simp] theorem openStep_gas (state : RunState) :
    openStep (.op .gas) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.resourceStep
          .gas state.evm) := rfl

@[simp] theorem openStep_msize (state : RunState) :
    openStep (.op .msize) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.resourceStep
          .msize state.evm) := rfl

@[simp] theorem openStep_call (state : RunState) :
    openStep (.op .call) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.callStep
          .call state.evm) := rfl

@[simp] theorem openStep_callcode (state : RunState) :
    openStep (.op .callcode) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.callStep
          .callcode state.evm) := rfl

@[simp] theorem openStep_delegatecall (state : RunState) :
    openStep (.op .delegatecall) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.callStep
          .delegatecall state.evm) := rfl

@[simp] theorem openStep_staticcall (state : RunState) :
    openStep (.op .staticcall) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.callStep
          .staticcall state.evm) := rfl

@[simp] theorem openStep_create (state : RunState) :
    openStep (.op .create) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.createStep
          .create state.evm) := rfl

@[simp] theorem openStep_create2 (state : RunState) :
    openStep (.op .create2) state =
      Simulation.Interaction.map state.withEVM
        (Assembly.InteractionSemantics.PrimOp.createStep
          .create2 state.evm) := rfl

end BasicInstr

namespace Terminal

def openStep (kind : Assembly.HaltKind)
    (state : RunState) : Open RunState :=
  Simulation.Interaction.map state.withEVM
    (Assembly.InteractionSemantics.PrimOp.openStep
      kind.toPrimOp state.evm)

end Terminal

def handler :
    EffectSemantics.Control.Handler
      (Simulation.Interaction EVMException) RunState where
  stepInstr := BasicInstr.openStep
  stepTerminal := Terminal.openStep

namespace Code

def openRun (code : Structured.Code) (state : RunState) :
    Open RunState :=
  EffectSemantics.Control.Code.run handler code state

def openPopCondition (state : RunState) :
    Open (RunState × Bool) :=
  EffectSemantics.Control.Code.popCondition
    EffectSemantics.Ordinary.runStateModel state

def openRunCondition (code : Structured.Code) (state : RunState) :
    Open (RunState × Bool) :=
  EffectSemantics.Control.Code.runCondition
    EffectSemantics.Ordinary.runStateModel handler code state

end Code

namespace Block

def openRun (program : Structured.Program) (fuel : Nat)
    (block : Structured.Block) (state : RunState) :
    Open Structured.Outcome :=
  EffectSemantics.Control.Block.run
    EffectSemantics.Ordinary.runStateModel handler
    program fuel block state

end Block

namespace Stmt

def openRunForLoop (program : Structured.Program) (fuel : Nat)
    (cond : Structured.Code) (post body : Structured.Block)
    (state : RunState) : Open Structured.Outcome :=
  EffectSemantics.Control.Stmt.runForLoop
    EffectSemantics.Ordinary.runStateModel handler
    program fuel cond post body state

def openRun (program : Structured.Program) (fuel : Nat)
    (stmt : Structured.Stmt) (state : RunState) :
    Open Structured.Outcome :=
  EffectSemantics.Control.Stmt.run
    EffectSemantics.Ordinary.runStateModel handler
    program fuel stmt state

end Stmt

namespace Program

def openRunState (fuel : Nat) (program : Structured.Program)
    (state : RunState) : Open Structured.Outcome :=
  EffectSemantics.Control.Program.runState
    EffectSemantics.Ordinary.runStateModel handler
    fuel program state

def openRun (fuel : Nat) (program : Structured.Program)
    (state : EVMState) : Open Structured.Outcome :=
  openRunState fuel program (Structured.Program.initialState state)

end Program

end InteractionSemantics
end Structured
end EvmCompiler
