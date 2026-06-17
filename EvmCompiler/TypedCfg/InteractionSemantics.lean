import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.TypedCfg.Control
import EvmCompiler.TypedCfg.Lower

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

namespace Terminator

/--
Generated return-dispatch tests use conditional jumps to enter their selected
case. The final jump from a case is unconditional and remains source-visible.
-/
def returnDispatchFlowPolicy : Assembly.Instr → Bool
  | .jumpi _ => true
  | _ => false

def assemblyFlowPolicy : TypedCfg.Terminator → Assembly.Instr → Bool
  | .returnDispatch _ _ => returnDispatchFlowPolicy
  | _ => fun _ => false

@[simp] theorem returnDispatchFlowPolicy_jumpi (label : Label) :
    returnDispatchFlowPolicy (.jumpi label) = true := rfl

@[simp] theorem returnDispatchFlowPolicy_jump (label : Label) :
    returnDispatchFlowPolicy (.jump label) = false := rfl

end Terminator

namespace CompiledBlock

/--
Execute one lowered TypedCfg block through the canonical Assembly runners.

The existing compiler selects the body and terminator fragments. This adapter
only sequences label execution, straight-line body execution, and the
terminator-owned transfer policy; it defines no primitive or external-effect
semantics of its own.
-/
def openRun (block : TypedCfg.Block)
    (program : Assembly.Program) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      .done (.error .InvalidInstruction)
  | some (bodyCode, output) =>
      if output = block.output then
        match block.term.lowerAt? output with
        | none =>
            .done (.error .InvalidInstruction)
        | some termCode => do
            let labelResult ←
              Assembly.InteractionSemantics.Source.openRunNResult
                program 1 state
            match labelResult with
            | .halted halt =>
                pure (.halted halt)
            | .running entry =>
                let bodyResult ←
                  Assembly.InteractionSemantics.Source.openRunNResult
                    program bodyCode.length entry
                match bodyResult with
                | .halted halt =>
                    pure (.halted halt)
                | .running mid =>
                    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                      (Terminator.assemblyFlowPolicy block.term)
                      program termCode.length mid
      else
        .done (.error .InvalidInstruction)

end CompiledBlock

namespace CompiledProgram

/--
Execute one compiled TypedCfg block selected by the concrete Assembly program
counter. Only an Assembly label at the current PC may enter a source block.
The source program supplies immutable block syntax; control selection remains
entirely target-driven.
-/
def openStep (source : TypedCfg.Program)
    (target : Assembly.Program) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match target.instrAtPc state.pc.toNat with
  | some (_, .label label) =>
      match source.findBlock? label with
      | some block =>
          CompiledBlock.openRun block target state
      | none =>
          .done (.error .InvalidInstruction)
  | _ =>
      .done (.error .InvalidInstruction)

def openRunN (source : TypedCfg.Program)
    (target : Assembly.Program) (fuel : Nat) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  Assembly.Control.runNResultWith
    (openStep source target) fuel state

@[simp] theorem openRunN_zero
    (source : TypedCfg.Program) (target : Assembly.Program)
    (state : EVMState) :
    openRunN source target 0 state =
      .done (.ok (.running state)) := rfl

theorem openRunN_succ
    (source : TypedCfg.Program) (target : Assembly.Program)
    (fuel : Nat) (state : EVMState) :
    openRunN source target (fuel + 1) state =
      (do
        let result ← openStep source target state
        match result with
        | .running state' =>
            openRunN source target fuel state'
        | .halted halt =>
            pure (.halted halt)) := rfl

end CompiledProgram

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
