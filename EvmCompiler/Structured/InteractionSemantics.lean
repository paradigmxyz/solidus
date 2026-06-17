import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Structured.EffectSemantics

namespace EvmCompiler
namespace Structured
namespace InteractionSemantics

abbrev Open (α : Type) :=
  Simulation.Interaction EVMException α

def ReturnsEq (returns : List ReturnDest) :
    Except EVMException RunState → Prop
  | .error _ => True
  | .ok final => final.returns = returns

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

theorem openStep_returns (instr : Structured.BasicInstr)
    (state : RunState) :
    Simulation.Interaction.AllDone
      (ReturnsEq state.returns)
      (openStep instr state) := by
  unfold openStep
  apply Simulation.Interaction.AllDone.map
    state.withEVM
    (Simulation.Interaction.AllDone.trivial
      (openStepEVM instr state.evm))
  · intro err _h
    trivial
  · intro final _h
    rfl

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

@[simp] theorem openRun_single
    (instr : Structured.BasicInstr) (state : RunState) :
    openRun [instr] state =
      BasicInstr.openStep instr state := by
  unfold openRun
  simp only [EffectSemantics.Control.Code.run]
  exact
    Simulation.Interaction.bind_pure
      (BasicInstr.openStep instr state)

def openPopCondition (state : RunState) :
    Open (RunState × Bool) :=
  EffectSemantics.Control.Code.popCondition
    EffectSemantics.Ordinary.runStateModel state

def openRunCondition (code : Structured.Code) (state : RunState) :
    Open (RunState × Bool) :=
  EffectSemantics.Control.Code.runCondition
    EffectSemantics.Ordinary.runStateModel handler code state

theorem openRun_append
    (left right : Structured.Code) (state : RunState) :
    openRun (left ++ right) state =
      Simulation.Interaction.bind
        (openRun left state) (openRun right) := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp only [openRun, List.cons_append,
        EffectSemantics.Control.Code.run]
      change
        Simulation.Interaction.bind
            (handler.stepInstr instr state)
            (fun middle =>
              EffectSemantics.Control.Code.run
                handler (rest ++ right) middle) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind
              (handler.stepInstr instr state)
              (EffectSemantics.Control.Code.run handler rest))
            (openRun right)
      rw [Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (handler.stepInstr instr state))
      intro middle _
      exact ih middle

def ConditionReturnsEq (returns : List ReturnDest) :
    Except EVMException (RunState × Bool) → Prop
  | .error _ => True
  | .ok result => result.1.returns = returns

theorem openRun_returns (code : Structured.Code) (state : RunState) :
    Simulation.Interaction.AllDone
      (ReturnsEq state.returns)
      (openRun code state) := by
  induction code generalizing state with
  | nil =>
      exact Simulation.Interaction.AllDone.done rfl
  | cons instr rest ih =>
      unfold openRun EffectSemantics.Control.Code.run
      apply Simulation.Interaction.AllDone.bind
        (BasicInstr.openStep_returns instr state)
      · intro err _h
        trivial
      · intro middle hMiddle
        apply Simulation.Interaction.AllDone.mono (ih middle)
        intro outcome hOutcome
        cases outcome with
        | error err =>
            trivial
        | ok final =>
            exact hOutcome.trans hMiddle

theorem openPopCondition_returns (state : RunState) :
    Simulation.Interaction.AllDone
      (ConditionReturnsEq state.returns)
      (openPopCondition state) := by
  unfold openPopCondition
    EffectSemantics.Control.Code.popCondition
  cases hPop : state.evm.stack.pop with
  | none =>
      simp only [
        EffectSemantics.Ordinary.runStateModel_evm, hPop,
        Simulation.Interaction.error]
      exact Simulation.Interaction.AllDone.done True.intro
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp only [
        EffectSemantics.Ordinary.runStateModel_evm, hPop,
        EffectSemantics.Ordinary.runStateModel_withEVM,
        Simulation.Interaction.pure]
      exact Simulation.Interaction.AllDone.done rfl

theorem openRunCondition_returns
    (code : Structured.Code) (state : RunState) :
    Simulation.Interaction.AllDone
      (ConditionReturnsEq state.returns)
      (openRunCondition code state) := by
  unfold openRunCondition
    EffectSemantics.Control.Code.runCondition
  apply Simulation.Interaction.AllDone.bind
    (openRun_returns code state)
  · intro err _h
    trivial
  · intro middle hMiddle
    apply Simulation.Interaction.AllDone.mono
      (openPopCondition_returns middle)
    intro outcome hOutcome
    cases outcome with
    | error err =>
        trivial
    | ok result =>
        exact hOutcome.trans hMiddle

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
