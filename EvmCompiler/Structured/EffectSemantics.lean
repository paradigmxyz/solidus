import EvmCompiler.Structured.Syntax
import EvmCompiler.Assembly.Semantics

namespace EvmCompiler
namespace Structured

def invalid {α : Type} : Except EVMException α :=
  .error .InvalidInstruction

namespace BasicOp

def step (op : BasicOp) (state : EVMState) : Except EVMException EVMState :=
  Assembly.Target.stepInstr (Assembly.TargetInstr.prim op.toPrimOp) state

end BasicOp

namespace BasicInstr

def step : BasicInstr → EVMState → Except EVMException EVMState
  | .push value, state =>
      Assembly.Target.stepInstr (Assembly.TargetInstr.push32 value) state
  | .op basicOp, state =>
      basicOp.step state
  | .bindLocals _offset _names, state =>
      .ok state
  | .bindScratch _baseDepth _name _slot, state =>
      .ok state

end BasicInstr

namespace Terminal

def step (kind : Assembly.HaltKind) (state : EVMState) :
    Except EVMException EVMState :=
  Assembly.Target.stepInstr
    (Assembly.TargetInstr.prim kind.toPrimOp) state

end Terminal

namespace StackFrame

def splitArgs? (argc : Nat) (stack : EvmYul.Stack Word) :
    Option (EvmYul.Stack Word × EvmYul.Stack Word) :=
  if argc ≤ stack.length then
    some (stack.take argc, stack.drop argc)
  else
    none

def attachReturns? (frame : ReturnDest) (stack : EvmYul.Stack Word) :
    Option (EvmYul.Stack Word) :=
  if stack.length = frame.retc then
    some (stack ++ frame.callerStack)
  else
    none

end StackFrame

namespace Switch

def select (scrutinee : Word) :
    List (Word × Block) → Option Block → Option Block
  | [], defaultBody => defaultBody
  | (value, body) :: rest, defaultBody =>
      if value = scrutinee then
        some body
      else
        select scrutinee rest defaultBody

end Switch

namespace EffectSemantics

/-!
The canonical Structured control interpreter.

`StateModel` exposes exactly the Structured state needed by control flow.
`Handler.afterInstr` is the sole extension point for observers and future
effects. Ordinary execution and transcript replay therefore share procedure,
branch, switch, loop, and terminal control recursion.
-/

structure StateModel (σ : Type) where
  source : σ → RunState
  withSource : σ → RunState → σ
  pushReturn : σ → EvmYul.Stack Word → Nat → σ
  popReturn? : σ → Option (ReturnDest × σ)

namespace StateModel

def evm {σ : Type} (model : StateModel σ) (state : σ) : EVMState :=
  (model.source state).evm

def returns {σ : Type} (model : StateModel σ) (state : σ) :
    List ReturnDest :=
  (model.source state).returns

def withEVM {σ : Type} (model : StateModel σ) (state : σ)
    (evm : EVMState) : σ :=
  model.withSource state ((model.source state).withEVM evm)

end StateModel

structure Handler (σ : Type) where
  afterInstr :
    BasicInstr → σ → Except EVMException σ

namespace Outcome

abbrev regular {σ : Type} := @OutcomeT.regular σ
abbrev brk {σ : Type} := @OutcomeT.brk σ
abbrev cont {σ : Type} := @OutcomeT.cont σ
abbrev leave {σ : Type} := @OutcomeT.leave σ
abbrev halt {σ : Type} := @OutcomeT.halt σ

end Outcome

namespace Code

def run {σ : Type} (model : StateModel σ) (handler : Handler σ) :
    Structured.Code → σ → Except EVMException σ
  | [], state => .ok state
  | instr :: rest, state => do
      let evm ← instr.step (model.evm state)
      let state' := model.withEVM state evm
      let state'' ← handler.afterInstr instr state'
      run model handler rest state''

def popCondition {σ : Type} (model : StateModel σ) (state : σ) :
    Except EVMException (σ × Bool) :=
  match (model.evm state).stack.pop with
  | some (stack, cond) =>
      .ok
        (model.withEVM state { model.evm state with stack := stack },
          cond != EvmYul.UInt256.ofNat 0)
  | none =>
      .error .StackUnderflow

def runCondition {σ : Type} (model : StateModel σ)
    (handler : Handler σ) (code : Structured.Code) (state : σ) :
    Except EVMException (σ × Bool) := do
  let state' ← run model handler code state
  popCondition model state'

end Code

mutual
  def Block.run {σ : Type} (model : StateModel σ)
      (handler : Handler σ) (program : Program) :
      Nat → Block → σ → Except EVMException (OutcomeT σ)
    | 0, _block, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Outcome.regular state)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let outcome ← Stmt.run model handler program fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.run model handler program fuel ⟨rest⟩ outcome.state
        | .brk | .cont | .leave | .halt _ => .ok outcome

  def Stmt.runForLoop {σ : Type} (model : StateModel σ)
      (handler : Handler σ) (program : Program) (fuel : Nat)
      (cond : Structured.Code) (post body : Block) (state : σ) :
      Except EVMException (OutcomeT σ) :=
    match fuel with
    | 0 =>
        invalid
    | fuel' + 1 =>
        match Code.runCondition model handler cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match
                  Block.run model handler program fuel' body stateAfterCond
              with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match
                          Block.run model handler program fuel' post
                            bodyOutcome.state
                      with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop model handler program fuel'
                                cond post body postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Outcome.regular stateAfterCond)

  def Stmt.run {σ : Type} (model : StateModel σ)
      (handler : Handler σ) (program : Program) :
      Nat → Stmt → σ → Except EVMException (OutcomeT σ)
    | _fuel, .code code, state => do
        let state' ← Code.run model handler code state
        .ok (Outcome.regular state')
    | 0, .if_ _cond _body, _state =>
        invalid
    | fuel + 1, .if_ cond body, state => do
        let (stateAfterCond, condTrue) ←
          Code.runCondition model handler cond state
        if condTrue then
          Block.run model handler program fuel body stateAfterCond
        else
          .ok (Outcome.regular stateAfterCond)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let stateAfterScrutinee ←
          Code.run model handler scrutinee state
        match (model.evm stateAfterScrutinee).stack.pop with
        | none =>
            .error .StackUnderflow
        | some ⟨stack, value⟩ =>
            let stateAfterPop :=
              model.withEVM stateAfterScrutinee
                { model.evm stateAfterScrutinee with stack := stack }
            match Switch.select value cases defaultBody with
            | some body =>
                Block.run model handler program fuel body stateAfterPop
            | none => .ok (Outcome.regular stateAfterPop)
    | 0, .for_ _init _cond _post _body, _state =>
        invalid
    | fuel + 1, .for_ init cond post body, state => do
        let initOutcome ←
          Block.run model handler program fuel init state
        match initOutcome.mode with
        | .regular =>
            Stmt.runForLoop model handler program fuel cond post body
              initOutcome.state
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok initOutcome
    | _fuel, .brk, state =>
        .ok (Outcome.brk state)
    | _fuel, .cont, state =>
        .ok (Outcome.cont state)
    | _fuel, .leave, state =>
        match model.returns state with
        | [] => invalid
        | _ :: _ => .ok (Outcome.leave state)
    | 0, .call _name, _state =>
        invalid
    | fuel + 1, .call name, state =>
        match ProcList.lookup? name program.procs with
        | none =>
            invalid
        | some proc =>
            match StackFrame.splitArgs? proc.argc (model.evm state).stack with
            | none =>
                .error .StackUnderflow
            | some (args, callerStack) =>
                let callEVM := { model.evm state with stack := args }
                let callState :=
                  model.pushReturn
                    (model.withEVM state callEVM) callerStack proc.retc
                match
                    Block.run model handler program fuel proc.body callState
                with
                | .error err => .error err
                | .ok outcome =>
                    match outcome.mode with
                    | .regular | .leave =>
                        match model.popReturn? outcome.state with
                        | none => invalid
                        | some (frame, returned) =>
                            match
                                StackFrame.attachReturns? frame
                                  (model.evm outcome.state).stack
                            with
                            | none => invalid
                            | some stack =>
                                let evm :=
                                  { model.evm outcome.state with
                                    stack := stack }
                                .ok
                                  (Outcome.regular
                                    (model.withEVM returned evm))
                    | .brk | .cont =>
                        invalid
                    | .halt kind =>
                        .ok (Outcome.halt kind outcome.state)
    | _fuel, .terminal kind, state => do
        let evm ← Terminal.step kind (model.evm state)
        .ok (Outcome.halt kind (model.withEVM state evm))
end

namespace Program

def runState {σ : Type} (model : StateModel σ)
    (handler : Handler σ) (fuel : Nat) (program : Structured.Program)
    (state : σ) : Except EVMException (OutcomeT σ) :=
  Block.run model handler program fuel program.body state

end Program

namespace Ordinary

def evmStateModel : StateModel EVMState where
  source state := RunState.initial state
  withSource _state source := source.evm
  pushReturn state _callerStack _retc := state
  popReturn? _state := none

def runStateModel : StateModel RunState where
  source := id
  withSource _state source := source
  pushReturn state callerStack retc :=
    state.pushReturn callerStack retc
  popReturn? := RunState.popReturn?

def handler {σ : Type} : Handler σ where
  afterInstr _instr state := .ok state

@[simp] theorem evmStateModel_evm (state : EVMState) :
    evmStateModel.evm state = state := rfl

@[simp] theorem evmStateModel_withEVM
    (state evm : EVMState) :
    evmStateModel.withEVM state evm = evm := rfl

@[simp] theorem runStateModel_source (state : RunState) :
    runStateModel.source state = state := rfl

@[simp] theorem runStateModel_evm (state : RunState) :
    runStateModel.evm state = state.evm := rfl

@[simp] theorem runStateModel_returns (state : RunState) :
    runStateModel.returns state = state.returns := rfl

@[simp] theorem runStateModel_withEVM
    (state : RunState) (evm : EVMState) :
    runStateModel.withEVM state evm = state.withEVM evm := rfl

@[simp] theorem runStateModel_pushReturn
    (state : RunState) (callerStack : EvmYul.Stack Word) (retc : Nat) :
    runStateModel.pushReturn state callerStack retc =
      state.pushReturn callerStack retc := rfl

@[simp] theorem runStateModel_popReturn? (state : RunState) :
    runStateModel.popReturn? state = state.popReturn? := rfl

@[simp] theorem handler_afterInstr {σ : Type}
    (instr : BasicInstr) (state : σ) :
    (handler : Handler σ).afterInstr instr state = .ok state := rfl

end Ordinary

end EffectSemantics

namespace Code

abbrev run (code : Code) (state : EVMState) :
    Except EVMException EVMState :=
  EffectSemantics.Code.run
    EffectSemantics.Ordinary.evmStateModel
    EffectSemantics.Ordinary.handler code state

def runState (code : Code) (state : RunState) :
    Except EVMException RunState := do
  let evm ← run code state.evm
  .ok (state.withEVM evm)

abbrev popCondition (state : EVMState) :
    Except EVMException (EVMState × Bool) :=
  EffectSemantics.Code.popCondition
    EffectSemantics.Ordinary.evmStateModel state

abbrev runCondition (code : Code) (state : EVMState) :
    Except EVMException (EVMState × Bool) :=
  EffectSemantics.Code.runCondition
    EffectSemantics.Ordinary.evmStateModel
    EffectSemantics.Ordinary.handler code state

def runConditionState (code : Code) (state : RunState) :
    Except EVMException (RunState × Bool) := do
  let (evm, cond) ← runCondition code state.evm
  .ok (state.withEVM evm, cond)

end Code

namespace Block

def run (program : Program) (fuel : Nat) (block : Block)
    (state : RunState) : Except EVMException Outcome :=
  EffectSemantics.Block.run
    EffectSemantics.Ordinary.runStateModel
    EffectSemantics.Ordinary.handler program fuel block state

end Block

namespace Stmt

def runForLoop (program : Program) (fuel : Nat) (cond : Code)
    (post body : Block) (state : RunState) :
    Except EVMException Outcome :=
  EffectSemantics.Stmt.runForLoop
    EffectSemantics.Ordinary.runStateModel
    EffectSemantics.Ordinary.handler program fuel cond post body state

def run (program : Program) (fuel : Nat) (stmt : Stmt)
    (state : RunState) : Except EVMException Outcome :=
  EffectSemantics.Stmt.run
    EffectSemantics.Ordinary.runStateModel
    EffectSemantics.Ordinary.handler program fuel stmt state

end Stmt

namespace Program

def initialState (state : EVMState) : RunState :=
  RunState.initial state

def runState (fuel : Nat) (program : Program) (state : RunState) :
    Except EVMException Outcome :=
  EffectSemantics.Program.runState
    EffectSemantics.Ordinary.runStateModel
    EffectSemantics.Ordinary.handler fuel program state

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  runState fuel program (initialState state)

end Program

namespace EffectSemantics

namespace Code

theorem ordinary_evm_run (code : Structured.Code) (state : EVMState) :
    run Ordinary.evmStateModel Ordinary.handler code state =
      Structured.Code.run code state := rfl

theorem ordinary_state_run (code : Structured.Code) (state : RunState) :
    run Ordinary.runStateModel Ordinary.handler code state =
      Structured.Code.runState code state := by
  induction code generalizing state with
  | nil =>
      rfl
  | cons instr rest ih =>
      cases hStep : instr.step state.evm with
      | error err =>
          simp [run, Structured.Code.runState, Structured.Code.run,
            hStep, Ordinary.handler_afterInstr,
            Ordinary.evmStateModel_evm,
            Ordinary.runStateModel_evm,
            Bind.bind, Except.bind]
      | ok evm =>
          simp [run, Structured.Code.runState, Structured.Code.run,
            hStep, ih, Ordinary.handler_afterInstr,
            Ordinary.evmStateModel_evm,
            Ordinary.evmStateModel_withEVM,
            Ordinary.runStateModel_evm,
            Ordinary.runStateModel_withEVM,
            RunState.withEVM,
            Bind.bind, Except.bind]

theorem ordinary_evm_popCondition (state : EVMState) :
    popCondition Ordinary.evmStateModel state =
      Structured.Code.popCondition state := rfl

theorem ordinary_evm_runCondition
    (code : Structured.Code) (state : EVMState) :
    runCondition Ordinary.evmStateModel Ordinary.handler code state =
      Structured.Code.runCondition code state := rfl

theorem ordinary_state_runCondition
    (code : Structured.Code) (state : RunState) :
    runCondition Ordinary.runStateModel Ordinary.handler code state =
      Structured.Code.runConditionState code state := by
  unfold Structured.Code.runConditionState
  simp only [runCondition]
  rw [ordinary_state_run]
  unfold Structured.Code.runState
  cases hRun : Structured.Code.run code state.evm with
  | error err =>
      simp [Structured.Code.runCondition, runCondition,
        hRun, Bind.bind, Except.bind]
  | ok evm =>
      simp [Structured.Code.runCondition, runCondition,
        hRun, Bind.bind, Except.bind]
      cases hPop : evm.stack.pop with
      | none =>
          simp [popCondition, Structured.Code.popCondition,
            Ordinary.evmStateModel_evm,
            Ordinary.runStateModel_evm, hPop]
      | some pair =>
          rcases pair with ⟨stack, value⟩
          simp [popCondition, Structured.Code.popCondition,
            Ordinary.evmStateModel_evm,
            Ordinary.evmStateModel_withEVM,
            Ordinary.runStateModel_evm,
            Ordinary.runStateModel_withEVM,
            RunState.withEVM, hPop]

end Code

namespace Block

theorem ordinary_run (program : Structured.Program) (fuel : Nat)
    (block : Structured.Block) (state : RunState) :
    run Ordinary.runStateModel Ordinary.handler program fuel block state =
      Structured.Block.run program fuel block state := rfl

end Block

namespace Stmt

theorem ordinary_runForLoop (program : Structured.Program) (fuel : Nat)
    (cond : Structured.Code) (post body : Structured.Block)
    (state : RunState) :
    runForLoop Ordinary.runStateModel Ordinary.handler
        program fuel cond post body state =
      Structured.Stmt.runForLoop program fuel cond post body state := rfl

theorem ordinary_run (program : Structured.Program) (fuel : Nat)
    (stmt : Structured.Stmt) (state : RunState) :
    run Ordinary.runStateModel Ordinary.handler program fuel stmt state =
      Structured.Stmt.run program fuel stmt state := rfl

end Stmt

end EffectSemantics

end Structured
end EvmCompiler
