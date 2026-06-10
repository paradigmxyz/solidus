import EvmCompiler.Expressions.Syntax
import EvmCompiler.Structured.Semantics

namespace EvmCompiler
namespace Expressions

abbrev RunState := Structured.RunState
abbrev Outcome := Structured.Outcome

abbrev invalid {α : Type} : Except EVMException α :=
  Structured.invalid

namespace Outcome

abbrev regular := Structured.Outcome.regular
abbrev brk := Structured.Outcome.brk
abbrev cont := Structured.Outcome.cont
abbrev leave := Structured.Outcome.leave
abbrev halt := Structured.Outcome.halt

end Outcome

mutual
  def Expr.run {results : Nat} (expr : Expr results)
      (state : EVMState) : Except EVMException EVMState :=
    match expr with
    | .lit value =>
        Structured.BasicInstr.step (.push value) state
    | .code code =>
        Structured.Code.run code state
    | .prim op args => do
        let state' ← ExprSeq.run args state
        op.step state'

  def ExprSeq.run {results : Nat} (exprs : ExprSeq results)
      (state : EVMState) : Except EVMException EVMState :=
    match exprs with
    | .nil => .ok state
    | .cons head tail => do
        let state' ← Expr.run head state
        ExprSeq.run tail state'
end

namespace Expr

def runState {results : Nat} (expr : Expr results) (state : RunState) :
    Except EVMException RunState := do
  let evm ← expr.run state.evm
  .ok (state.withEVM evm)

def runCondition (cond : Expr 1) (state : EVMState) :
    Except EVMException (EVMState × Bool) :=
  match cond.run state with
  | .ok state' => Structured.Code.popCondition state'
  | .error err => .error err

def runConditionState (cond : Expr 1) (state : RunState) :
    Except EVMException (RunState × Bool) := do
  let (evm, condTrue) ← runCondition cond state.evm
  .ok (state.withEVM evm, condTrue)

end Expr

namespace ProcList

def lookup? (name : Name) : List Proc → Option Proc
  | [] => none
  | proc :: rest =>
      if proc.name = name then
        some proc
      else
        lookup? name rest

end ProcList

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

mutual
  def Block.run (program : Program) : Nat → Block → RunState →
      Except EVMException Outcome
    | 0, _block, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Outcome.regular state)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let outcome ← Stmt.run program fuel stmt state
        match outcome.mode with
        | .regular => Block.run program fuel ⟨rest⟩ outcome.state
        | .brk | .cont | .leave | .halt _ => .ok outcome

  def Stmt.runForLoop (program : Program) (fuel : Nat) (cond : Expr 1)
      (post body : Block) (state : RunState) :
      Except EVMException Outcome :=
    match fuel with
    | 0 =>
        invalid
    | fuel' + 1 =>
        match Expr.runConditionState cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match Block.run program fuel' body stateAfterCond with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match Block.run program fuel' post bodyOutcome.state with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop program fuel' cond post body
                                postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Outcome.regular stateAfterCond)

  def Stmt.run (program : Program) : Nat → Stmt → RunState →
      Except EVMException Outcome
    | _fuel, Stmt.code code, state => do
        let state' ← Structured.Code.runState code state
        .ok (Outcome.regular state')
    | _fuel, Stmt.expr expr, state => do
        let state' ← Expr.runState expr state
        .ok (Outcome.regular state')
    | 0, Stmt.if_ _cond _body, _state =>
        invalid
    | fuel + 1, Stmt.if_ cond body, state =>
        match Expr.runConditionState cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              Block.run program fuel body stateAfterCond
            else
              .ok (Outcome.regular stateAfterCond)
    | 0, Stmt.switch _scrutinee _cases _defaultBody, _state =>
        invalid
    | fuel + 1, Stmt.switch scrutinee cases defaultBody, state => do
        let evmAfterScrutinee ← Expr.run scrutinee state.evm
        match evmAfterScrutinee.stack.pop with
        | none =>
            .error .StackUnderflow
        | some ⟨stack, value⟩ =>
            let evmAfterPop := { evmAfterScrutinee with stack := stack }
            let stateAfterPop := state.withEVM evmAfterPop
            match Switch.select value cases defaultBody with
            | some body => Block.run program fuel body stateAfterPop
            | none => .ok (Outcome.regular stateAfterPop)
    | 0, Stmt.for_ _init _cond _post _body, _state =>
        invalid
    | fuel + 1, Stmt.for_ init cond post body, state => do
        let initOutcome ← Block.run program fuel init state
        match initOutcome.mode with
        | .regular =>
            Stmt.runForLoop program fuel cond post body initOutcome.state
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok initOutcome
    | _fuel, Stmt.brk, state =>
        .ok (Outcome.brk state)
    | _fuel, Stmt.cont, state =>
        .ok (Outcome.cont state)
    | _fuel, Stmt.leave, state =>
        match state.returns with
        | [] => invalid
        | _ :: _ => .ok (Outcome.leave state)
    | 0, Stmt.call _name, _state =>
        invalid
    | fuel + 1, Stmt.call name, state =>
        match ProcList.lookup? name program.procs with
        | none =>
            invalid
        | some proc =>
            match Structured.StackFrame.splitArgs? proc.argc state.evm.stack with
            | none =>
                .error .StackUnderflow
            | some (args, callerStack) =>
                let callEVM := { state.evm with stack := args }
                let callState :=
                  (state.withEVM callEVM).pushReturn callerStack proc.retc
                match Block.run program fuel proc.body callState with
                | .error err => .error err
                | .ok outcome =>
                    match outcome.mode with
                    | .regular | .leave =>
                        match outcome.state.popReturn? with
                        | none => invalid
                        | some (frame, returned) =>
                            match Structured.StackFrame.attachReturns? frame
                                outcome.state.evm.stack with
                            | none => invalid
                            | some stack =>
                                let evm := { outcome.state.evm with stack := stack }
                                .ok (Outcome.regular (returned.withEVM evm))
                    | .brk | .cont =>
                        invalid
                    | .halt kind =>
                        .ok (Outcome.halt kind outcome.state)
    | _fuel, Stmt.terminal kind, state => do
        let evm ← Structured.Terminal.step kind state.evm
        .ok (Outcome.halt kind (state.withEVM evm))
end

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  Block.run program fuel program.body (Structured.Program.initialState state)

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : EVMState}
      {outcome : Outcome}
      (hRun : program.run fuel initial = .ok outcome) :
      Eval fuel program initial outcome

theorem eval_of_run {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hRun : run fuel program initial = .ok outcome) :
    Eval fuel program initial outcome := by
  exact Eval.ofRun hRun

end Program

end Expressions
end EvmCompiler
