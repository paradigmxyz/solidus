import EvmCompiler.Expressions.Syntax
import EvmCompiler.Structured.EffectSemantics

namespace EvmCompiler
namespace Expressions
namespace EffectSemantics

abbrev StateModel := Structured.EffectSemantics.StateModel
abbrev Handler := Structured.EffectSemantics.Control.Handler
abbrev OutcomeT := Structured.OutcomeT

namespace ProcList

def lookup? (name : Name) : List Proc → Option Proc
  | [] => none
  | proc :: rest =>
      if proc.name = name then
        some proc
      else
        lookup? name rest

theorem mem_of_lookup?
    {name : Name} {procs : List Proc} {proc : Proc}
    (hLookup : lookup? name procs = some proc) :
    proc ∈ procs := by
  induction procs with
  | nil => simp [lookup?] at hLookup
  | cons head rest ih =>
      by_cases hName : head.name = name
      · simp [lookup?, hName] at hLookup
        subst proc
        simp
      · have hTail : lookup? name rest = some proc := by
          simpa [lookup?, hName] using hLookup
        exact List.mem_cons_of_mem head (ih hTail)

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

namespace Control

mutual
  def Expr.run {M : Type → Type} [Monad M] {σ : Type}
      (handler : Handler M σ) {results : Nat}
      (expr : Expressions.Expr results) (state : σ) : M σ :=
    match expr with
    | .lit value =>
        handler.stepInstr (.push value) state
    | .code code =>
        Structured.EffectSemantics.Control.Code.run handler code state
    | .prim op args => do
        let state' ← ExprSeq.run handler args state
        handler.stepInstr (.op op) state'

  def ExprSeq.run {M : Type → Type} [Monad M] {σ : Type}
      (handler : Handler M σ) {results : Nat}
      (exprs : Expressions.ExprSeq results) (state : σ) : M σ :=
    match exprs with
    | .nil => pure state
    | .cons head tail => do
        let state' ← Expr.run handler head state
        ExprSeq.run handler tail state'
end

namespace Expr

def runCondition {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M] {σ : Type}
    (model : StateModel σ) (handler : Handler M σ)
    (cond : Expressions.Expr 1) (state : σ) : M (σ × Bool) := do
  let state' ← run handler cond state
  Structured.EffectSemantics.Control.Code.popCondition model state'

end Expr

mutual
  def Block.run {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M] {σ : Type}
      (model : StateModel σ) (handler : Handler M σ)
      (program : Program) :
      Nat → Block → σ → M (OutcomeT σ)
    | 0, _block, _state =>
        throw .OutOfFuel
    | _fuel + 1, ⟨[]⟩, state =>
        pure (Structured.EffectSemantics.Outcome.regular state)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let outcome ← Stmt.run model handler program fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.run model handler program fuel ⟨rest⟩ outcome.state
        | .brk | .cont | .leave | .halt _ =>
            pure outcome

  def Stmt.runForLoop {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M] {σ : Type}
      (model : StateModel σ) (handler : Handler M σ)
      (program : Program) (fuel : Nat) (cond : Expressions.Expr 1)
      (post body : Block) (state : σ) : M (OutcomeT σ) :=
    match fuel with
    | 0 =>
        throw .OutOfFuel
    | fuel' + 1 => do
        let (stateAfterCond, condTrue) ←
          Expr.runCondition model handler cond state
        if condTrue then
          let bodyOutcome ←
            Block.run model handler program fuel' body stateAfterCond
          match bodyOutcome.mode with
          | .brk =>
              pure
                (Structured.EffectSemantics.Outcome.regular
                  bodyOutcome.state)
          | .regular | .cont =>
              let postOutcome ←
                Block.run model handler program fuel' post bodyOutcome.state
              match postOutcome.mode with
              | .regular =>
                  Stmt.runForLoop model handler program fuel'
                    cond post body postOutcome.state
              | .brk | .cont =>
                  throw .InvalidInstruction
              | .leave | .halt _ =>
                  pure postOutcome
          | .leave | .halt _ =>
              pure bodyOutcome
        else
          pure
            (Structured.EffectSemantics.Outcome.regular stateAfterCond)

  def Stmt.run {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M] {σ : Type}
      (model : StateModel σ) (handler : Handler M σ)
      (program : Program) :
      Nat → Stmt → σ → M (OutcomeT σ)
    | _fuel, .code code, state => do
        let state' ←
          Structured.EffectSemantics.Control.Code.run handler code state
        pure (Structured.EffectSemantics.Outcome.regular state')
    | _fuel, .expr expr, state => do
        let state' ← Expr.run handler expr state
        pure (Structured.EffectSemantics.Outcome.regular state')
    | 0, .if_ _cond _body, _state =>
        throw .OutOfFuel
    | fuel + 1, .if_ cond body, state => do
        let (stateAfterCond, condTrue) ←
          Expr.runCondition model handler cond state
        if condTrue then
          Block.run model handler program fuel body stateAfterCond
        else
          pure
            (Structured.EffectSemantics.Outcome.regular stateAfterCond)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        throw .OutOfFuel
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let stateAfterScrutinee ← Expr.run handler scrutinee state
        match (model.evm stateAfterScrutinee).stack.pop with
        | none =>
            throw .StackUnderflow
        | some ⟨stack, value⟩ =>
            let stateAfterPop :=
              model.withEVM stateAfterScrutinee
                { model.evm stateAfterScrutinee with stack := stack }
            match Switch.select value cases defaultBody with
            | some body =>
                Block.run model handler program fuel body stateAfterPop
            | none =>
                pure
                  (Structured.EffectSemantics.Outcome.regular stateAfterPop)
    | 0, .for_ _init _cond _post _body, _state =>
        throw .OutOfFuel
    | fuel + 1, .for_ init cond post body, state => do
        let initOutcome ←
          Block.run model handler program fuel init state
        match initOutcome.mode with
        | .regular =>
            Stmt.runForLoop model handler program fuel cond post body
              initOutcome.state
        | .brk | .cont =>
            throw .InvalidInstruction
        | .leave | .halt _ =>
            pure initOutcome
    | _fuel, .brk, state =>
        pure (Structured.EffectSemantics.Outcome.brk state)
    | _fuel, .cont, state =>
        pure (Structured.EffectSemantics.Outcome.cont state)
    | _fuel, .leave, state =>
        match model.returns state with
        | [] => throw .InvalidInstruction
        | _ :: _ =>
            pure (Structured.EffectSemantics.Outcome.leave state)
    | 0, .call _name, _state =>
        throw .OutOfFuel
    | fuel + 1, .call name, state =>
        match ProcList.lookup? name program.procs with
        | none =>
            throw .InvalidInstruction
        | some proc =>
            match
                Structured.StackFrame.splitArgs?
                  proc.argc (model.evm state).stack
            with
            | none =>
                throw .StackUnderflow
            | some (args, callerStack) => do
                let callEVM := { model.evm state with stack := args }
                let callState :=
                  model.pushReturn
                    (model.withEVM state callEVM) callerStack proc.retc
                let outcome ←
                  Block.run model handler program fuel proc.body callState
                match outcome.mode with
                | .regular | .leave =>
                    match model.popReturn? outcome.state with
                    | none =>
                        throw .InvalidInstruction
                    | some (frame, returned) =>
                        match
                            Structured.StackFrame.attachReturns? frame
                              (model.evm outcome.state).stack
                        with
                        | none =>
                            throw .InvalidInstruction
                        | some stack =>
                            let evm :=
                              { model.evm outcome.state with stack := stack }
                            pure
                              (Structured.EffectSemantics.Outcome.regular
                                (model.withEVM returned evm))
                | .brk | .cont =>
                    throw .InvalidInstruction
                | .halt kind =>
                    pure
                      (Structured.EffectSemantics.Outcome.halt
                        kind outcome.state)
    | _fuel, .terminal kind, state => do
        let final ← handler.stepTerminal kind state
        pure (Structured.EffectSemantics.Outcome.halt kind final)
end

namespace Program

def runState {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M] {σ : Type}
    (model : StateModel σ) (handler : Handler M σ)
    (fuel : Nat) (program : Expressions.Program)
    (state : σ) : M (OutcomeT σ) :=
  Block.run model handler program fuel program.body state

end Program

end Control

namespace Ordinary

def evmHandler :
    Handler (Except EVMException) EVMState :=
  Structured.EffectSemantics.Control.Handler.ofLegacy
    Structured.EffectSemantics.Ordinary.evmStateModel
    Structured.EffectSemantics.Ordinary.handler

def runStateHandler :
    Handler (Except EVMException) Structured.RunState :=
  Structured.EffectSemantics.Control.Handler.ofLegacy
    Structured.EffectSemantics.Ordinary.runStateModel
    Structured.EffectSemantics.Ordinary.handler

end Ordinary

end EffectSemantics
end Expressions
end EvmCompiler
