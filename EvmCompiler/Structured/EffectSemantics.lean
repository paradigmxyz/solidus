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

/--
Terminal execution is defined whenever the source stack contains the operands
declared by the halt kind.

This is the source-owned fact used by backward compiler proofs: symbolic typing
must establish the arity bound, while the terminal semantics itself constructs
the resulting EVM state.
-/
theorem exists_step_of_argCount_le
    (kind : Assembly.HaltKind) (state : EVMState)
    (hStack : kind.argCount ≤ state.stack.length) :
    ∃ final, step kind state = .ok final := by
  cases state with
  | mk shared pc stack execLength =>
      cases kind with
      | stop =>
          exact ⟨_, rfl⟩
      | «return» =>
          cases stack with
          | nil =>
              simp [Assembly.HaltKind.argCount] at hStack
          | cons first rest =>
              cases rest with
              | nil =>
                  simp [Assembly.HaltKind.argCount] at hStack
              | cons second tail =>
                  exact ⟨_, rfl⟩
      | revert =>
          cases stack with
          | nil =>
              simp [Assembly.HaltKind.argCount] at hStack
          | cons first rest =>
              cases rest with
              | nil =>
                  simp [Assembly.HaltKind.argCount] at hStack
              | cons second tail =>
                  exact ⟨_, rfl⟩
      | selfdestruct =>
          cases stack with
          | nil =>
              simp [Assembly.HaltKind.argCount] at hStack
          | cons recipient tail =>
              exact ⟨_, rfl⟩

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

theorem run_cons_eq_run_single_bind
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (instr : BasicInstr) (rest : Structured.Code) (state : σ) :
    run model handler (instr :: rest) state =
      (run model handler [instr] state).bind
        (run model handler rest) := by
  unfold run
  cases hStep : instr.step (model.evm state) with
  | error err =>
      simp [hStep, Bind.bind, Except.bind]
  | ok evm =>
      cases hAfter :
          handler.afterInstr instr (model.withEVM state evm) with
      | error err =>
          simp [hStep, hAfter, Bind.bind, Except.bind]
      | ok final =>
          simp only [hStep, hAfter, Bind.bind, Except.bind]
          rw [show run model handler [] final = .ok final from rfl]

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

mutual
  /--
  Relational counterpart of the parameterized Structured interpreter.

  This is the single control-evaluation relation for ordinary execution,
  observer replay, and future effect handlers. Compiler proofs can therefore
  recurse over Structured control once while taking primitive-effect
  preservation as an adjacent-pass interface.
  -/
  inductive Block.Eval {σ : Type} (model : StateModel σ)
      (handler : Handler σ) (program : Program) :
      Nat → Block → σ → OutcomeT σ → Prop where
    | nil {fuel : Nat} {state : σ} :
        Block.Eval model handler program (fuel + 1) { stmts := [] } state
          (Outcome.regular state)
    | cons_regular {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state mid : σ} {outcome : OutcomeT σ}
        (hStmt :
          Stmt.Eval model handler program fuel stmt state
            (Outcome.regular mid))
        (hRest :
          Block.Eval model handler program fuel
            { stmts := rest } mid outcome) :
        Block.Eval model handler program (fuel + 1)
          { stmts := stmt :: rest } state outcome
    | cons_brk {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : σ}
        (hStmt :
          Stmt.Eval model handler program fuel stmt state
            (Outcome.brk outState)) :
        Block.Eval model handler program (fuel + 1)
          { stmts := stmt :: rest } state (Outcome.brk outState)
    | cons_cont {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : σ}
        (hStmt :
          Stmt.Eval model handler program fuel stmt state
            (Outcome.cont outState)) :
        Block.Eval model handler program (fuel + 1)
          { stmts := stmt :: rest } state (Outcome.cont outState)
    | cons_leave {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : σ}
        (hStmt :
          Stmt.Eval model handler program fuel stmt state
            (Outcome.leave outState)) :
        Block.Eval model handler program (fuel + 1)
          { stmts := stmt :: rest } state (Outcome.leave outState)
    | cons_halt {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : σ} {kind : Assembly.HaltKind}
        (hStmt :
          Stmt.Eval model handler program fuel stmt state
            (Outcome.halt kind outState)) :
        Block.Eval model handler program (fuel + 1)
          { stmts := stmt :: rest } state (Outcome.halt kind outState)

  inductive Stmt.Eval {σ : Type} (model : StateModel σ)
      (handler : Handler σ) (program : Program) :
      Nat → Stmt → σ → OutcomeT σ → Prop where
    | code {fuel : Nat} {code : Code} {state final : σ}
        (hCode : Code.run model handler code state = .ok final) :
        Stmt.Eval model handler program fuel (.code code) state
          (Outcome.regular final)
    | if_false {fuel : Nat} {cond : Code} {body : Block}
        {state stateAfterCond : σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, false)) :
        Stmt.Eval model handler program (fuel + 1) (.if_ cond body) state
          (Outcome.regular stateAfterCond)
    | if_true {fuel : Nat} {cond : Code} {body : Block}
        {state stateAfterCond : σ} {outcome : OutcomeT σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond outcome) :
        Stmt.Eval model handler program (fuel + 1) (.if_ cond body) state
          outcome
    | switch_none {fuel : Nat} {scrutinee : Code}
        {cases : List (Word × Block)} {defaultBody : Option Block}
        {state stateAfterScrutinee : σ}
        {stack : EvmYul.Stack Word} {value : Word}
        (hScrutinee :
          Code.run model handler scrutinee state =
            .ok stateAfterScrutinee)
        (hPop :
          (model.evm stateAfterScrutinee).stack.pop =
            some (stack, value))
        (hSelect : Switch.select value cases defaultBody = none) :
        Stmt.Eval model handler program (fuel + 1)
          (.switch scrutinee cases defaultBody) state
          (Outcome.regular
            (model.withEVM stateAfterScrutinee
              { model.evm stateAfterScrutinee with stack := stack }))
    | switch_some {fuel : Nat} {scrutinee : Code}
        {cases : List (Word × Block)} {defaultBody : Option Block}
        {state stateAfterScrutinee stateAfterPop : σ}
        {stack : EvmYul.Stack Word} {value : Word} {body : Block}
        {outcome : OutcomeT σ}
        (hScrutinee :
          Code.run model handler scrutinee state =
            .ok stateAfterScrutinee)
        (hPop :
          (model.evm stateAfterScrutinee).stack.pop =
            some (stack, value))
        (hStateAfterPop :
          stateAfterPop =
            model.withEVM stateAfterScrutinee
              { model.evm stateAfterScrutinee with stack := stack })
        (hSelect : Switch.select value cases defaultBody = some body)
        (hBody :
          Block.Eval model handler program fuel body stateAfterPop outcome) :
        Stmt.Eval model handler program (fuel + 1)
          (.switch scrutinee cases defaultBody) state outcome
    | for_init_regular {fuel : Nat} {init : Block} {cond : Code}
        {post body : Block} {state initState : σ}
        {outcome : OutcomeT σ}
        (hInit :
          Block.Eval model handler program fuel init state
            (Outcome.regular initState))
        (hLoop :
          For.Eval model handler program fuel cond post body initState
            outcome) :
        Stmt.Eval model handler program (fuel + 1)
          (.for_ init cond post body) state outcome
    | for_init_leave {fuel : Nat} {init : Block} {cond : Code}
        {post body : Block} {state outState : σ}
        (hInit :
          Block.Eval model handler program fuel init state
            (Outcome.leave outState)) :
        Stmt.Eval model handler program (fuel + 1)
          (.for_ init cond post body) state (Outcome.leave outState)
    | for_init_halt {fuel : Nat} {init : Block} {cond : Code}
        {post body : Block} {state outState : σ}
        {kind : Assembly.HaltKind}
        (hInit :
          Block.Eval model handler program fuel init state
            (Outcome.halt kind outState)) :
        Stmt.Eval model handler program (fuel + 1)
          (.for_ init cond post body) state (Outcome.halt kind outState)
    | brk {fuel : Nat} {state : σ} :
        Stmt.Eval model handler program fuel .brk state
          (Outcome.brk state)
    | cont {fuel : Nat} {state : σ} :
        Stmt.Eval model handler program fuel .cont state
          (Outcome.cont state)
    | leave {fuel : Nat} {state : σ}
        (hReturns : model.returns state ≠ []) :
        Stmt.Eval model handler program fuel .leave state
          (Outcome.leave state)
    | call_regular {fuel : Nat} {name : Name} {state : σ}
        {proc : Proc} {args callerStack stack : EvmYul.Stack Word}
        {bodyState returned : σ} {frame : ReturnDest}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc (model.evm state).stack =
            some (args, callerStack))
        (hBody :
          Block.Eval model handler program fuel proc.body
            (model.pushReturn
              (model.withEVM state
                { model.evm state with stack := args })
              callerStack proc.retc)
            (Outcome.regular bodyState))
        (hPop : model.popReturn? bodyState = some (frame, returned))
        (hAttach :
          StackFrame.attachReturns? frame (model.evm bodyState).stack =
            some stack) :
        Stmt.Eval model handler program (fuel + 1) (.call name) state
          (Outcome.regular
            (model.withEVM returned
              { model.evm bodyState with stack := stack }))
    | call_leave {fuel : Nat} {name : Name} {state : σ}
        {proc : Proc} {args callerStack stack : EvmYul.Stack Word}
        {bodyState returned : σ} {frame : ReturnDest}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc (model.evm state).stack =
            some (args, callerStack))
        (hBody :
          Block.Eval model handler program fuel proc.body
            (model.pushReturn
              (model.withEVM state
                { model.evm state with stack := args })
              callerStack proc.retc)
            (Outcome.leave bodyState))
        (hPop : model.popReturn? bodyState = some (frame, returned))
        (hAttach :
          StackFrame.attachReturns? frame (model.evm bodyState).stack =
            some stack) :
        Stmt.Eval model handler program (fuel + 1) (.call name) state
          (Outcome.regular
            (model.withEVM returned
              { model.evm bodyState with stack := stack }))
    | call_halt {fuel : Nat} {name : Name} {state : σ}
        {proc : Proc} {args callerStack : EvmYul.Stack Word}
        {bodyState : σ} {kind : Assembly.HaltKind}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc (model.evm state).stack =
            some (args, callerStack))
        (hBody :
          Block.Eval model handler program fuel proc.body
            (model.pushReturn
              (model.withEVM state
                { model.evm state with stack := args })
              callerStack proc.retc)
            (Outcome.halt kind bodyState)) :
        Stmt.Eval model handler program (fuel + 1) (.call name) state
          (Outcome.halt kind bodyState)
    | terminal {fuel : Nat} {kind : Assembly.HaltKind}
        {state : σ} {evm : EVMState}
        (hStep : Terminal.step kind (model.evm state) = .ok evm) :
        Stmt.Eval model handler program fuel (.terminal kind) state
          (Outcome.halt kind (model.withEVM state evm))

  inductive For.Eval {σ : Type} (model : StateModel σ)
      (handler : Handler σ) (program : Program) :
      Nat → Code → Block → Block → σ → OutcomeT σ → Prop where
    | false {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond : σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, false)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.regular stateAfterCond)
    | body_brk {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.brk bodyState)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.regular bodyState)
    | body_leave {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.leave bodyState)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.leave bodyState)
    | body_halt {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : σ} {kind : Assembly.HaltKind}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.halt kind bodyState)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.halt kind bodyState)
    | regular_post_regular {fuel : Nat} {cond : Code}
        {post body : Block} {state stateAfterCond bodyState postState : σ}
        {outcome : OutcomeT σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.regular bodyState))
        (hPost :
          Block.Eval model handler program fuel post bodyState
            (Outcome.regular postState))
        (hLoop :
          For.Eval model handler program fuel cond post body postState
            outcome) :
        For.Eval model handler program (fuel + 1) cond post body state
          outcome
    | cont_post_regular {fuel : Nat} {cond : Code}
        {post body : Block} {state stateAfterCond bodyState postState : σ}
        {outcome : OutcomeT σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.cont bodyState))
        (hPost :
          Block.Eval model handler program fuel post bodyState
            (Outcome.regular postState))
        (hLoop :
          For.Eval model handler program fuel cond post body postState
            outcome) :
        For.Eval model handler program (fuel + 1) cond post body state
          outcome
    | regular_post_leave {fuel : Nat} {cond : Code}
        {post body : Block} {state stateAfterCond bodyState postState : σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.regular bodyState))
        (hPost :
          Block.Eval model handler program fuel post bodyState
            (Outcome.leave postState)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.leave postState)
    | cont_post_leave {fuel : Nat} {cond : Code}
        {post body : Block} {state stateAfterCond bodyState postState : σ}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.cont bodyState))
        (hPost :
          Block.Eval model handler program fuel post bodyState
            (Outcome.leave postState)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.leave postState)
    | regular_post_halt {fuel : Nat} {cond : Code}
        {post body : Block} {state stateAfterCond bodyState postState : σ}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.regular bodyState))
        (hPost :
          Block.Eval model handler program fuel post bodyState
            (Outcome.halt kind postState)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.halt kind postState)
    | cont_post_halt {fuel : Nat} {cond : Code}
        {post body : Block} {state stateAfterCond bodyState postState : σ}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runCondition model handler cond state =
            .ok (stateAfterCond, true))
        (hBody :
          Block.Eval model handler program fuel body stateAfterCond
            (Outcome.cont bodyState))
        (hPost :
          Block.Eval model handler program fuel post bodyState
            (Outcome.halt kind postState)) :
        For.Eval model handler program (fuel + 1) cond post body state
          (Outcome.halt kind postState)
end

set_option linter.unusedSimpArgs false in
mutual
  theorem Block.eval_of_run {σ : Type} {model : StateModel σ}
      {handler : Handler σ} {program : Program} {fuel : Nat}
      {block : Block} {state : σ} {outcome : OutcomeT σ}
      (hRun : Block.run model handler program fuel block state = .ok outcome) :
      Block.Eval model handler program fuel block state outcome := by
    cases fuel with
    | zero =>
        simp [Block.run, invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simp [Block.run] at hRun
                cases hRun
                exact Block.Eval.nil
            | cons stmt rest =>
                unfold Block.run at hRun
                cases hStmtRun :
                    Stmt.run model handler program fuel stmt state with
                | error err =>
                    rw [hStmtRun] at hRun
                    cases hRun
                | ok stmtOutcome =>
                    rw [hStmtRun] at hRun
                    have hStmtEval := Stmt.eval_of_run hStmtRun
                    cases stmtOutcome with
                    | mk stmtState stmtMode =>
                        cases stmtMode with
                        | regular =>
                            exact
                              Block.Eval.cons_regular
                                (by
                                  simpa [Outcome.regular] using hStmtEval)
                                (Block.eval_of_run hRun)
                        | brk =>
                            cases hRun
                            exact
                              Block.Eval.cons_brk
                                (by simpa [Outcome.brk] using hStmtEval)
                        | cont =>
                            cases hRun
                            exact
                              Block.Eval.cons_cont
                                (by simpa [Outcome.cont] using hStmtEval)
                        | leave =>
                            cases hRun
                            exact
                              Block.Eval.cons_leave
                                (by simpa [Outcome.leave] using hStmtEval)
                        | halt kind =>
                            cases hRun
                            exact
                              Block.Eval.cons_halt
                                (by simpa [Outcome.halt] using hStmtEval)

  theorem Stmt.eval_of_run {σ : Type} {model : StateModel σ}
      {handler : Handler σ} {program : Program} {fuel : Nat}
      {stmt : Stmt} {state : σ} {outcome : OutcomeT σ}
      (hRun : Stmt.run model handler program fuel stmt state = .ok outcome) :
      Stmt.Eval model handler program fuel stmt state outcome := by
    cases stmt with
    | code code =>
        unfold Stmt.run at hRun
        cases hCode : Code.run model handler code state with
        | error err =>
            simp [hCode, Bind.bind, Except.bind] at hRun
        | ok final =>
            simp [hCode, Bind.bind, Except.bind] at hRun
            cases hRun
            exact Stmt.Eval.code hCode
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hCond :
                Code.runCondition model handler cond state with
            | error err =>
                rw [hCond] at hRun
                cases hRun
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                rw [hCond] at hRun
                cases condTrue with
                | false =>
                    simp at hRun
                    cases hRun
                    exact Stmt.Eval.if_false hCond
                | true =>
                    exact
                      Stmt.Eval.if_true hCond
                        (Block.eval_of_run hRun)
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hScrutinee :
                Code.run model handler scrutinee state with
            | error err =>
                simp [hScrutinee, Bind.bind, Except.bind] at hRun
            | ok stateAfterScrutinee =>
                simp [hScrutinee, Bind.bind, Except.bind] at hRun
                cases hPop :
                    (model.evm stateAfterScrutinee).stack.pop with
                | none =>
                    simp [hPop] at hRun
                | some popped =>
                    rcases popped with ⟨stack, value⟩
                    simp [hPop] at hRun
                    let stateAfterPop :=
                      model.withEVM stateAfterScrutinee
                        { model.evm stateAfterScrutinee with stack := stack }
                    cases hSelect :
                        Switch.select value cases defaultBody with
                    | none =>
                        simp [hSelect] at hRun
                        cases hRun
                        exact
                          Stmt.Eval.switch_none
                            hScrutinee hPop hSelect
                    | some body =>
                        simp [hSelect] at hRun
                        exact
                          Stmt.Eval.switch_some hScrutinee hPop
                            (show stateAfterPop =
                              model.withEVM stateAfterScrutinee
                                { model.evm stateAfterScrutinee with
                                  stack := stack } from rfl)
                            hSelect (Block.eval_of_run hRun)
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hInitRun :
                Block.run model handler program fuel init state with
            | error err =>
                simp [hInitRun, Bind.bind, Except.bind] at hRun
            | ok initOutcome =>
                simp [hInitRun, Bind.bind, Except.bind] at hRun
                have hInitEval := Block.eval_of_run hInitRun
                cases initOutcome with
                | mk initState initMode =>
                    cases initMode with
                    | regular =>
                        exact
                          Stmt.Eval.for_init_regular
                            (by simpa [Outcome.regular] using hInitEval)
                            (For.eval_of_run hRun)
                    | brk =>
                        dsimp [Bind.bind, Except.bind, invalid] at hRun
                        cases hRun
                    | cont =>
                        dsimp [Bind.bind, Except.bind, invalid] at hRun
                        cases hRun
                    | leave =>
                        change
                          Except.ok (Outcome.leave initState) =
                            Except.ok outcome at hRun
                        cases hRun
                        exact
                          Stmt.Eval.for_init_leave
                            (by simpa [Outcome.leave] using hInitEval)
                    | halt kind =>
                        change
                          Except.ok (Outcome.halt kind initState) =
                            Except.ok outcome at hRun
                        cases hRun
                        exact
                          Stmt.Eval.for_init_halt
                            (by simpa [Outcome.halt] using hInitEval)
    | brk =>
        simp [Stmt.run] at hRun
        cases hRun
        exact Stmt.Eval.brk
    | cont =>
        simp [Stmt.run] at hRun
        cases hRun
        exact Stmt.Eval.cont
    | leave =>
        unfold Stmt.run at hRun
        cases hReturns : model.returns state with
        | nil =>
            simp [hReturns, invalid] at hRun
        | cons frame returns =>
            simp [hReturns] at hRun
            cases hRun
            exact Stmt.Eval.leave (by simp [hReturns])
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                simp [hLookup, Bind.bind, Except.bind, invalid] at hRun
            | some proc =>
                simp [hLookup, Bind.bind, Except.bind] at hRun
                cases hSplit :
                    StackFrame.splitArgs? proc.argc (model.evm state).stack with
                | none =>
                    simp [hSplit, Bind.bind, Except.bind] at hRun
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    simp [hSplit, Bind.bind, Except.bind] at hRun
                    let callState : σ :=
                      model.pushReturn
                        (model.withEVM state
                          { model.evm state with stack := args })
                        callerStack proc.retc
                    cases hBodyRun :
                        Block.run model handler program fuel proc.body
                          callState with
                    | error err =>
                        simp [callState, hBodyRun,
                          Bind.bind, Except.bind] at hRun
                    | ok bodyOutcome =>
                        simp [callState, hBodyRun,
                          Bind.bind, Except.bind] at hRun
                        have hBodyEval := Block.eval_of_run hBodyRun
                        cases bodyOutcome with
                        | mk bodyState bodyMode =>
                            cases bodyMode with
                            | regular =>
                                simp [Outcome.regular] at hRun
                                cases hPop :
                                    model.popReturn? bodyState with
                                | none =>
                                    simp [hPop, invalid] at hRun
                                | some popped =>
                                    rcases popped with ⟨frame, returned⟩
                                    simp [hPop] at hRun
                                    cases hAttach :
                                        StackFrame.attachReturns? frame
                                          (model.evm bodyState).stack with
                                    | none =>
                                        simp [hAttach, invalid] at hRun
                                    | some stack =>
                                        simp [hAttach] at hRun
                                        cases hRun
                                        exact
                                          Stmt.Eval.call_regular hLookup hSplit
                                            (by
                                              simpa [callState,
                                                Outcome.regular]
                                                using hBodyEval)
                                            hPop hAttach
                            | brk =>
                                simp [Outcome.brk, invalid] at hRun
                            | cont =>
                                simp [Outcome.cont, invalid] at hRun
                            | leave =>
                                simp [Outcome.leave] at hRun
                                cases hPop :
                                    model.popReturn? bodyState with
                                | none =>
                                    simp [hPop, invalid] at hRun
                                | some popped =>
                                    rcases popped with ⟨frame, returned⟩
                                    simp [hPop] at hRun
                                    cases hAttach :
                                        StackFrame.attachReturns? frame
                                          (model.evm bodyState).stack with
                                    | none =>
                                        simp [hAttach, invalid] at hRun
                                    | some stack =>
                                        simp [hAttach] at hRun
                                        cases hRun
                                        exact
                                          Stmt.Eval.call_leave hLookup hSplit
                                            (by
                                              simpa [callState, Outcome.leave]
                                                using hBodyEval)
                                            hPop hAttach
                            | halt kind =>
                                simp [Outcome.halt] at hRun
                                cases hRun
                                exact
                                  Stmt.Eval.call_halt hLookup hSplit
                                    (by
                                      simpa [callState, Outcome.halt]
                                        using hBodyEval)
    | terminal kind =>
        unfold Stmt.run at hRun
        cases hStep : Terminal.step kind (model.evm state) with
        | error err =>
            simp [hStep] at hRun
            cases hRun
        | ok evm =>
            simp [hStep] at hRun
            cases hRun
            exact Stmt.Eval.terminal hStep

  theorem For.eval_of_run {σ : Type} {model : StateModel σ}
      {handler : Handler σ} {program : Program} {fuel : Nat}
      {cond : Code} {post body : Block} {state : σ}
      {outcome : OutcomeT σ}
      (hRun :
        Stmt.runForLoop model handler program fuel cond post body state =
          .ok outcome) :
      For.Eval model handler program fuel cond post body state outcome := by
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoop at hRun
        cases hCond :
            Code.runCondition model handler cond state with
        | error err =>
            simp [hCond, Bind.bind, Except.bind] at hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            simp [hCond, Bind.bind, Except.bind] at hRun
            cases condTrue with
            | false =>
                simp at hRun
                cases hRun
                exact For.Eval.false hCond
            | true =>
                cases hBodyRun :
                    Block.run model handler program fuel body
                      stateAfterCond with
                | error err =>
                    simp [hBodyRun, Bind.bind, Except.bind] at hRun
                | ok bodyOutcome =>
                    simp [hBodyRun, Bind.bind, Except.bind] at hRun
                    have hBodyEval := Block.eval_of_run hBodyRun
                    cases bodyOutcome with
                    | mk bodyState bodyMode =>
                        cases bodyMode with
                        | regular =>
                            simp [Outcome.regular] at hRun
                            cases hPostRun :
                                Block.run model handler program fuel post
                                  bodyState with
                            | error err =>
                                simp [hPostRun,
                                  Bind.bind, Except.bind] at hRun
                            | ok postOutcome =>
                                simp [hPostRun,
                                  Bind.bind, Except.bind] at hRun
                                have hPostEval :=
                                  Block.eval_of_run hPostRun
                                cases postOutcome with
                                | mk postState postMode =>
                                    cases postMode with
                                    | regular =>
                                        exact
                                          For.Eval.regular_post_regular hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.regular]
                                                using hPostEval)
                                            (For.eval_of_run hRun)
                                    | brk =>
                                        simp [invalid] at hRun
                                    | cont =>
                                        simp [invalid] at hRun
                                    | leave =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.regular_post_leave hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.leave]
                                                using hPostEval)
                                    | halt kind =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.regular_post_halt hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.halt]
                                                using hPostEval)
                        | brk =>
                            simp [Outcome.brk] at hRun
                            cases hRun
                            exact
                              For.Eval.body_brk hCond
                                (by
                                  simpa [Outcome.brk] using hBodyEval)
                        | cont =>
                            simp [Outcome.cont] at hRun
                            cases hPostRun :
                                Block.run model handler program fuel post
                                  bodyState with
                            | error err =>
                                simp [hPostRun,
                                  Bind.bind, Except.bind] at hRun
                            | ok postOutcome =>
                                simp [hPostRun,
                                  Bind.bind, Except.bind] at hRun
                                have hPostEval :=
                                  Block.eval_of_run hPostRun
                                cases postOutcome with
                                | mk postState postMode =>
                                    cases postMode with
                                    | regular =>
                                        exact
                                          For.Eval.cont_post_regular hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.regular]
                                                using hPostEval)
                                            (For.eval_of_run hRun)
                                    | brk =>
                                        simp [invalid] at hRun
                                    | cont =>
                                        simp [invalid] at hRun
                                    | leave =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.cont_post_leave hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.leave]
                                                using hPostEval)
                                    | halt kind =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.cont_post_halt hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.halt]
                                                using hPostEval)
                        | leave =>
                            simp [Outcome.leave] at hRun
                            cases hRun
                            exact
                              For.Eval.body_leave hCond
                                (by
                                  simpa [Outcome.leave] using hBodyEval)
                        | halt kind =>
                            simp [Outcome.halt] at hRun
                            cases hRun
                            exact
                              For.Eval.body_halt hCond
                                (by
                                  simpa [Outcome.halt] using hBodyEval)
end

namespace Program

def runState {σ : Type} (model : StateModel σ)
    (handler : Handler σ) (fuel : Nat) (program : Structured.Program)
    (state : σ) : Except EVMException (OutcomeT σ) :=
  Block.run model handler program fuel program.body state

theorem eval_of_runState {σ : Type} {model : StateModel σ}
    {handler : Handler σ} {fuel : Nat} {program : Structured.Program}
    {state : σ} {outcome : OutcomeT σ}
    (hRun : runState model handler fuel program state = .ok outcome) :
    Block.Eval model handler program fuel program.body state outcome :=
  Block.eval_of_run hRun

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
