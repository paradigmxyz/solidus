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

def Allowed (kind : Assembly.HaltKind) (state : EVMState) : Prop :=
  kind = .selfdestruct → state.executionEnv.perm = true

theorem not_allowed_iff
    {kind : Assembly.HaltKind} {state : EVMState} :
    ¬Allowed kind state ↔
      kind = .selfdestruct ∧ state.executionEnv.perm = false := by
  cases kind <;> cases hPermission : state.executionEnv.perm <;>
    simp [Allowed, hPermission]

theorem allowed_of_shared_eq
    {kind : Assembly.HaltKind} {source target : EVMState}
    (hShared : source.toSharedState = target.toSharedState)
    (hAllowed : Allowed kind source) :
    Allowed kind target := by
  intro hKind
  rw [← hShared]
  exact hAllowed hKind

theorem allowed_of_step
    {kind : Assembly.HaltKind} {state final : EVMState}
    (hStep : step kind state = .ok final) :
    Allowed kind state := by
  intro hSelfdestruct
  subst kind
  cases hPermission : state.executionEnv.perm with
  | false =>
      have hStatic :=
        Assembly.PrimOp.step_selfdestruct_of_static state hPermission
      change Assembly.PrimOp.selfdestruct.step state = .ok final at hStep
      rw [hStatic] at hStep
      contradiction
  | true => rfl

/--
Terminal execution is defined whenever the source stack contains the operands
declared by the halt kind.

This is the source-owned fact used by backward compiler proofs: symbolic typing
must establish the arity bound, while the terminal semantics itself constructs
the resulting EVM state.
-/
theorem exists_step_of_argCount_le
    (kind : Assembly.HaltKind) (state : EVMState)
    (hStack : kind.argCount ≤ state.stack.length)
    (hAllowed : Allowed kind state) :
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
              have hPermission : shared.executionEnv.perm = true :=
                hAllowed rfl
              let state : EVMState :=
                { toSharedState := shared
                  pc := pc
                  stack := recipient :: tail
                  execLength := execLength }
              have hRaw :
                  EvmYul.step (τ := .EVM) .SELFDESTRUCT none state =
                    .ok (EvmYul.EVM.selfdestructState
                      state recipient tail) :=
                EvmYul.EVM.step_selfdestruct_of_stack
                  state recipient tail rfl
              exact ⟨_, by
                change Assembly.PrimOp.selfdestruct.step state = _
                rw [Assembly.PrimOp.step_selfdestruct_of_permitted
                  state hPermission, hRaw]⟩

/--
Terminal operations consume only their declared stack prefix. Appending a
compiler-owned suffix therefore appends the same suffix to the final stack
without changing any source-visible runtime data.
-/
theorem step_append_stack
    (kind : Assembly.HaltKind) (state final : EVMState)
    (hidden : EvmYul.Stack Word)
    (hStep : step kind state = .ok final) :
    step kind { state with stack := state.stack ++ hidden } =
      .ok { final with stack := final.stack ++ hidden } := by
  cases state with
  | mk shared pc stack execLength =>
      cases kind with
      | stop =>
          cases hStep
          rfl
      | «return» =>
          cases stack with
          | nil =>
              contradiction
          | cons first rest =>
              cases rest with
              | nil =>
                  contradiction
              | cons second tail =>
                  cases hStep
                  rfl
      | revert =>
          cases stack with
          | nil =>
              contradiction
          | cons first rest =>
              cases rest with
              | nil =>
                  contradiction
              | cons second tail =>
                  cases hStep
                  rfl
      | selfdestruct =>
          have hAllowed := allowed_of_step hStep
          have hPermission : shared.executionEnv.perm = true :=
            hAllowed rfl
          cases stack with
          | nil =>
              change
                Assembly.PrimOp.selfdestruct.step
                    { toSharedState := shared
                      pc := pc
                      stack := []
                      execLength := execLength } =
                  .ok final at hStep
              rw [Assembly.PrimOp.step_selfdestruct_of_permitted _
                hPermission] at hStep
              change
                (Except.error .StackUnderflow :
                    Except EVMException EVMState) = .ok final at hStep
              contradiction
          | cons recipient tail =>
              let state : EVMState :=
                { toSharedState := shared
                  pc := pc
                  stack := recipient :: tail
                  execLength := execLength }
              let framed : EVMState :=
                { state with stack := state.stack ++ hidden }
              have hRaw :
                  EvmYul.step (τ := .EVM) .SELFDESTRUCT none state =
                    .ok (EvmYul.EVM.selfdestructState
                      state recipient tail) :=
                EvmYul.EVM.step_selfdestruct_of_stack
                  state recipient tail rfl
              have hRawFramed :
                  EvmYul.step (τ := .EVM) .SELFDESTRUCT none framed =
                    .ok (EvmYul.EVM.selfdestructState
                      framed recipient (tail ++ hidden)) := by
                apply EvmYul.EVM.step_selfdestruct_of_stack
                simp [framed, state]
              change Assembly.PrimOp.selfdestruct.step state = .ok final at hStep
              rw [Assembly.PrimOp.step_selfdestruct_of_permitted
                state hPermission, hRaw] at hStep
              cases hStep
              change Assembly.PrimOp.selfdestruct.step framed = _
              rw [Assembly.PrimOp.step_selfdestruct_of_permitted
                framed hPermission, hRawFramed]
              rfl

/--
Terminal execution is congruent when states differ only in compiler-owned
control counters.
-/
theorem step_map_eraseRuntimeControl
    (kind : Assembly.HaltKind) {target source : EVMState}
    (hRel : Assembly.SameRuntimeData target source) :
    (step kind target).map Assembly.eraseRuntimeControl =
      (step kind source).map Assembly.eraseRuntimeControl := by
  cases target with
  | mk targetShared targetPc targetStack targetExecLength =>
      cases source with
      | mk sourceShared sourcePc sourceStack sourceExecLength =>
          simp [Assembly.SameRuntimeData,
            Assembly.eraseRuntimeControl] at hRel
          rcases hRel with ⟨rfl, rfl⟩
          cases kind with
          | stop =>
              rfl
          | «return» =>
              cases targetStack with
              | nil =>
                  rfl
              | cons first rest =>
                  cases rest <;> rfl
          | revert =>
              cases targetStack with
              | nil =>
                  rfl
              | cons first rest =>
                  cases rest <;> rfl
          | selfdestruct =>
              cases hPermission : targetShared.executionEnv.perm with
              | false =>
                  change
                    (Assembly.PrimOp.selfdestruct.step
                        { toSharedState := targetShared
                          pc := targetPc
                          stack := targetStack
                          execLength := targetExecLength }).map
                          Assembly.eraseRuntimeControl =
                      (Assembly.PrimOp.selfdestruct.step
                        { toSharedState := targetShared
                          pc := sourcePc
                          stack := targetStack
                          execLength := sourceExecLength }).map
                          Assembly.eraseRuntimeControl
                  rw [Assembly.PrimOp.step_selfdestruct_of_static _
                      hPermission,
                    Assembly.PrimOp.step_selfdestruct_of_static _
                      hPermission]
              | true =>
                  cases targetStack with
                  | nil =>
                      change
                        (Assembly.PrimOp.selfdestruct.step
                            { toSharedState := targetShared
                              pc := targetPc
                              stack := []
                              execLength := targetExecLength }).map
                              Assembly.eraseRuntimeControl =
                          (Assembly.PrimOp.selfdestruct.step
                            { toSharedState := targetShared
                              pc := sourcePc
                              stack := []
                              execLength := sourceExecLength }).map
                              Assembly.eraseRuntimeControl
                      rw [Assembly.PrimOp.step_selfdestruct_of_permitted _
                          hPermission,
                        Assembly.PrimOp.step_selfdestruct_of_permitted _
                          hPermission]
                      rfl
                  | cons recipient tail =>
                      let target : EVMState :=
                        { toSharedState := targetShared
                          pc := targetPc
                          stack := recipient :: tail
                          execLength := targetExecLength }
                      let source : EVMState :=
                        { toSharedState := targetShared
                          pc := sourcePc
                          stack := recipient :: tail
                          execLength := sourceExecLength }
                      have hTarget :
                          EvmYul.step (τ := .EVM) .SELFDESTRUCT none target =
                            .ok (EvmYul.EVM.selfdestructState
                              target recipient tail) :=
                        EvmYul.EVM.step_selfdestruct_of_stack
                          target recipient tail rfl
                      have hSource :
                          EvmYul.step (τ := .EVM) .SELFDESTRUCT none source =
                            .ok (EvmYul.EVM.selfdestructState
                              source recipient tail) :=
                        EvmYul.EVM.step_selfdestruct_of_stack
                          source recipient tail rfl
                      change
                        (Assembly.PrimOp.selfdestruct.step target).map
                            Assembly.eraseRuntimeControl =
                          (Assembly.PrimOp.selfdestruct.step source).map
                            Assembly.eraseRuntimeControl
                      rw [Assembly.PrimOp.step_selfdestruct_of_permitted
                          target hPermission,
                        Assembly.PrimOp.step_selfdestruct_of_permitted
                          source hPermission,
                        hTarget, hSource]
                      rfl

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

/--
An exact argument prefix is split from its caller suffix.
-/
theorem splitArgs?_append
    (args callerStack : EvmYul.Stack Word) :
    splitArgs? args.length (args ++ callerStack) =
      some (args, callerStack) := by
  simp [splitArgs?]

/--
An exact return vector is reattached to the caller stack recorded in its
return destination.
-/
theorem attachReturns?_eq_some
    {returned callerStack : EvmYul.Stack Word} {retc : Nat}
    (hLength : returned.length = retc) :
    attachReturns?
        { callerStack := callerStack, retc := retc } returned =
      some (returned ++ callerStack) := by
  simp [attachReturns?, hLength]

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
The legacy `Handler.afterInstr` API remains as a compatibility specialization.
The canonical `Control.Handler` below owns complete primitive and terminal
steps, so ordinary execution, transcript replay, and open effects share
procedure, branch, switch, loop, and terminal control recursion.
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

def IsExit {σ : Type} (outcome : OutcomeT σ) : Prop :=
  match outcome.mode with
  | .leave | .halt _ => True
  | .regular | .brk | .cont => False

end Outcome

/-!
The monad-polymorphic Structured control kernel.

This is the only recursive Structured evaluator. `Handler.stepInstr` owns the
entire instruction step, so open handlers can suspend before CALL/CREATE while
ordinary and legacy observer handlers remain thin specializations.
-/
namespace Control

structure Handler (M : Type → Type) (σ : Type) where
  stepInstr : BasicInstr → σ → M σ
  stepTerminal : Assembly.HaltKind → σ → M σ

namespace Handler

def ofLegacy {σ : Type} (model : StateModel σ)
    (handler : EffectSemantics.Handler σ) :
    Control.Handler (Except EVMException) σ where
  stepInstr instr state := do
    let evm ← instr.step (model.evm state)
    handler.afterInstr instr (model.withEVM state evm)
  stepTerminal kind state := do
    let evm ← Terminal.step kind (model.evm state)
    .ok (model.withEVM state evm)

end Handler

namespace Code

def run {M : Type → Type} [Monad M] {σ : Type}
    (handler : Handler M σ) :
    Structured.Code → σ → M σ
  | [], state => pure state
  | instr :: rest, state => do
      let state' ← handler.stepInstr instr state
      run handler rest state'

def popCondition {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M] {σ : Type}
    (model : StateModel σ) (state : σ) : M (σ × Bool) :=
  match (model.evm state).stack.pop with
  | some (stack, cond) =>
      pure
        (model.withEVM state { model.evm state with stack := stack },
          cond != EvmYul.UInt256.ofNat 0)
  | none =>
      throw .StackUnderflow

def runCondition {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M] {σ : Type}
    (model : StateModel σ) (handler : Handler M σ)
    (code : Structured.Code) (state : σ) : M (σ × Bool) := do
  let state' ← run handler code state
  popCondition model state'

end Code

mutual
  def Block.run {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M] {σ : Type}
      (model : StateModel σ) (handler : Handler M σ)
      (program : Program) :
      Nat → Block → σ → M (OutcomeT σ)
    | 0, _block, _state =>
        throw .InvalidInstruction
    | _fuel + 1, ⟨[]⟩, state =>
        pure (Outcome.regular state)
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
      (program : Program) (fuel : Nat)
      (cond : Structured.Code) (post body : Block) (state : σ) :
      M (OutcomeT σ) :=
    match fuel with
    | 0 =>
        throw .InvalidInstruction
    | fuel' + 1 => do
        let (stateAfterCond, condTrue) ←
          Code.runCondition model handler cond state
        if condTrue then
          let bodyOutcome ←
            Block.run model handler program fuel' body stateAfterCond
          match bodyOutcome.mode with
          | .brk =>
              pure (Outcome.regular bodyOutcome.state)
          | .regular | .cont =>
              let postOutcome ←
                Block.run model handler program fuel' post
                  bodyOutcome.state
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
          pure (Outcome.regular stateAfterCond)

  def Stmt.run {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M] {σ : Type}
      (model : StateModel σ) (handler : Handler M σ)
      (program : Program) :
      Nat → Stmt → σ → M (OutcomeT σ)
    | _fuel, .code code, state => do
        let state' ← Code.run handler code state
        pure (Outcome.regular state')
    | 0, .if_ _cond _body, _state =>
        throw .InvalidInstruction
    | fuel + 1, .if_ cond body, state => do
        let (stateAfterCond, condTrue) ←
          Code.runCondition model handler cond state
        if condTrue then
          Block.run model handler program fuel body stateAfterCond
        else
          pure (Outcome.regular stateAfterCond)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        throw .InvalidInstruction
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let stateAfterScrutinee ← Code.run handler scrutinee state
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
                pure (Outcome.regular stateAfterPop)
    | 0, .for_ _init _cond _post _body, _state =>
        throw .InvalidInstruction
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
        pure (Outcome.brk state)
    | _fuel, .cont, state =>
        pure (Outcome.cont state)
    | _fuel, .leave, state =>
        match model.returns state with
        | [] => throw .InvalidInstruction
        | _ :: _ => pure (Outcome.leave state)
    | 0, .call _name, _state =>
        throw .InvalidInstruction
    | fuel + 1, .call name, state =>
        match ProcList.lookup? name program.procs with
        | none =>
            throw .InvalidInstruction
        | some proc =>
            match StackFrame.splitArgs? proc.argc (model.evm state).stack with
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
                            StackFrame.attachReturns? frame
                              (model.evm outcome.state).stack
                        with
                        | none =>
                            throw .InvalidInstruction
                        | some stack =>
                            let evm :=
                              { model.evm outcome.state with stack := stack }
                            pure
                              (Outcome.regular
                                (model.withEVM returned evm))
                | .brk | .cont =>
                    throw .InvalidInstruction
                | .halt kind =>
                    pure (Outcome.halt kind outcome.state)
    | _fuel, .terminal kind, state => do
        let final ← handler.stepTerminal kind state
        pure (Outcome.halt kind final)
end

namespace Program

def runState {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M] {σ : Type}
    (model : StateModel σ) (handler : Handler M σ)
    (fuel : Nat) (program : Structured.Program)
    (state : σ) : M (OutcomeT σ) :=
  Block.run model handler program fuel program.body state

end Program

end Control

namespace Code

abbrev run {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (code : Structured.Code) (state : σ) :
    Except EVMException σ :=
  Control.Code.run (Control.Handler.ofLegacy model handler) code state

abbrev popCondition {σ : Type} (model : StateModel σ) (state : σ) :
    Except EVMException (σ × Bool) :=
  Control.Code.popCondition model state

abbrev runCondition {σ : Type} (model : StateModel σ)
    (handler : Handler σ) (code : Structured.Code) (state : σ) :
    Except EVMException (σ × Bool) :=
  Control.Code.runCondition model
    (Control.Handler.ofLegacy model handler) code state

theorem run_cons_eq_run_single_bind
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (instr : BasicInstr) (rest : Structured.Code) (state : σ) :
    run model handler (instr :: rest) state =
      (run model handler [instr] state).bind
        (run model handler rest) := by
  cases hStep : instr.step (model.evm state) with
  | error err =>
      simp [run, Control.Code.run, Control.Handler.ofLegacy,
        hStep, Bind.bind, Except.bind]
  | ok evm =>
      cases hAfter :
          handler.afterInstr instr (model.withEVM state evm) with
      | error err =>
          simp [run, Control.Code.run, Control.Handler.ofLegacy,
            hStep, hAfter, Bind.bind, Except.bind]
      | ok final =>
          simp [run, Control.Code.run, Control.Handler.ofLegacy,
            hStep, hAfter, Bind.bind, Except.bind]

theorem run_append
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (left right : Structured.Code) (state : σ) :
    run model handler (left ++ right) state =
      (run model handler left state).bind
        (run model handler right) := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons instr rest ih =>
      rw [List.cons_append,
        run_cons_eq_run_single_bind
          model handler instr (rest ++ right) state,
        run_cons_eq_run_single_bind
          model handler instr rest state]
      cases hHead : run model handler [instr] state with
      | error error =>
          rfl
      | ok afterHead =>
          simpa [hHead] using ih afterHead

end Code

namespace Block

abbrev run {σ : Type} (model : StateModel σ)
    (handler : Handler σ) (program : Program)
    (fuel : Nat) (block : Block) (state : σ) :
    Except EVMException (OutcomeT σ) :=
  Control.Block.run model
    (Control.Handler.ofLegacy model handler)
    program fuel block state

end Block

namespace Stmt

abbrev runForLoop {σ : Type} (model : StateModel σ)
    (handler : Handler σ) (program : Program) (fuel : Nat)
    (cond : Structured.Code) (post body : Block) (state : σ) :
    Except EVMException (OutcomeT σ) :=
  Control.Stmt.runForLoop model
    (Control.Handler.ofLegacy model handler)
    program fuel cond post body state

abbrev run {σ : Type} (model : StateModel σ)
    (handler : Handler σ) (program : Program)
    (fuel : Nat) (stmt : Stmt) (state : σ) :
    Except EVMException (OutcomeT σ) :=
  Control.Stmt.run model
    (Control.Handler.ofLegacy model handler)
    program fuel stmt state

end Stmt

namespace Code

@[simp] theorem run_nil
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (state : σ) :
    run model handler [] state = .ok state := rfl

@[simp] theorem run_cons
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (instr : BasicInstr) (rest : Structured.Code) (state : σ) :
    run model handler (instr :: rest) state =
      (do
        let evm ← instr.step (model.evm state)
        let state' := model.withEVM state evm
        let state'' ← handler.afterInstr instr state'
        run model handler rest state'') := by
  simp [run, Control.Code.run, Control.Handler.ofLegacy]

theorem runCondition_eq_run_bind
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (code : Structured.Code) (state : σ) :
    runCondition model handler code state =
      (run model handler code state).bind (popCondition model) := rfl

end Code

namespace Block

@[simp] theorem run_zero
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (block : Block) (state : σ) :
    run model handler program 0 block state = invalid := rfl

@[simp] theorem run_nil
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (state : σ) :
    run model handler program (fuel + 1) { stmts := [] } state =
      .ok (Outcome.regular state) := rfl

@[simp] theorem run_cons
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (stmt : Stmt)
    (rest : List Stmt) (state : σ) :
    run model handler program (fuel + 1)
        { stmts := stmt :: rest } state =
      (do
        let outcome ← Stmt.run model handler program fuel stmt state
        match outcome.mode with
        | .regular =>
            run model handler program fuel { stmts := rest } outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok outcome) := rfl

end Block

namespace Stmt

@[simp] theorem runForLoop_zero
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (cond : Structured.Code)
    (post body : Block) (state : σ) :
    runForLoop model handler program 0 cond post body state =
      invalid := rfl

@[simp] theorem runForLoop_succ
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (cond : Structured.Code)
    (post body : Block) (state : σ) :
    runForLoop model handler program (fuel + 1)
        cond post body state =
      (match Code.runCondition model handler cond state with
       | .error err => .error err
       | .ok result =>
           if result.2 then
             match
                 Block.run model handler program fuel body result.1
             with
             | .error err => .error err
             | .ok bodyOutcome =>
                 match bodyOutcome.mode with
                 | .brk =>
                     .ok (Outcome.regular bodyOutcome.state)
                 | .regular | .cont =>
                     match
                         Block.run model handler program fuel post
                           bodyOutcome.state
                     with
                     | .error err => .error err
                     | .ok postOutcome =>
                         match postOutcome.mode with
                         | .regular =>
                             runForLoop model handler program fuel
                               cond post body postOutcome.state
                         | .brk | .cont =>
                             invalid
                         | .leave | .halt _ =>
                             .ok postOutcome
                 | .leave | .halt _ =>
                     .ok bodyOutcome
           else
             .ok (Outcome.regular result.1)) := by
  cases hCode :
      Control.Code.run
        (Control.Handler.ofLegacy model handler) cond state with
  | error err =>
      simp [runForLoop, Control.Stmt.runForLoop,
        Code.runCondition, Control.Code.runCondition, Block.run, invalid,
        hCode, Bind.bind, Except.bind]
  | ok afterCode =>
      cases hPop :
          Control.Code.popCondition (M := Except EVMException)
            model afterCode with
      | error err =>
          simp [runForLoop, Control.Stmt.runForLoop,
            Code.runCondition, Control.Code.runCondition, Block.run, invalid,
            hCode, hPop, Bind.bind, Except.bind]
      | ok result =>
          rcases result with ⟨stateAfterCond, condTrue⟩
          simp [runForLoop, Control.Stmt.runForLoop,
            Code.runCondition, Control.Code.runCondition, Block.run, invalid,
            hCode, hPop, Bind.bind, Except.bind]
          cases condTrue with
          | false =>
              rfl
          | true =>
              simp only [Bool.true_eq, if_true]
              cases hBody :
                  Control.Block.run model
                    (Control.Handler.ofLegacy model handler)
                    program fuel body stateAfterCond with
              | error err =>
                  simp [hBody]
              | ok bodyOutcome =>
                  cases bodyOutcome with
                  | mk bodyState bodyMode =>
                      cases bodyMode with
                      | brk =>
                          simp [hBody]
                      | leave =>
                          simp [hBody]
                      | halt kind =>
                          simp [hBody]
                      | regular =>
                          cases hPost :
                              Control.Block.run model
                                (Control.Handler.ofLegacy model handler)
                                program fuel post bodyState with
                          | error err =>
                              simp [hBody, hPost]
                          | ok postOutcome =>
                              cases postOutcome with
                              | mk postState postMode =>
                                  cases postMode <;> simp [hBody, hPost]
                      | cont =>
                          cases hPost :
                              Control.Block.run model
                                (Control.Handler.ofLegacy model handler)
                                program fuel post bodyState with
                          | error err =>
                              simp [hBody, hPost]
                          | ok postOutcome =>
                              cases postOutcome with
                              | mk postState postMode =>
                                  cases postMode <;> simp [hBody, hPost]

@[simp] theorem run_code
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (code : Structured.Code)
    (state : σ) :
    run model handler program fuel (.code code) state =
      (do
        let state' ← Code.run model handler code state
        .ok (Outcome.regular state')) := by
  simp [run, Control.Stmt.run]

@[simp] theorem run_if_zero
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (cond : Structured.Code)
    (body : Block) (state : σ) :
    run model handler program 0 (.if_ cond body) state =
      invalid := rfl

@[simp] theorem run_if_succ
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (cond : Structured.Code)
    (body : Block) (state : σ) :
    run model handler program (fuel + 1) (.if_ cond body) state =
      (do
        let (stateAfterCond, condTrue) ←
          Code.runCondition model handler cond state
        if condTrue then
          Block.run model handler program fuel body stateAfterCond
        else
          .ok (Outcome.regular stateAfterCond)) := rfl

@[simp] theorem run_switch_zero
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (scrutinee : Structured.Code)
    (cases : List (Word × Block)) (defaultBody : Option Block)
    (state : σ) :
    run model handler program 0
        (.switch scrutinee cases defaultBody) state =
      invalid := rfl

@[simp] theorem run_switch_succ
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat)
    (scrutinee : Structured.Code)
    (cases : List (Word × Block)) (defaultBody : Option Block)
    (state : σ) :
    run model handler program (fuel + 1)
        (.switch scrutinee cases defaultBody) state =
      (do
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
            | none =>
                .ok (Outcome.regular stateAfterPop)) := rfl

@[simp] theorem run_for_zero
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (init : Block) (cond : Structured.Code)
    (post body : Block) (state : σ) :
    run model handler program 0 (.for_ init cond post body) state =
      invalid := rfl

@[simp] theorem run_for_succ
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (init : Block)
    (cond : Structured.Code) (post body : Block) (state : σ) :
    run model handler program (fuel + 1)
        (.for_ init cond post body) state =
      (do
        let initOutcome ←
          Block.run model handler program fuel init state
        match initOutcome.mode with
        | .regular =>
            runForLoop model handler program fuel cond post body
              initOutcome.state
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok initOutcome) := rfl

@[simp] theorem run_brk
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (state : σ) :
    run model handler program fuel .brk state =
      .ok (Outcome.brk state) := by
  simp [run, Control.Stmt.run]

@[simp] theorem run_cont
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (state : σ) :
    run model handler program fuel .cont state =
      .ok (Outcome.cont state) := by
  simp [run, Control.Stmt.run]

@[simp] theorem run_leave
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (state : σ) :
    run model handler program fuel .leave state =
      (match model.returns state with
       | [] => invalid
       | _ :: _ => .ok (Outcome.leave state)) := by
  simp [run, Control.Stmt.run, invalid]

@[simp] theorem run_call_zero
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (name : Name) (state : σ) :
    run model handler program 0 (.call name) state =
      invalid := rfl

@[simp] theorem run_call_succ
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (name : Name) (state : σ) :
    run model handler program (fuel + 1) (.call name) state =
      (match ProcList.lookup? name program.procs with
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
                                 { model.evm outcome.state with stack := stack }
                               .ok
                                 (Outcome.regular
                                   (model.withEVM returned evm))
                   | .brk | .cont =>
                       invalid
                   | .halt kind =>
                       .ok (Outcome.halt kind outcome.state)) := by
  cases hLookup : ProcList.lookup? name program.procs with
  | none =>
      simp [run, Control.Stmt.run, Block.run, invalid,
        hLookup, Bind.bind, Except.bind]
  | some proc =>
      cases hSplit :
          StackFrame.splitArgs? proc.argc (model.evm state).stack with
      | none =>
          simp [run, Control.Stmt.run, Block.run, invalid,
            hLookup, hSplit, Bind.bind, Except.bind]
      | some split =>
          rcases split with ⟨args, callerStack⟩
          let callState :=
            model.pushReturn
              (model.withEVM state { model.evm state with stack := args })
              callerStack proc.retc
          cases hBody :
              Block.run model handler program fuel proc.body callState with
          | error err =>
              simp [run, Control.Stmt.run, Block.run, invalid,
                hLookup, hSplit, callState, hBody, Bind.bind, Except.bind]
          | ok outcome =>
              simp [run, Control.Stmt.run, Block.run, invalid,
                hLookup, hSplit, callState, hBody, Bind.bind, Except.bind]

@[simp] theorem run_terminal
    {σ : Type} (model : StateModel σ) (handler : Handler σ)
    (program : Program) (fuel : Nat) (kind : Assembly.HaltKind)
    (state : σ) :
    run model handler program fuel (.terminal kind) state =
      (do
        let evm ← Terminal.step kind (model.evm state)
        .ok (Outcome.halt kind (model.withEVM state evm))) := by
  simp [run, Control.Stmt.run, Control.Handler.ofLegacy]

end Stmt

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

mutual
  /--
  Relational Structured evaluation is monotone in source fuel. Fuel bounds only
  recursive control depth; increasing the bound does not change the
  reconstructed outcome.
  -/
  theorem Block.Eval.mono
      {σ : Type} {model : StateModel σ} {handler : Handler σ}
      {program : Program} {fuel fuel' : Nat}
      {block : Block} {state : σ} {outcome : OutcomeT σ}
      (hEval :
        Block.Eval model handler program fuel block state outcome)
      (hFuel : fuel ≤ fuel') :
      Block.Eval model handler program fuel' block state outcome := by
    cases hEval with
    | nil =>
        cases fuel' with
        | zero => omega
        | succ fuel' => exact Block.Eval.nil
    | cons_regular hStmt hRest =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Block.Eval.cons_regular
                (Stmt.Eval.mono hStmt (by omega))
                (Block.Eval.mono hRest (by omega))
    | cons_brk hStmt =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Block.Eval.cons_brk
                (Stmt.Eval.mono hStmt (by omega))
    | cons_cont hStmt =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Block.Eval.cons_cont
                (Stmt.Eval.mono hStmt (by omega))
    | cons_leave hStmt =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Block.Eval.cons_leave
                (Stmt.Eval.mono hStmt (by omega))
    | cons_halt hStmt =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Block.Eval.cons_halt
                (Stmt.Eval.mono hStmt (by omega))

  theorem Stmt.Eval.mono
      {σ : Type} {model : StateModel σ} {handler : Handler σ}
      {program : Program} {fuel fuel' : Nat}
      {stmt : Stmt} {state : σ} {outcome : OutcomeT σ}
      (hEval :
        Stmt.Eval model handler program fuel stmt state outcome)
      (hFuel : fuel ≤ fuel') :
      Stmt.Eval model handler program fuel' stmt state outcome := by
    cases hEval with
    | code hCode =>
        exact Stmt.Eval.code hCode
    | if_false hCond =>
        cases fuel' with
        | zero => omega
        | succ fuel' => exact Stmt.Eval.if_false hCond
    | if_true hCond hBody =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.if_true hCond
                (Block.Eval.mono hBody (by omega))
    | switch_none hScrutinee hPop hSelect =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.switch_none hScrutinee hPop hSelect
    | switch_some hScrutinee hPop hStateAfterPop hSelect hBody =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.switch_some hScrutinee hPop hStateAfterPop
                hSelect (Block.Eval.mono hBody (by omega))
    | for_init_regular hInit hLoop =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.for_init_regular
                (Block.Eval.mono hInit (by omega))
                (For.Eval.mono hLoop (by omega))
    | for_init_leave hInit =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.for_init_leave
                (Block.Eval.mono hInit (by omega))
    | for_init_halt hInit =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.for_init_halt
                (Block.Eval.mono hInit (by omega))
    | brk =>
        exact Stmt.Eval.brk
    | cont =>
        exact Stmt.Eval.cont
    | leave hReturns =>
        exact Stmt.Eval.leave hReturns
    | call_regular hLookup hSplit hBody hPop hAttach =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.call_regular hLookup hSplit
                (Block.Eval.mono hBody (by omega)) hPop hAttach
    | call_leave hLookup hSplit hBody hPop hAttach =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.call_leave hLookup hSplit
                (Block.Eval.mono hBody (by omega)) hPop hAttach
    | call_halt hLookup hSplit hBody =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              Stmt.Eval.call_halt hLookup hSplit
                (Block.Eval.mono hBody (by omega))
    | terminal hStep =>
        exact Stmt.Eval.terminal hStep

  theorem For.Eval.mono
      {σ : Type} {model : StateModel σ} {handler : Handler σ}
      {program : Program} {fuel fuel' : Nat}
      {cond : Code} {post body : Block}
      {state : σ} {outcome : OutcomeT σ}
      (hEval :
        For.Eval model handler program fuel cond post body state outcome)
      (hFuel : fuel ≤ fuel') :
      For.Eval model handler program fuel' cond post body state outcome := by
    cases hEval with
    | false hCond =>
        cases fuel' with
        | zero => omega
        | succ fuel' => exact For.Eval.false hCond
    | body_brk hCond hBody =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.body_brk hCond
                (Block.Eval.mono hBody (by omega))
    | body_leave hCond hBody =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.body_leave hCond
                (Block.Eval.mono hBody (by omega))
    | body_halt hCond hBody =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.body_halt hCond
                (Block.Eval.mono hBody (by omega))
    | regular_post_regular hCond hBody hPost hLoop =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.regular_post_regular hCond
                (Block.Eval.mono hBody (by omega))
                (Block.Eval.mono hPost (by omega))
                (For.Eval.mono hLoop (by omega))
    | cont_post_regular hCond hBody hPost hLoop =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.cont_post_regular hCond
                (Block.Eval.mono hBody (by omega))
                (Block.Eval.mono hPost (by omega))
                (For.Eval.mono hLoop (by omega))
    | regular_post_leave hCond hBody hPost =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.regular_post_leave hCond
                (Block.Eval.mono hBody (by omega))
                (Block.Eval.mono hPost (by omega))
    | cont_post_leave hCond hBody hPost =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.cont_post_leave hCond
                (Block.Eval.mono hBody (by omega))
                (Block.Eval.mono hPost (by omega))
    | regular_post_halt hCond hBody hPost =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.regular_post_halt hCond
                (Block.Eval.mono hBody (by omega))
                (Block.Eval.mono hPost (by omega))
    | cont_post_halt hCond hBody hPost =>
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            exact
              For.Eval.cont_post_halt hCond
                (Block.Eval.mono hBody (by omega))
                (Block.Eval.mono hPost (by omega))
end

/--
Sequential composition for two independently reconstructed regular-prefix
block evaluations. The resulting fuel is hidden because fuel bounds proof
recursion rather than observable execution.
-/
theorem Block.Eval.append_regular_exists
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program}
    {leftFuel rightFuel : Nat} {left right : List Stmt}
    {state mid : σ} {outcome : OutcomeT σ}
    (hLeft :
      Block.Eval model handler program leftFuel { stmts := left } state
        (Outcome.regular mid))
    (hRight :
      Block.Eval model handler program rightFuel { stmts := right } mid
        outcome) :
    ∃ fuel,
      Block.Eval model handler program fuel
        { stmts := left ++ right } state outcome := by
  cases hLeft with
  | nil =>
      exact ⟨rightFuel, by simpa using hRight⟩
  | @cons_regular fuel stmt rest state headMid _ hStmt hRest =>
      obtain ⟨tailFuel, hTail⟩ :=
        Block.Eval.append_regular_exists hRest hRight
      let combinedFuel := Nat.max fuel tailFuel
      exact
        ⟨combinedFuel + 1,
          Block.Eval.cons_regular
            (Stmt.Eval.mono hStmt (Nat.le_max_left _ _))
            (Block.Eval.mono hTail (Nat.le_max_right _ _))⟩
termination_by left.length

/--
Appending unreachable statements after a nonregular block outcome preserves
the exact evaluation and fuel.
-/
theorem Block.Eval.append_nonregular
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program}
    {fuel : Nat} {left right : List Stmt}
    {state : σ} {outcome : OutcomeT σ}
    (hLeft :
      Block.Eval model handler program fuel { stmts := left } state outcome)
    (hMode : outcome.mode ≠ .regular) :
    Block.Eval model handler program fuel
      { stmts := left ++ right } state outcome := by
  cases hLeft with
  | nil =>
      exact False.elim (hMode rfl)
  | cons_regular hStmt hRest =>
      exact
        Block.Eval.cons_regular hStmt
          (Block.Eval.append_nonregular hRest hMode)
  | cons_brk hStmt =>
      exact Block.Eval.cons_brk hStmt
  | cons_cont hStmt =>
      exact Block.Eval.cons_cont hStmt
  | cons_leave hStmt =>
      exact Block.Eval.cons_leave hStmt
  | cons_halt hStmt =>
      exact Block.Eval.cons_halt hStmt
termination_by left.length

/--
Invert execution of an appended block at the append boundary.

Either the left block completes regularly and execution continues through the
right block, or a nonregular left outcome makes the right block unreachable.
Fuel is existential because it bounds proof recursion rather than observable
execution.
-/
theorem Block.Eval.append_cases
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program}
    {fuel : Nat} {left right : List Stmt}
    {state : σ} {outcome : OutcomeT σ}
    (hEval :
      Block.Eval model handler program fuel
        { stmts := left ++ right } state outcome) :
    (∃ mid leftFuel rightFuel,
        Block.Eval model handler program leftFuel
            { stmts := left } state (Outcome.regular mid) ∧
          Block.Eval model handler program rightFuel
            { stmts := right } mid outcome) ∨
      ∃ leftOutcome leftFuel,
        leftOutcome.mode ≠ .regular ∧
          Block.Eval model handler program leftFuel
            { stmts := left } state leftOutcome ∧
          outcome = leftOutcome := by
  induction left generalizing fuel state outcome with
  | nil =>
      left
      exact
        ⟨state, 1, fuel, Block.Eval.nil, by simpa using hEval⟩
  | cons stmt rest ih =>
      simp only [List.cons_append] at hEval
      cases hEval with
      | @cons_regular stmtFuel _ _ _ mid _ hStmt hTail =>
          rcases ih hTail with hRegular | hNonregular
          · rcases hRegular with
              ⟨final, leftFuel, rightFuel, hLeft, hRight⟩
            left
            refine
              ⟨final, Nat.max stmtFuel leftFuel + 1, rightFuel, ?_,
                hRight⟩
            exact
              Block.Eval.cons_regular
                (Stmt.Eval.mono hStmt (Nat.le_max_left _ _))
                (Block.Eval.mono hLeft (Nat.le_max_right _ _))
          · rcases hNonregular with
              ⟨leftOutcome, leftFuel, hMode, hLeft, hOutcome⟩
            right
            refine
              ⟨leftOutcome, Nat.max stmtFuel leftFuel + 1, hMode, ?_,
                hOutcome⟩
            exact
              Block.Eval.cons_regular
                (Stmt.Eval.mono hStmt (Nat.le_max_left _ _))
                (Block.Eval.mono hLeft (Nat.le_max_right _ _))
      | @cons_brk stmtFuel _ _ _ final hStmt =>
          right
          refine ⟨Outcome.brk final, stmtFuel + 1, ?_, ?_, rfl⟩
          · intro hMode
            cases hMode
          · exact Block.Eval.cons_brk hStmt
      | @cons_cont stmtFuel _ _ _ final hStmt =>
          right
          refine ⟨Outcome.cont final, stmtFuel + 1, ?_, ?_, rfl⟩
          · intro hMode
            cases hMode
          · exact Block.Eval.cons_cont hStmt
      | @cons_leave stmtFuel _ _ _ final hStmt =>
          right
          refine ⟨Outcome.leave final, stmtFuel + 1, ?_, ?_, rfl⟩
          · intro hMode
            cases hMode
          · exact Block.Eval.cons_leave hStmt
      | @cons_halt stmtFuel _ _ _ final kind hStmt =>
          right
          refine ⟨Outcome.halt kind final, stmtFuel + 1, ?_, ?_, rfl⟩
          · intro hMode
            cases hMode
          · exact Block.Eval.cons_halt hStmt

/--
A regular appended-block result forces the left prefix to complete regularly
and exposes the exact right-suffix execution.
-/
theorem Block.Eval.append_regular_cases
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program}
    {fuel : Nat} {left right : List Stmt}
    {state final : σ}
    (hEval :
      Block.Eval model handler program fuel
        { stmts := left ++ right } state (Outcome.regular final)) :
    ∃ mid leftFuel rightFuel,
      Block.Eval model handler program leftFuel
          { stmts := left } state (Outcome.regular mid) ∧
        Block.Eval model handler program rightFuel
          { stmts := right } mid (Outcome.regular final) := by
  rcases Block.Eval.append_cases hEval with hRegular | hNonregular
  · exact hRegular
  · rcases hNonregular with
      ⟨leftOutcome, _leftFuel, hMode, _hLeft, hOutcome⟩
    rw [← hOutcome] at hMode
    exact False.elim (hMode rfl)

/--
A nonregular statement result exits its enclosing block immediately, making
the remaining statement list unreachable.
-/
theorem Block.Eval.cons_nonregular
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program}
    {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
    {state : σ} {outcome : OutcomeT σ}
    (hStmt :
      Stmt.Eval model handler program fuel stmt state outcome)
    (hMode : outcome.mode ≠ .regular) :
    Block.Eval model handler program (fuel + 1)
      { stmts := stmt :: rest } state outcome := by
  rcases outcome with ⟨final, outcomeMode⟩
  cases outcomeMode with
  | regular =>
      exact False.elim (hMode rfl)
  | brk =>
      exact Block.Eval.cons_brk hStmt
  | cont =>
      exact Block.Eval.cons_cont hStmt
  | leave =>
      exact Block.Eval.cons_leave hStmt
  | halt kind =>
      exact Block.Eval.cons_halt hStmt

/--
An activation-exiting initializer determines the result of the whole `for`
statement without evaluating its condition or loop bodies.
-/
theorem Stmt.Eval.for_init_exit
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program}
    {fuel : Nat} {init : Block} {cond : Code} {post body : Block}
    {state : σ} {outcome : OutcomeT σ}
    (hInit :
      Block.Eval model handler program fuel init state outcome)
    (hExit : Outcome.IsExit outcome) :
    Stmt.Eval model handler program (fuel + 1)
      (.for_ init cond post body) state outcome := by
  rcases outcome with ⟨final, outcomeMode⟩
  cases outcomeMode with
  | regular =>
      simp [Outcome.IsExit, Outcome.regular] at hExit
  | brk =>
      simp [Outcome.IsExit, Outcome.brk] at hExit
  | cont =>
      simp [Outcome.IsExit, Outcome.cont] at hExit
  | leave =>
      exact Stmt.Eval.for_init_leave hInit
  | halt kind =>
      exact Stmt.Eval.for_init_halt hInit

attribute [local simp] OutcomeT.regular OutcomeT.brk OutcomeT.cont
  OutcomeT.leave OutcomeT.halt

mutual
  /--
  Every relational Structured block evaluation is an execution of the
  canonical interpreter at the same fuel.
  -/
  theorem Block.run_of_eval
      {σ : Type} {model : StateModel σ} {handler : Handler σ}
      {program : Program} {fuel : Nat}
      {block : Block} {state : σ} {outcome : OutcomeT σ}
      (hEval :
        Block.Eval model handler program fuel block state outcome) :
      Block.run model handler program fuel block state = .ok outcome := by
    cases hEval with
    | nil =>
        rfl
    | cons_regular hStmt hRest =>
        simp [Block.run, Stmt.run_of_eval hStmt,
          Block.run_of_eval hRest, Outcome.regular, Bind.bind, Except.bind]
    | cons_brk hStmt =>
        simp [Block.run, Stmt.run_of_eval hStmt, Outcome.brk,
          Bind.bind, Except.bind]
    | cons_cont hStmt =>
        simp [Block.run, Stmt.run_of_eval hStmt, Outcome.cont,
          Bind.bind, Except.bind]
    | cons_leave hStmt =>
        simp [Block.run, Stmt.run_of_eval hStmt, Outcome.leave,
          Bind.bind, Except.bind]
    | cons_halt hStmt =>
        simp [Block.run, Stmt.run_of_eval hStmt, Outcome.halt,
          Bind.bind, Except.bind]

  theorem Stmt.run_of_eval
      {σ : Type} {model : StateModel σ} {handler : Handler σ}
      {program : Program} {fuel : Nat}
      {stmt : Stmt} {state : σ} {outcome : OutcomeT σ}
      (hEval :
        Stmt.Eval model handler program fuel stmt state outcome) :
      Stmt.run model handler program fuel stmt state = .ok outcome := by
    cases hEval with
    | code hCode =>
        simp [Stmt.run, hCode, Outcome.regular, Bind.bind, Except.bind]
    | if_false hCond =>
        simp [Stmt.run, hCond, Outcome.regular, Bind.bind, Except.bind]
    | if_true hCond hBody =>
        simp [Stmt.run, hCond, Block.run_of_eval hBody,
          Bind.bind, Except.bind]
    | switch_none hScrutinee hPop hSelect =>
        simp [Stmt.run, hScrutinee, hPop, hSelect, Outcome.regular,
          Bind.bind, Except.bind]
    | switch_some hScrutinee hPop hStateAfterPop hSelect hBody =>
        subst hStateAfterPop
        simp [Stmt.run, hScrutinee, hPop, hSelect,
          Block.run_of_eval hBody, Bind.bind, Except.bind]
    | for_init_regular hInit hLoop =>
        simp [Stmt.run, Block.run_of_eval hInit,
          For.run_of_eval hLoop, Outcome.regular, Bind.bind, Except.bind]
    | for_init_leave hInit =>
        simp [Stmt.run, Block.run_of_eval hInit, Outcome.leave,
          Bind.bind, Except.bind]
    | for_init_halt hInit =>
        simp [Stmt.run, Block.run_of_eval hInit, Outcome.halt,
          Bind.bind, Except.bind]
    | brk =>
        simp [Stmt.run, Outcome.brk]
    | cont =>
        simp [Stmt.run, Outcome.cont]
    | leave hReturns =>
        cases hReturnStack : model.returns state with
        | nil =>
            exact False.elim (hReturns hReturnStack)
        | cons head tail =>
            simp [Stmt.run, hReturnStack, Outcome.leave]
    | call_regular hLookup hSplit hBody hPop hAttach =>
        simp [Stmt.run, hLookup, hSplit, Block.run_of_eval hBody,
          hPop, hAttach, Outcome.regular, Bind.bind, Except.bind]
    | call_leave hLookup hSplit hBody hPop hAttach =>
        simp [Stmt.run, hLookup, hSplit, Block.run_of_eval hBody,
          hPop, hAttach, Outcome.leave, Outcome.regular,
          Bind.bind, Except.bind]
    | call_halt hLookup hSplit hBody =>
        simp [Stmt.run, hLookup, hSplit, Block.run_of_eval hBody,
          Outcome.halt, Bind.bind, Except.bind]
    | terminal hStep =>
        simp [Stmt.run, hStep, Outcome.halt, Bind.bind, Except.bind]

  theorem For.run_of_eval
      {σ : Type} {model : StateModel σ} {handler : Handler σ}
      {program : Program} {fuel : Nat}
      {cond : Code} {post body : Block}
      {state : σ} {outcome : OutcomeT σ}
      (hEval :
        For.Eval model handler program fuel cond post body state outcome) :
      Stmt.runForLoop model handler program fuel cond post body state =
        .ok outcome := by
    cases hEval with
    | false hCond =>
        simp [Stmt.runForLoop, hCond, Outcome.regular,
          Bind.bind, Except.bind]
    | body_brk hCond hBody =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Outcome.brk, Outcome.regular, Bind.bind, Except.bind]
    | body_leave hCond hBody =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Outcome.leave, Bind.bind, Except.bind]
    | body_halt hCond hBody =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Outcome.halt, Bind.bind, Except.bind]
    | regular_post_regular hCond hBody hPost hLoop =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Block.run_of_eval hPost, For.run_of_eval hLoop,
          Outcome.regular, Bind.bind, Except.bind]
    | cont_post_regular hCond hBody hPost hLoop =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Block.run_of_eval hPost, For.run_of_eval hLoop,
          Outcome.cont, Outcome.regular, Bind.bind, Except.bind]
    | regular_post_leave hCond hBody hPost =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Block.run_of_eval hPost, Outcome.regular, Outcome.leave,
          Bind.bind, Except.bind]
    | cont_post_leave hCond hBody hPost =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Block.run_of_eval hPost, Outcome.cont, Outcome.leave,
          Bind.bind, Except.bind]
    | regular_post_halt hCond hBody hPost =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Block.run_of_eval hPost, Outcome.regular, Outcome.halt,
          Bind.bind, Except.bind]
    | cont_post_halt hCond hBody hPost =>
        simp [Stmt.runForLoop, hCond, Block.run_of_eval hBody,
          Block.run_of_eval hPost, Outcome.cont, Outcome.halt,
          Bind.bind, Except.bind]
end

/--
Structured block evaluation determines one outcome independently of the chosen
sufficient fuel bound.
-/
theorem Block.Eval.outcome_unique
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program} {leftFuel rightFuel : Nat}
    {block : Block} {state : σ} {leftOutcome rightOutcome : OutcomeT σ}
    (hLeft :
      Block.Eval model handler program leftFuel block state leftOutcome)
    (hRight :
      Block.Eval model handler program rightFuel block state rightOutcome) :
    leftOutcome = rightOutcome := by
  have hLeftRun :=
    Block.run_of_eval
      (hLeft.mono (Nat.le_max_left leftFuel rightFuel))
  have hRightRun :=
    Block.run_of_eval
      (hRight.mono (Nat.le_max_right leftFuel rightFuel))
  rw [hLeftRun] at hRightRun
  exact Except.ok.inj hRightRun

/--
Structured statement evaluation determines one outcome independently of the
chosen sufficient fuel bound.
-/
theorem Stmt.Eval.outcome_unique
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program} {leftFuel rightFuel : Nat}
    {stmt : Stmt} {state : σ} {leftOutcome rightOutcome : OutcomeT σ}
    (hLeft :
      Stmt.Eval model handler program leftFuel stmt state leftOutcome)
    (hRight :
      Stmt.Eval model handler program rightFuel stmt state rightOutcome) :
    leftOutcome = rightOutcome := by
  have hLeftRun :=
    Stmt.run_of_eval
      (hLeft.mono (Nat.le_max_left leftFuel rightFuel))
  have hRightRun :=
    Stmt.run_of_eval
      (hRight.mono (Nat.le_max_right leftFuel rightFuel))
  rw [hLeftRun] at hRightRun
  exact Except.ok.inj hRightRun

/--
Structured loop evaluation determines one outcome independently of the chosen
sufficient fuel bound.
-/
theorem For.Eval.outcome_unique
    {σ : Type} {model : StateModel σ} {handler : Handler σ}
    {program : Program} {leftFuel rightFuel : Nat}
    {cond : Code} {post body : Block}
    {state : σ} {leftOutcome rightOutcome : OutcomeT σ}
    (hLeft :
      For.Eval model handler program leftFuel cond post body state leftOutcome)
    (hRight :
      For.Eval model handler program rightFuel cond post body state
        rightOutcome) :
    leftOutcome = rightOutcome := by
  have hLeftRun :=
    For.run_of_eval
      (hLeft.mono (Nat.le_max_left leftFuel rightFuel))
  have hRightRun :=
    For.run_of_eval
      (hRight.mono (Nat.le_max_right leftFuel rightFuel))
  rw [hLeftRun] at hRightRun
  exact Except.ok.inj hRightRun

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
                rw [Block.run_cons] at hRun
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
        rw [Stmt.run_code] at hRun
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
            rw [Stmt.run_if_succ] at hRun
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
            rw [Stmt.run_switch_succ] at hRun
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
            rw [Stmt.run_for_succ] at hRun
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
        rw [Stmt.run_brk] at hRun
        cases hRun
        exact Stmt.Eval.brk
    | cont =>
        rw [Stmt.run_cont] at hRun
        cases hRun
        exact Stmt.Eval.cont
    | leave =>
        rw [Stmt.run_leave] at hRun
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
            rw [Stmt.run_call_succ] at hRun
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
        rw [Stmt.run_terminal] at hRun
        cases hStep : Terminal.step kind (model.evm state) with
        | error err =>
            simp [hStep] at hRun
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
        rw [Stmt.runForLoop_succ] at hRun
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
  change
    (run Ordinary.runStateModel Ordinary.handler code state).bind
        (popCondition Ordinary.runStateModel) =
      ((run Ordinary.evmStateModel Ordinary.handler code state.evm).bind
          (popCondition Ordinary.evmStateModel)).bind
        (fun result => .ok (state.withEVM result.1, result.2))
  rw [ordinary_state_run, ordinary_evm_run]
  unfold Structured.Code.runState
  cases hRun : Structured.Code.run code state.evm with
  | error err =>
      simp [hRun, Bind.bind, Except.bind]
  | ok evm =>
      simp [hRun, Bind.bind, Except.bind]
      cases hPop : evm.stack.pop with
      | none =>
          simp [popCondition, Control.Code.popCondition,
            Structured.Code.popCondition,
            Ordinary.evmStateModel_evm,
            Ordinary.runStateModel_evm, hPop]
      | some pair =>
          rcases pair with ⟨stack, value⟩
          simp [popCondition, Control.Code.popCondition,
            Structured.Code.popCondition,
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
