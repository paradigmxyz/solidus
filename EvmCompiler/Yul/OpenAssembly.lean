import EvmCompiler.Core.Except
import EvmCompiler.Yul.OpenExternal
import EvmCompiler.Assembly.Accepted
import EvmCompiler.Assembly.Preservation
import EvmCompiler.Assembly.Semantics

/-!
Open external-call adapters for the gasless Assembly/EVM target layer.

The source-side CALL proof already uses `OpenExternal` at the compiler-source
primitive boundary.  This file starts the corresponding target-side vocabulary
without changing the closed Assembly interpreter: non-CALL primitives embed as
closed results, while CALL-family primitives suspend at the abstract external
request extracted from the EVM state.
-/

namespace EvmCompiler
namespace Yul
namespace OpenAssembly

attribute [local simp] OpenExternal.OpenResult.bind_call

abbrev EVMState := EvmYul.EVM.State
abbrev EVMException := EvmYul.EVM.ExecutionException

def evmCallResult (call : OpenExternal.OpenCall EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  .call
    { site := call.site
      resume := fun response => .done (.ok (call.resume response)) }

def evmCreateResult (create : OpenExternal.OpenCreate EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  .create
    { site := create.site
      resume := fun response => .done (.ok (create.resume response)) }

theorem evmCallResult_resolves
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (evmCallResult call)
      [{ site := call.site, response := response }]
      (.ok (call.resume response)) := by
  unfold evmCallResult
  exact OpenExternal.OpenResultResolves.call
    OpenExternal.OpenResultResolves.done

theorem evmCreateResult_resolves
    (create : OpenExternal.OpenCreate EVMState)
    (response : OpenExternal.CreateResponse) :
    OpenExternal.OpenResultResolves (evmCreateResult create)
      [OpenExternal.OpenEvent.create create.site response]
      (.ok (create.resume response)) := by
  unfold evmCreateResult
  exact OpenExternal.OpenResultResolves.create
    OpenExternal.OpenResultResolves.done

def evmInstructionCallResult (call : OpenExternal.OpenCall EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  .call
    { site := call.site
      resume := fun response =>
        .done (.ok (EvmYul.EVM.State.incrPC (call.resume response))) }

def evmInstructionCreateResult (create : OpenExternal.OpenCreate EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  .create
    { site := create.site
      resume := fun response =>
        .done (.ok (EvmYul.EVM.State.incrPC (create.resume response))) }

theorem evmInstructionCallResult_resolves
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (evmInstructionCallResult call)
      [{ site := call.site, response := response }]
      (.ok (EvmYul.EVM.State.incrPC (call.resume response))) := by
  unfold evmInstructionCallResult
  exact OpenExternal.OpenResultResolves.call
    OpenExternal.OpenResultResolves.done

theorem evmInstructionCreateResult_resolves
    (create : OpenExternal.OpenCreate EVMState)
    (response : OpenExternal.CreateResponse) :
    OpenExternal.OpenResultResolves (evmInstructionCreateResult create)
      [OpenExternal.OpenEvent.create create.site response]
      (.ok (EvmYul.EVM.State.incrPC (create.resume response))) := by
  unfold evmInstructionCreateResult
  exact OpenExternal.OpenResultResolves.create
    OpenExternal.OpenResultResolves.done

namespace PrimOp

def openStep (op : Assembly.PrimOp) (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match OpenExternal.CallKind.ofEVMOperation? op.toEVM with
  | some kind =>
      match OpenExternal.CallKind.evmOpenCall? state kind with
      | some call => evmCallResult call
      | none => .done (.error EvmYul.EVM.ExecutionException.StackUnderflow)
  | none =>
      match OpenExternal.CreateKind.ofEVMOperation? op.toEVM with
      | some kind =>
          match OpenExternal.CreateKind.evmOpenCreate? state kind with
          | some create => evmCreateResult create
          | none => .done (.error EvmYul.EVM.ExecutionException.StackUnderflow)
      | none => .done (op.step state)

theorem openStep_of_not_call_or_createKind
    {op : Assembly.PrimOp} {state : EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hCreateKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = none) :
    openStep op state = .done (op.step state) := by
  simp [openStep, hCallKind, hCreateKind]

theorem openStep_of_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call) :
    openStep op state = evmCallResult call := by
  simp [openStep, hKind, hCall]

theorem openStep_of_callKind_no_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none) :
    openStep op state =
      .done (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  simp [openStep, hKind, hCall]

theorem openStep_of_create
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CreateKind}
    {create : OpenExternal.OpenCreate EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind)
    (hCreate : OpenExternal.CreateKind.evmOpenCreate? state kind = some create) :
    openStep op state = evmCreateResult create := by
  simp [openStep, hCallKind, hKind, hCreate]

theorem openStep_of_createKind_no_create
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CreateKind}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind)
    (hCreate : OpenExternal.CreateKind.evmOpenCreate? state kind = none) :
    openStep op state =
      .done (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  simp [openStep, hCallKind, hKind, hCreate]

theorem openStep_resolves_closed_of_not_call_or_createKind
    {op : Assembly.PrimOp} {state state' : EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hCreateKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = none)
    (hStep : op.step state = .ok state') :
    OpenExternal.OpenResultResolves (openStep op state) [] (.ok state') := by
  rw [openStep_of_not_call_or_createKind hCallKind hCreateKind, hStep]
  exact OpenExternal.OpenResultResolves.done

theorem openStep_resolves_error_of_callKind_no_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none) :
    OpenExternal.OpenResultResolves (openStep op state) []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  rw [openStep_of_callKind_no_call hKind hCall]
  exact OpenExternal.OpenResultResolves.done

theorem openStep_resolves_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStep op state)
      [{ site := call.site, response := response }]
      (.ok (call.resume response)) := by
  rw [openStep_of_call hKind hCall]
  exact evmCallResult_resolves call response

theorem openStep_resolves_create
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CreateKind}
    {create : OpenExternal.OpenCreate EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind)
    (hCreate : OpenExternal.CreateKind.evmOpenCreate? state kind = some create)
    (response : OpenExternal.CreateResponse) :
    OpenExternal.OpenResultResolves (openStep op state)
      [OpenExternal.OpenEvent.create create.site response]
      (.ok (create.resume response)) := by
  rw [openStep_of_create hCallKind hKind hCreate]
  exact evmCreateResult_resolves create response

end PrimOp

namespace Target

def instrUsesCallCreate : Assembly.TargetInstr → Bool
  | .prim op => op.isCallCreate
  | _ => false

def codeUsesCallCreate (code : List Assembly.TargetInstr) : Bool :=
  code.any instrUsesCallCreate

theorem codeUsesCallCreate_false_of_emitInstr_no_call
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitInstr? program pc instr = some emitted) :
    codeUsesCallCreate (emitted.map Assembly.LocatedTarget.instr) = false := by
  cases instr with
  | label name =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      simp [codeUsesCallCreate, instrUsesCallCreate]
  | prim op =>
      simp [Assembly.emitInstr?, Assembly.Instr.usesCallCreate] at hEmit hNoInstr
      subst emitted
      simp [codeUsesCallCreate, instrUsesCallCreate, hNoInstr]
  | push value =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      simp [codeUsesCallCreate, instrUsesCallCreate]
  | jump target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.emitInstr?, hDest] at hEmit
          subst emitted
          simp [codeUsesCallCreate, instrUsesCallCreate]
  | jumpi target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.emitInstr?, hDest] at hEmit
          subst emitted
          simp [codeUsesCallCreate, instrUsesCallCreate]

def openStepInstr (instr : Assembly.TargetInstr) (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match instr with
  | .prim op =>
      match OpenExternal.CallKind.ofEVMOperation? op.toEVM with
      | some kind =>
          match OpenExternal.CallKind.evmOpenCall? state kind with
          | some call => evmInstructionCallResult call
          | none => .done (.error EvmYul.EVM.ExecutionException.StackUnderflow)
      | none =>
          match OpenExternal.CreateKind.ofEVMOperation? op.toEVM with
          | some kind =>
              match OpenExternal.CreateKind.evmOpenCreate? state kind with
              | some create => evmInstructionCreateResult create
              | none =>
                  .done (.error EvmYul.EVM.ExecutionException.StackUnderflow)
          | none => .done (Assembly.Target.stepInstr instr state)
  | _ => .done (Assembly.Target.stepInstr instr state)

theorem openStepInstr_of_non_prim
    {instr : Assembly.TargetInstr} {state : EVMState}
    (hInstr : ∀ op, instr ≠ .prim op) :
    openStepInstr instr state = .done (Assembly.Target.stepInstr instr state) := by
  cases instr <;> simp [openStepInstr]
  exact False.elim (hInstr _ rfl)

theorem openStepInstr_of_prim_not_call_or_createKind
    {op : Assembly.PrimOp} {state : EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hCreateKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = none) :
    openStepInstr (.prim op) state =
      .done (Assembly.Target.stepInstr (.prim op) state) := by
  simp [openStepInstr, hCallKind, hCreateKind]

theorem openStepInstr_of_prim_callKind_no_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none) :
    openStepInstr (.prim op) state =
      .done (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  simp [openStepInstr, hKind, hCall]

theorem openStepInstr_of_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call) :
    openStepInstr (.prim op) state = evmInstructionCallResult call := by
  simp [openStepInstr, hKind, hCall]

theorem openStepInstr_of_prim_createKind_no_create
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CreateKind}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind)
    (hCreate : OpenExternal.CreateKind.evmOpenCreate? state kind = none) :
    openStepInstr (.prim op) state =
      .done (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  simp [openStepInstr, hCallKind, hKind, hCreate]

theorem openStepInstr_of_prim_create
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CreateKind}
    {create : OpenExternal.OpenCreate EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind)
    (hCreate : OpenExternal.CreateKind.evmOpenCreate? state kind = some create) :
    openStepInstr (.prim op) state = evmInstructionCreateResult create := by
  simp [openStepInstr, hCallKind, hKind, hCreate]

theorem openStepInstr_resolves_closed_of_prim_not_call_or_createKind
    {op : Assembly.PrimOp} {state state' : EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hCreateKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = none)
    (hStep : Assembly.Target.stepInstr (.prim op) state = .ok state') :
    OpenExternal.OpenResultResolves
      (openStepInstr (.prim op) state) [] (.ok state') := by
  rw [openStepInstr_of_prim_not_call_or_createKind hCallKind hCreateKind,
    hStep]
  exact OpenExternal.OpenResultResolves.done

theorem openStepInstr_resolves_error_of_prim_callKind_no_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none) :
    OpenExternal.OpenResultResolves
      (openStepInstr (.prim op) state) []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  rw [openStepInstr_of_prim_callKind_no_call hKind hCall]
  exact OpenExternal.OpenResultResolves.done

theorem openStepInstr_resolves_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepInstr (.prim op) state)
      [{ site := call.site, response := response }]
      (.ok (EvmYul.EVM.State.incrPC (call.resume response))) := by
  rw [openStepInstr_of_prim_call hKind hCall]
  exact evmInstructionCallResult_resolves call response

theorem openStepInstr_resolves_prim_create
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CreateKind}
    {create : OpenExternal.OpenCreate EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind)
    (hCreate : OpenExternal.CreateKind.evmOpenCreate? state kind = some create)
    (response : OpenExternal.CreateResponse) :
    OpenExternal.OpenResultResolves (openStepInstr (.prim op) state)
      [OpenExternal.OpenEvent.create create.site response]
      (.ok (EvmYul.EVM.State.incrPC (create.resume response))) := by
  rw [openStepInstr_of_prim_create hCallKind hKind hCreate]
  exact evmInstructionCreateResult_resolves create response

theorem prim_haltKind?_none_of_callKind
    {op : Assembly.PrimOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind) :
    op.haltKind? = none := by
  cases op <;>
    simp [Assembly.PrimOp.toEVM, OpenExternal.CallKind.ofEVMOperation?,
      Assembly.PrimOp.haltKind?] at hKind ⊢

theorem prim_haltKind?_none_of_createKind
    {op : Assembly.PrimOp} {kind : OpenExternal.CreateKind}
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind) :
    op.haltKind? = none := by
  cases op <;>
    simp [Assembly.PrimOp.toEVM, OpenExternal.CreateKind.ofEVMOperation?,
      Assembly.PrimOp.haltKind?] at hKind ⊢

theorem callKind_none_of_not_isCallCreate
    {op : Assembly.PrimOp} (hNo : op.isCallCreate = false) :
    OpenExternal.CallKind.ofEVMOperation? op.toEVM = none := by
  cases op <;>
    simp [Assembly.PrimOp.isCallCreate, Assembly.PrimOp.toEVM,
      OpenExternal.CallKind.ofEVMOperation?] at hNo ⊢

theorem createKind_none_of_not_isCallCreate
    {op : Assembly.PrimOp} (hNo : op.isCallCreate = false) :
    OpenExternal.CreateKind.ofEVMOperation? op.toEVM = none := by
  cases op <;>
    simp [Assembly.PrimOp.isCallCreate, Assembly.PrimOp.toEVM,
      OpenExternal.CreateKind.ofEVMOperation?] at hNo ⊢

def stepResultAfter (instr : Assembly.TargetInstr) (state : EVMState) :
    Assembly.StepResult :=
  match instr.haltKind? with
  | some kind =>
      .halted { kind := kind, state := state, output := kind.output state }
  | none =>
      .running state

def openStepInstrResult (instr : Assembly.TargetInstr) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  OpenExternal.OpenResult.bind (openStepInstr instr state)
    (fun state' => .done (.ok (stepResultAfter instr state')))

theorem openStepInstr_of_no_callCreate
    {instr : Assembly.TargetInstr} {state : EVMState}
    (hNo : instrUsesCallCreate instr = false) :
    openStepInstr instr state = .done (Assembly.Target.stepInstr instr state) := by
  cases instr with
  | prim op =>
      simp [instrUsesCallCreate] at hNo
      have hCallKind := callKind_none_of_not_isCallCreate hNo
      have hCreateKind := createKind_none_of_not_isCallCreate hNo
      simp [openStepInstr, hCallKind, hCreateKind]
  | push32 value =>
      simp [openStepInstr]
  | jump =>
      simp [openStepInstr]
  | jumpi =>
      simp [openStepInstr]
  | jumpdest =>
      simp [openStepInstr]

theorem openStepInstrResult_resolves_closed_of_openStepInstr_done
    {instr : Assembly.TargetInstr} {state : EVMState}
    {result : Assembly.StepResult}
    (hOpen :
      openStepInstr instr state = .done (Assembly.Target.stepInstr instr state))
    (hStep : Assembly.Target.stepInstrResult instr state = .ok result) :
    OpenExternal.OpenResultResolves
      (openStepInstrResult instr state) [] (.ok result) := by
  unfold openStepInstrResult
  rw [hOpen]
  unfold Assembly.Target.stepInstrResult at hStep
  cases hRaw : Assembly.Target.stepInstr instr state with
  | error err =>
      rw [hRaw] at hStep
      cases hStep
  | ok state' =>
      rw [hRaw] at hStep
      have hResult : stepResultAfter instr state' = result := by
        cases hKind : instr.haltKind? with
        | none =>
            simpa [stepResultAfter, hKind] using hStep
        | some kind =>
            simpa [stepResultAfter, hKind] using hStep
      simpa [hResult] using
        (OpenExternal.OpenResultResolves.done :
          OpenExternal.OpenResultResolves
            ((.done (.ok result)) :
              OpenExternal.OpenResult EVMException Assembly.StepResult)
            [] (.ok result))

theorem openStepInstrResult_resolves_closed_of_no_callCreate
    {instr : Assembly.TargetInstr} {state : EVMState}
    {result : Assembly.StepResult}
    (hNo : instrUsesCallCreate instr = false)
    (hStep : Assembly.Target.stepInstrResult instr state = .ok result) :
    OpenExternal.OpenResultResolves
      (openStepInstrResult instr state) [] (.ok result) := by
  exact
    openStepInstrResult_resolves_closed_of_openStepInstr_done
      (openStepInstr_of_no_callCreate hNo) hStep

theorem openStepInstrResult_resolves_closed_inv_of_no_callCreate
    {instr : Assembly.TargetInstr} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hNo : instrUsesCallCreate instr = false)
    (hResolve :
      OpenExternal.OpenResultResolves
        (openStepInstrResult instr state) trace (.ok result)) :
    trace = [] ∧
      Assembly.Target.stepInstrResult instr state = .ok result := by
  have hOpen := openStepInstr_of_no_callCreate (state := state) hNo
  unfold openStepInstrResult at hResolve
  rw [hOpen] at hResolve
  cases hStep : Assembly.Target.stepInstr instr state with
  | error err =>
      rw [hStep] at hResolve
      change
        OpenExternal.OpenResultResolves
          ((.done (.error err)) :
            OpenExternal.OpenResult EVMException Assembly.StepResult)
          trace (.ok result) at hResolve
      cases hResolve
  | ok state' =>
      rw [hStep] at hResolve
      change
        OpenExternal.OpenResultResolves
          ((.done (.ok (stepResultAfter instr state'))) :
            OpenExternal.OpenResult EVMException Assembly.StepResult)
          trace (.ok result) at hResolve
      cases hResolve
      exact
        ⟨rfl,
          by
            unfold Assembly.Target.stepInstrResult stepResultAfter
            rw [hStep]
            cases instr.haltKind? <;> rfl⟩

theorem openStepInstrResult_resolves_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepInstrResult (.prim op) state)
      [{ site := call.site, response := response }]
    (.ok (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  unfold openStepInstrResult
  rw [openStepInstr_of_prim_call hKind hCall]
  unfold evmInstructionCallResult
  have hHalt : (Assembly.TargetInstr.prim op).haltKind? = none := by
    simpa [Assembly.TargetInstr.haltKind?] using
      prim_haltKind?_none_of_callKind hKind
  refine OpenExternal.OpenResultResolves.call ?_
  simpa [stepResultAfter, hHalt] using
    (OpenExternal.OpenResultResolves.done :
      OpenExternal.OpenResultResolves
        (.done
          (.ok
            (Assembly.StepResult.running
              (EvmYul.EVM.State.incrPC (call.resume response)))))
        []
        (.ok
          (Assembly.StepResult.running
            (EvmYul.EVM.State.incrPC (call.resume response)))))

theorem openStepInstrResult_resolves_prim_create
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CreateKind}
    {create : OpenExternal.OpenCreate EVMState}
    (hCallKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hKind : OpenExternal.CreateKind.ofEVMOperation? op.toEVM = some kind)
    (hCreate : OpenExternal.CreateKind.evmOpenCreate? state kind = some create)
    (response : OpenExternal.CreateResponse) :
    OpenExternal.OpenResultResolves (openStepInstrResult (.prim op) state)
      [OpenExternal.OpenEvent.create create.site response]
    (.ok (.running (EvmYul.EVM.State.incrPC (create.resume response)))) := by
  unfold openStepInstrResult
  rw [openStepInstr_of_prim_create hCallKind hKind hCreate]
  unfold evmInstructionCreateResult
  have hHalt : (Assembly.TargetInstr.prim op).haltKind? = none := by
    simpa [Assembly.TargetInstr.haltKind?] using
      prim_haltKind?_none_of_createKind hKind
  refine OpenExternal.OpenResultResolves.create ?_
  simpa [stepResultAfter, hHalt] using
    (OpenExternal.OpenResultResolves.done :
      OpenExternal.OpenResultResolves
        (.done
          (.ok
            (Assembly.StepResult.running
              (EvmYul.EVM.State.incrPC (create.resume response)))))
        []
        (.ok
          (Assembly.StepResult.running
            (EvmYul.EVM.State.incrPC (create.resume response)))))

def openRunListResult : List Assembly.TargetInstr → EVMState →
    OpenExternal.OpenResult EVMException Assembly.StepResult
  | [], state => .done (.ok (.running state))
  | instr :: rest, state =>
      OpenExternal.OpenResult.bind (openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' => openRunListResult rest state'
          | .halted halt => .done (.ok (.halted halt)))

theorem openRunListResult_nil (state : EVMState) :
    openRunListResult [] state = .done (.ok (.running state)) := by
  rfl

theorem openRunListResult_cons
    (instr : Assembly.TargetInstr) (rest : List Assembly.TargetInstr)
    (state : EVMState) :
    openRunListResult (instr :: rest) state =
      OpenExternal.OpenResult.bind (openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' => openRunListResult rest state'
          | .halted halt => .done (.ok (.halted halt))) := by
  rfl

theorem all_false_of_codeUsesCallCreate_false
    {code : List Assembly.TargetInstr}
    (hCode : codeUsesCallCreate code = false) :
    ∀ instr ∈ code, instrUsesCallCreate instr = false := by
  simpa [codeUsesCallCreate] using hCode

theorem openRunListResult_resolves_closed_of_forall_no_callCreate :
    ∀ {code : List Assembly.TargetInstr} {state : EVMState}
      {result : Assembly.StepResult},
      (∀ instr ∈ code, instrUsesCallCreate instr = false) →
      Assembly.Target.runListResult code state = .ok result →
      OpenExternal.OpenResultResolves (openRunListResult code state)
        [] (.ok result) := by
  intro code
  induction code with
  | nil =>
      intro state result _hNo hRun
      simp [Assembly.Target.runListResult] at hRun
      subst result
      exact OpenExternal.OpenResultResolves.done
  | cons instr rest ih =>
      intro state result hNo hRun
      have hInstrNo : instrUsesCallCreate instr = false := hNo instr (by simp)
      have hRestNo :
          ∀ restInstr ∈ rest, instrUsesCallCreate restInstr = false := by
        intro restInstr hMem
        exact hNo restInstr (by simp [hMem])
      rw [openRunListResult_cons]
      cases hStep : Assembly.Target.stepInstrResult instr state with
      | error err =>
          rw [Assembly.Target.runListResult, hStep] at hRun
          cases hRun
      | ok stepResult =>
          rw [Assembly.Target.runListResult, hStep] at hRun
          have hOpenStep :=
            openStepInstrResult_resolves_closed_of_no_callCreate
              hInstrNo hStep
          cases stepResult with
          | running mid =>
              have hRest := ih hRestNo hRun
              simpa using
                OpenExternal.OpenResultResolves.bind_ok
                  hOpenStep hRest
          | halted halt =>
              cases hRun
              have hDone :
                  OpenExternal.OpenResultResolves
                    ((.done (.ok (Assembly.StepResult.halted halt))) :
                      OpenExternal.OpenResult EVMException Assembly.StepResult)
                    [] (.ok (Assembly.StepResult.halted halt)) :=
                OpenExternal.OpenResultResolves.done
              simpa using
                OpenExternal.OpenResultResolves.bind_ok
                  hOpenStep hDone

theorem openRunListResult_resolves_closed_of_no_callCreate
    {code : List Assembly.TargetInstr} {state : EVMState}
    {result : Assembly.StepResult}
    (hCode : codeUsesCallCreate code = false)
    (hRun : Assembly.Target.runListResult code state = .ok result) :
    OpenExternal.OpenResultResolves (openRunListResult code state)
      [] (.ok result) := by
  exact
    openRunListResult_resolves_closed_of_forall_no_callCreate
      (all_false_of_codeUsesCallCreate_false hCode) hRun

theorem openRunListResult_resolves_closed_inv_of_forall_no_callCreate :
    ∀ {code : List Assembly.TargetInstr} {state : EVMState}
      {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult},
      (∀ instr ∈ code, instrUsesCallCreate instr = false) →
      OpenExternal.OpenResultResolves (openRunListResult code state)
        trace (.ok result) →
      trace = [] ∧ Assembly.Target.runListResult code state = .ok result := by
  intro code
  induction code with
  | nil =>
      intro state trace result _hNo hResolve
      simp [openRunListResult_nil] at hResolve
      cases hResolve
      exact ⟨rfl, rfl⟩
  | cons instr rest ih =>
      intro state trace result hNo hResolve
      have hInstrNo : instrUsesCallCreate instr = false :=
        hNo instr (by simp)
      have hRestNo :
          ∀ restInstr ∈ rest, instrUsesCallCreate restInstr = false := by
        intro restInstr hMem
        exact hNo restInstr (by simp [hMem])
      rw [openRunListResult_cons] at hResolve
      rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
        hError | hOk
      · rcases hError with ⟨err, _hStepErr, hResult⟩
        cases hResult
      · rcases hOk with
          ⟨left, right, stepResult, hTrace, hStep, hRest⟩
        have hStepClosed :=
          openStepInstrResult_resolves_closed_inv_of_no_callCreate
            hInstrNo hStep
        rcases hStepClosed with ⟨hLeft, hStepTarget⟩
        subst left
        cases stepResult with
        | running mid =>
            have hRestClosed := ih hRestNo hRest
            rcases hRestClosed with ⟨hRight, hRunRest⟩
            subst right
            constructor
            · simpa using hTrace
            · rw [Assembly.Target.runListResult, hStepTarget]
              exact hRunRest
        | halted halt =>
            simp at hRest
            cases hRest
            constructor
            · simpa using hTrace
            · rw [Assembly.Target.runListResult, hStepTarget]
              rfl

theorem openRunListResult_resolves_closed_inv_of_no_callCreate
    {code : List Assembly.TargetInstr} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hCode : codeUsesCallCreate code = false)
    (hResolve :
      OpenExternal.OpenResultResolves (openRunListResult code state)
        trace (.ok result)) :
    trace = [] ∧ Assembly.Target.runListResult code state = .ok result :=
  openRunListResult_resolves_closed_inv_of_forall_no_callCreate
    (all_false_of_codeUsesCallCreate_false hCode) hResolve

theorem openRunListResult_single_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves
      (openRunListResult [Assembly.TargetInstr.prim op] state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  rw [openRunListResult_cons]
  have hStep :=
    openStepInstrResult_resolves_prim_call hKind hCall response
  have hRest :
      OpenExternal.OpenResultResolves
        (openRunListResult []
          (EvmYul.EVM.State.incrPC (call.resume response)))
        []
        (.ok
          (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
    exact OpenExternal.OpenResultResolves.done
  simpa [openRunListResult_nil] using
    OpenExternal.OpenResultResolves.bind_ok hStep hRest

theorem openRunListResult_emitInstr_prim_call
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {emitted : List Assembly.LocatedTarget} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEmit : Assembly.emitInstr? program pc (.prim op) = some emitted)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves
      (openRunListResult (emitted.map Assembly.LocatedTarget.instr) state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  simp [Assembly.emitInstr?] at hEmit
  subst emitted
  simpa using openRunListResult_single_prim_call hKind hCall response

universe u v

theorem openResultResolves_done_inv
    {ε : Type u} {α : Type v}
    {result result' : Except ε α} {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        ((.done result) : OpenExternal.OpenResult ε α) trace result') :
    trace = [] ∧ result = result' := by
  cases hResolve
  exact ⟨rfl, rfl⟩

theorem openStepInstrResult_resolves_halted_haltKind?_some
    {instr : Assembly.TargetInstr} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    (hResolve :
      OpenExternal.OpenResultResolves (openStepInstrResult instr state)
        trace (.ok (.halted halt))) :
    ∃ kind : Assembly.HaltKind, instr.haltKind? = some kind := by
  unfold openStepInstrResult at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with hErr | hOk
  · rcases hErr with ⟨err, _hStepErr, hResult⟩
    cases hResult
  · rcases hOk with
      ⟨left, right, stateAfter, _hTrace, _hStep, hNext⟩
    change
      OpenExternal.OpenResultResolves
        ((.done (.ok (stepResultAfter instr stateAfter))) :
          OpenExternal.OpenResult EVMException Assembly.StepResult)
        right (.ok (.halted halt)) at hNext
    rcases openResultResolves_done_inv hNext with ⟨_hRight, hStepAfterOk⟩
    injection hStepAfterOk with hStepAfter
    unfold stepResultAfter at hStepAfter
    cases hKind : instr.haltKind? with
    | none =>
        simp [hKind] at hStepAfter
    | some kind =>
        exact ⟨kind, rfl⟩

theorem openRunListResult_emitInstr_halted_no_callCreate
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (openRunListResult (emitted.map Assembly.LocatedTarget.instr) state)
        trace (.ok (.halted halt))) :
    Assembly.Instr.usesCallCreate instr = false := by
  cases instr with
  | label name =>
      simp [Assembly.Instr.usesCallCreate]
  | prim op =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      change
        OpenExternal.OpenResultResolves
          (openRunListResult [Assembly.TargetInstr.prim op] state)
          trace (.ok (.halted halt)) at hRun
      rw [openRunListResult_cons] at hRun
      rcases OpenExternal.OpenResultResolves.bind_inv hRun with hErr | hOk
      · rcases hErr with ⟨err, _hStepErr, hResult⟩
        cases hResult
      · rcases hOk with
          ⟨left, right, stepResult, _hTrace, hStep, hRest⟩
        cases stepResult with
        | running mid =>
            change
              OpenExternal.OpenResultResolves
                ((.done (.ok (Assembly.StepResult.running mid))) :
                  OpenExternal.OpenResult EVMException Assembly.StepResult)
                right (.ok (.halted halt)) at hRest
            rcases openResultResolves_done_inv hRest with ⟨_hRight, hStepResult⟩
            cases hStepResult
        | halted halt' =>
            rcases
                openStepInstrResult_resolves_halted_haltKind?_some hStep with
              ⟨kind, hKind⟩
            cases op <;>
              simp [Assembly.Instr.usesCallCreate,
                Assembly.PrimOp.isCallCreate,
                Assembly.TargetInstr.haltKind?,
                Assembly.PrimOp.haltKind?] at hKind ⊢
  | push value =>
      simp [Assembly.Instr.usesCallCreate]
  | jump target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.Instr.usesCallCreate]
  | jumpi target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.Instr.usesCallCreate]

def openStep (target : Assembly.TargetProgram) (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match target.fetch state.pc.toNat with
  | some instr => openStepInstr instr state
  | none => .done (.error .InvalidInstruction)

def openStepResult (target : Assembly.TargetProgram) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  match target.fetch state.pc.toNat with
  | some instr => openStepInstrResult instr state
  | none => .done (.error .InvalidInstruction)

def openRunNResult (target : Assembly.TargetProgram) :
    Nat → EVMState → OpenExternal.OpenResult EVMException Assembly.StepResult
  | 0, state => .done (.ok (.running state))
  | fuel + 1, state =>
      OpenExternal.OpenResult.bind (openStepResult target state)
        (fun result =>
          match result with
          | .running state' => openRunNResult target fuel state'
          | .halted halt => .done (.ok (.halted halt)))

end Target

namespace Source

theorem instr_usesCallCreate_false_of_instrAtPcFrom
    {program : Assembly.Program} {base query pc : Nat}
    {instr : Assembly.Instr}
    (hNoCallCreate : Assembly.Program.usesCallCreate program = false)
    (hAt :
      Assembly.Program.instrAtPcFrom program base query =
        some (pc, instr)) :
    Assembly.Instr.usesCallCreate instr = false := by
  induction program generalizing base with
  | nil =>
      simp [Assembly.Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      have hSplit :
          Assembly.Instr.usesCallCreate head = false ∧
            Assembly.Program.usesCallCreate rest = false := by
        simpa [Assembly.Program.usesCallCreate] using hNoCallCreate
      by_cases hQuery : query = base
      · simp [Assembly.Program.instrAtPcFrom, hQuery] at hAt
        have hPair : (base, head) = (pc, instr) := by
          simpa using hAt
        cases hPair
        exact hSplit.1
      · simp [Assembly.Program.instrAtPcFrom, hQuery] at hAt
        exact ih hSplit.2 hAt

theorem instr_usesCallCreate_false_of_instrAtPc
    {program : Assembly.Program} {query pc : Nat}
    {instr : Assembly.Instr}
    (hNoCallCreate : Assembly.Program.usesCallCreate program = false)
    (hAt :
      Assembly.Program.instrAtPc program query =
        some (pc, instr)) :
    Assembly.Instr.usesCallCreate instr = false :=
  instr_usesCallCreate_false_of_instrAtPcFrom hNoCallCreate hAt

def stepResultAfter (instr : Assembly.Instr) (state : EVMState) :
    Assembly.StepResult :=
  match instr.haltKind? with
  | some kind =>
      .halted { kind := kind, state := state, output := kind.output state }
  | none =>
      .running state

def openStepAt (program : Assembly.Program) (pc : Nat)
    (instr : Assembly.Instr) (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match instr with
  | .prim op => Target.openStepInstr (.prim op) state
  | _ => .done (Assembly.Source.stepAt program pc instr state)

def openStepAtResult (program : Assembly.Program) (pc : Nat)
    (instr : Assembly.Instr) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  OpenExternal.OpenResult.bind (openStepAt program pc instr state)
    (fun state' => .done (.ok (stepResultAfter instr state')))

def openStepResult (program : Assembly.Program) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  match Assembly.Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => openStepAtResult program pc instr state
  | none => .done (.error .InvalidInstruction)

def openRunNResult (program : Assembly.Program) :
    Nat → EVMState → OpenExternal.OpenResult EVMException Assembly.StepResult
  | 0, state => .done (.ok (.running state))
  | fuel + 1, state =>
      OpenExternal.OpenResult.bind (openStepResult program state)
        (fun result =>
          match result with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt)))

theorem openRunNResult_zero (program : Assembly.Program) (state : EVMState) :
    openRunNResult program 0 state =
      .done (.ok (.running state)) := by
  rfl

theorem openRunNResult_succ
    (program : Assembly.Program) (fuel : Nat) (state : EVMState) :
    openRunNResult program (fuel + 1) state =
      OpenExternal.OpenResult.bind (openStepResult program state)
        (fun result =>
          match result with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt))) := by
  rfl

theorem openStepAt_of_non_prim
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {state : EVMState}
    (hInstr : ∀ op, instr ≠ .prim op) :
    openStepAt program pc instr state =
      .done (Assembly.Source.stepAt program pc instr state) := by
  cases instr <;> simp [openStepAt]
  exact False.elim (hInstr _ rfl)

theorem openStepAt_of_prim_no_callCreate
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {state : EVMState}
    (hNo : op.isCallCreate = false) :
    openStepAt program pc (.prim op) state =
      .done (Assembly.Source.stepAt program pc (.prim op) state) := by
  have hOpen := Target.openStepInstr_of_no_callCreate
    (instr := Assembly.TargetInstr.prim op) (state := state) hNo
  simpa [openStepAt, Assembly.Source.stepAt] using hOpen

theorem openStepAtResult_resolves_closed_of_openStepAt_done
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {state : EVMState} {result : Assembly.StepResult}
    (hOpen :
      openStepAt program pc instr state =
        .done (Assembly.Source.stepAt program pc instr state))
    (hStep :
      Assembly.Source.stepAtResult program pc instr state = .ok result) :
    OpenExternal.OpenResultResolves
      (openStepAtResult program pc instr state) [] (.ok result) := by
  unfold openStepAtResult
  rw [hOpen]
  unfold Assembly.Source.stepAtResult at hStep
  cases hRaw : Assembly.Source.stepAt program pc instr state with
  | error err =>
      rw [hRaw] at hStep
      cases hStep
  | ok state' =>
      rw [hRaw] at hStep
      have hResult : stepResultAfter instr state' = result := by
        cases hKind : instr.haltKind? with
        | none =>
            simpa [stepResultAfter, hKind] using hStep
        | some kind =>
            simpa [stepResultAfter, hKind] using hStep
      simpa [hResult] using
        (OpenExternal.OpenResultResolves.done :
          OpenExternal.OpenResultResolves
            ((.done (.ok result)) :
              OpenExternal.OpenResult EVMException Assembly.StepResult)
            [] (.ok result))

theorem openStepAtResult_resolves_closed_of_non_prim
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {state : EVMState} {result : Assembly.StepResult}
    (hInstr : ∀ op, instr ≠ .prim op)
    (hStep :
      Assembly.Source.stepAtResult program pc instr state = .ok result) :
    OpenExternal.OpenResultResolves
      (openStepAtResult program pc instr state) [] (.ok result) := by
  exact
    openStepAtResult_resolves_closed_of_openStepAt_done
      (openStepAt_of_non_prim hInstr) hStep

theorem openStepAtResult_resolves_closed_of_prim_no_callCreate
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {state : EVMState} {result : Assembly.StepResult}
    (hNo : op.isCallCreate = false)
    (hStep :
      Assembly.Source.stepAtResult program pc (.prim op) state = .ok result) :
    OpenExternal.OpenResultResolves
      (openStepAtResult program pc (.prim op) state) [] (.ok result) := by
  exact
    openStepAtResult_resolves_closed_of_openStepAt_done
      (openStepAt_of_prim_no_callCreate hNo) hStep

theorem openStepAtResult_resolves_closed_inv_of_openStepAt_done
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hOpen :
      openStepAt program pc instr state =
        .done (Assembly.Source.stepAt program pc instr state))
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepAtResult program pc instr state) trace (.ok result)) :
    trace = [] ∧
      Assembly.Source.stepAtResult program pc instr state = .ok result := by
  unfold openStepAtResult at hStep
  rw [hOpen] at hStep
  cases hRaw : Assembly.Source.stepAt program pc instr state with
  | error err =>
      simp [hRaw] at hStep
      cases hStep
  | ok state' =>
      cases hKind : instr.haltKind? with
      | none =>
          simp [hRaw, stepResultAfter, hKind]
            at hStep
          cases hStep
          exact ⟨rfl, by simp [Assembly.Source.stepAtResult, hRaw, hKind]⟩
      | some kind =>
          simp [hRaw, stepResultAfter, hKind]
            at hStep
          cases hStep
          exact ⟨rfl, by simp [Assembly.Source.stepAtResult, hRaw, hKind]⟩

theorem openStepAtResult_resolves_prim_call
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves
      (openStepAtResult program pc (.prim op) state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  unfold openStepAtResult openStepAt
  have hStep :=
    Target.openStepInstr_resolves_prim_call
      (op := op) hKind hCall response
  have hHalt : (Assembly.Instr.prim op).haltKind? = none := by
    simpa [Assembly.Instr.haltKind?] using
      Target.prim_haltKind?_none_of_callKind hKind
  have hDone :
      OpenExternal.OpenResultResolves
        ((.done
          (.ok
            (Assembly.StepResult.running
              (EvmYul.EVM.State.incrPC (call.resume response))))) :
          OpenExternal.OpenResult EVMException Assembly.StepResult)
        []
        (.ok
          (Assembly.StepResult.running
            (EvmYul.EVM.State.incrPC (call.resume response)))) :=
    OpenExternal.OpenResultResolves.done
  simpa [stepResultAfter, hHalt] using
    OpenExternal.OpenResultResolves.bind_ok hStep hDone

theorem openStepResult_current_prim_call
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  unfold openStepResult
  rw [hAt]
  exact openStepAtResult_resolves_prim_call hKind hCall response

theorem openStepResult_current_stepAt
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr}
    {trace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepAtResult program pc instr state) trace result) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      trace result := by
  unfold openStepResult
  rw [hAt]
  exact hStep

theorem openStepResult_resolves_closed_of_current_instr_no_callCreate
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr}
    {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hStep : Assembly.Source.stepResult program state = .ok result) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [] (.ok result) := by
  have hStepAt :
      Assembly.Source.stepAtResult program pc instr state = .ok result := by
    unfold Assembly.Source.stepResult at hStep
    rw [hAt] at hStep
    exact hStep
  cases instr with
  | label name =>
      exact
        openStepResult_current_stepAt hAt
          (openStepAtResult_resolves_closed_of_non_prim
            (by intro op h; cases h) hStepAt)
  | prim op =>
      have hNo : op.isCallCreate = false := by
        simpa [Assembly.Instr.usesCallCreate] using hNoInstr
      exact
        openStepResult_current_stepAt hAt
          (openStepAtResult_resolves_closed_of_prim_no_callCreate
            hNo hStepAt)
  | push value =>
      exact
        openStepResult_current_stepAt hAt
          (openStepAtResult_resolves_closed_of_non_prim
            (by intro op h; cases h) hStepAt)
  | jump target =>
      exact
        openStepResult_current_stepAt hAt
          (openStepAtResult_resolves_closed_of_non_prim
            (by intro op h; cases h) hStepAt)
  | jumpi target =>
      exact
        openStepResult_current_stepAt hAt
          (openStepAtResult_resolves_closed_of_non_prim
            (by intro op h; cases h) hStepAt)

theorem openStepResult_resolves_closed_of_no_callCreate
    {program : Assembly.Program} {state : EVMState}
    {result : Assembly.StepResult}
    (hNoCallCreate : Assembly.Program.usesCallCreate program = false)
    (hStep : Assembly.Source.stepResult program state = .ok result) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [] (.ok result) := by
  unfold openStepResult
  unfold Assembly.Source.stepResult at hStep
  cases hAt : Assembly.Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp [hAt] at hStep ⊢
      cases instr with
      | label name =>
          exact
            openStepAtResult_resolves_closed_of_non_prim
              (by intro op h; cases h) hStep
      | prim op =>
          have hNoInstr :
              op.isCallCreate = false := by
            simpa [Assembly.Instr.usesCallCreate] using
              instr_usesCallCreate_false_of_instrAtPc hNoCallCreate hAt
          exact
            openStepAtResult_resolves_closed_of_prim_no_callCreate
              hNoInstr hStep
      | push value =>
          exact
            openStepAtResult_resolves_closed_of_non_prim
              (by intro op h; cases h) hStep
      | jump target =>
          exact
            openStepAtResult_resolves_closed_of_non_prim
              (by intro op h; cases h) hStep
      | jumpi target =>
          exact
            openStepAtResult_resolves_closed_of_non_prim
              (by intro op h; cases h) hStep

theorem openRunNResult_resolves_step_running
    {program : Assembly.Program} {fuel : Nat} {state mid : EVMState}
    {headTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        headTrace (.ok (.running mid)))
    (hRest :
      OpenExternal.OpenResultResolves (openRunNResult program fuel mid)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      (headTrace ++ tailTrace) result := by
  rw [openRunNResult_succ]
  exact OpenExternal.OpenResultResolves.bind_ok hStep hRest

theorem openRunNResult_resolves_step_halted
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    (hStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        headTrace (.ok (.halted halt))) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      headTrace (.ok (.halted halt)) := by
  rw [openRunNResult_succ]
  have hDone :
      OpenExternal.OpenResultResolves
        ((match Assembly.StepResult.halted halt with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt))) :
          OpenExternal.OpenResult EVMException Assembly.StepResult)
        [] (.ok (.halted halt)) :=
    OpenExternal.OpenResultResolves.done
  simpa using
    (OpenExternal.OpenResultResolves.bind_ok
      (source := openStepResult program state)
      (next := fun stepResult =>
        match stepResult with
        | .running state' => openRunNResult program fuel state'
        | .halted halt => .done (.ok (.halted halt)))
      (left := headTrace) (right := [])
      (value := Assembly.StepResult.halted halt)
      (result := (.ok (.halted halt) :
        Except EVMException Assembly.StepResult))
      hStep hDone)

theorem openRunNResult_resolves_running_continue
    {program : Assembly.Program} {prefixFuel tailFuel : Nat}
    {state mid : EVMState}
    {prefixTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hPrefix :
      OpenExternal.OpenResultResolves
        (openRunNResult program prefixFuel state)
        prefixTrace (.ok (.running mid)))
    (hTail :
      OpenExternal.OpenResultResolves
        (openRunNResult program tailFuel mid)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (prefixFuel + tailFuel) state)
      (prefixTrace ++ tailTrace) result := by
  induction prefixFuel generalizing state mid prefixTrace with
  | zero =>
      rw [openRunNResult_zero] at hPrefix
      cases hPrefix
      simpa using hTail
  | succ fuel ih =>
      rw [openRunNResult_succ] at hPrefix
      rcases OpenExternal.OpenResultResolves.bind_inv hPrefix with
        hStepError | hStepOk
      · rcases hStepError with ⟨err, _hStep, hResult⟩
        cases hResult
      · rcases hStepOk with
          ⟨headTrace, restTrace, stepResult, hTrace, hStep, hRest⟩
        cases stepResult with
        | running next =>
            subst prefixTrace
            have hRestAndTail :=
              ih hRest hTail
            have hCombined :
                OpenExternal.OpenResultResolves
                  (openRunNResult program ((fuel + tailFuel) + 1) state)
                  (headTrace ++ (restTrace ++ tailTrace)) result :=
              openRunNResult_resolves_step_running
                (fuel := fuel + tailFuel) hStep hRestAndTail
            have hFuel :
                (fuel + tailFuel) + 1 = fuel + 1 + tailFuel := by
              omega
            simpa [hFuel, List.append_assoc] using hCombined
        | halted halt =>
            cases hRest

theorem openRunNResult_current_no_call_running_continue_of_current_instr
    {program : Assembly.Program} {state mid : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr}
    {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hStep :
      Assembly.Source.stepResult program state = .ok (.running mid))
    (hRest :
      OpenExternal.OpenResultResolves
        (openRunNResult program fuel mid) tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state) tailTrace result := by
  have hOpenStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        [] (.ok (.running mid)) :=
    openStepResult_resolves_closed_of_current_instr_no_callCreate
      hAt hNoInstr hStep
  simpa using
    openRunNResult_resolves_step_running
      (fuel := fuel) hOpenStep hRest

theorem openRunNResult_current_no_call_halted_of_current_instr
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr} {halt : Assembly.Halt}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hStep :
      Assembly.Source.stepResult program state = .ok (.halted halt)) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      [] (.ok (.halted halt)) := by
  have hOpenStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        [] (.ok (.halted halt)) :=
    openStepResult_resolves_closed_of_current_instr_no_callCreate
      hAt hNoInstr hStep
  exact openRunNResult_resolves_step_halted hOpenStep

theorem openRunNResult_current_prim_call_continue
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenExternal.OpenResultResolves
        (openRunNResult program fuel
          (EvmYul.EVM.State.incrPC (call.resume response)))
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hStep :=
    openStepResult_current_prim_call hAt hKind hCall response
  simpa using
    openRunNResult_resolves_step_running
      (fuel := fuel) hStep hRest

theorem openRunNResult_current_stepAt_running_continue
    {program : Assembly.Program} {fuel : Nat}
    {state mid : EVMState} {pc : Nat} {instr : Assembly.Instr}
    {headTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepAtResult program pc instr state)
        headTrace (.ok (.running mid)))
    (hRest :
      OpenExternal.OpenResultResolves (openRunNResult program fuel mid)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      (headTrace ++ tailTrace) result :=
  openRunNResult_resolves_step_running
    (fuel := fuel) (openStepResult_current_stepAt hAt hStep) hRest

theorem openRunNResult_current_stepAt_halted
    {program : Assembly.Program} {fuel : Nat}
    {state : EVMState} {pc : Nat} {instr : Assembly.Instr}
    {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepAtResult program pc instr state)
        headTrace (.ok (.halted halt))) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      headTrace (.ok (.halted halt)) :=
  openRunNResult_resolves_step_halted
    (fuel := fuel) (openStepResult_current_stepAt hAt hStep)

theorem openRunNResult_resolves_closed_of_no_callCreate
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {result : Assembly.StepResult}
    (hNoCallCreate : Assembly.Program.usesCallCreate program = false)
    (hRun :
      Assembly.Source.runNResult program fuel state = .ok result) :
    OpenExternal.OpenResultResolves (openRunNResult program fuel state)
      [] (.ok result) := by
  induction fuel generalizing state result with
  | zero =>
      simp [Assembly.Source.runNResult, openRunNResult] at hRun ⊢
      cases hRun
      exact OpenExternal.OpenResultResolves.done
  | succ fuel ih =>
      rw [openRunNResult_succ]
      unfold Assembly.Source.runNResult at hRun
      cases hStep : Assembly.Source.stepResult program state with
      | error err =>
          simp [hStep] at hRun
      | ok stepResult =>
          have hOpenStep :
              OpenExternal.OpenResultResolves
                (openStepResult program state) [] (.ok stepResult) :=
            openStepResult_resolves_closed_of_no_callCreate
              hNoCallCreate hStep
          cases stepResult with
          | running mid =>
              simp [hStep] at hRun
              have hRest :
                  OpenExternal.OpenResultResolves
                    (openRunNResult program fuel mid) [] (.ok result) :=
                ih hRun
              simpa using
                OpenExternal.OpenResultResolves.bind_ok
                  (source := openStepResult program state)
                  (next := fun stepResult =>
                    match stepResult with
                    | .running state' => openRunNResult program fuel state'
                    | .halted halt => .done (.ok (.halted halt)))
                  (left := []) (right := [])
                  (value := Assembly.StepResult.running mid)
                  (result := (.ok result :
                    Except EVMException Assembly.StepResult))
                  hOpenStep hRest
          | halted halt =>
              simp [hStep] at hRun
              cases hRun
              have hDone :
                  OpenExternal.OpenResultResolves
                    ((.done (.ok (Assembly.StepResult.halted halt))) :
                      OpenExternal.OpenResult EVMException
                        Assembly.StepResult)
                    [] (.ok (.halted halt)) :=
                OpenExternal.OpenResultResolves.done
              simpa using
                OpenExternal.OpenResultResolves.bind_ok
                  (source := openStepResult program state)
                  (next := fun stepResult =>
                    match stepResult with
                    | .running state' => openRunNResult program fuel state'
                    | .halted halt => .done (.ok (.halted halt)))
                  (left := []) (right := [])
                  (value := Assembly.StepResult.halted halt)
                  (result := (.ok (.halted halt) :
                    Except EVMException Assembly.StepResult))
                  hOpenStep hDone

theorem openStepAtResult_prim_eq_target
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {state : EVMState} :
    openStepAtResult program pc (.prim op) state =
      Target.openStepInstrResult (.prim op) state := by
  simp [openStepAtResult, openStepAt, Target.openStepInstrResult,
    stepResultAfter, Target.stepResultAfter, Assembly.Instr.haltKind?,
    Assembly.TargetInstr.haltKind?]

theorem openStepAtResult_emit_resolves_target
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepAtResult program pc instr state) trace (.ok result)) :
    OpenExternal.OpenResultResolves
      (Target.openRunListResult (emitted.map Assembly.LocatedTarget.instr)
        state)
      trace (.ok result) := by
  cases instr with
  | prim op =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      change
        OpenExternal.OpenResultResolves
          (Target.openRunListResult [Assembly.TargetInstr.prim op] state)
          trace (.ok result)
      rw [Target.openRunListResult_cons]
      have hStep' :
          OpenExternal.OpenResultResolves
            (Target.openStepInstrResult (.prim op) state) trace
            (.ok result) := by
        simpa [openStepAtResult_prim_eq_target] using hStep
      cases result with
      | running mid =>
          have hRest :
              OpenExternal.OpenResultResolves
                (Target.openRunListResult [] mid) []
                (.ok (.running mid)) := by
            exact OpenExternal.OpenResultResolves.done
          simpa [Target.openRunListResult_nil] using
            OpenExternal.OpenResultResolves.bind_ok
              (source := Target.openStepInstrResult (.prim op) state)
              (next := fun stepResult =>
                match stepResult with
                | .running state' => Target.openRunListResult [] state'
                | .halted halt => .done (.ok (.halted halt)))
              (left := trace) (right := [])
              (value := Assembly.StepResult.running mid)
              (result := (.ok (.running mid) :
                Except EVMException Assembly.StepResult))
              hStep' hRest
      | halted halt =>
          have hRest :
              OpenExternal.OpenResultResolves
                ((.done (.ok (Assembly.StepResult.halted halt))) :
                  OpenExternal.OpenResult EVMException Assembly.StepResult)
                [] (.ok (.halted halt)) := by
            exact OpenExternal.OpenResultResolves.done
          simpa using
            OpenExternal.OpenResultResolves.bind_ok
              (source := Target.openStepInstrResult (.prim op) state)
              (next := fun stepResult =>
                match stepResult with
                | .running state' => Target.openRunListResult [] state'
                | .halted halt => .done (.ok (.halted halt)))
              (left := trace) (right := [])
              (value := Assembly.StepResult.halted halt)
              (result := (.ok (.halted halt) :
                Except EVMException Assembly.StepResult))
              hStep' hRest
  | label name =>
      have hOpen :
          openStepAt program pc (.label name) state =
            .done (Assembly.Source.stepAt program pc (.label name) state) :=
        openStepAt_of_non_prim (by intro op h; cases h)
      rcases
          openStepAtResult_resolves_closed_inv_of_openStepAt_done
            hOpen hStep with
        ⟨hTrace, hClosed⟩
      subst trace
      have hRun :
          Assembly.Target.runListResult
            (emitted.map Assembly.LocatedTarget.instr) state =
            .ok result :=
        Assembly.Preservation.stepAt_emit_result_sound hEmit hClosed
      have hCode :
          Target.codeUsesCallCreate
            (emitted.map Assembly.LocatedTarget.instr) = false :=
        Target.codeUsesCallCreate_false_of_emitInstr_no_call
          (by rfl) hEmit
      exact
        Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun
  | push value =>
      have hOpen :
          openStepAt program pc (.push value) state =
            .done (Assembly.Source.stepAt program pc (.push value) state) :=
        openStepAt_of_non_prim (by intro op h; cases h)
      rcases
          openStepAtResult_resolves_closed_inv_of_openStepAt_done
            hOpen hStep with
        ⟨hTrace, hClosed⟩
      subst trace
      have hRun :
          Assembly.Target.runListResult
            (emitted.map Assembly.LocatedTarget.instr) state =
            .ok result :=
        Assembly.Preservation.stepAt_emit_result_sound hEmit hClosed
      have hCode :
          Target.codeUsesCallCreate
            (emitted.map Assembly.LocatedTarget.instr) = false :=
        Target.codeUsesCallCreate_false_of_emitInstr_no_call
          (by rfl) hEmit
      exact
        Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun
  | jump target =>
      have hOpen :
          openStepAt program pc (.jump target) state =
            .done (Assembly.Source.stepAt program pc (.jump target) state) :=
        openStepAt_of_non_prim (by intro op h; cases h)
      rcases
          openStepAtResult_resolves_closed_inv_of_openStepAt_done
            hOpen hStep with
        ⟨hTrace, hClosed⟩
      subst trace
      have hRun :
          Assembly.Target.runListResult
            (emitted.map Assembly.LocatedTarget.instr) state =
            .ok result :=
        Assembly.Preservation.stepAt_emit_result_sound hEmit hClosed
      have hCode :
          Target.codeUsesCallCreate
            (emitted.map Assembly.LocatedTarget.instr) = false :=
        Target.codeUsesCallCreate_false_of_emitInstr_no_call
          (by rfl) hEmit
      exact
        Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun
  | jumpi target =>
      have hOpen :
          openStepAt program pc (.jumpi target) state =
            .done (Assembly.Source.stepAt program pc (.jumpi target) state) :=
        openStepAt_of_non_prim (by intro op h; cases h)
      rcases
          openStepAtResult_resolves_closed_inv_of_openStepAt_done
            hOpen hStep with
        ⟨hTrace, hClosed⟩
      subst trace
      have hRun :
          Assembly.Target.runListResult
            (emitted.map Assembly.LocatedTarget.instr) state =
            .ok result :=
        Assembly.Preservation.stepAt_emit_result_sound hEmit hClosed
      have hCode :
          Target.codeUsesCallCreate
            (emitted.map Assembly.LocatedTarget.instr) = false :=
        Target.codeUsesCallCreate_false_of_emitInstr_no_call
          (by rfl) hEmit
      exact
        Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun

theorem openStepResult_resolves_target_current
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hAsm : Assembly.assemble? program = some target)
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepResult program state) trace (.ok result)) :
    ∃ pc instr emitted before after,
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr) ∧
        Assembly.emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        OpenExternal.OpenResultResolves
          (Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok result) := by
  unfold openStepResult at hStep
  cases hAt : Assembly.Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
      cases hStep
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp [hAt] at hStep
      rcases
          Assembly.Preservation.assemble_covers_current_pc hAsm hAt with
        ⟨before, emitted, after, hTargetBlock, hEmit⟩
      exact
        ⟨pc, instr, emitted, before, after, rfl, hEmit, hTargetBlock,
          openStepAtResult_emit_resolves_target hEmit hStep⟩

inductive OpenTraceResult (program : Assembly.Program) :
    Nat → EVMState → OpenExternal.OpenTrace → Assembly.StepResult → Prop where
  | done (state : EVMState) :
      OpenTraceResult program 0 state [] (.running state)
  | stepRunning
      {fuel : Nat} {state mid : EVMState}
      {headTrace tailTrace : OpenExternal.OpenTrace}
      {result : Assembly.StepResult}
      (hStep :
        OpenExternal.OpenResultResolves (openStepResult program state)
          headTrace (.ok (.running mid)))
      (hRest : OpenTraceResult program fuel mid tailTrace result) :
      OpenTraceResult program (fuel + 1) state
        (headTrace ++ tailTrace) result
  | stepHalted
      {fuel : Nat} {state : EVMState}
      {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
      (hStep :
        OpenExternal.OpenResultResolves (openStepResult program state)
          headTrace (.ok (.halted halt))) :
      OpenTraceResult program (fuel + 1) state headTrace (.halted halt)

namespace OpenTraceResult

theorem resolves
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hTrace : OpenTraceResult program fuel state trace result) :
    OpenExternal.OpenResultResolves (openRunNResult program fuel state)
      trace (.ok result) := by
  induction hTrace with
  | done state =>
      exact OpenExternal.OpenResultResolves.done
  | stepRunning hStep _hRest ih =>
      exact openRunNResult_resolves_step_running hStep ih
  | stepHalted hStep =>
      exact openRunNResult_resolves_step_halted hStep

theorem of_resolves
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hResolve :
      OpenExternal.OpenResultResolves (openRunNResult program fuel state)
        trace (.ok result)) :
    OpenTraceResult program fuel state trace result := by
  induction fuel generalizing state trace result with
  | zero =>
      simp [openRunNResult] at hResolve
      cases hResolve
      exact OpenTraceResult.done state
  | succ fuel ih =>
      rw [openRunNResult_succ] at hResolve
      rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
        hError | hOk
      · rcases hError with ⟨err, _hStep, hResult⟩
        cases hResult
      · rcases hOk with
          ⟨headTrace, tailTrace, stepResult, hTrace, hStep, hRest⟩
        cases stepResult with
        | running mid =>
            subst trace
            exact OpenTraceResult.stepRunning hStep (ih hRest)
        | halted halt =>
            cases hRest
            subst trace
            simpa using OpenTraceResult.stepHalted hStep

theorem of_closed_no_callCreate
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {result : Assembly.StepResult}
    (hNoCallCreate : Assembly.Program.usesCallCreate program = false)
    (hRun :
      Assembly.Source.runNResult program fuel state = .ok result) :
    OpenTraceResult program fuel state [] result :=
  of_resolves
    (openRunNResult_resolves_closed_of_no_callCreate hNoCallCreate hRun)

theorem current_stepAt_running_continue
    {program : Assembly.Program} {state mid : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr}
    {headTrace tailTrace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepAtResult program pc instr state)
        headTrace (.ok (.running mid)))
    (hRest : OpenTraceResult program fuel mid tailTrace result) :
    OpenTraceResult program (fuel + 1) state
      (headTrace ++ tailTrace) result :=
  OpenTraceResult.stepRunning (openStepResult_current_stepAt hAt hStep)
    hRest

theorem current_stepAt_halted
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr}
    {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hStep :
      OpenExternal.OpenResultResolves
        (openStepAtResult program pc instr state)
        headTrace (.ok (.halted halt))) :
    OpenTraceResult program (fuel + 1) state headTrace (.halted halt) :=
  OpenTraceResult.stepHalted (openStepResult_current_stepAt hAt hStep)

theorem current_prim_call_continue
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenTraceResult program fuel
        (EvmYul.EVM.State.incrPC (call.resume response))
        tailTrace result) :
    OpenTraceResult program (fuel + 1) state
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hStep :=
    openStepResult_current_prim_call hAt hKind hCall response
  simpa using OpenTraceResult.stepRunning hStep hRest

end OpenTraceResult

end Source

namespace Compiled

def openStepResult (program : Assembly.Program) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  match Assembly.emitCurrent? program state with
  | some code => Target.openRunListResult code state
  | none => .done (.error .InvalidInstruction)

def openRunNResult (program : Assembly.Program) :
    Nat → EVMState → OpenExternal.OpenResult EVMException Assembly.StepResult
  | 0, state => .done (.ok (.running state))
  | fuel + 1, state =>
      OpenExternal.OpenResult.bind (openStepResult program state)
        (fun result =>
          match result with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt)))

theorem openRunNResult_zero (program : Assembly.Program) (state : EVMState) :
    openRunNResult program 0 state =
      .done (.ok (.running state)) := by
  rfl

theorem openRunNResult_succ
    (program : Assembly.Program) (fuel : Nat) (state : EVMState) :
    openRunNResult program (fuel + 1) state =
      OpenExternal.OpenResult.bind (openStepResult program state)
        (fun result =>
          match result with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt))) := by
  rfl

theorem openRunNResult_resolves_step_running
    {program : Assembly.Program} {fuel : Nat} {state mid : EVMState}
    {headTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        headTrace (.ok (.running mid)))
    (hRest :
      OpenExternal.OpenResultResolves (openRunNResult program fuel mid)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      (headTrace ++ tailTrace) result := by
  rw [openRunNResult_succ]
  exact OpenExternal.OpenResultResolves.bind_ok hStep hRest

theorem openRunNResult_resolves_step_halted
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    (hStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        headTrace (.ok (.halted halt))) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      headTrace (.ok (.halted halt)) := by
  rw [openRunNResult_succ]
  have hDone :
      OpenExternal.OpenResultResolves
        ((match Assembly.StepResult.halted halt with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt))) :
          OpenExternal.OpenResult EVMException Assembly.StepResult)
        [] (.ok (.halted halt)) :=
    OpenExternal.OpenResultResolves.done
  simpa using
    (OpenExternal.OpenResultResolves.bind_ok
      (source := openStepResult program state)
      (next := fun stepResult =>
        match stepResult with
        | .running state' => openRunNResult program fuel state'
        | .halted halt => .done (.ok (.halted halt)))
      (left := headTrace) (right := [])
      (value := Assembly.StepResult.halted halt)
      (result := (.ok (.halted halt) :
        Except EVMException Assembly.StepResult))
      hStep hDone)

theorem openStepResult_resolves_closed_of_emitCurrent_no_callCreate
    {program : Assembly.Program} {state : EVMState}
    {code : List Assembly.TargetInstr} {result : Assembly.StepResult}
    (hEmit : Assembly.emitCurrent? program state = some code)
    (hCode : Target.codeUsesCallCreate code = false)
    (hStep : Assembly.Compiled.stepResult program state = .ok result) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [] (.ok result) := by
  unfold openStepResult
  rw [hEmit]
  unfold Assembly.Compiled.stepResult at hStep
  rw [hEmit] at hStep
  exact Target.openRunListResult_resolves_closed_of_no_callCreate hCode hStep

theorem codeUsesCallCreate_false_of_current_no_call
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr} {code : List Assembly.TargetInstr}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitCurrent? program state = some code) :
    Target.codeUsesCallCreate code = false := by
  unfold Assembly.emitCurrent? at hEmit
  rw [hAt] at hEmit
  cases hEmitInstr : Assembly.emitInstr? program pc instr with
  | none =>
      simp [hEmitInstr] at hEmit
  | some emitted =>
      simp [hEmitInstr] at hEmit
      subst code
      exact
        Target.codeUsesCallCreate_false_of_emitInstr_no_call
          hNoInstr hEmitInstr

theorem openStepResult_emitCurrent_single_prim_call
    {program : Assembly.Program} {state : EVMState} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEmit : Assembly.emitCurrent? program state =
      some [Assembly.TargetInstr.prim op])
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  unfold openStepResult
  rw [hEmit]
  exact Target.openRunListResult_single_prim_call hKind hCall response

theorem openStepResult_current_prim_call
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  have hEmit :
      Assembly.emitCurrent? program state =
        some [Assembly.TargetInstr.prim op] := by
    simp [Assembly.emitCurrent?, hAt, Assembly.emitInstr?]
  exact
    openStepResult_emitCurrent_single_prim_call
      (op := op) hEmit hKind hCall response

theorem openRunNResult_current_prim_call_continue
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenExternal.OpenResultResolves
        (openRunNResult program fuel
          (EvmYul.EVM.State.incrPC (call.resume response)))
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hStep :=
    openStepResult_current_prim_call hAt hKind hCall response
  simpa using
    openRunNResult_resolves_step_running
      (fuel := fuel) hStep hRest

inductive OpenTraceResult (program : Assembly.Program) :
    Nat → EVMState → OpenExternal.OpenTrace → Assembly.StepResult → Prop where
  | done (state : EVMState) :
      OpenTraceResult program 0 state [] (.running state)
  | stepRunning
      {fuel : Nat} {state mid : EVMState}
      {headTrace tailTrace : OpenExternal.OpenTrace}
      {result : Assembly.StepResult}
      (hStep :
        OpenExternal.OpenResultResolves (openStepResult program state)
          headTrace (.ok (.running mid)))
      (hRest : OpenTraceResult program fuel mid tailTrace result) :
      OpenTraceResult program (fuel + 1) state
        (headTrace ++ tailTrace) result
  | stepHalted
      {fuel : Nat} {state : EVMState}
      {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
      (hStep :
        OpenExternal.OpenResultResolves (openStepResult program state)
          headTrace (.ok (.halted halt))) :
      OpenTraceResult program (fuel + 1) state headTrace (.halted halt)

namespace OpenTraceResult

theorem resolves
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hTrace : OpenTraceResult program fuel state trace result) :
    OpenExternal.OpenResultResolves (openRunNResult program fuel state)
      trace (.ok result) := by
  induction hTrace with
  | done state =>
      exact OpenExternal.OpenResultResolves.done
  | stepRunning hStep _hRest ih =>
      exact openRunNResult_resolves_step_running hStep ih
  | stepHalted hStep =>
      exact openRunNResult_resolves_step_halted hStep

theorem of_resolves
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hResolve :
      OpenExternal.OpenResultResolves (openRunNResult program fuel state)
        trace (.ok result)) :
    OpenTraceResult program fuel state trace result := by
  induction fuel generalizing state trace result with
  | zero =>
      simp [openRunNResult] at hResolve
      cases hResolve
      exact OpenTraceResult.done state
  | succ fuel ih =>
      rw [openRunNResult_succ] at hResolve
      rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
        hError | hOk
      · rcases hError with ⟨err, _hStep, hResult⟩
        cases hResult
      · rcases hOk with
          ⟨headTrace, tailTrace, stepResult, hTrace, hStep, hRest⟩
        cases stepResult with
        | running mid =>
            subst trace
            exact OpenTraceResult.stepRunning hStep (ih hRest)
        | halted halt =>
            cases hRest
            subst trace
            simpa using OpenTraceResult.stepHalted hStep

theorem current_prim_call_continue
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenTraceResult program fuel
        (EvmYul.EVM.State.incrPC (call.resume response))
        tailTrace result) :
    OpenTraceResult program (fuel + 1) state
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hStep :=
    openStepResult_current_prim_call hAt hKind hCall response
  simpa using OpenTraceResult.stepRunning hStep hRest

theorem current_no_call_running_continue
    {program : Assembly.Program} {state mid : EVMState}
    {fuel : Nat} {code : List Assembly.TargetInstr}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hEmit : Assembly.emitCurrent? program state = some code)
    (hCode : Target.codeUsesCallCreate code = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.running mid))
    (hRest : OpenTraceResult program fuel mid tailTrace result) :
    OpenTraceResult program (fuel + 1) state tailTrace result := by
  have hOpenStep :=
    openStepResult_resolves_closed_of_emitCurrent_no_callCreate
      hEmit hCode hStep
  simpa using OpenTraceResult.stepRunning hOpenStep hRest

theorem current_no_call_halted
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {code : List Assembly.TargetInstr} {halt : Assembly.Halt}
    (hEmit : Assembly.emitCurrent? program state = some code)
    (hCode : Target.codeUsesCallCreate code = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.halted halt)) :
    OpenTraceResult program (fuel + 1) state [] (.halted halt) := by
  have hOpenStep :=
    openStepResult_resolves_closed_of_emitCurrent_no_callCreate
      hEmit hCode hStep
  exact OpenTraceResult.stepHalted hOpenStep

theorem current_no_call_running_continue_of_current_instr
    {program : Assembly.Program} {state mid : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.running mid))
    (hRest : OpenTraceResult program fuel mid tailTrace result) :
    OpenTraceResult program (fuel + 1) state tailTrace result := by
  cases hEmit : Assembly.emitCurrent? program state with
  | none =>
      unfold Assembly.Compiled.stepResult at hStep
      rw [hEmit] at hStep
      cases hStep
  | some code =>
      have hCode :
          Target.codeUsesCallCreate code = false :=
        codeUsesCallCreate_false_of_current_no_call hAt hNoInstr hEmit
      exact
        current_no_call_running_continue hEmit hCode hStep hRest

theorem current_no_call_halted_of_current_instr
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr} {halt : Assembly.Halt}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.halted halt)) :
    OpenTraceResult program (fuel + 1) state [] (.halted halt) := by
  cases hEmit : Assembly.emitCurrent? program state with
  | none =>
      unfold Assembly.Compiled.stepResult at hStep
      rw [hEmit] at hStep
      cases hStep
  | some code =>
      have hCode :
          Target.codeUsesCallCreate code = false :=
        codeUsesCallCreate_false_of_current_no_call hAt hNoInstr hEmit
      exact current_no_call_halted hEmit hCode hStep

end OpenTraceResult

end Compiled

inductive OpenBlockTraceResult
    (program : Assembly.Program) (target : Assembly.TargetProgram) :
    Nat → EVMState → OpenExternal.OpenTrace → Assembly.StepResult → Prop where
  | done (state : EVMState) :
      OpenBlockTraceResult program target 0 state [] (.running state)
  | stepRunning
      {fuel : Nat} {state mid : EVMState}
      {trace tailTrace : OpenExternal.OpenTrace}
      {result : Assembly.StepResult}
      {pc : Nat} {instr : Assembly.Instr}
      {emitted before after : List Assembly.LocatedTarget}
      (hAt :
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr))
      (hEmit : Assembly.emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        OpenExternal.OpenResultResolves
          (Target.openRunListResult (emitted.map Assembly.LocatedTarget.instr)
            state)
          trace (.ok (.running mid)))
      (hRest : OpenBlockTraceResult program target fuel mid tailTrace result) :
      OpenBlockTraceResult program target (fuel + 1) state
        (trace ++ tailTrace) result
  | stepHalted
      {fuel : Nat} {state : EVMState}
      {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
      {pc : Nat} {instr : Assembly.Instr}
      {emitted before after : List Assembly.LocatedTarget}
      (hAt :
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr))
      (hEmit : Assembly.emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        OpenExternal.OpenResultResolves
          (Target.openRunListResult (emitted.map Assembly.LocatedTarget.instr)
            state)
          trace (.ok (.halted halt))) :
      OpenBlockTraceResult program target (fuel + 1) state trace
        (.halted halt)

namespace OpenBlockTraceResult

theorem emitCurrent?_of_instrAt_emit
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted) :
    Assembly.emitCurrent? program state =
      some (emitted.map Assembly.LocatedTarget.instr) := by
  simp [Assembly.emitCurrent?, hAt, hEmit]

theorem openStepResult_resolves_of_emit
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult (emitted.map Assembly.LocatedTarget.instr)
          state)
        trace (.ok result)) :
    OpenExternal.OpenResultResolves
      (Compiled.openStepResult program state) trace (.ok result) := by
  have hCurrent := emitCurrent?_of_instrAt_emit hAt hEmit
  unfold Compiled.openStepResult
  rw [hCurrent]
  exact hRun

theorem to_compiled_trace
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hTrace : OpenBlockTraceResult program target fuel state trace result) :
    Compiled.OpenTraceResult program fuel state trace result := by
  induction hTrace with
  | done state =>
      exact Compiled.OpenTraceResult.done state
  | stepRunning hAt hEmit _hTargetBlock hRun _hRest ih =>
      exact
        Compiled.OpenTraceResult.stepRunning
          (openStepResult_resolves_of_emit hAt hEmit hRun) ih
  | stepHalted hAt hEmit _hTargetBlock hRun =>
      exact
        Compiled.OpenTraceResult.stepHalted
          (openStepResult_resolves_of_emit hAt hEmit hRun)

theorem resolves_compiled
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hTrace : OpenBlockTraceResult program target fuel state trace result) :
    OpenExternal.OpenResultResolves
      (Compiled.openRunNResult program fuel state)
      trace (.ok result) :=
  (to_compiled_trace hTrace).resolves

theorem current_prim_call_continue
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {state : EVMState} {fuel : Nat}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit : Assembly.emitInstr? program pc (.prim op) = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenBlockTraceResult program target fuel
        (EvmYul.EVM.State.incrPC (call.resume response))
        tailTrace result) :
    OpenBlockTraceResult program target (fuel + 1) state
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        [{ site := call.site, response := response }]
        (.ok (.running
          (EvmYul.EVM.State.incrPC (call.resume response)))) :=
    Target.openRunListResult_emitInstr_prim_call
      hEmit hKind hCall response
  simpa using
    OpenBlockTraceResult.stepRunning hAt hEmit hTargetBlock hRun hRest

theorem current_no_call_running_continue
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {state mid : EVMState} {fuel : Nat}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hRun :
      Assembly.Target.runListResult
        (emitted.map Assembly.LocatedTarget.instr) state =
        .ok (.running mid))
    (hRest : OpenBlockTraceResult program target fuel mid tailTrace result) :
    OpenBlockTraceResult program target (fuel + 1) state tailTrace result := by
  have hCode :
      Target.codeUsesCallCreate
        (emitted.map Assembly.LocatedTarget.instr) = false :=
    Target.codeUsesCallCreate_false_of_emitInstr_no_call hNoInstr hEmit
  have hOpenRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        [] (.ok (.running mid)) :=
    Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun
  simpa using
    OpenBlockTraceResult.stepRunning hAt hEmit hTargetBlock hOpenRun hRest

theorem current_no_call_halted
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {state : EVMState} {fuel : Nat}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {halt : Assembly.Halt}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hRun :
      Assembly.Target.runListResult
        (emitted.map Assembly.LocatedTarget.instr) state =
        .ok (.halted halt)) :
    OpenBlockTraceResult program target (fuel + 1) state [] (.halted halt) := by
  have hCode :
      Target.codeUsesCallCreate
        (emitted.map Assembly.LocatedTarget.instr) = false :=
    Target.codeUsesCallCreate_false_of_emitInstr_no_call hNoInstr hEmit
  have hOpenRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        [] (.ok (.halted halt)) :=
    Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun
  exact
    OpenBlockTraceResult.stepHalted hAt hEmit hTargetBlock hOpenRun

end OpenBlockTraceResult

namespace Source
namespace OpenTraceResult

theorem to_openBlockTrace
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hAsm : Assembly.assemble? program = some target)
    (hTrace : OpenTraceResult program fuel state trace result) :
    OpenBlockTraceResult program target fuel state trace result := by
  induction hTrace with
  | done state =>
      exact OpenBlockTraceResult.done state
  | stepRunning hStep _hRest ih =>
      rcases openStepResult_resolves_target_current hAsm hStep with
        ⟨pc, instr, emitted, before, after, hAt, hEmit, hTargetBlock, hRun⟩
      exact
        OpenBlockTraceResult.stepRunning hAt hEmit hTargetBlock hRun ih
  | stepHalted hStep =>
      rcases openStepResult_resolves_target_current hAsm hStep with
        ⟨pc, instr, emitted, before, after, hAt, hEmit, hTargetBlock, hRun⟩
      exact
        OpenBlockTraceResult.stepHalted hAt hEmit hTargetBlock hRun

theorem resolves_compiled_of_assemble
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hAsm : Assembly.assemble? program = some target)
    (hTrace : OpenTraceResult program fuel state trace result) :
    OpenExternal.OpenResultResolves
      (Compiled.openRunNResult program fuel state)
      trace (.ok result) :=
  (to_openBlockTrace hAsm hTrace).resolves_compiled

theorem to_openBlockTrace_of_compile
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hCompile : Assembly.compile? program = some target)
    (hTrace : OpenTraceResult program fuel state trace result) :
    OpenBlockTraceResult program target fuel state trace result :=
  to_openBlockTrace (Assembly.Preservation.compile?_some_assemble hCompile)
    hTrace

theorem resolves_compiled_of_compile
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hCompile : Assembly.compile? program = some target)
    (hTrace : OpenTraceResult program fuel state trace result) :
    OpenExternal.OpenResultResolves
      (Compiled.openRunNResult program fuel state)
      trace (.ok result) :=
  (to_openBlockTrace_of_compile hCompile hTrace).resolves_compiled

end OpenTraceResult
end Source

theorem compile_openRunN_result_openBlockTrace_sound
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hCompile : Assembly.compile? program = some target)
    (hRun :
      OpenExternal.OpenResultResolves
        (Source.openRunNResult program fuel state) trace (.ok result)) :
    Assembly.Accepted program ∧
      OpenBlockTraceResult program target fuel state trace result := by
  exact
    ⟨Assembly.Preservation.compile?_some_accepted hCompile,
      Source.OpenTraceResult.to_openBlockTrace_of_compile hCompile
        (Source.OpenTraceResult.of_resolves hRun)⟩

theorem compile_openRunN_result_compiled_sound
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hCompile : Assembly.compile? program = some target)
    (hRun :
      OpenExternal.OpenResultResolves
        (Source.openRunNResult program fuel state) trace (.ok result)) :
    Assembly.Accepted program ∧
      OpenExternal.OpenResultResolves
        (Compiled.openRunNResult program fuel state) trace (.ok result) := by
  rcases compile_openRunN_result_openBlockTrace_sound hCompile hRun with
    ⟨hAccepted, hTrace⟩
  exact ⟨hAccepted, hTrace.resolves_compiled⟩

theorem compile_closed_no_callCreate_runN_result_openBlockTrace_sound
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {result : Assembly.StepResult}
    (hNoCallCreate : Assembly.Program.usesCallCreate program = false)
    (hCompile : Assembly.compile? program = some target)
    (hRun :
      Assembly.Source.runNResult program fuel state = .ok result) :
    Assembly.Accepted program ∧
      OpenBlockTraceResult program target fuel state [] result :=
  compile_openRunN_result_openBlockTrace_sound hCompile
    (Source.openRunNResult_resolves_closed_of_no_callCreate
      hNoCallCreate hRun)

theorem compile_closed_no_callCreate_runN_result_compiled_sound
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {result : Assembly.StepResult}
    (hNoCallCreate : Assembly.Program.usesCallCreate program = false)
    (hCompile : Assembly.compile? program = some target)
    (hRun :
      Assembly.Source.runNResult program fuel state = .ok result) :
    Assembly.Accepted program ∧
      OpenExternal.OpenResultResolves
        (Compiled.openRunNResult program fuel state) [] (.ok result) :=
  compile_openRunN_result_compiled_sound hCompile
    (Source.openRunNResult_resolves_closed_of_no_callCreate
      hNoCallCreate hRun)

end OpenAssembly
end Yul
end EvmCompiler
