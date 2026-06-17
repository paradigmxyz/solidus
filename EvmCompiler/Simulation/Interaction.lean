import EvmCompiler.Simulation.OpenWorld
import EvmYul.Data.Stack
import EvmYul.MachineStateOps
import EvmYul.Operations

namespace EvmCompiler
namespace Simulation

abbrev InteractionWord := EvmYul.UInt256
abbrev InteractionAddress := EvmYul.AccountAddress
abbrev InteractionStack := EvmYul.Stack InteractionWord

inductive CallKind where
  | call
  | callcode
  | delegatecall
  | staticcall
  deriving DecidableEq, Repr

namespace CallKind

def toYulOperation : CallKind → EvmYul.Operation .Yul
  | .call => .System .CALL
  | .callcode => .System .CALLCODE
  | .delegatecall => .System .DELEGATECALL
  | .staticcall => .System .STATICCALL

def toEVMOperation : CallKind → EvmYul.Operation .EVM
  | .call => .CALL
  | .callcode => .CALLCODE
  | .delegatecall => .DELEGATECALL
  | .staticcall => .STATICCALL

def ofYulOperation? : EvmYul.Operation .Yul → Option CallKind
  | .System .CALL => some .call
  | .System .CALLCODE => some .callcode
  | .System .DELEGATECALL => some .delegatecall
  | .System .STATICCALL => some .staticcall
  | _ => none

def ofEVMOperation? : EvmYul.Operation .EVM → Option CallKind
  | .CALL => some .call
  | .CALLCODE => some .callcode
  | .DELEGATECALL => some .delegatecall
  | .STATICCALL => some .staticcall
  | _ => none

def inputArity : CallKind → Nat
  | .call | .callcode => 7
  | .delegatecall | .staticcall => 6

@[simp] theorem ofYulOperation?_toYulOperation (kind : CallKind) :
    ofYulOperation? kind.toYulOperation = some kind := by
  cases kind <;> rfl

@[simp] theorem ofEVMOperation?_toEVMOperation (kind : CallKind) :
    ofEVMOperation? kind.toEVMOperation = some kind := by
  cases kind <;> rfl

end CallKind

inductive CreateKind where
  | create
  | create2
  deriving DecidableEq, Repr

namespace CreateKind

def toYulOperation : CreateKind → EvmYul.Operation .Yul
  | .create => .System .CREATE
  | .create2 => .System .CREATE2

def toEVMOperation : CreateKind → EvmYul.Operation .EVM
  | .create => .CREATE
  | .create2 => .CREATE2

def ofYulOperation? : EvmYul.Operation .Yul → Option CreateKind
  | .System .CREATE => some .create
  | .System .CREATE2 => some .create2
  | _ => none

def ofEVMOperation? : EvmYul.Operation .EVM → Option CreateKind
  | .CREATE => some .create
  | .CREATE2 => some .create2
  | _ => none

def inputArity : CreateKind → Nat
  | .create => 3
  | .create2 => 4

@[simp] theorem ofYulOperation?_toYulOperation (kind : CreateKind) :
    ofYulOperation? kind.toYulOperation = some kind := by
  cases kind <;> rfl

@[simp] theorem ofEVMOperation?_toEVMOperation (kind : CreateKind) :
    ofEVMOperation? kind.toEVMOperation = some kind := by
  cases kind <;> rfl

end CreateKind

/-- The complete opcode family that suspends at the open-world boundary. -/
inductive ExternalKind where
  | call : CallKind → ExternalKind
  | create : CreateKind → ExternalKind
  deriving DecidableEq, Repr

namespace ExternalKind

def toYulOperation : ExternalKind → EvmYul.Operation .Yul
  | .call kind => kind.toYulOperation
  | .create kind => kind.toYulOperation

def toEVMOperation : ExternalKind → EvmYul.Operation .EVM
  | .call kind => kind.toEVMOperation
  | .create kind => kind.toEVMOperation

def ofYulOperation? (op : EvmYul.Operation .Yul) : Option ExternalKind :=
  match CallKind.ofYulOperation? op with
  | some kind => some (.call kind)
  | none => (CreateKind.ofYulOperation? op).map .create

def ofEVMOperation? (op : EvmYul.Operation .EVM) : Option ExternalKind :=
  match CallKind.ofEVMOperation? op with
  | some kind => some (.call kind)
  | none => (CreateKind.ofEVMOperation? op).map .create

@[simp] theorem ofYulOperation?_toYulOperation (kind : ExternalKind) :
    ofYulOperation? kind.toYulOperation = some kind := by
  cases kind with
  | call kind => cases kind <;> rfl
  | create kind => cases kind <;> rfl

@[simp] theorem ofEVMOperation?_toEVMOperation (kind : ExternalKind) :
    ofEVMOperation? kind.toEVMOperation = some kind := by
  cases kind with
  | call kind => cases kind <;> rfl
  | create kind => cases kind <;> rfl

@[simp] theorem classifies_call :
    ofEVMOperation? EvmYul.Operation.CALL =
      some (.call .call) := rfl

@[simp] theorem classifies_callcode :
    ofEVMOperation? EvmYul.Operation.CALLCODE =
      some (.call .callcode) := rfl

@[simp] theorem classifies_delegatecall :
    ofEVMOperation? EvmYul.Operation.DELEGATECALL =
      some (.call .delegatecall) := rfl

@[simp] theorem classifies_staticcall :
    ofEVMOperation? EvmYul.Operation.STATICCALL =
      some (.call .staticcall) := rfl

@[simp] theorem classifies_create :
    ofEVMOperation? EvmYul.Operation.CREATE =
      some (.create .create) := rfl

@[simp] theorem classifies_create2 :
    ofEVMOperation? EvmYul.Operation.CREATE2 =
      some (.create .create2) := rfl

end ExternalKind

structure CallRequest where
  kind : CallKind
  requestedGas : InteractionWord
  caller : InteractionAddress
  recipient : InteractionAddress
  codeAddress : InteractionAddress
  transferValue : InteractionWord
  apparentValue : InteractionWord
  calldata : ByteArray
  permission : Bool

structure CallLocal where
  inputOffset : InteractionWord
  inputSize : InteractionWord
  outputOffset : InteractionWord
  outputSize : InteractionWord

structure CreateRequest where
  kind : CreateKind
  creator : InteractionAddress
  value : InteractionWord
  initCode : ByteArray
  salt : Option InteractionWord
  permission : Bool

structure CreateLocal where
  initOffset : InteractionWord
  initSize : InteractionWord

structure CallOperands where
  requestedGas : InteractionWord
  address : InteractionWord
  valueArg : InteractionWord
  inputOffset : InteractionWord
  inputSize : InteractionWord
  outputOffset : InteractionWord
  outputSize : InteractionWord

namespace CallOperands

def callLocal (operands : CallOperands) : CallLocal where
  inputOffset := operands.inputOffset
  inputSize := operands.inputSize
  outputOffset := operands.outputOffset
  outputSize := operands.outputSize

end CallOperands

structure CreateOperands where
  value : InteractionWord
  initOffset : InteractionWord
  initSize : InteractionWord
  saltArg : InteractionWord

namespace CreateOperands

def createLocal (operands : CreateOperands) : CreateLocal where
  initOffset := operands.initOffset
  initSize := operands.initSize

end CreateOperands

/-- Protected caller-frame data needed to normalize an external request. -/
structure ExternalFrame where
  machine : EvmYul.MachineState
  codeOwner : InteractionAddress
  source : InteractionAddress
  apparentCallValue : InteractionWord
  permission : Bool

namespace ExternalFrame

def ofShared {τ : EvmYul.OperationType}
    (state : EvmYul.SharedState τ) : ExternalFrame where
  machine := state.toMachineState
  codeOwner := state.executionEnv.codeOwner
  source := state.executionEnv.source
  apparentCallValue := state.executionEnv.weiValue
  permission := state.executionEnv.perm

def calldata (frame : ExternalFrame) (callLocal : CallLocal) : ByteArray :=
  frame.machine.memory.readWithPadding
    callLocal.inputOffset.toNat callLocal.inputSize.toNat

def initCode (frame : ExternalFrame) (createLocal : CreateLocal) : ByteArray :=
  frame.machine.memory.readWithPadding
    createLocal.initOffset.toNat createLocal.initSize.toNat

def callRequest (frame : ExternalFrame)
    (kind : CallKind) (operands : CallOperands) : CallRequest :=
  let target := EvmYul.AccountAddress.ofUInt256 operands.address
  let callLocal := operands.callLocal
  match kind with
  | .call =>
      { kind := kind
        requestedGas := operands.requestedGas
        caller := frame.codeOwner
        recipient := target
        codeAddress := target
        transferValue := operands.valueArg
        apparentValue := operands.valueArg
        calldata := frame.calldata callLocal
        permission := frame.permission }
  | .callcode =>
      { kind := kind
        requestedGas := operands.requestedGas
        caller := frame.codeOwner
        recipient := frame.codeOwner
        codeAddress := target
        transferValue := operands.valueArg
        apparentValue := operands.valueArg
        calldata := frame.calldata callLocal
        permission := frame.permission }
  | .delegatecall =>
      { kind := kind
        requestedGas := operands.requestedGas
        caller := frame.source
        recipient := frame.codeOwner
        codeAddress := target
        transferValue := EvmYul.UInt256.ofNat 0
        apparentValue := frame.apparentCallValue
        calldata := frame.calldata callLocal
        permission := frame.permission }
  | .staticcall =>
      { kind := kind
        requestedGas := operands.requestedGas
        caller := frame.codeOwner
        recipient := target
        codeAddress := target
        transferValue := EvmYul.UInt256.ofNat 0
        apparentValue := EvmYul.UInt256.ofNat 0
        calldata := frame.calldata callLocal
        permission := false }

def createRequest (frame : ExternalFrame)
    (kind : CreateKind) (operands : CreateOperands) : CreateRequest :=
  { kind := kind
    creator := frame.codeOwner
    value := operands.value
    initCode := frame.initCode operands.createLocal
    salt :=
      match kind with
      | .create => none
      | .create2 => some operands.saltArg
    permission := frame.permission }

end ExternalFrame

namespace CallKind

def canonicalOperands : CallKind → CallOperands → CallOperands
  | .call, operands => operands
  | .callcode, operands => operands
  | .delegatecall, operands =>
      { operands with valueArg := EvmYul.UInt256.ofNat 0 }
  | .staticcall, operands =>
      { operands with valueArg := EvmYul.UInt256.ofNat 0 }

def args : CallKind → CallOperands → List InteractionWord
  | .call, operands
  | .callcode, operands =>
      [operands.requestedGas, operands.address, operands.valueArg,
        operands.inputOffset, operands.inputSize, operands.outputOffset,
        operands.outputSize]
  | .delegatecall, operands
  | .staticcall, operands =>
      [operands.requestedGas, operands.address, operands.inputOffset,
        operands.inputSize, operands.outputOffset, operands.outputSize]

@[simp] theorem args_length (kind : CallKind) (operands : CallOperands) :
    (kind.args operands).length = kind.inputArity := by
  cases kind <;> rfl

def evmOperands? :
    CallKind → InteractionStack →
      Option (InteractionStack × CallOperands)
  | .call, stack =>
      match stack.pop7 with
      | some ⟨rest, gas, address, value, inputOffset, inputSize,
          outputOffset, outputSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := value
                inputOffset := inputOffset
                inputSize := inputSize
                outputOffset := outputOffset
                outputSize := outputSize })
      | none => none
  | .callcode, stack =>
      match stack.pop7 with
      | some ⟨rest, gas, address, value, inputOffset, inputSize,
          outputOffset, outputSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := value
                inputOffset := inputOffset
                inputSize := inputSize
                outputOffset := outputOffset
                outputSize := outputSize })
      | none => none
  | .delegatecall, stack =>
      match stack.pop6 with
      | some ⟨rest, gas, address, inputOffset, inputSize,
          outputOffset, outputSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := EvmYul.UInt256.ofNat 0
                inputOffset := inputOffset
                inputSize := inputSize
                outputOffset := outputOffset
                outputSize := outputSize })
      | none => none
  | .staticcall, stack =>
      match stack.pop6 with
      | some ⟨rest, gas, address, inputOffset, inputSize,
          outputOffset, outputSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := EvmYul.UInt256.ofNat 0
                inputOffset := inputOffset
                inputSize := inputSize
                outputOffset := outputOffset
                outputSize := outputSize })
      | none => none

@[simp] theorem evmOperands?_args
    (kind : CallKind) (operands : CallOperands)
    (rest : InteractionStack) :
    kind.evmOperands? (kind.args operands ++ rest) =
      some (rest, kind.canonicalOperands operands) := by
  cases kind <;> rfl

/--
Intrinsic static-mode legality checked by the suspended caller before an
external request is exposed.
-/
def allowedIn (kind : CallKind) (frame : ExternalFrame)
    (operands : CallOperands) : Bool :=
  match kind with
  | .call =>
      frame.permission ||
        operands.valueArg == EvmYul.UInt256.ofNat 0
  | .callcode | .delegatecall | .staticcall => true

end CallKind

namespace CreateKind

def canonicalOperands : CreateKind → CreateOperands → CreateOperands
  | .create, operands =>
      { operands with saltArg := EvmYul.UInt256.ofNat 0 }
  | .create2, operands => operands

def args : CreateKind → CreateOperands → List InteractionWord
  | .create, operands =>
      [operands.value, operands.initOffset, operands.initSize]
  | .create2, operands =>
      [operands.value, operands.initOffset, operands.initSize,
        operands.saltArg]

@[simp] theorem args_length (kind : CreateKind) (operands : CreateOperands) :
    (kind.args operands).length = kind.inputArity := by
  cases kind <;> rfl

def evmOperands? :
    CreateKind → InteractionStack →
      Option (InteractionStack × CreateOperands)
  | .create, stack =>
      match stack.pop3 with
      | some ⟨rest, value, initOffset, initSize⟩ =>
          some
            (rest,
              { value := value
                initOffset := initOffset
                initSize := initSize
                saltArg := EvmYul.UInt256.ofNat 0 })
      | none => none
  | .create2, stack =>
      match stack.pop4 with
      | some ⟨rest, value, initOffset, initSize, salt⟩ =>
          some
            (rest,
              { value := value
                initOffset := initOffset
                initSize := initSize
                saltArg := salt })
      | none => none

@[simp] theorem evmOperands?_args
    (kind : CreateKind) (operands : CreateOperands)
    (rest : InteractionStack) :
    kind.evmOperands? (kind.args operands ++ rest) =
      some (rest, kind.canonicalOperands operands) := by
  cases kind <;> rfl

end CreateKind

inductive ResourceQuery where
  | gas
  | msize
  deriving DecidableEq, Repr

inductive ExternalRequest where
  | call : CallRequest → ExternalRequest
  | create : CreateRequest → ExternalRequest

inductive Query where
  | resource : ResourceQuery → Query
  | external : OpenWorld → ExternalRequest → Query

structure CallResponse where
  success : Bool
  returnData : ByteArray
  postWorld : OpenWorld

namespace CallResponse

def statusWord (response : CallResponse) : InteractionWord :=
  if response.success then
    EvmYul.UInt256.ofNat 1
  else
    EvmYul.UInt256.ofNat 0

end CallResponse

structure CreateResponse where
  address : InteractionWord
  returnData : ByteArray
  postWorld : OpenWorld

namespace CallLocal

def finishMachine (callLocal : CallLocal) (machine : EvmYul.MachineState)
    (returnData : ByteArray) : EvmYul.MachineState :=
  machine.finishExternalCall returnData
    callLocal.inputOffset callLocal.inputSize
    callLocal.outputOffset callLocal.outputSize

end CallLocal

namespace CreateLocal

def finishMachine (createLocal : CreateLocal) (machine : EvmYul.MachineState)
    (returnData : ByteArray) : EvmYul.MachineState :=
  machine.finishExternalCall returnData
    createLocal.initOffset createLocal.initSize
    (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)

end CreateLocal

def Answer : Query → Type
  | .resource _ => InteractionWord
  | .external _ (.call _) => CallResponse
  | .external _ (.create _) => CreateResponse

universe u1 v1 u2 v2 u3 v3 w1 w2

/--
The one ordered carrier for resource observations and open-world effects.
-/
inductive Interaction (Error : Type u1) (Result : Type v1) :
    Type (max u1 v1) where
  | done : Except Error Result → Interaction Error Result
  | request :
      (query : Query) →
      (Answer query → Interaction Error Result) →
      Interaction Error Result

namespace Interaction

def pure {Error : Type u1} {Result : Type v1}
    (value : Result) : Interaction Error Result :=
  .done (.ok value)

def error {Error : Type u1} {Result : Type v1}
    (err : Error) : Interaction Error Result :=
  .done (.error err)

def bind {Error : Type u1} {Source : Type v1} {Target : Type w1}
    (result : Interaction Error Source)
    (next : Source → Interaction Error Target) :
    Interaction Error Target :=
  match result with
  | .done (.ok value) => next value
  | .done (.error err) => .done (.error err)
  | .request query resume =>
      .request query fun answer => bind (resume answer) next

def map {Error : Type u1} {Source : Type v1} {Target : Type w1}
    (f : Source → Target) (result : Interaction Error Source) :
    Interaction Error Target :=
  bind result fun value => pure (f value)

@[simp] theorem bind_done_ok
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    (value : Source) (next : Source → Interaction Error Target) :
    bind (.done (.ok value)) next = next value := rfl

@[simp] theorem bind_done_error
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    (err : Error) (next : Source → Interaction Error Target) :
    bind (.done (.error err)) next =
      (.done (.error err) : Interaction Error Target) := rfl

theorem bind_request
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    (query : Query)
    (resume : Answer query → Interaction Error Source)
    (next : Source → Interaction Error Target) :
    bind (.request query resume) next =
      .request query fun answer => bind (resume answer) next := rfl

inductive ExceptRel
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    (errorRel : Error₁ → Error₂ → Prop)
    (resultRel : Result₁ → Result₂ → Prop) :
    Except Error₁ Result₁ → Except Error₂ Result₂ → Prop where
  | error {left right} :
      errorRel left right →
      ExceptRel errorRel resultRel (.error left) (.error right)
  | ok {left right} :
      resultRel left right →
      ExceptRel errorRel resultRel (.ok left) (.ok right)

/--
Structural open-world equivalence. Related computations expose the exact same
query and remain related for every exact shared answer.
-/
inductive Rel
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    (doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop) :
    Interaction Error₁ Result₁ →
    Interaction Error₂ Result₂ → Prop where
  | done {left right} :
      doneRel left right →
      Rel doneRel (.done left) (.done right)
  | request {query} {left right} :
      (∀ answer, Rel doneRel (left answer) (right answer)) →
      Rel doneRel (.request query left) (.request query right)

namespace Rel

theorem refl
    {Error : Type u1} {Result : Type v1}
    {doneRel :
      Except Error Result → Except Error Result → Prop}
    (hDone : ∀ result, doneRel result result)
    (interaction : Interaction Error Result) :
    Rel doneRel interaction interaction := by
  induction interaction with
  | done result =>
      exact .done (hDone result)
  | request query resume ih =>
      exact .request ih

theorem symm
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel left right) :
    Rel (fun rightDone leftDone => doneRel leftDone rightDone)
      right left := by
  induction hRel with
  | done hDone =>
      exact .done hDone
  | request hResume ih =>
      exact .request ih

theorem trans
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {Error₃ : Type u3} {Result₃ : Type v3}
    {doneRel₁₂ :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {doneRel₂₃ :
      Except Error₂ Result₂ → Except Error₃ Result₃ → Prop}
    {left : Interaction Error₁ Result₁}
    {middle : Interaction Error₂ Result₂}
    {right : Interaction Error₃ Result₃}
    (hLeft : Rel doneRel₁₂ left middle)
    (hRight : Rel doneRel₂₃ middle right) :
    Rel
      (fun leftDone rightDone =>
        ∃ middleDone,
          doneRel₁₂ leftDone middleDone ∧
            doneRel₂₃ middleDone rightDone)
      left right := by
  induction hLeft generalizing right with
  | done hDone =>
      cases hRight with
      | done hRightDone =>
          exact .done ⟨_, hDone, hRightDone⟩
  | request hResume ih =>
      cases hRight with
      | request hRightResume =>
          exact .request fun answer =>
            ih answer (hRightResume answer)

theorem bind
    {Error₁ : Type u1} {Source₁ : Type v1} {Target₁ : Type w1}
    {Error₂ : Type u2} {Source₂ : Type v2} {Target₂ : Type w2}
    {errorRel : Error₁ → Error₂ → Prop}
    {sourceRel : Source₁ → Source₂ → Prop}
    {targetRel : Target₁ → Target₂ → Prop}
    {left : Interaction Error₁ Source₁}
    {right : Interaction Error₂ Source₂}
    {leftNext : Source₁ → Interaction Error₁ Target₁}
    {rightNext : Source₂ → Interaction Error₂ Target₂}
    (hResult :
      Rel (ExceptRel errorRel sourceRel) left right)
    (hNext :
      ∀ leftValue rightValue,
        sourceRel leftValue rightValue →
          Rel (ExceptRel errorRel targetRel)
            (leftNext leftValue) (rightNext rightValue)) :
    Rel (ExceptRel errorRel targetRel)
      (Interaction.bind left leftNext)
      (Interaction.bind right rightNext) := by
  induction hResult with
  | done hDone =>
      cases hDone with
      | error hError =>
          exact .done (.error hError)
      | ok hValue =>
          exact hNext _ _ hValue
  | request hResume ih =>
      exact .request fun answer => ih answer

theorem done_left
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {leftDone : Except Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel (.done leftDone) right) :
    ∃ rightDone,
      right = .done rightDone ∧ doneRel leftDone rightDone := by
  cases hRel with
  | done hDone =>
      exact ⟨_, rfl, hDone⟩

theorem request_left
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {query : Query}
    {left : Answer query → Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel (.request query left) right) :
    ∃ rightResume : Answer query → Interaction Error₂ Result₂,
      right = .request query rightResume ∧
        ∀ answer, Rel doneRel (left answer) (rightResume answer) := by
  cases hRel with
  | request hResume =>
      exact ⟨_, rfl, hResume⟩

end Rel

/-- A deterministic client for the open interaction tree. -/
abbrev Strategy := (query : Query) → Answer query

def interpret {Error : Type u1} {Result : Type v1}
    (strategy : Strategy) :
    Interaction Error Result → Except Error Result
  | .done result => result
  | .request query resume =>
      interpret strategy (resume (strategy query))

theorem Rel.interpret
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (strategy : Strategy)
    (hRel : Rel doneRel left right) :
    doneRel (interpret strategy left) (interpret strategy right) := by
  induction hRel with
  | done hDone =>
      exact hDone
  | @request query left right hResume ih =>
      exact ih (strategy query)

end Interaction

end Simulation
end EvmCompiler
