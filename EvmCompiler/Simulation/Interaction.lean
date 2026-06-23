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

theorem eq_toYulOperation_of_ofYulOperation?_eq_some
    {op : EvmYul.Operation .Yul} {kind : ExternalKind}
    (hKind : ofYulOperation? op = some kind) :
    op = kind.toYulOperation := by
  cases op <;> rename_i family <;> cases family <;>
    simp [ofYulOperation?, CallKind.ofYulOperation?,
      CreateKind.ofYulOperation?] at hKind
  all_goals subst kind <;> rfl

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
Appending an opaque suffix below a complete CALL-family operand prefix leaves
the parsed operands unchanged and appends the suffix only to the remainder.
-/
theorem evmOperands?_append_of_some
    (kind : CallKind) {stack rest : InteractionStack}
    {operands : CallOperands} (hidden : InteractionStack)
    (hOperands :
      kind.evmOperands? stack = some (rest, operands)) :
    kind.evmOperands? (stack ++ hidden) =
      some (rest ++ hidden, operands) := by
  cases kind with
  | call | callcode =>
      unfold evmOperands? at hOperands ⊢
      cases hPop : stack.pop7 with
      | none =>
          simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, gas, address, value, inputOffset, inputSize,
              outputOffset, outputSize⟩
          have hAppend :
              (stack ++ hidden).pop7 =
                some
                  (parsedRest ++ hidden, gas, address, value,
                    inputOffset, inputSize, outputOffset, outputSize) := by
            cases stack with
            | nil => simp [EvmYul.Stack.pop7] at hPop
            | cons a stack =>
                cases stack with
                | nil => simp [EvmYul.Stack.pop7] at hPop
                | cons b stack =>
                    cases stack with
                    | nil => simp [EvmYul.Stack.pop7] at hPop
                    | cons c stack =>
                        cases stack with
                        | nil => simp [EvmYul.Stack.pop7] at hPop
                        | cons d stack =>
                            cases stack with
                            | nil => simp [EvmYul.Stack.pop7] at hPop
                            | cons e stack =>
                                cases stack with
                                | nil => simp [EvmYul.Stack.pop7] at hPop
                                | cons f stack =>
                                    cases stack with
                                    | nil =>
                                        simp [EvmYul.Stack.pop7] at hPop
                                    | cons g tail =>
                                        simp [EvmYul.Stack.pop7] at hPop ⊢
                                        rcases hPop with
                                          ⟨rfl, rfl, rfl, rfl, rfl, rfl,
                                            rfl, rfl⟩
                                        simp
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simp [hAppend]
  | delegatecall | staticcall =>
      unfold evmOperands? at hOperands ⊢
      cases hPop : stack.pop6 with
      | none =>
          simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, gas, address, inputOffset, inputSize,
              outputOffset, outputSize⟩
          have hAppend :
              (stack ++ hidden).pop6 =
                some
                  (parsedRest ++ hidden, gas, address, inputOffset,
                    inputSize, outputOffset, outputSize) := by
            cases stack with
            | nil => simp [EvmYul.Stack.pop6] at hPop
            | cons a stack =>
                cases stack with
                | nil => simp [EvmYul.Stack.pop6] at hPop
                | cons b stack =>
                    cases stack with
                    | nil => simp [EvmYul.Stack.pop6] at hPop
                    | cons c stack =>
                        cases stack with
                        | nil => simp [EvmYul.Stack.pop6] at hPop
                        | cons d stack =>
                            cases stack with
                            | nil => simp [EvmYul.Stack.pop6] at hPop
                            | cons e stack =>
                                cases stack with
                                | nil => simp [EvmYul.Stack.pop6] at hPop
                                | cons f tail =>
                                    simp [EvmYul.Stack.pop6] at hPop ⊢
                                    rcases hPop with
                                      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                                    simp
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simp [hAppend]

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

/--
Appending an opaque suffix below a complete CREATE-family operand prefix
leaves the parsed operands unchanged and appends the suffix only to the
remainder.
-/
theorem evmOperands?_append_of_some
    (kind : CreateKind) {stack rest : InteractionStack}
    {operands : CreateOperands} (hidden : InteractionStack)
    (hOperands :
      kind.evmOperands? stack = some (rest, operands)) :
    kind.evmOperands? (stack ++ hidden) =
      some (rest ++ hidden, operands) := by
  cases kind with
  | create =>
      unfold evmOperands? at hOperands ⊢
      cases hPop : stack.pop3 with
      | none =>
          simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, value, inputOffset, inputSize⟩
          have hAppend :
              (stack ++ hidden).pop3 =
                some
                  (parsedRest ++ hidden, value, inputOffset, inputSize) := by
            cases stack with
            | nil => simp [EvmYul.Stack.pop3] at hPop
            | cons a stack =>
                cases stack with
                | nil => simp [EvmYul.Stack.pop3] at hPop
                | cons b stack =>
                    cases stack with
                    | nil => simp [EvmYul.Stack.pop3] at hPop
                    | cons c tail =>
                        simp [EvmYul.Stack.pop3] at hPop ⊢
                        rcases hPop with ⟨rfl, rfl, rfl, rfl⟩
                        simp
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simp [hAppend]
  | create2 =>
      unfold evmOperands? at hOperands ⊢
      cases hPop : stack.pop4 with
      | none =>
          simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, value, inputOffset, inputSize, salt⟩
          have hAppend :
              (stack ++ hidden).pop4 =
                some
                  (parsedRest ++ hidden, value, inputOffset, inputSize,
                    salt) := by
            cases stack with
            | nil => simp [EvmYul.Stack.pop4] at hPop
            | cons a stack =>
                cases stack with
                | nil => simp [EvmYul.Stack.pop4] at hPop
                | cons b stack =>
                    cases stack with
                    | nil => simp [EvmYul.Stack.pop4] at hPop
                    | cons c stack =>
                        cases stack with
                        | nil => simp [EvmYul.Stack.pop4] at hPop
                        | cons d tail =>
                            simp [EvmYul.Stack.pop4] at hPop ⊢
                            rcases hPop with ⟨rfl, rfl, rfl, rfl, rfl⟩
                            simp
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simp [hAppend]

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

/-- One canonical answer used only to select a branch of an open interaction
tree. Compiler theorems still quantify over every answer through `AllDone`. -/
def Query.defaultAnswer : (query : Query) → Answer query
  | .resource _ => EvmYul.UInt256.ofNat 0
  | .external world (.call _) =>
      { success := false, returnData := default, postWorld := world }
  | .external world (.create _) =>
      { address := EvmYul.UInt256.ofNat 0, returnData := default,
        postWorld := world }

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

/-- One exact query/answer exchange along a concrete interaction branch. -/
structure Exchange where
  query : Query
  answer : Answer query

abbrev Transcript := List Exchange

/-- A concrete ordered transcript is a prefix of an interaction tree. Unlike
`Executes`, this relation need not end at a terminal leaf. -/
inductive Follows {Error : Type u1} {Result : Type v1} :
    Interaction Error Result → Transcript → Prop where
  | nil (interaction : Interaction Error Result) : Follows interaction []
  | request {query : Query}
      {resume : Answer query → Interaction Error Result}
      {answer : Answer query} {transcript : Transcript} :
      Follows (resume answer) transcript →
      Follows (.request query resume)
        ({ query := query, answer := answer } :: transcript)

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

def tryCatch {Error : Type u1} {Result : Type v1}
    (result : Interaction Error Result)
    (handler : Error → Interaction Error Result) :
    Interaction Error Result :=
  match result with
  | .done (.error err) => handler err
  | .done (.ok value) => .done (.ok value)
  | .request query resume =>
      .request query fun answer => tryCatch (resume answer) handler

instance {Error : Type u1} : Monad (Interaction Error) where
  pure := pure
  bind := bind
  map := map

instance {Error : Type u1} : MonadExceptOf Error (Interaction Error) where
  throw := error
  tryCatch := tryCatch

/--
A property of every terminal leaf of an open interaction tree.

Unlike a concrete execution transcript, `AllDone` quantifies over every
possible answer at every request. Pass proofs use it for branch-independent
invariants such as program-counter advancement.
-/
inductive AllDone
    {Error : Type u1} {Result : Type v1}
    (property : Except Error Result → Prop) :
    Interaction Error Result → Prop where
  | done {outcome} :
      property outcome →
      AllDone property (.done outcome)
  | request {query : Query}
      {resume : Answer query → Interaction Error Result} :
      (∀ answer, AllDone property (resume answer)) →
      AllDone property (.request query resume)

namespace AllDone

/-- A universal terminal property in particular holds on the canonical branch.
This eliminates no open-world quantification; it merely witnesses that an
interaction tree has a terminal leaf. -/
theorem exists_done
    {Error : Type u1} {Result : Type v1}
    {property : Except Error Result → Prop}
    {interaction : Interaction Error Result}
    (hAll : AllDone property interaction) :
    ∃ outcome, property outcome := by
  induction interaction with
  | done outcome =>
      cases hAll with
      | done hProperty => exact ⟨outcome, hProperty⟩
  | request query resume ih =>
      cases hAll with
      | request hResume =>
          exact ih query.defaultAnswer (hResume query.defaultAnswer)

theorem trivial
    {Error : Type u1} {Result : Type v1}
    (interaction : Interaction Error Result) :
    AllDone (fun _ => True) interaction := by
  induction interaction with
  | done outcome =>
      exact .done True.intro
  | request query resume ih =>
      exact .request ih

/-- Intersect two leaf properties over the same open interaction tree. -/
theorem inter
    {Error : Type u1} {Result : Type v1}
    {left right : Except Error Result → Prop}
    {interaction : Interaction Error Result}
    (hLeft : AllDone left interaction)
    (hRight : AllDone right interaction) :
    AllDone (fun outcome => left outcome ∧ right outcome) interaction := by
  induction hLeft with
  | done hLeftDone =>
      cases hRight with
      | done hRightDone => exact .done ⟨hLeftDone, hRightDone⟩
  | request hLeftResume ih =>
      cases hRight with
      | request hRightResume =>
          exact .request fun answer => ih answer (hRightResume answer)

theorem mono
    {Error : Type u1} {Result : Type v1}
    {left right : Except Error Result → Prop}
    {interaction : Interaction Error Result}
    (hInteraction : AllDone left interaction)
    (hProperty : ∀ outcome, left outcome → right outcome) :
    AllDone right interaction := by
  induction hInteraction with
  | done hDone =>
      exact .done (hProperty _ hDone)
  | request hResume ih =>
      exact .request ih

theorem bind
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {sourceProperty : Except Error Source → Prop}
    {targetProperty : Except Error Target → Prop}
    {interaction : Interaction Error Source}
    {next : Source → Interaction Error Target}
    (hInteraction : AllDone sourceProperty interaction)
    (hError :
      ∀ err, sourceProperty (.error err) →
        targetProperty (.error err))
    (hNext :
      ∀ value, sourceProperty (.ok value) →
        AllDone targetProperty (next value)) :
    AllDone targetProperty (Interaction.bind interaction next) := by
  induction hInteraction with
  | @done outcome hDone =>
      cases outcome with
      | error err =>
          exact .done (hError err hDone)
      | ok value =>
          exact hNext value hDone
  | request hResume ih =>
      exact .request ih

theorem map
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {sourceProperty : Except Error Source → Prop}
    {targetProperty : Except Error Target → Prop}
    {interaction : Interaction Error Source}
    (f : Source → Target)
    (hInteraction : AllDone sourceProperty interaction)
    (hError :
      ∀ err, sourceProperty (.error err) →
        targetProperty (.error err))
    (hValue :
      ∀ value, sourceProperty (.ok value) →
        targetProperty (.ok (f value))) :
    AllDone targetProperty (Interaction.map f interaction) := by
  exact
    bind hInteraction hError fun value hSource =>
      .done (hValue value hSource)

/--
Two continuations are interchangeable when they agree at every successful
leaf reachable from the first interaction.
-/
theorem bind_congr
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {property : Except Error Source → Prop}
    {interaction : Interaction Error Source}
    {left right : Source → Interaction Error Target}
    (hInteraction : AllDone property interaction)
    (hNext :
      ∀ value, property (.ok value) →
        left value = right value) :
    Interaction.bind interaction left =
      Interaction.bind interaction right := by
  induction interaction generalizing left right with
  | done outcome =>
      cases hInteraction with
      | done hDone =>
        cases outcome with
        | error err =>
            rfl
        | ok value =>
            exact hNext value hDone
  | request query resume ih =>
      cases hInteraction with
      | request hResume =>
        change
          Interaction.request query
              (fun answer =>
                Interaction.bind (resume answer) left) =
            Interaction.request query
              (fun answer =>
                Interaction.bind (resume answer) right)
        congr
        funext answer
        exact ih answer (hResume answer) hNext

/-- Invert a terminal property through a bind into its reachable continuations. -/
theorem bind_inv
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {targetProperty : Except Error Target → Prop}
    {interaction : Interaction Error Source}
    {next : Source → Interaction Error Target}
    (hResult : AllDone targetProperty (Interaction.bind interaction next)) :
    AllDone
      (fun outcome =>
        match outcome with
        | .error err => targetProperty (.error err)
        | .ok value => AllDone targetProperty (next value))
      interaction := by
  induction interaction with
  | done outcome =>
      cases outcome with
      | error err =>
          cases hResult with
          | done hDone => exact .done hDone
      | ok value =>
          exact .done hResult
  | request query resume ih =>
      cases hResult with
      | request hResume =>
          exact .request fun answer => ih answer (hResume answer)

end AllDone

/-- Every open-world terminal branch returns successfully. -/
def Successful
    {Error : Type u1} {Result : Type v1}
    (interaction : Interaction Error Result) : Prop :=
  AllDone
    (fun outcome =>
      match outcome with
      | .error _ => False
      | .ok _ => True)
    interaction

namespace Successful

theorem bind_inv
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {interaction : Interaction Error Source}
    {next : Source → Interaction Error Target}
    (hResult : Successful (Interaction.bind interaction next)) :
    AllDone
      (fun outcome =>
        match outcome with
        | .error _ => False
        | .ok value => Successful (next value))
      interaction :=
  AllDone.bind_inv hResult

/-- Successful continuation execution implies that the bound prefix itself
has no failing open-world branch. -/
theorem bind_left
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {interaction : Interaction Error Source}
    {next : Source → Interaction Error Target}
    (hResult : Successful (Interaction.bind interaction next)) :
    Successful interaction := by
  apply AllDone.mono (bind_inv hResult)
  intro outcome hOutcome
  cases outcome with
  | error _ => exact hOutcome
  | ok _ => trivial

theorem error_false
    {Error : Type u1} {Result : Type v1} (err : Error)
    (hResult : Successful (Interaction.error (Result := Result) err)) :
    False := by
  cases hResult with
  | done hDone => exact hDone

end Successful

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

@[simp] theorem bind_pure
    {Error : Type u1} {Result : Type v1}
    (result : Interaction Error Result) :
    bind result pure = result := by
  induction result with
  | done outcome =>
      cases outcome <;> rfl
  | request query resume ih =>
      simp only [bind_request]
      congr
      funext answer
      exact ih answer

theorem bind_assoc
    {Error : Type u1} {First : Type v1}
    {Second : Type w1} {Third : Type u2}
    (result : Interaction Error First)
    (next : First → Interaction Error Second)
    (finish : Second → Interaction Error Third) :
    bind (bind result next) finish =
      bind result fun value => bind (next value) finish := by
  induction result with
  | done outcome =>
      cases outcome <;> rfl
  | request query resume ih =>
      simp only [bind_request]
      congr
      funext answer
      exact ih answer

@[simp] theorem monad_pure_bind
    {Error : Type u1} {Source Target : Type v1}
    (value : Source) (next : Source → Interaction Error Target) :
    (do
      let source ← (pure value : Interaction Error Source)
      next source) =
      next value := rfl

@[simp] theorem monad_error_bind
    {Error : Type u1} {Source Target : Type v1}
    (err : Error) (next : Source → Interaction Error Target) :
    (do
      let source ← (error err : Interaction Error Source)
      next source) =
      error err := rfl

@[simp] theorem monad_bind_pure
    {Error : Type u1} {Result : Type v1}
    (result : Interaction Error Result) :
    (do
      let value ← result
      pure value) =
      result := by
  exact bind_pure result

/--
A concrete branch through an open interaction tree.

The transcript records the exact ordered query and answer at every suspension.
It is external-world behavior, not compiler-generated evidence.
-/
inductive Executes
    {Error : Type u1} {Result : Type v1} :
    Interaction Error Result →
    Transcript →
    Except Error Result →
    Prop where
  | done (outcome : Except Error Result) :
      Executes (.done outcome) [] outcome
  | request {query : Query}
      {resume : Answer query → Interaction Error Result}
      (answer : Answer query)
      {transcript : Transcript}
      {outcome : Except Error Result}
      (tail : Executes (resume answer) transcript outcome) :
      Executes (.request query resume)
        ({ query := query, answer := answer } :: transcript) outcome

namespace Executes

/-- Every terminal execution also witnesses its transcript as a prefix. -/
theorem follows
    {Error : Type u1} {Result : Type v1}
    {interaction : Interaction Error Result}
    {transcript : Transcript} {outcome : Except Error Result}
    (hExec : Executes interaction transcript outcome) :
    Follows interaction transcript := by
  induction hExec with
  | done outcome => exact .nil _
  | request answer tail ih => exact .request ih

theorem bind_ok
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {first : Interaction Error Source}
    {next : Source → Interaction Error Target}
    {firstTranscript restTranscript : Transcript}
    {value : Source} {outcome : Except Error Target}
    (hFirst : Executes first firstTranscript (.ok value))
    (hRest : Executes (next value) restTranscript outcome) :
    Executes (bind first next)
      (firstTranscript ++ restTranscript) outcome := by
  generalize hOutcome : (.ok value : Except Error Source) = firstOutcome
    at hFirst
  induction hFirst generalizing value restTranscript outcome with
  | done firstOutcome =>
      cases hOutcome
      simpa using hRest
  | request answer tail ih =>
      simpa [bind_request] using
        Executes.request answer (ih hRest hOutcome)

theorem bind_error
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {first : Interaction Error Source}
    {next : Source → Interaction Error Target}
    {transcript : Transcript} {err : Error}
    (hFirst : Executes first transcript (.error err)) :
    Executes (bind first next) transcript (.error err) := by
  generalize hOutcome : (.error err : Except Error Source) = firstOutcome
    at hFirst
  induction hFirst generalizing err with
  | done firstOutcome =>
      cases hOutcome
      exact Executes.done (.error err)
  | request answer tail ih =>
      simpa [bind_request] using
        Executes.request answer (ih hOutcome)

theorem bind_cases
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {first : Interaction Error Source}
    {next : Source → Interaction Error Target}
    {transcript : Transcript} {outcome : Except Error Target}
    (hExec : Executes (bind first next) transcript outcome) :
    (∃ err,
        outcome = .error err ∧
          Executes first transcript (.error err)) ∨
      ∃ value firstTranscript restTranscript,
        transcript = firstTranscript ++ restTranscript ∧
          Executes first firstTranscript (.ok value) ∧
            Executes (next value) restTranscript outcome := by
  induction first generalizing transcript outcome with
  | done firstOutcome =>
      cases firstOutcome with
      | error err =>
          change Executes (.done (.error err)) transcript outcome at hExec
          cases hExec
          exact .inl ⟨err, rfl, Executes.done _⟩
      | ok value =>
          exact
            .inr
              ⟨value, [], transcript, by simp, Executes.done _, hExec⟩
  | request query resume ih =>
      change
        Executes
          (.request query fun answer => bind (resume answer) next)
          transcript outcome at hExec
      cases hExec with
      | request answer tail =>
          rcases ih answer tail with hError | hOk
          · rcases hError with ⟨err, hOutcome, hFirst⟩
            exact
              .inl
                ⟨err, hOutcome, Executes.request answer hFirst⟩
          · rcases hOk with
              ⟨value, firstTranscript, restTranscript,
                hTranscript, hFirst, hRest⟩
            exact
              .inr
                ⟨value,
                  { query := query, answer := answer } :: firstTranscript,
                  restTranscript,
                  by simp [hTranscript],
                  Executes.request answer hFirst,
                  hRest⟩

end Executes

namespace Follows

/-- Binding after an interaction cannot erase an already exposed transcript. -/
theorem bind
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {first : Interaction Error Source}
    {next : Source -> Interaction Error Target}
    {transcript : Transcript}
    (hFollow : Follows first transcript) :
    Follows (Interaction.bind first next) transcript := by
  induction hFollow with
  | nil interaction => exact .nil _
  | request tail ih => exact .request ih

/-- A completed left side followed by a prefix of its continuation yields the
concatenated prefix of the monadic bind. -/
theorem bind_ok
    {Error : Type u1} {Source : Type v1} {Target : Type w1}
    {first : Interaction Error Source}
    {next : Source -> Interaction Error Target}
    {firstTranscript restTranscript : Transcript}
    {value : Source}
    (hFirst : Executes first firstTranscript (.ok value))
    (hRest : Follows (next value) restTranscript) :
    Follows (Interaction.bind first next)
      (firstTranscript ++ restTranscript) := by
  generalize hOutcome : (.ok value : Except Error Source) = firstOutcome
    at hFirst
  induction hFirst generalizing value restTranscript with
  | done firstOutcome =>
      cases hOutcome
      simpa using hRest
  | request answer tail ih =>
      exact .request (ih hRest hOutcome)

/-- Invert one followed request at its first exchange. -/
theorem request_inv
    {Error : Type u1} {Result : Type v1}
    {query : Query}
    {resume : Answer query -> Interaction Error Result}
    {exchange : Exchange} {transcript : Transcript}
    (hFollow : Follows (.request query resume) (exchange :: transcript)) :
    exists answer,
      exchange = { query := query, answer := answer } /\
        Follows (resume answer) transcript := by
  cases hFollow with
  | request tail => exact ⟨_, rfl, tail⟩

end Follows

namespace AllDone

/-- Select one concrete branch witnessing a universal terminal property. -/
theorem exists_executes
    {Error : Type u1} {Result : Type v1}
    {property : Except Error Result -> Prop}
    {interaction : Interaction Error Result}
    (hAll : AllDone property interaction) :
    exists transcript outcome,
      Executes interaction transcript outcome /\ property outcome := by
  induction hAll with
  | done hProperty =>
      exact ⟨[], _, Executes.done _, hProperty⟩
  | @request query resume hResume ih =>
      obtain ⟨transcript, outcome, hExec, hProperty⟩ :=
        ih query.defaultAnswer
      exact
        ⟨{ query := query, answer := query.defaultAnswer } :: transcript,
          outcome, Executes.request query.defaultAnswer hExec, hProperty⟩

/-- A property of every terminal leaf holds on any selected concrete branch. -/
theorem property_of_executes
    {Error : Type u1} {Result : Type v1}
    {property : Except Error Result -> Prop}
    {interaction : Interaction Error Result}
    {transcript : Transcript} {outcome : Except Error Result}
    (hAll : AllDone property interaction)
    (hExec : Executes interaction transcript outcome) :
    property outcome := by
  induction hExec with
  | done outcome =>
      cases hAll with
      | done hProperty => exact hProperty
  | @request query resume answer transcript outcome hTail ih =>
      cases hAll with
      | request hResume => exact ih (hResume answer)

end AllDone

namespace Executes

/-- Invert one concrete execution of a request at its first exchange. -/
theorem request_inv
    {Error : Type u1} {Result : Type v1}
    {query : Query}
    {resume : Answer query -> Interaction Error Result}
    {exchange : Exchange} {transcript : Transcript}
    {outcome : Except Error Result}
    (hExec :
      Executes (.request query resume) (exchange :: transcript) outcome) :
    exists answer,
      exchange = { query := query, answer := answer } /\
        Executes (resume answer) transcript outcome := by
  cases hExec with
  | request answer tail =>
      exact ⟨answer, rfl, tail⟩

end Executes

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

theorem mono
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel₁ doneRel₂ :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel₁ left right)
    (hDone :
      ∀ leftDone rightDone,
        doneRel₁ leftDone rightDone →
          doneRel₂ leftDone rightDone) :
    Rel doneRel₂ left right := by
  induction hRel with
  | done hResult =>
      exact .done (hDone _ _ hResult)
  | request hResume ih =>
      exact .request ih

/-- Intersect two proofs over the same open interaction tree. -/
theorem inter
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel₁ doneRel₂ :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hFirst : Rel doneRel₁ left right)
    (hSecond : Rel doneRel₂ left right) :
    Rel (fun leftDone rightDone =>
      doneRel₁ leftDone rightDone ∧ doneRel₂ leftDone rightDone)
      left right := by
  induction hFirst with
  | done hFirstDone =>
      cases hSecond with
      | done hSecondDone => exact .done ⟨hFirstDone, hSecondDone⟩
  | request hFirstResume ih =>
      cases hSecond with
      | request hSecondResume =>
          exact .request fun answer =>
            ih answer (hSecondResume answer)

theorem strengthen_left
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {property : Except Error₁ Result₁ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel left right)
    (hAll : AllDone property left) :
    Rel (fun leftDone rightDone =>
      doneRel leftDone rightDone ∧ property leftDone)
      left right := by
  induction hRel with
  | done hDone =>
      cases hAll with
      | done hProperty =>
          exact .done ⟨hDone, hProperty⟩
  | request hResume ih =>
      cases hAll with
      | request hProperty =>
          exact .request fun answer =>
            ih answer (hProperty answer)

/-- Strengthen a relation with a target-side invariant at every terminal
leaf. -/
theorem strengthen_right
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {property : Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel left right)
    (hAll : AllDone property right) :
    Rel (fun leftDone rightDone =>
      doneRel leftDone rightDone ∧ property rightDone)
      left right := by
  induction hRel with
  | done hDone =>
      cases hAll with
      | done hProperty => exact .done ⟨hDone, hProperty⟩
  | request hResume ih =>
      cases hAll with
      | request hProperty =>
          exact .request fun answer => ih answer (hProperty answer)

theorem allDone_right
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {property : Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel left right)
    (hDone :
      ∀ leftDone rightDone,
        doneRel leftDone rightDone →
          property rightDone) :
    AllDone property right := by
  induction hRel with
  | done hRelated =>
      exact .done (hDone _ _ hRelated)
  | request hResume ih =>
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

/-- Compose through a representation-transparent right boundary. -/
theorem trans_eq_right
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {doneRel :
      Except Error1 Result1 -> Except Error2 Result2 -> Prop}
    {left : Interaction Error1 Result1}
    {middle right : Interaction Error2 Result2}
    (hLeft : Rel doneRel left middle)
    (hRight : Rel Eq middle right) :
    Rel doneRel left right := by
  apply Rel.mono (Rel.trans hLeft hRight)
  intro leftDone rightDone hDone
  rcases hDone with ⟨middleDone, hRelated, hEq⟩
  subst rightDone
  exact hRelated

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

theorem bind_custom
    {Error₁ : Type u1} {Source₁ : Type v1} {Target₁ : Type w1}
    {Error₂ : Type u2} {Source₂ : Type v2} {Target₂ : Type w2}
    {sourceDoneRel :
      Except Error₁ Source₁ → Except Error₂ Source₂ → Prop}
    {targetDoneRel :
      Except Error₁ Target₁ → Except Error₂ Target₂ → Prop}
    {left : Interaction Error₁ Source₁}
    {right : Interaction Error₂ Source₂}
    {leftNext : Source₁ → Interaction Error₁ Target₁}
    {rightNext : Source₂ → Interaction Error₂ Target₂}
    (hResult : Rel sourceDoneRel left right)
    (hNext :
      ∀ leftDone rightDone,
        sourceDoneRel leftDone rightDone →
          Rel targetDoneRel
            (match leftDone with
            | .error error => .done (.error error)
            | .ok value => leftNext value)
            (match rightDone with
            | .error error => .done (.error error)
            | .ok value => rightNext value)) :
    Rel targetDoneRel
      (Interaction.bind left leftNext)
      (Interaction.bind right rightNext) := by
  induction hResult with
  | @done leftDone rightDone hDone =>
      cases leftDone <;> cases rightDone <;>
        simpa [Interaction.bind] using
          hNext _ _ hDone
  | request hResume ih =>
      exact .request fun answer => ih answer

/-- Remove a pure administrative map from the left side of a relation. -/
theorem bind_pure_left_inv
    {Error₁ : Type u1} {Source₁ : Type v1} {Target₁ : Type w1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Target₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Source₁}
    {right : Interaction Error₂ Result₂}
    {f : Source₁ → Target₁}
    (hRel :
      Rel doneRel
        (Interaction.bind left
          (fun value => Interaction.pure (f value)))
        right) :
    Rel
      (fun leftDone rightDone =>
        match leftDone with
        | .error err => doneRel (.error err) rightDone
        | .ok value => doneRel (.ok (f value)) rightDone)
      left right := by
  induction left generalizing right with
  | done outcome =>
      cases outcome with
      | error err =>
          cases hRel with
          | done hDone => exact .done hDone
      | ok value =>
          cases hRel with
          | done hDone => exact .done hDone
  | request query resume ih =>
      cases hRel with
      | request hResume =>
          exact .request fun answer => ih answer (hResume answer)

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

/--
Reconstruct a structural open-world relation from exact preservation of every
successful concrete branch. Universal source success rules out the only missing
case: a source error leaf, for which the branch premise intentionally has no
obligation.
-/
theorem of_successful_executes
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {doneRel :
      Except Error1 Result1 -> Except Error2 Result2 -> Prop}
    {left : Interaction Error1 Result1}
    {right : Interaction Error2 Result2}
    (hSuccessful : Successful left)
    (hExec :
      forall transcript leftResult,
        Executes left transcript (.ok leftResult) ->
          exists rightDone,
            Executes right transcript rightDone /\
              doneRel (.ok leftResult) rightDone) :
    Rel doneRel left right := by
  induction left generalizing right with
  | done leftDone =>
      cases leftDone with
      | error err =>
          exact False.elim (Successful.error_false err hSuccessful)
      | ok value =>
          obtain ⟨rightDone, hRightExec, hDone⟩ :=
            hExec [] value (Executes.done (.ok value))
          cases hRightExec with
          | done => exact .done hDone
  | request query resume ih =>
      cases hSuccessful with
      | request hResumeSuccessful =>
          cases right with
          | done rightDone =>
              obtain
                  ⟨tailTranscript, leftDone, hLeftTail, hLeftSuccess⟩ :=
                AllDone.exists_executes
                  (hResumeSuccessful query.defaultAnswer)
              cases leftDone with
              | error err => exact False.elim hLeftSuccess
              | ok value =>
                  obtain ⟨targetDone, hTargetExec, _hDone⟩ :=
                    hExec
                      ({ query := query, answer := query.defaultAnswer } ::
                        tailTranscript)
                      value
                      (Executes.request query.defaultAnswer hLeftTail)
                  cases hTargetExec
          | request targetQuery targetResume =>
              obtain
                  ⟨tailTranscript, leftDone, hLeftTail, hLeftSuccess⟩ :=
                AllDone.exists_executes
                  (hResumeSuccessful query.defaultAnswer)
              cases leftDone with
              | error err => exact False.elim hLeftSuccess
              | ok value =>
                  obtain ⟨targetDone, hTargetExec, _hDone⟩ :=
                    hExec
                      ({ query := query, answer := query.defaultAnswer } ::
                        tailTranscript)
                      value
                      (Executes.request query.defaultAnswer hLeftTail)
                  obtain ⟨targetAnswer, hExchange, _hTargetTail⟩ :=
                    Executes.request_inv hTargetExec
                  have hQuery : query = targetQuery :=
                    congrArg Exchange.query hExchange
                  subst targetQuery
                  exact .request fun answer => by
                    apply ih answer (hResumeSuccessful answer)
                    intro transcript leftResult hLeftExec
                    obtain ⟨rightDone, hRightExec, hDone⟩ :=
                      hExec
                        ({ query := query, answer := answer } :: transcript)
                        leftResult
                        (Executes.request answer hLeftExec)
                    obtain ⟨rightAnswer, hHead, hRightTail⟩ :=
                      Executes.request_inv hRightExec
                    cases hHead
                    exact ⟨rightDone, hRightTail, hDone⟩

/-- Reconstruct a structural open-world relation from exact preservation of
every concrete branch, including error outcomes. -/
theorem of_executes
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {doneRel :
      Except Error1 Result1 -> Except Error2 Result2 -> Prop}
    {left : Interaction Error1 Result1}
    {right : Interaction Error2 Result2}
    (hExec :
      forall transcript leftDone,
        Executes left transcript leftDone ->
          exists rightDone,
            Executes right transcript rightDone /\
              doneRel leftDone rightDone) :
    Rel doneRel left right := by
  induction left generalizing right with
  | done leftDone =>
      obtain ⟨rightDone, hRightExec, hDone⟩ :=
        hExec [] leftDone (Executes.done leftDone)
      cases hRightExec with
      | done => exact .done hDone
  | request query resume ih =>
      cases right with
      | done rightDone =>
          obtain ⟨tailTranscript, leftDone, hLeftTail, _⟩ :=
            AllDone.exists_executes
              (AllDone.trivial (resume query.defaultAnswer))
          obtain ⟨targetDone, hTargetExec, _hDone⟩ :=
            hExec
              ({ query := query, answer := query.defaultAnswer } ::
                tailTranscript)
              leftDone
              (Executes.request query.defaultAnswer hLeftTail)
          cases hTargetExec
      | request targetQuery targetResume =>
          obtain ⟨tailTranscript, leftDone, hLeftTail, _⟩ :=
            AllDone.exists_executes
              (AllDone.trivial (resume query.defaultAnswer))
          obtain ⟨targetDone, hTargetExec, _hDone⟩ :=
            hExec
              ({ query := query, answer := query.defaultAnswer } ::
                tailTranscript)
              leftDone
              (Executes.request query.defaultAnswer hLeftTail)
          obtain ⟨targetAnswer, hExchange, _hTargetTail⟩ :=
            Executes.request_inv hTargetExec
          have hQuery : query = targetQuery :=
            congrArg Exchange.query hExchange
          subst targetQuery
          exact .request fun answer => by
            apply ih answer
            intro transcript leftDone hLeftExec
            obtain ⟨rightDone, hRightExec, hDone⟩ :=
              hExec
                ({ query := query, answer := answer } :: transcript)
                leftDone
                (Executes.request answer hLeftExec)
            obtain ⟨rightAnswer, hHead, hRightTail⟩ :=
              Executes.request_inv hRightExec
            cases hHead
            exact ⟨rightDone, hRightTail, hDone⟩

/--
Structural open equivalence transports every concrete external-world branch
with the exact same ordered transcript.
-/
theorem executes
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    {transcript : Transcript}
    {leftOutcome : Except Error₁ Result₁}
    (hRel : Rel doneRel left right)
    (hExec : Executes left transcript leftOutcome) :
    ∃ rightOutcome,
      Executes right transcript rightOutcome ∧
        doneRel leftOutcome rightOutcome := by
  induction hExec generalizing right with
  | done outcome =>
      cases hRel with
      | done hDone =>
          exact ⟨_, Executes.done _, hDone⟩
  | request answer tail ih =>
      cases hRel with
      | request hResume =>
          obtain ⟨rightOutcome, hRight, hDone⟩ :=
            ih (hResume answer)
          exact
            ⟨rightOutcome, Executes.request answer hRight, hDone⟩

end Rel

/--
Forward open-world refinement with an explicit source-side truncation error.

Before truncation, the source and target expose the exact same query and all
exact shared answers remain related. A truncated source computation carries no
claim about the target suffix. This is the appropriate relation for
fuel-indexed source semantics when compiler expansion changes the amount of
target fuel needed to realize one source control step.
-/
inductive ForwardRel
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    (truncated : Error₁ → Prop)
    (doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop) :
    Interaction Error₁ Result₁ →
    Interaction Error₂ Result₂ → Prop where
  | truncated {error : Error₁}
      {right : Interaction Error₂ Result₂} :
      truncated error →
      ForwardRel truncated doneRel (.done (.error error)) right
  | done {left : Except Error₁ Result₁}
      {right : Except Error₂ Result₂} :
      doneRel left right →
      ForwardRel truncated doneRel (.done left) (.done right)
  | request {query : Query}
      {left : Answer query → Interaction Error₁ Result₁}
      {right : Answer query → Interaction Error₂ Result₂} :
      (∀ answer,
        ForwardRel truncated doneRel (left answer) (right answer)) →
      ForwardRel truncated doneRel
        (.request query left) (.request query right)

namespace ForwardRel

/--
Reconstruct source-truncating forward refinement from concrete branches.

A non-truncated source branch must execute to a related target outcome. A
truncated source branch only requires its exact ordered transcript to remain a
prefix of the target interaction. This is the branchwise interface needed when
the compiler gives the target more fuel than the source.
-/
theorem of_executes_or_follows
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ -> Prop}
    {doneRel :
      Except Error₁ Result₁ -> Except Error₂ Result₂ -> Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hBranches :
      forall transcript leftDone,
        Executes left transcript leftDone ->
          (exists error,
              leftDone = .error error /\
                truncated error /\ Follows right transcript) \/
            exists rightDone,
              Executes right transcript rightDone /\
                doneRel leftDone rightDone) :
    ForwardRel truncated doneRel left right := by
  induction left generalizing right with
  | done leftDone =>
      rcases hBranches [] leftDone (Executes.done leftDone) with
        hTruncated | hDone
      · obtain ⟨error, hError, hTruncated, _hFollow⟩ := hTruncated
        subst leftDone
        exact .truncated hTruncated
      · obtain ⟨rightDone, hRight, hDone⟩ := hDone
        cases hRight with
        | done => exact .done hDone
  | request query resume ih =>
      cases right with
      | done rightDone =>
          obtain ⟨transcript, leftDone, hLeft, _⟩ :=
            AllDone.exists_executes
              (AllDone.trivial (resume query.defaultAnswer))
          rcases hBranches
              ({ query := query, answer := query.defaultAnswer } :: transcript)
              leftDone
              (Executes.request query.defaultAnswer hLeft) with
            hTruncated | hDone
          · obtain ⟨_error, _hError, _hTruncated, hFollow⟩ := hTruncated
            cases hFollow
          · obtain ⟨_rightDone, hRight, _hDone⟩ := hDone
            cases hRight
      | request targetQuery targetResume =>
          obtain ⟨transcript, leftDone, hLeft, _⟩ :=
            AllDone.exists_executes
              (AllDone.trivial (resume query.defaultAnswer))
          have hQuery : query = targetQuery := by
            rcases hBranches
                ({ query := query, answer := query.defaultAnswer } :: transcript)
                leftDone
                (Executes.request query.defaultAnswer hLeft) with
              hTruncated | hDone
            · obtain ⟨_error, _hError, _hTruncated, hFollow⟩ := hTruncated
              obtain ⟨_answer, hHead, _hTail⟩ :=
                Follows.request_inv hFollow
              exact congrArg Exchange.query hHead
            · obtain ⟨_rightDone, hRight, _hDone⟩ := hDone
              obtain ⟨_answer, hHead, _hTail⟩ :=
                Executes.request_inv hRight
              exact congrArg Exchange.query hHead
          subst targetQuery
          exact .request fun answer => by
            apply ih answer
            intro tailTranscript tailDone hTail
            rcases hBranches
                ({ query := query, answer := answer } :: tailTranscript)
                tailDone
                (Executes.request answer hTail) with
              hTruncated | hDone
            · obtain ⟨error, hError, hTruncated, hFollow⟩ := hTruncated
              obtain ⟨_targetAnswer, hHead, hTargetTail⟩ :=
                Follows.request_inv hFollow
              cases hHead
              exact .inl ⟨error, hError, hTruncated, hTargetTail⟩
            · obtain ⟨rightDone, hRight, hDone⟩ := hDone
              obtain ⟨_targetAnswer, hHead, hTargetTail⟩ :=
                Executes.request_inv hRight
              cases hHead
              exact .inr ⟨rightDone, hTargetTail, hDone⟩

/-- Strengthen every related target leaf with a universal target invariant.
Source truncation remains truncation and therefore needs no target relation. -/
theorem strengthen_right
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {property : Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : ForwardRel truncated doneRel left right)
    (hAll : AllDone property right) :
    ForwardRel truncated
      (fun leftDone rightDone => doneRel leftDone rightDone ∧ property rightDone)
      left right := by
  induction hRel with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | done hDone =>
      cases hAll with
      | done hProperty => exact .done ⟨hDone, hProperty⟩
  | request hResume ih =>
      cases hAll with
      | request hProperty =>
          exact .request fun answer => ih answer (hProperty answer)

/-- Sequence a target-only continuation while leaving the completed source
result unchanged. -/
theorem bind_right
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Source₂ : Type v2} {Target₂ : Type w2}
    {truncated : Error₁ → Prop}
    {sourceDoneRel :
      Except Error₁ Result₁ → Except Error₂ Source₂ → Prop}
    {targetDoneRel :
      Except Error₁ Result₁ → Except Error₂ Target₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Source₂}
    {rightNext : Source₂ → Interaction Error₂ Target₂}
    (hRel : ForwardRel truncated sourceDoneRel left right)
    (hNext :
      ∀ leftDone rightDone,
        sourceDoneRel leftDone rightDone →
          ForwardRel truncated targetDoneRel
            (.done leftDone)
            (match rightDone with
            | .error error => .done (.error error)
            | .ok value => rightNext value)) :
    ForwardRel truncated targetDoneRel left
      (Interaction.bind right rightNext) := by
  induction hRel with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | @done leftDone rightDone hDone =>
      cases rightDone with
      | error error =>
          simpa [Interaction.bind] using
            hNext leftDone (.error error) hDone
      | ok value =>
          simpa [Interaction.bind] using
            hNext leftDone (.ok value) hDone
  | request hResume ih =>
      exact .request ih

theorem ofRel
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : Rel doneRel left right) :
    ForwardRel truncated doneRel left right := by
  induction hRel with
  | done hDone =>
      exact .done hDone
  | request hResume ih =>
      exact .request ih

theorem mono
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel₁ doneRel₂ :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : ForwardRel truncated doneRel₁ left right)
    (hDone :
      ∀ leftDone rightDone,
        doneRel₁ leftDone rightDone →
          doneRel₂ leftDone rightDone) :
    ForwardRel truncated doneRel₂ left right := by
  induction hRel with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | done hRelated =>
      exact .done (hDone _ _ hRelated)
  | request hResume ih =>
      exact .request ih

/-- Remove a pure administrative map from the source side of a forward
simulation while preserving source truncation. -/
theorem bind_pure_left_inv
    {Error₁ : Type u1} {Source₁ : Type v1} {Target₁ : Type w1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel :
      Except Error₁ Target₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Source₁}
    {right : Interaction Error₂ Result₂}
    {f : Source₁ → Target₁}
    (hRel :
      ForwardRel truncated doneRel
        (Interaction.bind left
          (fun value => Interaction.pure (f value)))
        right) :
    ForwardRel truncated
      (fun leftDone rightDone =>
        match leftDone with
        | .error err => doneRel (.error err) rightDone
        | .ok value => doneRel (.ok (f value)) rightDone)
      left right := by
  induction left generalizing right with
  | done outcome =>
      cases outcome with
      | error error =>
          cases hRel with
          | truncated hTruncated => exact .truncated hTruncated
          | done hDone => exact .done hDone
      | ok value =>
          cases hRel with
          | done hDone => exact .done hDone
  | request query resume ih =>
      cases hRel with
      | request hResume =>
          exact .request fun answer => ih answer (hResume answer)

/-- A forward simulation followed by an exact open-world relation composes
without replaying or interpreting either interaction tree. -/
theorem trans_rel
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {Error3 : Type u3} {Result3 : Type v3}
    {truncated : Error1 → Prop}
    {doneRel12 :
      Except Error1 Result1 → Except Error2 Result2 → Prop}
    {doneRel23 :
      Except Error2 Result2 → Except Error3 Result3 → Prop}
    {left : Interaction Error1 Result1}
    {middle : Interaction Error2 Result2}
    {right : Interaction Error3 Result3}
    (hLeft : ForwardRel truncated doneRel12 left middle)
    (hRight : Rel doneRel23 middle right) :
    ForwardRel truncated
      (fun leftDone rightDone =>
        ∃ middleDone,
          doneRel12 leftDone middleDone ∧
            doneRel23 middleDone rightDone)
      left right := by
  induction hLeft generalizing right with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | @done leftDone middleDone hDone =>
      cases hRight with
      | done hRightDone =>
          exact .done ⟨middleDone, hDone, hRightDone⟩
  | @request query leftResume middleResume hResume ih =>
      cases hRight with
      | request hRightResume =>
          exact .request fun answer =>
            ih answer (hRightResume answer)

/--
Compose two source-truncating forward refinements. The first adjacent boundary
owns the only extra fact required for composition: if its target outcome is a
truncation for the second boundary, then the original source outcome was
already a truncation. No target suffix is inspected or replayed.
-/
theorem trans
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {Error3 : Type u3} {Result3 : Type v3}
    {truncated1 : Error1 → Prop}
    {truncated2 : Error2 → Prop}
    {doneRel12 :
      Except Error1 Result1 → Except Error2 Result2 → Prop}
    {doneRel23 :
      Except Error2 Result2 → Except Error3 Result3 → Prop}
    {left : Interaction Error1 Result1}
    {middle : Interaction Error2 Result2}
    {right : Interaction Error3 Result3}
    (hLeft : ForwardRel truncated1 doneRel12 left middle)
    (hRight : ForwardRel truncated2 doneRel23 middle right)
    (hReflect :
      ∀ leftDone middleError,
        doneRel12 leftDone (.error middleError) →
          truncated2 middleError →
            ∃ leftError,
              leftDone = .error leftError ∧ truncated1 leftError) :
    ForwardRel truncated1
      (fun leftDone rightDone =>
        ∃ middleDone,
          doneRel12 leftDone middleDone ∧
            doneRel23 middleDone rightDone)
      left right := by
  induction hLeft generalizing right with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | @done leftDone middleDone hDone =>
      cases hRight with
      | truncated hMiddleTruncated =>
          obtain ⟨leftError, hLeftDone, hLeftTruncated⟩ :=
            hReflect leftDone _ hDone hMiddleTruncated
          subst leftDone
          exact .truncated hLeftTruncated
      | done hRightDone =>
          exact .done ⟨middleDone, hDone, hRightDone⟩
  | @request query leftResume middleResume hResume ih =>
      cases hRight with
      | request hRightResume =>
          exact .request fun answer =>
            ih answer (hRightResume answer)

/-- Universal source success crosses a forward simulation whenever every
related successful source leaf has a successful target leaf. -/
theorem successful_right
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {truncated : Error1 → Prop}
    {doneRel :
      Except Error1 Result1 → Except Error2 Result2 → Prop}
    {left : Interaction Error1 Result1}
    {right : Interaction Error2 Result2}
    (hRel : ForwardRel truncated doneRel left right)
    (hSuccessful : Successful left)
    (hDone : ∀ leftDone rightDone,
      doneRel leftDone rightDone →
        (match leftDone with | .error _ => False | .ok _ => True) →
          (match rightDone with | .error _ => False | .ok _ => True)) :
    Successful right := by
  induction hRel with
  | truncated hTruncated =>
      cases hSuccessful with
      | done hSource => exact False.elim hSource
  | @done leftDone rightDone hRelated =>
      cases hSuccessful with
      | done hSource => exact .done (hDone leftDone rightDone hRelated hSource)
  | @request query leftResume rightResume hResume ih =>
      cases hSuccessful with
      | request hSource =>
          exact .request fun answer =>
            ih answer (hSource answer)

/-- A universally successful source cannot reach the truncation constructor,
so a forward refinement becomes a full structural open-world relation. -/
theorem rel_of_successful
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {truncated : Error1 -> Prop}
    {doneRel :
      Except Error1 Result1 -> Except Error2 Result2 -> Prop}
    {left : Interaction Error1 Result1}
    {right : Interaction Error2 Result2}
    (hRel : ForwardRel truncated doneRel left right)
    (hSuccessful : Successful left) :
    Rel doneRel left right := by
  induction hRel with
  | truncated hTruncated =>
      cases hSuccessful with
      | done hSource => exact False.elim hSource
  | done hDone =>
      exact .done hDone
  | request hResume ih =>
      cases hSuccessful with
      | request hSource =>
          exact .request fun answer => ih answer (hSource answer)

/-- A source-leaf invariant that excludes every truncated failure upgrades a
forward refinement to a full structural open-world relation. -/
theorem rel_of_allDone
    {Error1 : Type u1} {Result1 : Type v1}
    {Error2 : Type u2} {Result2 : Type v2}
    {truncated : Error1 -> Prop}
    {doneRel :
      Except Error1 Result1 -> Except Error2 Result2 -> Prop}
    {property : Except Error1 Result1 -> Prop}
    {left : Interaction Error1 Result1}
    {right : Interaction Error2 Result2}
    (hRel : ForwardRel truncated doneRel left right)
    (hAll : AllDone property left)
    (hExcludes : forall error, property (.error error) ->
      Not (truncated error)) :
    Rel doneRel left right := by
  induction hRel with
  | truncated hTruncated =>
      cases hAll with
      | done hProperty =>
          exact False.elim (hExcludes _ hProperty hTruncated)
  | done hDone =>
      exact .done hDone
  | request hResume ih =>
      cases hAll with
      | request hProperty =>
          exact .request fun answer => ih answer (hProperty answer)

/-- Strengthen a forward simulation with a source-side invariant that holds at
every terminal leaf. Source truncation remains source truncation and therefore
does not require a target relation. -/
theorem strengthen_left
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {property : Except Error₁ Result₁ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (hRel : ForwardRel truncated doneRel left right)
    (hAll : AllDone property left) :
    ForwardRel truncated
      (fun leftDone rightDone =>
        doneRel leftDone rightDone ∧ property leftDone)
      left right := by
  induction hRel with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | done hDone =>
      cases hAll with
      | done hProperty =>
          exact .done ⟨hDone, hProperty⟩
  | request hResume ih =>
      cases hAll with
      | request hProperty =>
          exact .request fun answer =>
            ih answer (hProperty answer)

theorem bind
    {Error₁ : Type u1} {Source₁ : Type v1} {Target₁ : Type w1}
    {Error₂ : Type u2} {Source₂ : Type v2} {Target₂ : Type w2}
    {truncated : Error₁ → Prop}
    {errorRel : Error₁ → Error₂ → Prop}
    {sourceRel : Source₁ → Source₂ → Prop}
    {targetRel : Target₁ → Target₂ → Prop}
    {left : Interaction Error₁ Source₁}
    {right : Interaction Error₂ Source₂}
    {leftNext : Source₁ → Interaction Error₁ Target₁}
    {rightNext : Source₂ → Interaction Error₂ Target₂}
    (hResult :
      ForwardRel truncated (ExceptRel errorRel sourceRel) left right)
    (hNext :
      ∀ leftValue rightValue,
        sourceRel leftValue rightValue →
          ForwardRel truncated (ExceptRel errorRel targetRel)
            (leftNext leftValue) (rightNext rightValue)) :
    ForwardRel truncated (ExceptRel errorRel targetRel)
      (Interaction.bind left leftNext)
      (Interaction.bind right rightNext) := by
  induction hResult with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | done hDone =>
      cases hDone with
      | error hError =>
          exact .done (.error hError)
      | ok hValue =>
          exact hNext _ _ hValue
  | request hResume ih =>
      exact .request ih

theorem bind_custom
    {Error₁ : Type u1} {Source₁ : Type v1} {Target₁ : Type w1}
    {Error₂ : Type u2} {Source₂ : Type v2} {Target₂ : Type w2}
    {truncated : Error₁ → Prop}
    {sourceDoneRel :
      Except Error₁ Source₁ → Except Error₂ Source₂ → Prop}
    {targetDoneRel :
      Except Error₁ Target₁ → Except Error₂ Target₂ → Prop}
    {left : Interaction Error₁ Source₁}
    {right : Interaction Error₂ Source₂}
    {leftNext : Source₁ → Interaction Error₁ Target₁}
    {rightNext : Source₂ → Interaction Error₂ Target₂}
    (hResult : ForwardRel truncated sourceDoneRel left right)
    (hNext :
      ∀ leftDone rightDone,
        sourceDoneRel leftDone rightDone →
          ForwardRel truncated targetDoneRel
            (match leftDone with
            | .error error => .done (.error error)
            | .ok value => leftNext value)
            (match rightDone with
            | .error error => .done (.error error)
            | .ok value => rightNext value)) :
    ForwardRel truncated targetDoneRel
      (Interaction.bind left leftNext)
      (Interaction.bind right rightNext) := by
  induction hResult with
  | truncated hTruncated =>
      exact .truncated hTruncated
  | @done leftDone rightDone hDone =>
      cases leftDone <;> cases rightDone <;>
        simpa [Interaction.bind] using
          hNext _ _ hDone
  | request hResume ih =>
      exact .request ih

/--
Every non-truncated concrete source execution is reproduced by the target with
the exact same ordered query/answer transcript.
-/
theorem executes
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    {transcript : Transcript}
    {leftOutcome : Except Error₁ Result₁}
    (hRel : ForwardRel truncated doneRel left right)
    (hExec : Executes left transcript leftOutcome)
    (hNotTruncated :
      ∀ error, leftOutcome = .error error → ¬ truncated error) :
    ∃ rightOutcome,
      Executes right transcript rightOutcome ∧
        doneRel leftOutcome rightOutcome := by
  induction hExec generalizing right with
  | done outcome =>
      cases hRel with
      | truncated hTruncated =>
          exact False.elim (hNotTruncated _ rfl hTruncated)
      | done hDone =>
          exact ⟨_, Executes.done _, hDone⟩
  | request answer tail ih =>
      cases hRel with
      | request hResume =>
          obtain ⟨rightOutcome, hRight, hDone⟩ :=
            ih (hResume answer) hNotTruncated
          exact
            ⟨rightOutcome, Executes.request answer hRight, hDone⟩

theorem executes_ok
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    {transcript : Transcript}
    {leftResult : Result₁}
    (hRel : ForwardRel truncated doneRel left right)
    (hExec : Executes left transcript (.ok leftResult)) :
    ∃ rightOutcome,
      Executes right transcript rightOutcome ∧
        doneRel (.ok leftResult) rightOutcome := by
  apply executes hRel hExec
  intro error hError
  cases hError

end ForwardRel

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

theorem ForwardRel.interpret
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {truncated : Error₁ → Prop}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    (strategy : Strategy)
    (hRel : ForwardRel truncated doneRel left right)
    (hNotTruncated :
      ∀ error, interpret strategy left = .error error →
        ¬ truncated error) :
    doneRel (interpret strategy left) (interpret strategy right) := by
  induction hRel with
  | truncated hTruncated =>
      exact False.elim (hNotTruncated _ rfl hTruncated)
  | done hDone =>
      exact hDone
  | @request query left right hResume ih =>
      exact ih (strategy query) hNotTruncated

end Interaction

end Simulation
end EvmCompiler
