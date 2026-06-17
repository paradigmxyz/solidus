import EvmCompiler.Compiler.MemoryRelation
import EvmCompiler.Structured.Syntax

namespace EvmCompiler
namespace Simulation
namespace MemorySafety

abbrev Word := Assembly.Word

/--
A dynamic source memory range is safe for allocation lowering when it does not
overlap the compiler-owned scratch reservation. Stack-only compilation has no
reserved interval and therefore permits every source range.
-/
@[simp] abbrev RegionAllowed (contract : MemoryContract.Contract)
    (address size : Nat) : Prop :=
  match contract.scratch? with
  | none => True
  | some reservation =>
      reservation.sourceAccessAllowed address size

/--
Ordinary EVM memory states do not contain materialized bytes beyond the active
memory extent. This source-facing invariant prevents target spill allocation
from exposing dormant source bytes through a later `mload`.
-/
@[simp] abbrev MemoryConsistent (machine : EvmYul.MachineState) : Prop :=
  Compiler.MemoryRelation.MemoryConsistent machine

/--
Every memory expansion performed by a primitive remains representable by the
ordinary EVM active-word counter and its `MSIZE` byte value.
-/
@[simp] abbrev PrimitiveExpansionSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mload, [address]
  | .mstore, [address, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat MemoryContract.wordBytes
  | .mstore8, [address, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat 1
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size]
  | .extcodecopy, [_, destination, _source, size] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat
  | .mcopy, [destination, source, size] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        (max destination.toNat source.toNat) size.toNat
  | .keccak256, [address, size]
  | .log0, [address, size]
  | .log1, [address, size, _]
  | .log2, [address, size, _, _]
  | .log3, [address, size, _, _, _]
  | .log4, [address, size, _, _, _, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat size.toNat
  | _, _ => True

/--
Memory writes and finite memory reads stay inside the host byte-array address
space used by the executable semantics.
-/
@[simp] abbrev PrimitiveHostSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mstore, [address, _] =>
      address.toNat + MemoryContract.wordBytes < USize.size
  | .mstore8, [address, _] =>
      address.toNat + 1 < USize.size
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size]
  | .extcodecopy, [_, destination, _source, size] =>
      destination.toNat + size.toNat < USize.size
  | .mcopy, [destination, source, size] =>
      destination.toNat + size.toNat < USize.size ∧
        source.toNat + size.toNat < USize.size
  | .keccak256, [address, size]
  | .log0, [address, size]
  | .log1, [address, size, _]
  | .log2, [address, size, _, _]
  | .log3, [address, size, _, _, _]
  | .log4, [address, size, _, _, _, _] =>
      address.toNat + size.toNat < USize.size
  | _, _ => True

/--
Source-facing memory safety for one primitive application.

`values` follows the stack-free source argument order. Reversing it
reconstructs concrete EVM pop order. External call/create operations are
deliberately excluded from this closed-world contract.
-/
@[simp] abbrev PrimitiveMemorySafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (machine : EvmYul.MachineState)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mload, [address] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat MemoryContract.wordBytes ∧
        PrimitiveExpansionSafe op values
  | .mstore, [address, _value] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat MemoryContract.wordBytes ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .mstore8, [address, _value] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat 1 ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .extcodecopy, [_account, destination, _source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .mcopy, [destination, source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        RegionAllowed contract source.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .keccak256, [address, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .log0, [address, size]
  | .log1, [address, size, _topic0]
  | .log2, [address, size, _topic0, _topic1]
  | .log3, [address, size, _topic0, _topic1, _topic2]
  | .log4, [address, size, _topic0, _topic1, _topic2, _topic3] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .create, _
  | .call, _
  | .callcode, _
  | .delegatecall, _
  | .create2, _
  | .staticcall, _ =>
      False
  | _, _ => True

/--
A source memory window used by an open-world request or response.

Zero-length windows are safe regardless of their offset: the executable EVM
semantics reads, writes, and expands no bytes in that case. Nonempty windows
must avoid compiler scratch storage and satisfy both EVM and host bounds.
-/
def WindowSafe (contract : MemoryContract.Contract)
    (address size : Nat) : Prop :=
  size = 0 ∨
    (RegionAllowed contract address size ∧
      Compiler.MemoryRelation.ExpansionNoWrap address size ∧
      address + size < USize.size)

@[simp] theorem windowSafe_zero
    (contract : MemoryContract.Contract) (address : Nat) :
    WindowSafe contract address 0 :=
  Or.inl rfl

/--
Source-facing primitive safety for the open interaction semantics.

CALL-family requests read calldata and may write returndata. CREATE-family
requests read init code. The concrete gas operand is intentionally irrelevant
to this memory contract. Every nonexternal operation keeps the established
`PrimitiveMemorySafe` contract.
-/
def OpenPrimitiveMemorySafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (machine : EvmYul.MachineState)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .call, [_gas, _address, _value,
      inputOffset, inputSize, outputOffset, outputSize]
  | .callcode, [_gas, _address, _value,
      inputOffset, inputSize, outputOffset, outputSize] =>
      MemoryConsistent machine ∧
        WindowSafe contract inputOffset.toNat inputSize.toNat ∧
        WindowSafe contract outputOffset.toNat outputSize.toNat
  | .delegatecall, [_gas, _address,
      inputOffset, inputSize, outputOffset, outputSize]
  | .staticcall, [_gas, _address,
      inputOffset, inputSize, outputOffset, outputSize] =>
      MemoryConsistent machine ∧
        WindowSafe contract inputOffset.toNat inputSize.toNat ∧
        WindowSafe contract outputOffset.toNat outputSize.toNat
  | .create, [_value, initOffset, initSize]
  | .create2, [_value, initOffset, initSize, _salt] =>
      MemoryConsistent machine ∧
        WindowSafe contract initOffset.toNat initSize.toNat
  | _, _ => PrimitiveMemorySafe contract op machine values

@[simp] theorem openPrimitiveMemorySafe_call_zero_windows
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState)
    (gas address value inputOffset outputOffset : Word)
    (hConsistent : MemoryConsistent machine) :
    OpenPrimitiveMemorySafe contract .call machine
      [EvmYul.UInt256.ofNat 0, outputOffset,
        EvmYul.UInt256.ofNat 0, inputOffset, value, address, gas] := by
  change
    MemoryConsistent machine ∧
      WindowSafe contract inputOffset.toNat 0 ∧
      WindowSafe contract outputOffset.toNat 0
  exact
    ⟨hConsistent, windowSafe_zero contract inputOffset.toNat,
      windowSafe_zero contract outputOffset.toNat⟩

@[simp] theorem openPrimitiveMemorySafe_create_zero_window
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState)
    (value initOffset : Word)
    (hConsistent : MemoryConsistent machine) :
    OpenPrimitiveMemorySafe contract .create machine
      [EvmYul.UInt256.ofNat 0, initOffset, value] := by
  change
    MemoryConsistent machine ∧
      WindowSafe contract initOffset.toNat 0
  exact ⟨hConsistent, windowSafe_zero contract initOffset.toNat⟩

theorem noExternal_of_primitiveMemorySafe
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    {machine : EvmYul.MachineState} {values : List Word}
    (hSafe : PrimitiveMemorySafe contract op machine values) :
    op.toPrimOp.isExternalCallCreate = false := by
  cases op <;>
    simp [PrimitiveMemorySafe, Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isExternalCallCreate] at hSafe ⊢

/--
Terminal source memory reads obey the same reservation contract. `RETURN` and
`REVERT` read a byte range; `STOP` and `SELFDESTRUCT` do not read memory.
-/
@[simp] abbrev TerminalMemorySafe (contract : MemoryContract.Contract)
    (kind : Assembly.HaltKind) (values : List Word) : Prop :=
  match kind, values.reverse with
  | .return, [address, size]
  | .revert, [address, size] =>
      RegionAllowed contract address.toNat size.toNat ∧
        Compiler.MemoryRelation.ExpansionNoWrap
          address.toNat size.toNat ∧
        address.toNat + size.toNat < USize.size
  | .stop, []
  | .selfdestruct, [_recipient] =>
      True
  | _, _ => False

@[simp] theorem regionAllowed_unrestricted (address size : Nat) :
    RegionAllowed MemoryContract.unrestricted address size := by
  simp [RegionAllowed, MemoryContract.unrestricted]

theorem primitiveMemorySafe_unrestricted_of_noExternal
    {op : Structured.BasicOp} {machine : EvmYul.MachineState}
    {values : List Word}
    (hNoExternal : op.toPrimOp.isExternalCallCreate = false) :
    MemoryConsistent machine →
      PrimitiveExpansionSafe op values →
      PrimitiveHostSafe op values →
      PrimitiveMemorySafe MemoryContract.unrestricted op machine values := by
  intro hConsistent hExpansion hHost
  unfold PrimitiveMemorySafe
  simp only [RegionAllowed, MemoryContract.unrestricted]
  split <;>
    simp_all [MemoryConsistent, PrimitiveExpansionSafe, PrimitiveHostSafe,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isExternalCallCreate]

@[simp] theorem primitiveMemorySafe_gas
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .gas machine [] := by
  simp [PrimitiveMemorySafe]

@[simp] theorem primitiveMemorySafe_msize
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .msize machine [] := by
  simp [PrimitiveMemorySafe]

@[simp] theorem terminalMemorySafe_stop
    (contract : MemoryContract.Contract) :
    TerminalMemorySafe contract .stop [] := by
  simp [TerminalMemorySafe]

@[simp] theorem terminalMemorySafe_selfdestruct
    (contract : MemoryContract.Contract) (recipient : Word) :
    TerminalMemorySafe contract .selfdestruct [recipient] := by
  simp [TerminalMemorySafe]

end MemorySafety
end Simulation
end EvmCompiler
