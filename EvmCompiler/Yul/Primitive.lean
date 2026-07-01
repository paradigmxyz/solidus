import EvmCompiler.Yul.Syntax

namespace EvmCompiler
namespace Yul
namespace Prim

def toBasicOp? : EvmYul.Operation .Yul → Option Structured.BasicOp
  | .StopArith .STOP => none
  | .StopArith .ADD => some .add
  | .StopArith .MUL => some .mul
  | .StopArith .SUB => some .sub
  | .StopArith .DIV => some .div
  | .StopArith .SDIV => some .sdiv
  | .StopArith .MOD => some .mod
  | .StopArith .SMOD => some .smod
  | .StopArith .ADDMOD => some .addmod
  | .StopArith .MULMOD => some .mulmod
  | .StopArith .EXP => some .exp
  | .StopArith .SIGNEXTEND => some .signextend
  | .CompBit .LT => some .lt
  | .CompBit .GT => some .gt
  | .CompBit .SLT => some .slt
  | .CompBit .SGT => some .sgt
  | .CompBit .EQ => some .eq
  | .CompBit .ISZERO => some .iszero
  | .CompBit .AND => some .and
  | .CompBit .OR => some .or
  | .CompBit .XOR => some .xor
  | .CompBit .NOT => some .not
  | .CompBit .BYTE => some .byte
  | .CompBit .SHL => some .shl
  | .CompBit .SHR => some .shr
  | .CompBit .SAR => some .sar
  | .CompBit .CLZ => none
  | .Keccak .KECCAK256 => some .keccak256
  | .Env .ADDRESS => some .address
  | .Env .BALANCE => some .balance
  | .Env .ORIGIN => some .origin
  | .Env .CALLER => some .caller
  | .Env .CALLVALUE => some .callvalue
  | .Env .CALLDATALOAD => some .calldataload
  | .Env .CALLDATASIZE => some .calldatasize
  | .Env .CALLDATACOPY => some .calldatacopy
  | .Env .CODESIZE => some .codesize
  | .Env .GASPRICE => some .gasprice
  | .Env .CODECOPY => some .codecopy
  | .Env .EXTCODESIZE => some .extcodesize
  | .Env .EXTCODECOPY => some .extcodecopy
  | .Env .RETURNDATASIZE => some .returndatasize
  | .Env .RETURNDATACOPY => some .returndatacopy
  | .Env .EXTCODEHASH => some .extcodehash
  | .Block .BLOCKHASH => some .blockhash
  | .Block .COINBASE => some .coinbase
  | .Block .TIMESTAMP => some .timestamp
  | .Block .NUMBER => some .number
  | .Block .PREVRANDAO => some .prevrandao
  | .Block .GASLIMIT => some .gaslimit
  | .Block .CHAINID => some .chainid
  | .Block .SELFBALANCE => some .selfbalance
  | .Block .BASEFEE => some .basefee
  | .Block .BLOBHASH => some .blobhash
  | .Block .BLOBBASEFEE => some .blobbasefee
  | .StackMemFlow .POP => some .pop
  | .StackMemFlow .MLOAD => some .mload
  | .StackMemFlow .MSTORE => some .mstore
  | .StackMemFlow .SLOAD => some .sload
  | .StackMemFlow .SSTORE => some .sstore
  | .StackMemFlow .MSTORE8 => some .mstore8
  | .StackMemFlow .MSIZE => none
  | .StackMemFlow .GAS => none
  | .StackMemFlow .TLOAD => some .tload
  | .StackMemFlow .TSTORE => some .tstore
  | .StackMemFlow .MCOPY => some .mcopy
  | .Log .LOG0 => some .log0
  | .Log .LOG1 => some .log1
  | .Log .LOG2 => some .log2
  | .Log .LOG3 => some .log3
  | .Log .LOG4 => some .log4
  | .System .CREATE => some .create
  | .System .CALL => some .call
  | .System .CALLCODE => some .callcode
  | .System .RETURN => none
  | .System .DELEGATECALL => some .delegatecall
  | .System .CREATE2 => some .create2
  | .System .STATICCALL => some .staticcall
  | .System .REVERT => none
  | .System .INVALID => some .invalid
  | .System .SELFDESTRUCT => none

@[simp] theorem toBasicOp?_gas :
    toBasicOp? ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) = none := rfl

@[simp] theorem toBasicOp?_msize :
    toBasicOp? ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) = none := rfl

@[simp] theorem toBasicOp?_clz :
    toBasicOp? ((.CompBit .CLZ : EvmYul.Operation .Yul)) = none := rfl

def toUncheckedBasicOp? (prim : EvmYul.Operation .Yul) :
    Option Structured.BasicOp :=
  match prim with
  | .StackMemFlow .MSIZE => some .msize
  | .StackMemFlow .GAS => some .gas
  | _ => toBasicOp? prim

def stop? : EvmYul.Operation .Yul → Option Assembly.HaltKind
  | .StopArith .STOP => some .stop
  | _ => none

def terminal? : EvmYul.Operation .Yul → Option Assembly.HaltKind
  | .StopArith .STOP => some .stop
  | .System .RETURN => some .return
  | .System .REVERT => some .revert
  | .System .SELFDESTRUCT => some .selfdestruct
  | _ => none

theorem toBasicOp?_some_terminal_none
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hOp : toBasicOp? prim = some op) :
    terminal? prim = none := by
  cases prim <;> rename_i primitive <;> cases primitive <;>
    simp [toBasicOp?, terminal?] at hOp ⊢

theorem toUncheckedBasicOp?_some_terminal_none
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hOp : toUncheckedBasicOp? prim = some op) :
    terminal? prim = none := by
  cases prim <;> rename_i primitive <;> cases primitive <;>
    simp [toBasicOp?, toUncheckedBasicOp?, terminal?] at hOp ⊢

theorem toUncheckedBasicOp?_of_toBasicOp?
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hOp : toBasicOp? prim = some op) :
    toUncheckedBasicOp? prim = some op := by
  cases prim <;> rename_i primitive <;> cases primitive <;>
    simp [toBasicOp?, toUncheckedBasicOp?] at hOp ⊢ <;>
    assumption

end Prim
end Yul
end EvmCompiler
