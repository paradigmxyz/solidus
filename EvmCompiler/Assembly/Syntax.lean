import EvmYul.Operations
import EvmYul.UInt256

namespace EvmCompiler
namespace Assembly

inductive Label where
  | named (name : String)
  | generated (scope : Nat) (tag : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr
abbrev Word := EvmYul.UInt256
abbrev EVMOp := EvmYul.Operation EvmYul.OperationType.EVM

inductive HaltKind where
  | stop
  | return
  | revert
  | selfdestruct
  deriving DecidableEq, Repr

theorem UInt256_ofNat_add (left right : Nat) :
    EvmYul.UInt256.ofNat left + EvmYul.UInt256.ofNat right =
      EvmYul.UInt256.ofNat (left + right) := by
  change
    EvmYul.UInt256.add (EvmYul.UInt256.ofNat left)
      (EvmYul.UInt256.ofNat right) =
        EvmYul.UInt256.ofNat (left + right)
  unfold EvmYul.UInt256.add EvmYul.UInt256.ofNat
  congr
  ext
  simp [Id.run, Fin.val_add, Nat.add_mod]

/--
Primitive operations admitted directly into the first assembly layer.

Control transfer, labels, and pushes are represented by dedicated assembly
instructions. Raw `JUMP`/`JUMPI`/`JUMPDEST` are represented by labeled
control-flow instructions. The source/compiler tower does not admit `GAS` as
an ordinary continuing source primitive; gas accounting remains only in the
final gas-aware runner. `GAS` is still present in assembly syntax so executable
unchecked object images can emit the real opcode for Solidity/Forge
compatibility.
-/
inductive PrimOp where
  | stop
  | add | mul | sub | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar
  | address | balance | origin | caller | callvalue | calldataload | calldatasize
  | calldatacopy | codesize | codecopy | gasprice | extcodesize | extcodecopy
  | returndatasize | returndatacopy | extcodehash
  | blockhash | coinbase | timestamp | number | prevrandao | gaslimit | chainid
  | selfbalance | basefee | blobhash | blobbasefee
  | pop | mload | mstore | sload | sstore | mstore8 | pc | msize
  | tload | tstore
  | mcopy
  | keccak256
  | dup1 | dup2 | dup3 | dup4 | dup5 | dup6 | dup7 | dup8
  | dup9 | dup10 | dup11 | dup12 | dup13 | dup14 | dup15 | dup16
  | swap1 | swap2 | swap3 | swap4 | swap5 | swap6 | swap7 | swap8
  | swap9 | swap10 | swap11 | swap12 | swap13 | swap14 | swap15 | swap16
  | log0 | log1 | log2 | log3 | log4
  | create | call | callcode | return | delegatecall | create2 | staticcall
  | revert | invalid | selfdestruct
  | gas
  deriving DecidableEq, Repr

namespace HaltKind

def argCount : HaltKind → Nat
  | .stop => 0
  | .return => 2
  | .revert => 2
  | .selfdestruct => 1

def toPrimOp : HaltKind → PrimOp
  | .stop => .stop
  | .return => .return
  | .revert => .revert
  | .selfdestruct => .selfdestruct

end HaltKind

namespace PrimOp

def isCallCreate : PrimOp → Bool
  | .create | .call | .callcode | .delegatecall | .create2 | .staticcall
  | .gas =>
      true
  | _ =>
      false

def toEVM : PrimOp → EVMOp
  | .stop => EvmYul.Operation.STOP
  | .add => EvmYul.Operation.ADD
  | .mul => EvmYul.Operation.MUL
  | .sub => EvmYul.Operation.SUB
  | .div => EvmYul.Operation.DIV
  | .sdiv => EvmYul.Operation.SDIV
  | .mod => EvmYul.Operation.MOD
  | .smod => EvmYul.Operation.SMOD
  | .addmod => EvmYul.Operation.ADDMOD
  | .mulmod => EvmYul.Operation.MULMOD
  | .exp => EvmYul.Operation.EXP
  | .signextend => EvmYul.Operation.SIGNEXTEND
  | .lt => EvmYul.Operation.LT
  | .gt => EvmYul.Operation.GT
  | .slt => EvmYul.Operation.SLT
  | .sgt => EvmYul.Operation.SGT
  | .eq => EvmYul.Operation.EQ
  | .iszero => EvmYul.Operation.ISZERO
  | .and => EvmYul.Operation.AND
  | .or => EvmYul.Operation.OR
  | .xor => EvmYul.Operation.XOR
  | .not => EvmYul.Operation.NOT
  | .byte => EvmYul.Operation.BYTE
  | .shl => EvmYul.Operation.SHL
  | .shr => EvmYul.Operation.SHR
  | .sar => EvmYul.Operation.SAR
  | .address => EvmYul.Operation.ADDRESS
  | .balance => EvmYul.Operation.BALANCE
  | .origin => EvmYul.Operation.ORIGIN
  | .caller => EvmYul.Operation.CALLER
  | .callvalue => EvmYul.Operation.CALLVALUE
  | .calldataload => EvmYul.Operation.CALLDATALOAD
  | .calldatasize => EvmYul.Operation.CALLDATASIZE
  | .calldatacopy => EvmYul.Operation.CALLDATACOPY
  | .codesize => EvmYul.Operation.CODESIZE
  | .codecopy => EvmYul.Operation.CODECOPY
  | .gasprice => EvmYul.Operation.GASPRICE
  | .extcodesize => EvmYul.Operation.EXTCODESIZE
  | .extcodecopy => EvmYul.Operation.EXTCODECOPY
  | .returndatasize => EvmYul.Operation.RETURNDATASIZE
  | .returndatacopy => EvmYul.Operation.RETURNDATACOPY
  | .extcodehash => EvmYul.Operation.EXTCODEHASH
  | .blockhash => EvmYul.Operation.BLOCKHASH
  | .coinbase => EvmYul.Operation.COINBASE
  | .timestamp => EvmYul.Operation.TIMESTAMP
  | .number => EvmYul.Operation.NUMBER
  | .prevrandao => EvmYul.Operation.PREVRANDAO
  | .gaslimit => EvmYul.Operation.GASLIMIT
  | .chainid => EvmYul.Operation.CHAINID
  | .selfbalance => EvmYul.Operation.SELFBALANCE
  | .basefee => EvmYul.Operation.BASEFEE
  | .blobhash => EvmYul.Operation.BLOBHASH
  | .blobbasefee => EvmYul.Operation.BLOBBASEFEE
  | .pop => EvmYul.Operation.POP
  | .mload => EvmYul.Operation.MLOAD
  | .mstore => EvmYul.Operation.MSTORE
  | .sload => EvmYul.Operation.SLOAD
  | .sstore => EvmYul.Operation.SSTORE
  | .mstore8 => EvmYul.Operation.MSTORE8
  | .pc => EvmYul.Operation.PC
  | .msize => EvmYul.Operation.MSIZE
  | .gas => EvmYul.Operation.GAS
  | .tload => EvmYul.Operation.TLOAD
  | .tstore => EvmYul.Operation.TSTORE
  | .mcopy => EvmYul.Operation.MCOPY
  | .keccak256 => EvmYul.Operation.KECCAK256
  | .dup1 => EvmYul.Operation.DUP1
  | .dup2 => EvmYul.Operation.DUP2
  | .dup3 => EvmYul.Operation.DUP3
  | .dup4 => EvmYul.Operation.DUP4
  | .dup5 => EvmYul.Operation.DUP5
  | .dup6 => EvmYul.Operation.DUP6
  | .dup7 => EvmYul.Operation.DUP7
  | .dup8 => EvmYul.Operation.DUP8
  | .dup9 => EvmYul.Operation.DUP9
  | .dup10 => EvmYul.Operation.DUP10
  | .dup11 => EvmYul.Operation.DUP11
  | .dup12 => EvmYul.Operation.DUP12
  | .dup13 => EvmYul.Operation.DUP13
  | .dup14 => EvmYul.Operation.DUP14
  | .dup15 => EvmYul.Operation.DUP15
  | .dup16 => EvmYul.Operation.DUP16
  | .swap1 => EvmYul.Operation.SWAP1
  | .swap2 => EvmYul.Operation.SWAP2
  | .swap3 => EvmYul.Operation.SWAP3
  | .swap4 => EvmYul.Operation.SWAP4
  | .swap5 => EvmYul.Operation.SWAP5
  | .swap6 => EvmYul.Operation.SWAP6
  | .swap7 => EvmYul.Operation.SWAP7
  | .swap8 => EvmYul.Operation.SWAP8
  | .swap9 => EvmYul.Operation.SWAP9
  | .swap10 => EvmYul.Operation.SWAP10
  | .swap11 => EvmYul.Operation.SWAP11
  | .swap12 => EvmYul.Operation.SWAP12
  | .swap13 => EvmYul.Operation.SWAP13
  | .swap14 => EvmYul.Operation.SWAP14
  | .swap15 => EvmYul.Operation.SWAP15
  | .swap16 => EvmYul.Operation.SWAP16
  | .log0 => EvmYul.Operation.LOG0
  | .log1 => EvmYul.Operation.LOG1
  | .log2 => EvmYul.Operation.LOG2
  | .log3 => EvmYul.Operation.LOG3
  | .log4 => EvmYul.Operation.LOG4
  | .create => EvmYul.Operation.CREATE
  | .call => EvmYul.Operation.CALL
  | .callcode => EvmYul.Operation.CALLCODE
  | .return => EvmYul.Operation.RETURN
  | .delegatecall => EvmYul.Operation.DELEGATECALL
  | .create2 => EvmYul.Operation.CREATE2
  | .staticcall => EvmYul.Operation.STATICCALL
  | .revert => EvmYul.Operation.REVERT
  | .invalid => EvmYul.Operation.INVALID
  | .selfdestruct => EvmYul.Operation.SELFDESTRUCT

end PrimOp

inductive Instr where
  | label (name : Label)
  | prim (op : PrimOp)
  | push (value : Word)
  | jump (target : Label)
  | jumpi (target : Label)
  deriving DecidableEq, Repr

abbrev Program := List Instr

namespace Instr

def push32Size : Nat := 33
def jumpSize : Nat := push32Size + 1

def byteSize : Instr → Nat
  | .label _ => 1
  | .prim _ => 1
  | .push _ => push32Size
  | .jump _ => jumpSize
  | .jumpi _ => jumpSize

theorem byteSize_pos (instr : Instr) : 0 < instr.byteSize := by
  cases instr <;> simp [byteSize, push32Size, jumpSize]

def targets : Instr → List Label
  | .jump target => [target]
  | .jumpi target => [target]
  | _ => []

def usesCallCreate : Instr → Bool
  | .prim op => op.isCallCreate
  | .label _ | .push _ | .jump _ | .jumpi _ => false

end Instr

namespace Program

def byteLength : Program → Nat
  | [] => 0
  | instr :: rest => instr.byteSize + byteLength rest

@[simp]
theorem byteLength_nil : byteLength ([] : Program) = 0 := rfl

@[simp]
theorem byteLength_cons (instr : Instr) (rest : Program) :
    byteLength (instr :: rest) = instr.byteSize + byteLength rest := rfl

theorem byteLength_append (left right : Program) :
    byteLength (left ++ right) = byteLength left + byteLength right := by
  induction left with
  | nil =>
      simp [byteLength]
  | cons instr rest ih =>
      simp [byteLength, ih, Nat.add_assoc]

theorem byteLength_pos_of_cons (instr : Instr) (rest : Program) :
    0 < byteLength (instr :: rest) := by
  simp [byteLength, Instr.byteSize_pos]

def pcAfter (program : Program) : Word :=
  EvmYul.UInt256.ofNat (byteLength program)

def PCFits (program : Program) : Prop :=
  program.pcAfter.toNat = program.byteLength

def PCFitsFrom : Program → Program → Prop
  | pre, [] => pre.PCFits
  | pre, instr :: rest =>
      pre.PCFits ∧ PCFitsFrom (pre ++ [instr]) rest

def usesCallCreate (program : Program) : Bool :=
  program.any Instr.usesCallCreate

theorem usesCallCreate_append (left right : Program) :
    usesCallCreate (left ++ right) =
      (usesCallCreate left || usesCallCreate right) := by
  simp [usesCallCreate]

theorem usesCallCreate_append_eq_false {left right : Program}
    (hLeft : usesCallCreate left = false)
    (hRight : usesCallCreate right = false) :
    usesCallCreate (left ++ right) = false := by
  simp [usesCallCreate_append, hLeft, hRight]

@[simp]
theorem pcAfter_nil : pcAfter ([] : Program) = EvmYul.UInt256.ofNat 0 := rfl

theorem pcAfter_append (left right : Program) :
    pcAfter (left ++ right) =
      pcAfter left + EvmYul.UInt256.ofNat (byteLength right) := by
  unfold pcAfter
  rw [byteLength_append]
  exact (UInt256_ofNat_add (byteLength left) (byteLength right)).symm

theorem pcAfter_snoc (program : Program) (instr : Instr) :
    pcAfter (program ++ [instr]) =
      pcAfter program + EvmYul.UInt256.ofNat instr.byteSize := by
  simpa [byteLength] using pcAfter_append program [instr]

instance pcFitsDecidable (program : Program) :
    Decidable program.PCFits := by
  unfold PCFits
  infer_instance

def pcFitsFromDecidable (pre code : Program) :
    Decidable (PCFitsFrom pre code) :=
  match code with
  | [] => pcFitsDecidable pre
  | instr :: rest =>
      @instDecidableAnd pre.PCFits
        (PCFitsFrom (pre ++ [instr]) rest)
        (pcFitsDecidable pre)
        (pcFitsFromDecidable (pre ++ [instr]) rest)

instance (pre code : Program) :
    Decidable (PCFitsFrom pre code) :=
  pcFitsFromDecidable pre code

theorem PCFitsFrom.start {pre code : Program}
    (hFits : PCFitsFrom pre code) :
    pre.PCFits := by
  cases code with
  | nil =>
      simpa [PCFitsFrom] using hFits
  | cons _instr _rest =>
      exact hFits.1

theorem PCFitsFrom.end {pre code : Program}
    (hFits : PCFitsFrom pre code) :
    (pre ++ code).PCFits := by
  induction code generalizing pre with
  | nil =>
      simpa [PCFitsFrom] using hFits
  | cons instr rest ih =>
      simpa [PCFitsFrom, List.append_assoc] using ih hFits.2

theorem PCFitsFrom.left {pre first second : Program}
    (hFits : PCFitsFrom pre (first ++ second)) :
    PCFitsFrom pre first := by
  induction first generalizing pre with
  | nil =>
      exact PCFitsFrom.start hFits
  | cons _instr _rest ih =>
      rcases hFits with ⟨hHere, hRest⟩
      exact ⟨hHere, ih hRest⟩

theorem PCFitsFrom.right {pre first second : Program}
    (hFits : PCFitsFrom pre (first ++ second)) :
    PCFitsFrom (pre ++ first) second := by
  induction first generalizing pre with
  | nil =>
      simpa using hFits
  | cons instr rest ih =>
      rcases hFits with ⟨_hHere, hRest⟩
      simpa [List.append_assoc] using ih hRest

theorem PCFits.of_byteLength_le {program whole : Program}
    (hFits : whole.PCFits)
    (hLe : program.byteLength ≤ whole.byteLength) :
    program.PCFits := by
  have hWholeLt : whole.byteLength < EvmYul.UInt256.size := by
    have hWordLt : whole.pcAfter.toNat < EvmYul.UInt256.size :=
      whole.pcAfter.val.isLt
    rw [hFits] at hWordLt
    exact hWordLt
  unfold PCFits pcAfter
  exact
    EvmYul.UInt256.toNat_ofNat_of_lt
      (Nat.lt_of_le_of_lt hLe hWholeLt)

theorem PCFitsFrom.of_append {pre code post : Program}
    (hFits : (pre ++ code ++ post).PCFits) :
    PCFitsFrom pre code := by
  induction code generalizing pre post with
  | nil =>
      exact
        PCFits.of_byteLength_le hFits
          (by simp [byteLength_append])
  | cons instr rest ih =>
      refine ⟨?_, ?_⟩
      · exact
          PCFits.of_byteLength_le hFits
            (by
              simp [byteLength_append, byteLength])
      · apply ih (pre := pre ++ [instr]) (post := post)
        simpa [List.append_assoc] using hFits

end Program

end Assembly
end EvmCompiler
