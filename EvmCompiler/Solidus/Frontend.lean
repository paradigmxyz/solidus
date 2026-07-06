import EvmYul.UInt256
import EvmYul.Operations
import EvmCompiler.Core.MemoryContract

/-!
# Frozen frontend spec types (Solidus Arena freeze cone)

`EvmCompiler.Solidus.compile_correct` existentially quantifies over a
`Solidity.Frontend.ObjectBuiltinContext` and runs the frozen source semantics
against it. The witness type and the pure data types it is built from are
relocated here out of the mutable, 4.7k-line compiler frontend
`EvmCompiler/Solidity/Frontend.lean` so that an adversary cannot collapse the
context's shape to a trivial type while leaving the frozen hashes unchanged.

Only the pure data *types* move (`Name`, `Word`, `ObjectLayout`,
`ObjectLayout.Entry`, `ImmutableReference`, `ObjectBuiltinContext`); all
compiler methods and constructors on them stay mutable in the original file,
which now imports this module. Names and the `Solidity.Frontend` namespace are
preserved, so downstream references remain valid.
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

abbrev Name := String
abbrev Word := EvmYul.UInt256

structure ObjectLayout.Entry where
  name : Name
  offset : Word
  size : Word
  deriving Inhabited, Repr

structure ObjectLayout where
  entries : List ObjectLayout.Entry
  deriving Inhabited, Repr

structure ImmutableReference where
  start : Nat
  length : Nat
  deriving Inhabited, Repr

/-- Existential builtin-resolution witness handed to the frozen source
semantics. Every field is pure data; `layout` and the association lists resolve
`datasize`/`dataoffset`/linker/immutable builtins, and `memoryContract`
records the (stack-only) memory policy. -/
structure ObjectBuiltinContext where
  layout : ObjectLayout
  dataSizes : List (Name × Word)
  dataOffsets : List (Name × Word)
  linkerSymbols : List (Name × Word)
  immutableValues : List (Name × Word) := []
  immutableReferences : List (Name × List ImmutableReference) := []
  selfSize? : Option (Name × Word) := none
  memoryContract : MemoryContract.Contract :=
    MemoryContract.unrestricted
  deriving Inhabited, Repr

/-!
## Source-semantics helpers (freeze cone)

The following pure helpers are referenced by the frozen source interpreter
(`Solidity.RawAst.Raw.SourceSemantics`) that `compile_correct` runs, so they are
relocated here out of the mutable 4.7k-line `EvmCompiler/Solidity/Frontend.lean`
(which now imports this module). Names and the `Solidity.Frontend` namespace are
preserved; every definition is pure data over the frozen spec types + EvmYul, so
the moves are definitionally identical.
-/

/-- Call classification for the imported Yul AST (referenced by the frozen
source semantics / `CallClass.classifyCall`). -/
inductive CallKind where
  | primitive
  | user
  | objectBuiltin
  | dialectBuiltin
  deriving BEq, Inhabited, Repr

namespace StringLiteral

def maxBytes : Nat :=
  32

def packBytes (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

def wordBytes? (bytes : List UInt8) : Option Word :=
  if bytes.length <= maxBytes then
    some
      (EvmYul.UInt256.ofNat
        (packBytes bytes * 256 ^ (maxBytes - bytes.length)))
  else
    none

def word? (value : String) : Option Word :=
  wordBytes? value.toUTF8.toList

end StringLiteral

namespace Name

def containsDot (name : Name) : Bool :=
  name.toList.contains '.'

def objectPathComponent? (name : Name) : Bool :=
  !containsDot name

end Name

namespace ObjectLayout

def findEntry? (layout : ObjectLayout) (name : Name) :
    Option ObjectLayout.Entry :=
  layout.entries.find? fun entry => entry.name == name

def offset? (layout : ObjectLayout) (name : Name) : Option Word := do
  let entry ← layout.findEntry? name
  some entry.offset

def size? (layout : ObjectLayout) (name : Name) : Option Word := do
  let entry ← layout.findEntry? name
  some entry.size

end ObjectLayout

namespace ImmutableReference

def patchLength : Nat :=
  32

def isPatchable (reference : ImmutableReference) : Bool :=
  reference.length == patchLength

end ImmutableReference

namespace ObjectBuiltinContext

def findDataSize? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.dataSizes.find? fun entry => entry.fst == name
  some entry.snd

def findDataOffset? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.dataOffsets.find? fun entry => entry.fst == name
  some entry.snd

def findLinkerSymbol? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.linkerSymbols.find? fun entry => entry.fst == name
  some entry.snd

def findImmutableValue? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.immutableValues.find? fun entry => entry.fst == name
  some entry.snd

def collectImmutableReferences
    (entries : List (Name × List ImmutableReference)) (name : Name) :
    List ImmutableReference :=
  entries.foldr
    (fun entry refs =>
      if entry.fst == name then
        entry.snd ++ refs
      else
        refs)
    []

def findImmutableReferences? (context : ObjectBuiltinContext) (name : Name) :
    Option (List ImmutableReference) :=
  let refs := collectImmutableReferences context.immutableReferences name
  match refs with
  | [] => none
  | _ :: _ => some refs

def findSelfSize? (context : ObjectBuiltinContext) (name : Name) :
    Option Word :=
  match context.selfSize? with
  | some (selfName, size) =>
      if selfName == name && Name.objectPathComponent? selfName then
        some size
      else
        none
  | none => none

def size? (context : ObjectBuiltinContext) (name : Name) : Option Word :=
  match context.findDataSize? name with
  | some size => some size
  | none =>
      match context.findSelfSize? name with
      | some size => some size
      | none => context.layout.size? name

def offset? (context : ObjectBuiltinContext) (name : Name) : Option Word :=
  match context.findDataOffset? name with
  | some offset => some offset
  | none => context.layout.offset? name

end ObjectBuiltinContext

namespace Primitive

/-- Primitive names recognized from solc's Yul AST (relocated from the mutable
frontend; referenced by the frozen source semantics and `CallClass`). -/
def ofName? : Name → Option (EvmYul.Operation .Yul)
  | "stop" => some .STOP
  | "add" => some .ADD
  | "mul" => some .MUL
  | "sub" => some .SUB
  | "div" => some .DIV
  | "sdiv" => some .SDIV
  | "mod" => some .MOD
  | "smod" => some .SMOD
  | "addmod" => some .ADDMOD
  | "mulmod" => some .MULMOD
  | "exp" => some .EXP
  | "signextend" => some .SIGNEXTEND
  | "lt" => some .LT
  | "gt" => some .GT
  | "slt" => some .SLT
  | "sgt" => some .SGT
  | "eq" => some .EQ
  | "iszero" => some .ISZERO
  | "and" => some .AND
  | "or" => some .OR
  | "xor" => some .XOR
  | "not" => some .NOT
  | "byte" => some .BYTE
  | "shl" => some .SHL
  | "shr" => some .SHR
  | "sar" => some .SAR
  | "clz" => some (.CompBit .CLZ)
  | "keccak256" => some .KECCAK256
  | "sha3" => some .KECCAK256
  | "address" => some .ADDRESS
  | "balance" => some .BALANCE
  | "origin" => some .ORIGIN
  | "caller" => some .CALLER
  | "callvalue" => some .CALLVALUE
  | "calldataload" => some .CALLDATALOAD
  | "calldatasize" => some .CALLDATASIZE
  | "calldatacopy" => some .CALLDATACOPY
  | "codesize" => some .CODESIZE
  | "codecopy" => some .CODECOPY
  | "gasprice" => some .GASPRICE
  | "extcodesize" => some .EXTCODESIZE
  | "extcodecopy" => some .EXTCODECOPY
  | "returndatasize" => some .RETURNDATASIZE
  | "returndatacopy" => some .RETURNDATACOPY
  | "extcodehash" => some .EXTCODEHASH
  | "blockhash" => some .BLOCKHASH
  | "coinbase" => some .COINBASE
  | "timestamp" => some .TIMESTAMP
  | "number" => some .NUMBER
  | "prevrandao" => some .PREVRANDAO
  | "difficulty" => some .PREVRANDAO
  | "gaslimit" => some .GASLIMIT
  | "chainid" => some .CHAINID
  | "selfbalance" => some .SELFBALANCE
  | "basefee" => some .BASEFEE
  | "blobhash" => some .BLOBHASH
  | "blobbasefee" => some .BLOBBASEFEE
  | "pop" => some .POP
  | "mload" => some .MLOAD
  | "mstore" => some .MSTORE
  | "sload" => some .SLOAD
  | "sstore" => some .SSTORE
  | "mstore8" => some .MSTORE8
  | "msize" => some .MSIZE
  | "gas" => some .GAS
  | "tload" => some .TLOAD
  | "tstore" => some .TSTORE
  | "mcopy" => some .MCOPY
  | "log0" => some .LOG0
  | "log1" => some .LOG1
  | "log2" => some .LOG2
  | "log3" => some .LOG3
  | "log4" => some .LOG4
  | "create" => some .CREATE
  | "call" => some .CALL
  | "callcode" => some .CALLCODE
  | "return" => some .RETURN
  | "delegatecall" => some .DELEGATECALL
  | "create2" => some .CREATE2
  | "staticcall" => some .STATICCALL
  | "revert" => some .REVERT
  | "invalid" => some .INVALID
  | "selfdestruct" => some .SELFDESTRUCT
  | _ => none

end Primitive

namespace Expr

def objectBuiltinNameFromBytes (bytes : List UInt8) : Name :=
  String.ofList (bytes.map (fun byte => Char.ofNat byte.toNat))

end Expr

end Frontend
end Solidity
end EvmCompiler
