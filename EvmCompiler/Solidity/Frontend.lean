import EvmCompiler.Yul.Compiler
import EvmCompiler.Yul.SolcValidation
import EvmCompiler.Objects.Layout
import EvmCompiler.Compiler.StackArtifact
import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Assembly.Compact

namespace EvmCompiler
namespace Solidity
namespace Frontend

abbrev Name := String
abbrev Word := EvmYul.UInt256
abbrev AstExpr := EvmYul.Yul.Ast.Expr
abbrev AstStmt := EvmYul.Yul.Ast.Stmt
abbrev AstFunctionDefinition := EvmYul.Yul.Ast.FunctionDefinition
abbrev AstContract := EvmYul.Yul.Ast.YulContract

/--
The kind of Yul call as it appears in solc's Yul AST.

The compiler backend lowers primitive EVM/Yul operations and user functions
through `EvmYul.Yul.Ast.Expr.Call`. Object builtins are kept as their own call
kind until the object-image path computes object/data placement, resolves them,
and only then enters core Yul lowering. Dialect builtins are preserved so the
bridge can reject unsupported dialect surfaces explicitly instead of losing that
source-shape information.
-/
inductive CallKind where
  | primitive
  | user
  | objectBuiltin
  | dialectBuiltin
  deriving BEq, DecidableEq, Inhabited, Repr

namespace CallKind

def backendRepresentable : CallKind → Bool
  | .primitive => true
  | .user => true
  | .objectBuiltin => false
  | .dialectBuiltin => false

end CallKind

inductive Expr where
  | lit (value : Word)
  | stringLit (value : String)
  | bytesLit (bytes : List UInt8)
  | var (name : Name)
  | call (kind : CallKind) (callee : Name) (args : List Expr)
  deriving Inhabited, Repr

inductive SwitchCaseValue where
  | word (value : Word)
  | stringLit (value : String)
  | bytesLit (bytes : List UInt8)
  | boolLit (value : Bool)
  deriving Inhabited, Repr

inductive Stmt where
  | block (stmts : List Stmt)
  | letDecl (names : List Name) (value : Option Expr)
  | assign (names : List Name) (value : Expr)
  | exprStmt (expr : Expr)
  | functionDef (name : Name) (params returns : List Name) (body : List Stmt)
  | switch (scrutinee : Expr) (cases : List (SwitchCaseValue × List Stmt))
      (default : List Stmt)
  | forLoop (pre : List Stmt) (condition : Expr) (post : List Stmt)
      (body : List Stmt)
  | ifThen (condition : Expr) (body : List Stmt)
  | break
  | continue
  | leave
  deriving Inhabited, Repr

structure FunctionDef where
  params : List Name
  returns : List Name
  body : List Stmt
  deriving Inhabited, Repr

structure DataSection where
  name? : Option Name
  bytes : List UInt8
  deriving Inhabited, Repr

inductive ObjectItemRef where
  | data (index : Nat)
  | object (index : Nat)
  deriving BEq, DecidableEq, Inhabited, Repr

structure Object where
  name : Name
  dispatcher : List Stmt
  functions : List (Name × FunctionDef)
  data : List DataSection
  objects : List Object
  items : List ObjectItemRef
  memoryContract : MemoryContract.Contract :=
    MemoryContract.unrestricted
  evmVersion : Yul.SolcValidation.EvmVersion := .cancun
  deriving Inhabited, Repr

structure Program where
  source : String
  contract : String
  object : Object
  deriving Inhabited, Repr

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

namespace SwitchCaseValue

def toWord? : SwitchCaseValue → Option Word
  | .word value => some value
  | .stringLit value => StringLiteral.word? value
  | .bytesLit bytes => StringLiteral.wordBytes? bytes
  | .boolLit value =>
      some (EvmYul.UInt256.ofNat (if value then 1 else 0))

end SwitchCaseValue

namespace Name

def containsDot (name : Name) : Bool :=
  name.toList.contains '.'

def objectPathComponent? (name : Name) : Bool :=
  !containsDot name

def objectPath (pathPrefix name : Name) : Name :=
  pathPrefix ++ "." ++ name

end Name

/--
A visible layout witness for Yul object/data pseudo-builtins.

Resolving through this structure only replaces `datasize("name")` and
`dataoffset("name")` with literals before entering the current backend
`Yul.Program`.  The executable `bytecodeImageUnchecked?` path below computes
its own object/data layout and appends payload bytes; this witness remains for
explicit-layout debugging, compatibility code-only conversions, and checked
layout theorem work.
-/
structure ObjectLayout.Entry where
  name : Name
  offset : Word
  size : Word
  deriving Inhabited, Repr

structure ObjectLayout where
  entries : List ObjectLayout.Entry
  deriving Inhabited, Repr

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

namespace Entry

def addBase (base : Nat) (entry : ObjectLayout.Entry) :
    ObjectLayout.Entry :=
  { entry with offset := EvmYul.UInt256.ofNat (base + entry.offset.toNat) }

def addBaseAndPrefix (base : Nat) (pathPrefix : Name)
    (entry : ObjectLayout.Entry) : ObjectLayout.Entry :=
  { name := Name.objectPath pathPrefix entry.name
    offset := EvmYul.UInt256.ofNat (base + entry.offset.toNat)
    size := entry.size }

end Entry

end ObjectLayout

namespace DataSection

def toObjects (dataSection : DataSection) : Objects.DataSection :=
  { name? := dataSection.name?
    bytes := dataSection.bytes }

namespace List

def toObjects : List DataSection → List Objects.DataSection :=
  List.map DataSection.toObjects

end List

def size (dataSection : DataSection) : Word :=
  EvmYul.UInt256.ofNat dataSection.bytes.length

def sizeEntry? (dataSection : DataSection) : Option (Name × Word) :=
  match dataSection.name? with
  | some name =>
      if Name.objectPathComponent? name then
        some (name, dataSection.size)
      else
        none
  | none => none

def sizeEntries : List DataSection → List (Name × Word)
  | [] => []
  | dataSection :: rest =>
      match dataSection.sizeEntry? with
      | some entry => entry :: sizeEntries rest
      | none => sizeEntries rest

def offsetEntryFromNat? (base : Nat) (dataSection : DataSection) :
    Option (Name × Word) :=
  match dataSection.name? with
  | some name =>
      if Name.objectPathComponent? name then
        some (name, EvmYul.UInt256.ofNat base)
      else
        none
  | none => none

def offsetEntriesFromNat : Nat → List DataSection → List (Name × Word)
  | _, [] => []
  | base, dataSection :: rest =>
      let tail :=
        offsetEntriesFromNat (base + dataSection.bytes.length) rest
      match dataSection.offsetEntryFromNat? base with
      | some entry => entry :: tail
      | none => tail

namespace List

def payloadBytes : List DataSection → List UInt8
  | [] => []
  | sect :: rest => sect.bytes ++ payloadBytes rest

theorem toObjects_payloadBytes (sections : List DataSection) :
    Objects.DataSection.Sections.payloadBytes (toObjects sections) =
      payloadBytes sections := by
  induction sections with
  | nil =>
      rfl
  | cons sect rest ih =>
      cases sect with
      | mk name? bytes =>
          have hRest :
              Objects.DataSection.Sections.payloadBytes
                  (List.map DataSection.toObjects rest) =
                payloadBytes rest := by
            simpa [toObjects] using ih
          simp [toObjects, payloadBytes, DataSection.toObjects,
            Objects.DataSection.Sections.payloadBytes, hRest]

theorem toObjects_namedSizeEntries (sections : List DataSection) :
    Objects.DataSection.Sections.namedSizeEntries (toObjects sections) =
      DataSection.sizeEntries sections := by
  induction sections with
  | nil =>
      rfl
  | cons sect rest ih =>
      cases sect with
      | mk name? bytes =>
          have hRest :
              Objects.DataSection.Sections.namedSizeEntries
                  (List.map DataSection.toObjects rest) =
                DataSection.sizeEntries rest := by
            simpa [toObjects] using ih
          cases name? <;>
            simp [toObjects, DataSection.toObjects,
              DataSection.sizeEntries, DataSection.sizeEntry?,
              DataSection.size, Objects.DataSection.Sections.namedSizeEntries,
              Objects.DataSection.namedSizeEntry?, Objects.DataSection.size,
              Objects.DataSection.byteLength, Objects.Name.objectPathComponent?,
              Objects.Name.containsDot, Name.objectPathComponent?,
              Name.containsDot, hRest]
          all_goals rfl

theorem toObjects_namedOffsetEntriesFromNat
    (base : Nat) (sections : List DataSection) :
    Objects.DataSection.Sections.namedOffsetEntriesFromNat base
        (toObjects sections) =
      DataSection.offsetEntriesFromNat base sections := by
  induction sections generalizing base with
  | nil =>
      rfl
  | cons sect rest ih =>
      cases sect with
      | mk name? bytes =>
          have hRest :
              Objects.DataSection.Sections.namedOffsetEntriesFromNat
                  (base + bytes.length) (List.map DataSection.toObjects rest) =
                DataSection.offsetEntriesFromNat (base + bytes.length) rest := by
            simpa [toObjects] using ih (base + bytes.length)
          cases name? <;>
            simp [toObjects, DataSection.toObjects,
              DataSection.offsetEntriesFromNat,
              DataSection.offsetEntryFromNat?,
              Objects.DataSection.Sections.namedOffsetEntriesFromNat,
              Objects.DataSection.namedOffsetEntryFromNat?,
              Objects.DataSection.byteLength,
              Objects.Name.objectPathComponent?, Objects.Name.containsDot,
              Name.objectPathComponent?, Name.containsDot, hRest]
          all_goals rfl

end List

end DataSection

structure ImmutableReference where
  start : Nat
  length : Nat
  deriving Inhabited, Repr

namespace ImmutableReference

def patchLength : Nat :=
  32

def isPatchable (reference : ImmutableReference) : Bool :=
  reference.length == patchLength

end ImmutableReference

mutual
  def Expr.loweringFuel : Expr → Nat
    | .lit _ => 1
    | .stringLit _ => 1
    | .bytesLit _ => 1
    | .var _ => 1
    | .call _ _ args => Expr.List.loweringFuel args + 1

  def Expr.List.loweringFuel : List Expr → Nat
    | [] => 1
    | expr :: rest =>
        Expr.loweringFuel expr + Expr.List.loweringFuel rest + 1
end

mutual
  def Stmt.loweringFuel : Stmt → Nat
    | .block stmts => Stmt.List.loweringFuel stmts + 1
    | .letDecl _ none => 1
    | .letDecl _ (some value) => Expr.loweringFuel value + 1
    | .assign _ value => Expr.loweringFuel value + 1
    | .exprStmt expr => Expr.loweringFuel expr + 1
    | .functionDef _ _ _ body => Stmt.List.loweringFuel body + 1
    | .switch scrutinee cases default =>
        Expr.loweringFuel scrutinee +
          Stmt.CaseList.loweringFuel cases +
          Stmt.List.loweringFuel default + 1
    | .forLoop pre condition post body =>
        Expr.loweringFuel condition +
          Stmt.List.loweringFuel pre +
          Stmt.List.loweringFuel post +
          Stmt.List.loweringFuel body + 1
    | .ifThen condition body =>
        Expr.loweringFuel condition + Stmt.List.loweringFuel body + 1
    | .break => 1
    | .continue => 1
    | .leave => 1

  def Stmt.List.loweringFuel : List Stmt → Nat
    | [] => 1
    | stmt :: rest =>
        Stmt.loweringFuel stmt + Stmt.List.loweringFuel rest + 1

  def Stmt.CaseList.loweringFuel :
      List (SwitchCaseValue × List Stmt) → Nat
    | [] => 1
    | (_value, body) :: rest =>
        Stmt.List.loweringFuel body + Stmt.CaseList.loweringFuel rest + 1
end

namespace FunctionDef

def loweringFuel (fn : FunctionDef) : Nat :=
  Stmt.List.loweringFuel fn.body + 1

namespace List

def loweringFuel : List (Name × FunctionDef) → Nat
  | [] => 1
  | (_name, fn) :: rest => fn.loweringFuel + loweringFuel rest + 1

end List
end FunctionDef

namespace MemoryGuard

mutual
  def Expr.sizes? : Expr → Option (List Word)
    | .lit _ | .stringLit _ | .bytesLit _ | .var _ =>
        some []
    | .call .objectBuiltin "memoryguard" [.lit size] =>
        some [size]
    | .call .objectBuiltin "memoryguard" _ =>
        none
    | .call _ _ args =>
        Expr.List.sizes? args

  def Expr.List.sizes? : List Expr → Option (List Word)
    | [] => some []
    | expr :: rest => do
        let head ← Expr.sizes? expr
        let tail ← Expr.List.sizes? rest
        some (head ++ tail)
end

mutual
  def Stmt.sizes? : Stmt → Option (List Word)
    | .block stmts =>
        Stmt.List.sizes? stmts
    | .letDecl _ none =>
        some []
    | .letDecl _ (some value) =>
        Expr.sizes? value
    | .assign _ value =>
        Expr.sizes? value
    | .exprStmt expr =>
        Expr.sizes? expr
    | .functionDef _ _ _ body =>
        Stmt.List.sizes? body
    | .switch scrutinee cases defaultBody => do
        let scrutineeSizes ← Expr.sizes? scrutinee
        let caseSizes ← Stmt.CaseList.sizes? cases
        let defaultSizes ← Stmt.List.sizes? defaultBody
        some (scrutineeSizes ++ caseSizes ++ defaultSizes)
    | .forLoop pre condition post body => do
        let preSizes ← Stmt.List.sizes? pre
        let conditionSizes ← Expr.sizes? condition
        let postSizes ← Stmt.List.sizes? post
        let bodySizes ← Stmt.List.sizes? body
        some (preSizes ++ conditionSizes ++ postSizes ++ bodySizes)
    | .ifThen condition body => do
        let conditionSizes ← Expr.sizes? condition
        let bodySizes ← Stmt.List.sizes? body
        some (conditionSizes ++ bodySizes)
    | .break | .continue | .leave =>
        some []

  def Stmt.List.sizes? : List Stmt → Option (List Word)
    | [] => some []
    | stmt :: rest => do
        let head ← Stmt.sizes? stmt
        let tail ← Stmt.List.sizes? rest
        some (head ++ tail)

  def Stmt.CaseList.sizes? :
      List (SwitchCaseValue × List Stmt) → Option (List Word)
    | [] => some []
    | (_, body) :: rest => do
        let head ← Stmt.List.sizes? body
        let tail ← Stmt.CaseList.sizes? rest
        some (head ++ tail)
end

def FunctionDef.sizes? (fn : FunctionDef) : Option (List Word) :=
  Stmt.List.sizes? fn.body

def FunctionDef.List.sizes? :
    List (Name × FunctionDef) → Option (List Word)
  | [] => some []
  | (_, fn) :: rest => do
      let head ← FunctionDef.sizes? fn
      let tail ← FunctionDef.List.sizes? rest
      some (head ++ tail)

def Object.sizes? (object : @& Object) : Option (List Word) := do
  let dispatcher ← Stmt.List.sizes? object.dispatcher
  let functions ← FunctionDef.List.sizes? object.functions
  some (dispatcher ++ functions)

def Object.inferredContract? (object : @& Object) :
    Option MemoryContract.Contract := do
  let sizes ← MemoryGuard.Object.sizes? object
  if object.memoryContract = MemoryContract.unrestricted then
    match sizes with
    | [] => some MemoryContract.unrestricted
    | size :: rest =>
        if rest.all fun candidate => candidate == size then
          some MemoryContract.unrestricted
        else
          none
  else
    none

end MemoryGuard

namespace Bytecode

def concat (chunks : List (List UInt8)) : List UInt8 :=
  chunks.foldr (· ++ ·) []

end Bytecode

/--
Resolution context for object pseudo-builtins at the Solidity front-end
boundary.

Offsets for named local data sections can be computed from typed byte payloads
once the object-layer base address is supplied.  Other offsets still come from
a visible layout witness, because they depend on final code/object placement.
Sizes for named local data sections are computed from the typed byte payloads
imported from solc, so `datasize("dataName")` no longer needs an external size
witness for those sections.
-/
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

namespace ObjectBuiltinContext

def ofLayout (layout : ObjectLayout) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := []
    dataOffsets := []
    linkerSymbols := [] }

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

def immutableReferencesFor (context : ObjectBuiltinContext) (name : Name) :
    List ImmutableReference :=
  collectImmutableReferences context.immutableReferences name

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

def objectDataNames (context : ObjectBuiltinContext) : List Name :=
  context.layout.entries.map (fun entry => entry.name) ++
    context.dataSizes.map Prod.fst ++
      match context.selfSize? with
      | some (selfName, _size) =>
          if Name.objectPathComponent? selfName then [selfName] else []
      | none => []

def objectDataNamesUnique? (context : ObjectBuiltinContext) : Bool :=
  decide context.objectDataNames.Nodup

end ObjectBuiltinContext

namespace Primitive

/--
Primitive names recognized from solc's Yul AST.

This is intentionally the broad Solidity/Yul import surface, not the old
CALL-free structured subset.  The table includes CALL-family boundaries
(`call`, `callcode`, `delegatecall`, `staticcall`), CREATE-family boundaries
(`create`, `create2`), and account-code/state queries (`balance`,
`extcodesize`, `extcodecopy`, `extcodehash`).  Yul object builtins such as
`datasize`, `dataoffset`, `datacopy`, `loadimmutable`, `setimmutable`, and
`memoryguard` are handled through `CallKind.objectBuiltin` and the computed
object-image path rather than through this primitive table.
-/
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

def objectBuiltinNameArg? : Expr → Option Name
  | .stringLit name => some name
  | .bytesLit bytes => some (objectBuiltinNameFromBytes bytes)
  | _ => none

end Expr

namespace ForkSpelling

def primitiveAvailable? (version : Yul.SolcValidation.EvmVersion)
    (callee : Name) : Bool :=
  if callee == "difficulty" then
    !version.atLeast? .paris
  else if callee == "prevrandao" then
    version.atLeast? .paris
  else
    true

theorem difficulty_london : primitiveAvailable? .london "difficulty" = true :=
  rfl

theorem prevrandao_london : primitiveAvailable? .london "prevrandao" = false :=
  rfl

theorem difficulty_paris : primitiveAvailable? .paris "difficulty" = false :=
  rfl

theorem prevrandao_paris : primitiveAvailable? .paris "prevrandao" = true :=
  rfl

end ForkSpelling

mutual
  def Expr.forkSpellingOk? (version : Yul.SolcValidation.EvmVersion) :
      Expr → Bool
    | .lit _ => true
    | .stringLit _ => true
    | .bytesLit _ => true
    | .var _ => true
    | .call kind callee args =>
        (match kind with
          | .primitive => ForkSpelling.primitiveAvailable? version callee
          | _ => true) &&
          Expr.List.forkSpellingOk? version args

  def Expr.List.forkSpellingOk? (version : Yul.SolcValidation.EvmVersion) :
      List Expr → Bool
    | [] => true
    | expr :: rest =>
        expr.forkSpellingOk? version &&
          Expr.List.forkSpellingOk? version rest
end

mutual
  def Stmt.forkSpellingOk? (version : Yul.SolcValidation.EvmVersion) :
      Stmt → Bool
    | .block stmts => Stmt.List.forkSpellingOk? version stmts
    | .letDecl _ none => true
    | .letDecl _ (some value) => value.forkSpellingOk? version
    | .assign _ value => value.forkSpellingOk? version
    | .exprStmt expr => expr.forkSpellingOk? version
    | .functionDef _ _ _ body => Stmt.List.forkSpellingOk? version body
    | .switch scrutinee cases default =>
        scrutinee.forkSpellingOk? version &&
          (Stmt.CaseList.forkSpellingOk? version cases &&
            Stmt.List.forkSpellingOk? version default)
    | .forLoop pre condition post body =>
        Stmt.List.forkSpellingOk? version pre &&
          (condition.forkSpellingOk? version &&
            (Stmt.List.forkSpellingOk? version post &&
              Stmt.List.forkSpellingOk? version body))
    | .ifThen condition body =>
        condition.forkSpellingOk? version &&
          Stmt.List.forkSpellingOk? version body
    | .break => true
    | .continue => true
    | .leave => true

  def Stmt.List.forkSpellingOk? (version : Yul.SolcValidation.EvmVersion) :
      List Stmt → Bool
    | [] => true
    | stmt :: rest =>
        stmt.forkSpellingOk? version &&
          Stmt.List.forkSpellingOk? version rest

  def Stmt.CaseList.forkSpellingOk?
      (version : Yul.SolcValidation.EvmVersion) :
      List (SwitchCaseValue × List Stmt) → Bool
    | [] => true
    | (_value, body) :: rest =>
        Stmt.List.forkSpellingOk? version body &&
          Stmt.CaseList.forkSpellingOk? version rest
end

mutual
  def Expr.loadImmutableNames : Expr → List Name
    | .lit _ => []
    | .stringLit _ => []
    | .bytesLit _ => []
    | .var _ => []
    | .call .objectBuiltin "loadimmutable" [nameArg] =>
        match Expr.objectBuiltinNameArg? nameArg with
        | some name => [name]
        | none => []
    | .call _ _ args => Expr.List.loadImmutableNames args

  def Expr.List.loadImmutableNames : List Expr → List Name
    | [] => []
    | expr :: rest =>
        Expr.loadImmutableNames expr ++ Expr.List.loadImmutableNames rest
end

mutual
  def Stmt.loadImmutableNames : Stmt → List Name
    | .block stmts => Stmt.List.loadImmutableNames stmts
    | .letDecl _ none => []
    | .letDecl _ (some value) => value.loadImmutableNames
    | .assign _ value => value.loadImmutableNames
    | .exprStmt expr => expr.loadImmutableNames
    | .functionDef _ _ _ body => Stmt.List.loadImmutableNames body
    | .switch scrutinee cases default =>
        scrutinee.loadImmutableNames ++
          Stmt.CaseList.loadImmutableNames cases ++
          Stmt.List.loadImmutableNames default
    | .forLoop pre condition post body =>
        condition.loadImmutableNames ++
          Stmt.List.loadImmutableNames pre ++
          Stmt.List.loadImmutableNames post ++
          Stmt.List.loadImmutableNames body
    | .ifThen condition body =>
        condition.loadImmutableNames ++ Stmt.List.loadImmutableNames body
    | .break => []
    | .continue => []
    | .leave => []

  def Stmt.List.loadImmutableNames : List Stmt → List Name
    | [] => []
    | stmt :: rest =>
        Stmt.loadImmutableNames stmt ++ Stmt.List.loadImmutableNames rest

  def Stmt.CaseList.loadImmutableNames :
      List (SwitchCaseValue × List Stmt) → List Name
    | [] => []
    | (_value, body) :: rest =>
        Stmt.List.loadImmutableNames body ++
          Stmt.CaseList.loadImmutableNames rest
end

mutual
  def Expr.usesCodeLayoutBuiltinFor? (objectName : Name) : Expr → Bool
    | .lit _ => false
    | .stringLit _ => false
    | .bytesLit _ => false
    | .var _ => false
    | .call .objectBuiltin "dataoffset" _ => true
    | .call .objectBuiltin "datasize" args =>
        match args with
        | [nameArg] =>
            match Expr.objectBuiltinNameArg? nameArg with
            | some name => name == objectName && Name.objectPathComponent? objectName
            | none => true
        | _ => true
    | .call _ _ args => Expr.List.usesCodeLayoutBuiltinFor? objectName args

  def Expr.List.usesCodeLayoutBuiltinFor? (objectName : Name) :
      List Expr → Bool
    | [] => false
    | expr :: rest =>
        Expr.usesCodeLayoutBuiltinFor? objectName expr ||
          Expr.List.usesCodeLayoutBuiltinFor? objectName rest
end

mutual
  def Stmt.usesCodeLayoutBuiltinFor? (objectName : Name) : Stmt → Bool
    | .block stmts => Stmt.List.usesCodeLayoutBuiltinFor? objectName stmts
    | .letDecl _ none => false
    | .letDecl _ (some value) =>
        Expr.usesCodeLayoutBuiltinFor? objectName value
    | .assign _ value => Expr.usesCodeLayoutBuiltinFor? objectName value
    | .exprStmt expr => Expr.usesCodeLayoutBuiltinFor? objectName expr
    | .functionDef _ _ _ body =>
        Stmt.List.usesCodeLayoutBuiltinFor? objectName body
    | .switch scrutinee cases default =>
        Expr.usesCodeLayoutBuiltinFor? objectName scrutinee ||
          Stmt.CaseList.usesCodeLayoutBuiltinFor? objectName cases ||
            Stmt.List.usesCodeLayoutBuiltinFor? objectName default
    | .forLoop pre condition post body =>
        Stmt.List.usesCodeLayoutBuiltinFor? objectName pre ||
          Expr.usesCodeLayoutBuiltinFor? objectName condition ||
            Stmt.List.usesCodeLayoutBuiltinFor? objectName post ||
              Stmt.List.usesCodeLayoutBuiltinFor? objectName body
    | .ifThen condition body =>
        Expr.usesCodeLayoutBuiltinFor? objectName condition ||
          Stmt.List.usesCodeLayoutBuiltinFor? objectName body
    | .break => false
    | .continue => false
    | .leave => false

  def Stmt.List.usesCodeLayoutBuiltinFor? (objectName : Name) :
      List Stmt → Bool
    | [] => false
    | stmt :: rest =>
        Stmt.usesCodeLayoutBuiltinFor? objectName stmt ||
          Stmt.List.usesCodeLayoutBuiltinFor? objectName rest

  def Stmt.CaseList.usesCodeLayoutBuiltinFor? (objectName : Name) :
      List (SwitchCaseValue × List Stmt) → Bool
    | [] => false
    | (_value, body) :: rest =>
        Stmt.List.usesCodeLayoutBuiltinFor? objectName body ||
          Stmt.CaseList.usesCodeLayoutBuiltinFor? objectName rest
end

namespace SwitchCaseValue

def literalValues : SwitchCaseValue → List Word
  | .word value => [value]
  | .stringLit value =>
      match StringLiteral.word? value with
      | some literal => [literal]
      | none => []
  | .bytesLit bytes =>
      match StringLiteral.wordBytes? bytes with
      | some literal => [literal]
      | none => []
  | .boolLit value => [EvmYul.UInt256.ofNat (if value then 1 else 0)]

end SwitchCaseValue

mutual
  def Expr.literalValues : Expr → List Word
    | .lit value => [value]
    | .stringLit _ => []
    | .bytesLit _ => []
    | .var _ => []
    | .call _ _ args => Expr.List.literalValues args

  def Expr.List.literalValues : List Expr → List Word
    | [] => []
    | expr :: rest => Expr.literalValues expr ++ Expr.List.literalValues rest
end

mutual
  def Stmt.literalValues : Stmt → List Word
    | .block stmts => Stmt.List.literalValues stmts
    | .letDecl _ none => []
    | .letDecl _ (some value) => Expr.literalValues value
    | .assign _ value => Expr.literalValues value
    | .exprStmt expr => Expr.literalValues expr
    | .functionDef _ _ _ body => Stmt.List.literalValues body
    | .switch scrutinee cases default =>
        Expr.literalValues scrutinee ++
          Stmt.CaseList.literalValues cases ++
            Stmt.List.literalValues default
    | .forLoop pre condition post body =>
        Stmt.List.literalValues pre ++
          Expr.literalValues condition ++
            Stmt.List.literalValues post ++ Stmt.List.literalValues body
    | .ifThen condition body =>
        Expr.literalValues condition ++ Stmt.List.literalValues body
    | .break => []
    | .continue => []
    | .leave => []

  def Stmt.List.literalValues : List Stmt → List Word
    | [] => []
    | stmt :: rest => Stmt.literalValues stmt ++ Stmt.List.literalValues rest

  def Stmt.CaseList.literalValues :
      List (SwitchCaseValue × List Stmt) → List Word
    | [] => []
    | (value, body) :: rest =>
        SwitchCaseValue.literalValues value ++
          Stmt.List.literalValues body ++ Stmt.CaseList.literalValues rest
end

mutual
  def Expr.usesObjectBuiltinOtherThanLoadImmutable? : Expr → Bool
    | .lit _ => false
    | .stringLit _ => false
    | .bytesLit _ => false
    | .var _ => false
    | .call .objectBuiltin "loadimmutable" _ => false
    | .call .objectBuiltin _ _ => true
    | .call _ _ args => Expr.List.usesObjectBuiltinOtherThanLoadImmutable? args

  def Expr.List.usesObjectBuiltinOtherThanLoadImmutable? :
      List Expr → Bool
    | [] => false
    | expr :: rest =>
        Expr.usesObjectBuiltinOtherThanLoadImmutable? expr ||
          Expr.List.usesObjectBuiltinOtherThanLoadImmutable? rest
end

mutual
  def Stmt.usesObjectBuiltinOtherThanLoadImmutable? : Stmt → Bool
    | .block stmts => Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? stmts
    | .letDecl _ none => false
    | .letDecl _ (some value) =>
        Expr.usesObjectBuiltinOtherThanLoadImmutable? value
    | .assign _ value => Expr.usesObjectBuiltinOtherThanLoadImmutable? value
    | .exprStmt expr => Expr.usesObjectBuiltinOtherThanLoadImmutable? expr
    | .functionDef _ _ _ body =>
        Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? body
    | .switch scrutinee cases default =>
        Expr.usesObjectBuiltinOtherThanLoadImmutable? scrutinee ||
          Stmt.CaseList.usesObjectBuiltinOtherThanLoadImmutable? cases ||
            Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? default
    | .forLoop pre condition post body =>
        Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? pre ||
          Expr.usesObjectBuiltinOtherThanLoadImmutable? condition ||
            Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? post ||
              Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? body
    | .ifThen condition body =>
        Expr.usesObjectBuiltinOtherThanLoadImmutable? condition ||
          Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? body
    | .break => false
    | .continue => false
    | .leave => false

  def Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? :
      List Stmt → Bool
    | [] => false
    | stmt :: rest =>
        Stmt.usesObjectBuiltinOtherThanLoadImmutable? stmt ||
          Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? rest

  def Stmt.CaseList.usesObjectBuiltinOtherThanLoadImmutable? :
      List (SwitchCaseValue × List Stmt) → Bool
    | [] => false
    | (_value, body) :: rest =>
        Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? body ||
          Stmt.CaseList.usesObjectBuiltinOtherThanLoadImmutable? rest
end

mutual
  def Expr.hasCallNamed? (wanted : Name) : Expr → Bool
    | .lit _ => false
    | .stringLit _ => false
    | .bytesLit _ => false
    | .var _ => false
    | .call _ callee args =>
        callee == wanted || Expr.List.hasCallNamed? wanted args

  def Expr.List.hasCallNamed? (wanted : Name) : List Expr → Bool
    | [] => false
    | expr :: rest =>
        Expr.hasCallNamed? wanted expr ||
          Expr.List.hasCallNamed? wanted rest
end

mutual
  def Stmt.hasCallNamed? (wanted : Name) : Stmt → Bool
    | .block stmts => Stmt.List.hasCallNamed? wanted stmts
    | .letDecl _ none => false
    | .letDecl _ (some value) => Expr.hasCallNamed? wanted value
    | .assign _ value => Expr.hasCallNamed? wanted value
    | .exprStmt expr => Expr.hasCallNamed? wanted expr
    | .functionDef _ _ _ body => Stmt.List.hasCallNamed? wanted body
    | .switch scrutinee cases default =>
        Expr.hasCallNamed? wanted scrutinee ||
          Stmt.CaseList.hasCallNamed? wanted cases ||
            Stmt.List.hasCallNamed? wanted default
    | .forLoop pre condition post body =>
        Stmt.List.hasCallNamed? wanted pre ||
          Expr.hasCallNamed? wanted condition ||
            Stmt.List.hasCallNamed? wanted post ||
              Stmt.List.hasCallNamed? wanted body
    | .ifThen condition body =>
        Expr.hasCallNamed? wanted condition ||
          Stmt.List.hasCallNamed? wanted body
    | .break => false
    | .continue => false
    | .leave => false

  def Stmt.List.hasCallNamed? (wanted : Name) : List Stmt → Bool
    | [] => false
    | stmt :: rest =>
        Stmt.hasCallNamed? wanted stmt ||
          Stmt.List.hasCallNamed? wanted rest

  def Stmt.CaseList.hasCallNamed? (wanted : Name) :
      List (SwitchCaseValue × List Stmt) → Bool
    | [] => false
    | (_value, body) :: rest =>
        Stmt.List.hasCallNamed? wanted body ||
          Stmt.CaseList.hasCallNamed? wanted rest
end

namespace NameList

def insertUnique (name : Name) : List Name → List Name
  | [] => [name]
  | head :: rest =>
      if head == name then
        head :: rest
      else
        head :: insertUnique name rest

def unique : List Name → List Name
  | [] => []
  | name :: rest => insertUnique name (unique rest)

end NameList

namespace FunctionDef

def loadImmutableNames (fn : FunctionDef) : List Name :=
  Stmt.List.loadImmutableNames fn.body

def forkSpellingOk? (version : Yul.SolcValidation.EvmVersion)
    (fn : FunctionDef) : Bool :=
  Stmt.List.forkSpellingOk? version fn.body

def hasCallNamed? (wanted : Name) (fn : FunctionDef) : Bool :=
  Stmt.List.hasCallNamed? wanted fn.body

namespace List

def loadImmutableNames : List (Name × FunctionDef) → List Name
  | [] => []
  | (_name, fn) :: rest =>
      fn.loadImmutableNames ++ loadImmutableNames rest

def forkSpellingOk? (version : Yul.SolcValidation.EvmVersion) :
    List (Name × FunctionDef) → Bool
  | [] => true
  | (_name, fn) :: rest =>
      fn.forkSpellingOk? version && forkSpellingOk? version rest

def hasCallNamed? (wanted : Name) : List (Name × FunctionDef) → Bool
  | [] => false
  | (_name, fn) :: rest =>
      fn.hasCallNamed? wanted || hasCallNamed? wanted rest

end List
end FunctionDef

namespace Object

def dialectProfile (object : Object) :
    Yul.SolcValidation.DialectProfile :=
  object.evmVersion.dialectProfile

def forkSpellingOk? (object : Object) : Bool :=
  Stmt.List.forkSpellingOk? object.evmVersion object.dispatcher &&
    FunctionDef.List.forkSpellingOk? object.evmVersion object.functions

def loadImmutableNames (object : Object) : List Name :=
  NameList.unique
    (Stmt.List.loadImmutableNames object.dispatcher ++
      FunctionDef.List.loadImmutableNames object.functions)

def codeUsesCodeLayoutBuiltin? (object : Object) : Bool :=
  Stmt.List.usesCodeLayoutBuiltinFor? object.name object.dispatcher ||
    object.functions.any
      (fun entry =>
        Stmt.List.usesCodeLayoutBuiltinFor? object.name entry.snd.body)

def literalValues (object : Object) : List Word :=
  Stmt.List.literalValues object.dispatcher ++
    object.functions.foldr
      (fun entry acc => Stmt.List.literalValues entry.snd.body ++ acc)
      []

def usesObjectBuiltinOtherThanLoadImmutable? (object : Object) : Bool :=
  Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? object.dispatcher ||
    object.functions.any
      (fun entry =>
        Stmt.List.usesObjectBuiltinOtherThanLoadImmutable? entry.snd.body)

def callSearchFuel : Nat := 100000

mutual
  def hasCallNamedFuel? : Nat → Name → Object → Bool
    | 0, _, _ => true
    | fuel + 1, wanted, object =>
        Stmt.List.hasCallNamed? wanted object.dispatcher ||
          FunctionDef.List.hasCallNamed? wanted object.functions ||
            Object.List.hasCallNamedFuel? fuel wanted object.objects

  def List.hasCallNamedFuel? : Nat → Name → List Object → Bool
    | 0, _, _ => true
    | _fuel + 1, _, [] => false
    | fuel + 1, wanted, object :: rest =>
        object.hasCallNamedFuel? fuel wanted ||
          List.hasCallNamedFuel? fuel wanted rest
end

def hasCallNamed? (wanted : Name) (object : Object) : Bool :=
  object.hasCallNamedFuel? callSearchFuel wanted

def noRawClzCall? (object : Object) : Bool :=
  !object.hasCallNamed? "clz"

end Object

namespace ImmutableReference

def patchStmt? (reference : ImmutableReference) (base value : Expr) :
    Option Stmt :=
  if reference.isPatchable then
    some
      (.exprStmt
        (.call .primitive "mstore"
          [ .call .primitive "add"
              [base, .lit (EvmYul.UInt256.ofNat reference.start)]
          , value ]))
  else
    none

namespace List

def patchStmts? : List ImmutableReference → Expr → Expr → Option (List Stmt)
  | [], _base, _value => some []
  | reference :: rest, base, value => do
      let head ← reference.patchStmt? base value
      let tail ← patchStmts? rest base value
      some (head :: tail)

end List
end ImmutableReference

namespace ImmutableReference

def markerBase : Nat :=
  2 ^ 255

def markerValue (index : Nat) : Word :=
  EvmYul.UInt256.ofNat (markerBase + index + 1)

def markerEntriesFromNat : Nat → List Name → List (Name × Word)
  | _, [] => []
  | index, name :: rest =>
      (name, markerValue index) :: markerEntriesFromNat (index + 1) rest

def entriesDisjointFromValues? (entries : List (Name × Word))
    (values : List Word) : Bool :=
  entries.all
    (fun entry => !values.any (fun value => value == entry.snd))

def zeroEntries : List Name → List (Name × Word)
  | [] => []
  | name :: rest => (name, EvmYul.UInt256.ofNat 0) :: zeroEntries rest

def shift (base : Nat) (reference : ImmutableReference) :
    ImmutableReference :=
  { reference with start := base + reference.start }

def shiftReferences (base : Nat) : List ImmutableReference →
    List ImmutableReference :=
  List.map (shift base)

def shiftEntry (base : Nat)
    (entry : Name × List ImmutableReference) :
    Name × List ImmutableReference :=
  (entry.fst, shiftReferences base entry.snd)

def shiftEntries (base : Nat) :
    List (Name × List ImmutableReference) →
      List (Name × List ImmutableReference) :=
  List.map (shiftEntry base)

end ImmutableReference

namespace Bytecode

def startsWithAt (needle bytes : List UInt8) (start : Nat) : Bool :=
  (bytes.drop start).take needle.length == needle

def findOccurrencesAux (needle bytes : List UInt8) :
    Nat → Nat → List Nat → List Nat
  | _start, 0, acc => acc.reverse
  | start, fuel + 1, acc =>
      let acc :=
        if startsWithAt needle bytes start then
          start :: acc
        else
          acc
      findOccurrencesAux needle bytes (start + 1) fuel acc

def findOccurrencesCursorAux (needle : List UInt8) :
    List UInt8 → Nat → Nat → List Nat → List Nat
  | _cursor, _start, 0, acc => acc.reverse
  | [], _start, _fuel + 1, acc => acc.reverse
  | cursor@(_byte :: tail), start, fuel + 1, acc =>
      let acc :=
        if cursor.take needle.length == needle then
          start :: acc
        else
          acc
      findOccurrencesCursorAux needle tail (start + 1) fuel acc

def findOccurrencesFast (needle bytes : List UInt8) : List Nat :=
  match needle with
  | [] => []
  | _ :: _ =>
      findOccurrencesCursorAux needle bytes 0 (bytes.length + 1) []

@[implemented_by findOccurrencesFast]
def findOccurrences (needle bytes : List UInt8) : List Nat :=
  match needle with
  | [] => []
  | _ :: _ => findOccurrencesAux needle bytes 0 (bytes.length + 1) []

private theorem findOccurrencesCursorAux_eq
    {needle bytes cursor : List UInt8} {start : Nat} {acc : List Nat}
    (hNeedle : needle ≠ [])
    (hCursor : bytes.drop start = cursor) :
    findOccurrencesCursorAux needle cursor start (cursor.length + 1) acc =
      findOccurrencesAux needle bytes start (cursor.length + 1) acc := by
  induction cursor generalizing bytes start acc with
  | nil =>
      simp [findOccurrencesCursorAux, findOccurrencesAux,
        startsWithAt, hCursor, hNeedle]
  | cons byte tail ih =>
      have hTail : bytes.drop (start + 1) = tail := by
        calc
          bytes.drop (start + 1) = (bytes.drop start).drop 1 := by
            exact (List.drop_drop (i := 1) (j := start) (l := bytes)).symm
          _ = tail := by simp [hCursor]
      have hStarts :
          startsWithAt needle bytes start =
            ((byte :: tail).take needle.length == needle) := by
        simp [startsWithAt, hCursor]
      rw [findOccurrencesCursorAux, findOccurrencesAux, hStarts]
      exact ih hTail

theorem findOccurrencesFast_eq
    (needle bytes : List UInt8) :
    findOccurrencesFast needle bytes = findOccurrences needle bytes := by
  cases needle with
  | nil => rfl
  | cons byte tail =>
      apply findOccurrencesCursorAux_eq
      · simp
      · rfl

def zeroWord32 : List UInt8 :=
  Assembly.Bytecode.encodeWord32 (EvmYul.UInt256.ofNat 0)

def patchBytesAt (start : Nat) (replacement bytes : List UInt8) :
    List UInt8 :=
  bytes.take start ++ replacement ++ bytes.drop (start + replacement.length)

def zeroImmutableReferences : List UInt8 → List ImmutableReference → List UInt8
  | bytes, [] => bytes
  | bytes, reference :: rest =>
      zeroImmutableReferences
        (patchBytesAt reference.start zeroWord32 bytes) rest

def zeroImmutableReferenceEntries : List UInt8 →
    List (Name × List ImmutableReference) → List UInt8
  | bytes, [] => bytes
  | bytes, (_name, references) :: rest =>
      zeroImmutableReferenceEntries
        (zeroImmutableReferences bytes references) rest

def immutableReferencesForMarker (bytes : List UInt8) (value : Word) :
    List ImmutableReference :=
  (findOccurrences (Assembly.Bytecode.encodeWord32 value) bytes).map
    fun start => { start := start, length := ImmutableReference.patchLength }

def immutableReferencesForMarkerFromCodes
    (zeroBytes markerBytes : List UInt8) (value : Word) :
    List ImmutableReference :=
  (findOccurrences (Assembly.Bytecode.encodeWord32 value) markerBytes).filter
      (fun start => startsWithAt zeroWord32 zeroBytes start)
    |>.map
      fun start => { start := start, length := ImmutableReference.patchLength }

def immutableReferenceEntries (bytes : List UInt8) :
    List (Name × Word) → List (Name × List ImmutableReference)
  | [] => []
  | (name, value) :: rest =>
      (name, immutableReferencesForMarker bytes value) ::
        immutableReferenceEntries bytes rest

def immutableReferenceEntriesFromCodes
    (zeroBytes markerBytes : List UInt8) :
    List (Name × Word) → List (Name × List ImmutableReference)
  | [] => []
  | (name, value) :: rest =>
      (name, immutableReferencesForMarkerFromCodes zeroBytes markerBytes value) ::
        immutableReferenceEntriesFromCodes zeroBytes markerBytes rest

end Bytecode

namespace Object

def canUseSingleImmutableMarkerPass? (object : Object)
    (markerImmutableValues : List (Name × Word)) : Bool :=
  !object.codeUsesCodeLayoutBuiltin? &&
    !object.usesObjectBuiltinOtherThanLoadImmutable? &&
      ImmutableReference.entriesDisjointFromValues?
        markerImmutableValues object.literalValues

end Object

mutual
  def Expr.toYul? : Expr → Option AstExpr
    | .lit value => some (.Lit value)
    | .stringLit value => do
        let word ← StringLiteral.word? value
        some (.Lit word)
    | .bytesLit bytes => do
        let word ← StringLiteral.wordBytes? bytes
        some (.Lit word)
    | .var name => some (.Var name)
    | .call .primitive callee args => do
        let op ← Primitive.ofName? callee
        let args' ← Expr.List.toYul? args
        some (.Call (.inl op) args')
    | .call .user callee args => do
        let args' ← Expr.List.toYul? args
        some (.Call (.inr callee) args')
    | .call .objectBuiltin _ _ => none
    | .call .dialectBuiltin _ _ => none

  def Expr.List.toYul? : List Expr → Option (List AstExpr)
    | [] => some []
    | expr :: rest => do
        let head ← Expr.toYul? expr
        let tail ← Expr.List.toYul? rest
        some (head :: tail)

  def Stmt.toYul? : Stmt → Option AstStmt
    | .block stmts => do
        let stmts' ← Stmt.List.toYul? stmts
        some (.Block stmts')
    | .letDecl names none =>
        some (.Let names none)
    | .letDecl names (some value) => do
        let value' ← value.toYul?
        some (.Let names (some value'))
    | .assign names value => do
        let value' ← value.toYul?
        some (.Assign names value')
    | .exprStmt expr => do
        let expr' ← expr.toYul?
        some (.ExprStmtCall expr')
    | .functionDef _ _ _ _ =>
        some (.Block [])
    | .switch scrutinee cases default => do
        let scrutinee' ← scrutinee.toYul?
        let cases' ← Stmt.CaseList.toYul? cases
        let default' ← Stmt.List.toYul? default
        some (.Switch scrutinee' cases' default')
    | .forLoop pre condition post body => do
        let pre' ← Stmt.List.toYul? pre
        let condition' ← condition.toYul?
        let post' ← Stmt.List.toYul? post
        let body' ← Stmt.List.toYul? body
        let loop := .For condition' post' body'
        match pre' with
        | [] => some loop
        | _ => some (.Block (pre' ++ [loop]))
    | .ifThen condition body => do
        let condition' ← condition.toYul?
        let body' ← Stmt.List.toYul? body
        some (.If condition' body')
    | .break => some .Break
    | .continue => some .Continue
    | .leave => some .Leave

  def Stmt.List.toYul? : List Stmt → Option (List AstStmt)
    | [] => some []
    | stmt :: rest => do
        let head ← Stmt.toYul? stmt
        let tail ← Stmt.List.toYul? rest
        some (head :: tail)

  def Stmt.CaseList.toYul? : List (SwitchCaseValue × List Stmt) →
      Option (List (Word × List AstStmt))
    | [] => some []
    | (value, body) :: rest => do
        let value' ← value.toWord?
        let body' ← Stmt.List.toYul? body
        let rest' ← Stmt.CaseList.toYul? rest
        some ((value', body') :: rest')

  def FunctionDef.toYul? (fn : FunctionDef) :
      Option AstFunctionDefinition := do
    let body ← Stmt.List.toYul? fn.body
    some (.Def fn.params fn.returns body)

  def FunctionDef.List.toYul? : List (Name × FunctionDef) →
      Option (List (Name × AstFunctionDefinition))
    | [] => some []
    | (name, fn) :: rest => do
        let fn' ← FunctionDef.toYul? fn
        let rest' ← FunctionDef.List.toYul? rest
        some ((name, fn') :: rest')
end

namespace Stmt

theorem toYul?_functionDef_erases
    (name : Name) (params returns : List Name) (body : List Stmt) :
    Stmt.toYul? (.functionDef name params returns body) =
      some (.Block []) := by
  rfl

end Stmt

mutual
  def Expr.resolveObjectBuiltinsIn? (expr : Expr)
      (context : ObjectBuiltinContext) : Option Expr :=
    match expr with
    | .lit value => some (.lit value)
    | .stringLit value => some (.stringLit value)
    | .bytesLit bytes => some (.bytesLit bytes)
    | .var name => some (.var name)
    | .call .objectBuiltin "datasize" [nameArg] => do
        let name ← Expr.objectBuiltinNameArg? nameArg
        let size ← context.size? name
        some (.lit size)
    | .call .objectBuiltin "dataoffset" [nameArg] => do
        let name ← Expr.objectBuiltinNameArg? nameArg
        let offset ← context.offset? name
        some (.lit offset)
    | .call .objectBuiltin "linkersymbol" [nameArg] => do
        let name ← Expr.objectBuiltinNameArg? nameArg
        let value ← context.findLinkerSymbol? name
        some (.lit value)
    | .call .objectBuiltin "loadimmutable" [nameArg] => do
        let name ← Expr.objectBuiltinNameArg? nameArg
        let value ← context.findImmutableValue? name
        some (.lit value)
    | .call .objectBuiltin "datacopy" [target, offset, size] => do
        let target' ← Expr.resolveObjectBuiltinsIn? target context
        let offset' ← Expr.resolveObjectBuiltinsIn? offset context
        let size' ← Expr.resolveObjectBuiltinsIn? size context
        some (.call .primitive "codecopy" [target', offset', size'])
    | .call .objectBuiltin "memoryguard" [value] => do
      let value' ← Expr.resolveObjectBuiltinsIn? value context
      let size ←
          match value' with
          | .lit size => some size
          | _ => none
      some (.lit size)
    | .call kind callee args => do
        let args' ← Expr.List.resolveObjectBuiltinsIn? args context
        some (.call kind callee args')

  def Expr.List.resolveObjectBuiltinsIn? (exprs : List Expr)
      (context : ObjectBuiltinContext) : Option (List Expr) :=
    match exprs with
    | [] => some []
    | expr :: rest => do
        let head ← Expr.resolveObjectBuiltinsIn? expr context
        let tail ← Expr.List.resolveObjectBuiltinsIn? rest context
        some (head :: tail)

  def Stmt.resolveObjectBuiltinsIn? (stmt : Stmt)
      (context : ObjectBuiltinContext) : Option Stmt :=
    match stmt with
    | .block stmts => do
        let stmts' ← Stmt.List.resolveObjectBuiltinsIn? stmts context
        some (.block stmts')
    | .letDecl names none =>
        some (.letDecl names none)
    | .letDecl names (some value) => do
        let value' ← value.resolveObjectBuiltinsIn? context
        some (.letDecl names (some value'))
    | .assign names value => do
        let value' ← value.resolveObjectBuiltinsIn? context
        some (.assign names value')
    | .exprStmt (.call .objectBuiltin "setimmutable"
          [base, nameArg, value]) => do
        let name ← Expr.objectBuiltinNameArg? nameArg
        let base' ← base.resolveObjectBuiltinsIn? context
        let value' ← value.resolveObjectBuiltinsIn? context
        let references := context.immutableReferencesFor name
        let stmts ←
          ImmutableReference.List.patchStmts? references base' value'
        some (.block stmts)
    | .exprStmt expr => do
        let expr' ← expr.resolveObjectBuiltinsIn? context
        some (.exprStmt expr')
    | .functionDef name params returns body => do
        let body' ← Stmt.List.resolveObjectBuiltinsIn? body context
        some (.functionDef name params returns body')
    | .switch scrutinee cases default => do
        let scrutinee' ← scrutinee.resolveObjectBuiltinsIn? context
        let cases' ← Stmt.CaseList.resolveObjectBuiltinsIn? cases context
        let default' ← Stmt.List.resolveObjectBuiltinsIn? default context
        some (.switch scrutinee' cases' default')
    | .forLoop pre condition post body => do
        let pre' ← Stmt.List.resolveObjectBuiltinsIn? pre context
        let condition' ← condition.resolveObjectBuiltinsIn? context
        let post' ← Stmt.List.resolveObjectBuiltinsIn? post context
        let body' ← Stmt.List.resolveObjectBuiltinsIn? body context
        some (.forLoop pre' condition' post' body')
    | .ifThen condition body => do
        let condition' ← condition.resolveObjectBuiltinsIn? context
        let body' ← Stmt.List.resolveObjectBuiltinsIn? body context
        some (.ifThen condition' body')
    | .break => some .break
    | .continue => some .continue
    | .leave => some .leave

  def Stmt.List.resolveObjectBuiltinsIn? (stmts : List Stmt)
      (context : ObjectBuiltinContext) : Option (List Stmt) :=
    match stmts with
    | [] => some []
    | stmt :: rest => do
        let head ← Stmt.resolveObjectBuiltinsIn? stmt context
        let tail ← Stmt.List.resolveObjectBuiltinsIn? rest context
        some (head :: tail)

  def Stmt.CaseList.resolveObjectBuiltinsIn?
      (cases : List (SwitchCaseValue × List Stmt))
      (context : ObjectBuiltinContext) :
      Option (List (SwitchCaseValue × List Stmt)) :=
    match cases with
    | [] => some []
    | (value, body) :: rest => do
        let body' ← Stmt.List.resolveObjectBuiltinsIn? body context
        let rest' ← Stmt.CaseList.resolveObjectBuiltinsIn? rest context
        some ((value, body') :: rest')

  def FunctionDef.resolveObjectBuiltinsIn? (fn : FunctionDef)
      (context : ObjectBuiltinContext) : Option FunctionDef := do
    let body ← Stmt.List.resolveObjectBuiltinsIn? fn.body context
    some { params := fn.params, returns := fn.returns, body := body }

  def FunctionDef.List.resolveObjectBuiltinsIn?
      (functions : List (Name × FunctionDef)) (context : ObjectBuiltinContext) :
      Option (List (Name × FunctionDef)) :=
    match functions with
    | [] => some []
    | (name, fn) :: rest => do
        let fn' ← FunctionDef.resolveObjectBuiltinsIn? fn context
        let rest' ← FunctionDef.List.resolveObjectBuiltinsIn? rest context
        some ((name, fn') :: rest')
end

namespace Expr

def resolveObjectBuiltins? (expr : Expr) (layout : ObjectLayout) :
    Option Expr :=
  expr.resolveObjectBuiltinsIn? (ObjectBuiltinContext.ofLayout layout)

namespace List

def resolveObjectBuiltins? (exprs : List Expr) (layout : ObjectLayout) :
    Option (List Expr) :=
  Expr.List.resolveObjectBuiltinsIn? exprs
    (ObjectBuiltinContext.ofLayout layout)

end List
end Expr

namespace Stmt

def resolveObjectBuiltins? (stmt : Stmt) (layout : ObjectLayout) :
    Option Stmt :=
  stmt.resolveObjectBuiltinsIn? (ObjectBuiltinContext.ofLayout layout)

namespace List

def resolveObjectBuiltins? (stmts : List Stmt) (layout : ObjectLayout) :
    Option (List Stmt) :=
  Stmt.List.resolveObjectBuiltinsIn? stmts
    (ObjectBuiltinContext.ofLayout layout)

end List

namespace CaseList

def resolveObjectBuiltins? (cases : List (SwitchCaseValue × List Stmt))
    (layout : ObjectLayout) :
    Option (List (SwitchCaseValue × List Stmt)) :=
  Stmt.CaseList.resolveObjectBuiltinsIn? cases
    (ObjectBuiltinContext.ofLayout layout)

end CaseList
end Stmt

namespace FunctionDef

def resolveObjectBuiltins? (fn : FunctionDef) (layout : ObjectLayout) :
    Option FunctionDef :=
  fn.resolveObjectBuiltinsIn? (ObjectBuiltinContext.ofLayout layout)

namespace List

def resolveObjectBuiltins? (functions : List (Name × FunctionDef))
    (layout : ObjectLayout) :
    Option (List (Name × FunctionDef)) :=
  FunctionDef.List.resolveObjectBuiltinsIn? functions
    (ObjectBuiltinContext.ofLayout layout)

end List
end FunctionDef

namespace Expr

theorem resolveObjectBuiltins_datacopy_codecopy
    {context : ObjectBuiltinContext} {target offset size : Expr}
    {target' offset' size' : Expr}
    (hTarget : target.resolveObjectBuiltinsIn? context = some target')
    (hOffset : offset.resolveObjectBuiltinsIn? context = some offset')
    (hSize : size.resolveObjectBuiltinsIn? context = some size') :
    Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datacopy" [target, offset, size]) context =
      some (.call .primitive "codecopy" [target', offset', size']) := by
  simp [Expr.resolveObjectBuiltinsIn?, hTarget, hOffset, hSize]

theorem resolveObjectBuiltins_datasize_namedData
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout}
    (hName : Name.objectPathComponent? name = true) :
    Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datasize" [.stringLit name])
        { layout := layout
          dataSizes := DataSection.sizeEntries [
            DataSection.mk (some name) bytes
          ]
          dataOffsets := []
          linkerSymbols := [] } =
      some (.lit (EvmYul.UInt256.ofNat bytes.length)) := by
  simp [Expr.resolveObjectBuiltinsIn?, Expr.objectBuiltinNameArg?,
    ObjectBuiltinContext.size?, ObjectBuiltinContext.findDataSize?,
    DataSection.sizeEntries, DataSection.sizeEntry?, DataSection.size, hName]

theorem resolveObjectBuiltins_dataoffset_namedDataBase
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout} {base : Nat}
    (hName : Name.objectPathComponent? name = true) :
    Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "dataoffset" [.stringLit name])
        { layout := layout
          dataSizes := []
          dataOffsets := DataSection.offsetEntriesFromNat base [
            DataSection.mk (some name) bytes
          ]
          linkerSymbols := [] } =
      some (.lit (EvmYul.UInt256.ofNat base)) := by
  simp [Expr.resolveObjectBuiltinsIn?, Expr.objectBuiltinNameArg?,
    ObjectBuiltinContext.offset?, ObjectBuiltinContext.findDataOffset?,
    DataSection.offsetEntriesFromNat, DataSection.offsetEntryFromNat?, hName]

theorem toYul_after_resolveObjectBuiltins_datasize_namedData
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout}
    (hName : Name.objectPathComponent? name = true) :
    (Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datasize" [.stringLit name])
        { layout := layout
          dataSizes := DataSection.sizeEntries [
            DataSection.mk (some name) bytes
          ]
          dataOffsets := []
          linkerSymbols := [] } >>= Expr.toYul?) =
      some (.Lit (EvmYul.UInt256.ofNat bytes.length)) := by
  simp [resolveObjectBuiltins_datasize_namedData hName, Expr.toYul?]

theorem toYul_after_resolveObjectBuiltins_dataoffset_namedDataBase
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout} {base : Nat}
    (hName : Name.objectPathComponent? name = true) :
    (Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "dataoffset" [.stringLit name])
        { layout := layout
          dataSizes := []
          dataOffsets := DataSection.offsetEntriesFromNat base [
            DataSection.mk (some name) bytes
          ]
          linkerSymbols := [] } >>= Expr.toYul?) =
      some (.Lit (EvmYul.UInt256.ofNat base)) := by
  simp [resolveObjectBuiltins_dataoffset_namedDataBase hName, Expr.toYul?]

theorem toYul_after_resolveObjectBuiltins_datacopy_codecopy
    {context : ObjectBuiltinContext} {target offset size : Expr}
    {target' offset' size' : Expr}
    {targetYul offsetYul sizeYul : AstExpr}
    (hTarget : target.resolveObjectBuiltinsIn? context = some target')
    (hOffset : offset.resolveObjectBuiltinsIn? context = some offset')
    (hSize : size.resolveObjectBuiltinsIn? context = some size')
    (hTargetYul : target'.toYul? = some targetYul)
    (hOffsetYul : offset'.toYul? = some offsetYul)
    (hSizeYul : size'.toYul? = some sizeYul) :
    (Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datacopy" [target, offset, size])
        context >>= Expr.toYul?) =
      some
        (.Call (.inl ((.Env .CODECOPY : EvmYul.Operation .Yul)))
          [targetYul, offsetYul, sizeYul]) := by
  simp [resolveObjectBuiltins_datacopy_codecopy hTarget hOffset hSize,
    Expr.toYul?, Expr.List.toYul?, Primitive.ofName?, hTargetYul, hOffsetYul,
    hSizeYul]

theorem resolveObjectBuiltins_memoryguard
    {context : ObjectBuiltinContext} {value : Expr} {size : Word}
    (hValue : value.resolveObjectBuiltinsIn? context = some (.lit size)) :
    Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "memoryguard" [value])
        context =
      some (.lit size) := by
  simp [Expr.resolveObjectBuiltinsIn?, hValue]

end Expr

namespace FunctionPrep

theorem list_sizeOf_lt_sizeOf_of_mem {α : Type} [SizeOf α]
    {x : α} {xs : List α} (hMem : x ∈ xs) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      cases hMem <;> rw [List.cons.sizeOf_spec]
      · omega
      · specialize ih ‹x ∈ tail›
        omega

namespace Expr

mutual
  def names {results : Nat} : Functions.Expr results → List Name
    | .lit _value => []
    | .var name => [name]
    | .code _code => []
    | .prim _op args => ExprSeq.names args

  def ExprSeq.names {results : Nat} :
      Locals.ExprSeq results → List Name
    | .nil => []
    | .cons head tail => names head ++ ExprSeq.names tail
end

end Expr

def anyNameIn (needles haystack : List Name) : Bool :=
  needles.any fun name => haystack.contains name

mutual
  def Stmt.touchNames : Functions.Stmt → List Name
    | .expr expr => Expr.names expr
    | .let_ name value => name :: Expr.names value
    | .assign name value => name :: Expr.names value
    | .block body => Block.touchNames body
    | .if_ cond body => Expr.names cond ++ Block.touchNames body
    | .switch scrutinee cases defaultBody =>
        Expr.names scrutinee ++
          CaseList.touchNames cases ++ Default.touchNames defaultBody
    | .for_ init cond post body =>
        Block.touchNames init ++ Expr.names cond ++
          Block.touchNames post ++ Block.touchNames body
    | .brk => []
    | .cont => []
    | .leave => []
    | .call targets _functionName args =>
        targets ++ args.foldr (fun arg names => Expr.names arg ++ names) []
    | .terminal _kind => []
    | .terminalArgs _kind args => Expr.ExprSeq.names args
  termination_by stmt => sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.touchNames (block : Functions.Block) : List Name :=
    StmtList.touchNames block.stmts
  termination_by sizeOf block
  decreasing_by
    cases block
    simp_wf

  def StmtList.touchNames : List Functions.Stmt → List Name
    | [] => []
    | stmt :: rest => Stmt.touchNames stmt ++ StmtList.touchNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact list_sizeOf_lt_sizeOf_of_mem (by assumption)
      | omega

  def CaseList.touchNames :
      List (Word × Functions.Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        Block.touchNames body ++ CaseList.touchNames rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Default.touchNames : Option Functions.Block → List Name
    | none => []
    | some body => Block.touchNames body
  termination_by defaultBody => sizeOf defaultBody
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def Stmt.declaredNames : Functions.Stmt → List Name
    | .let_ name _value => [name]
    | .block body => Block.declaredNames body
    | .if_ _cond body => Block.declaredNames body
    | .switch _scrutinee cases defaultBody =>
        CaseList.declaredNames cases ++ Default.declaredNames defaultBody
    | .for_ init _cond post body =>
        Block.declaredNames init ++
          Block.declaredNames post ++ Block.declaredNames body
    | _ => []
  termination_by stmt => sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.declaredNames (block : Functions.Block) : List Name :=
    StmtList.declaredNames block.stmts
  termination_by sizeOf block
  decreasing_by
    cases block
    simp_wf

  def StmtList.declaredNames : List Functions.Stmt → List Name
    | [] => []
    | stmt :: rest => Stmt.declaredNames stmt ++ StmtList.declaredNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def CaseList.declaredNames :
      List (Word × Functions.Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        Block.declaredNames body ++ CaseList.declaredNames rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Default.declaredNames : Option Functions.Block → List Name
    | none => []
    | some body => Block.declaredNames body
  termination_by defaultBody => sizeOf defaultBody
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def letName? : Functions.Stmt → Option Name
  | .let_ name _value => some name
  | _ => none

def splitAfterLastTouch (names : List Name) :
    List Functions.Stmt → List Functions.Stmt × List Functions.Stmt
  | [] => ([], [])
  | stmt :: rest =>
      let (inside, outside) := splitAfterLastTouch names rest
      if anyNameIn names (Stmt.touchNames stmt) then
        (stmt :: inside, outside)
      else
        match inside with
        | [] => ([], stmt :: outside)
        | _ => (stmt :: inside, outside)

def splitClosedAfterLastTouchFuel :
    Nat → List Name → List Functions.Stmt →
      List Functions.Stmt × List Functions.Stmt
  | 0, names, stmts => splitAfterLastTouch names stmts
  | fuel + 1, names, stmts =>
      let (inside, outside) := splitAfterLastTouch names stmts
      let declaredInside := StmtList.declaredNames inside
      if anyNameIn declaredInside (StmtList.touchNames outside) then
        splitClosedAfterLastTouchFuel fuel (names ++ declaredInside) stmts
      else
        (inside, outside)

def StmtList.scopeLetLifetimesMappedFuel :
    Nat → List Functions.Stmt → List Functions.Stmt
  | 0, stmts => stmts
  | _fuel + 1, [] => []
  | fuel + 1, stmt :: rest =>
      match letName? stmt with
      | some name =>
          let (inside, outside) :=
            splitClosedAfterLastTouchFuel (rest.length + 1) [name] rest
          let declaredInside := StmtList.declaredNames inside
          let outsideTouches := StmtList.touchNames outside
          if anyNameIn declaredInside outsideTouches then
            stmt :: StmtList.scopeLetLifetimesMappedFuel fuel rest
          else
            .block
                { stmts :=
                    stmt ::
                      StmtList.scopeLetLifetimesMappedFuel fuel inside } ::
              StmtList.scopeLetLifetimesMappedFuel fuel outside
      | none =>
          stmt :: StmtList.scopeLetLifetimesMappedFuel fuel rest
termination_by fuel stmts => (fuel, sizeOf stmts)
decreasing_by
  all_goals simp_wf
  all_goals omega

mutual
  def Stmt.scopeLetLifetimes : Functions.Stmt → Functions.Stmt
    | .block body => .block (Block.scopeLetLifetimes body)
    | .if_ cond body => .if_ cond (Block.scopeLetLifetimes body)
    | .switch scrutinee cases defaultBody =>
        .switch scrutinee (CaseList.scopeLetLifetimes cases)
          (Default.scopeLetLifetimes defaultBody)
    | .for_ init cond post body =>
        .for_ (Block.scopeLetLifetimes init) cond
          (Block.scopeLetLifetimes post) (Block.scopeLetLifetimes body)
    | stmt => stmt
  termination_by stmt => sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.scopeLetLifetimes (block : Functions.Block) :
      Functions.Block :=
    { stmts := StmtList.scopeLetLifetimes block.stmts }
  termination_by sizeOf block
  decreasing_by
    cases block
    simp_wf

  def StmtList.scopeLetLifetimes :
      List Functions.Stmt → List Functions.Stmt
    | stmts =>
        let mapped := stmts.map Stmt.scopeLetLifetimes
        StmtList.scopeLetLifetimesMappedFuel (mapped.length + 1) mapped
  termination_by stmts => sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact list_sizeOf_lt_sizeOf_of_mem (by assumption)
      | omega

  def CaseList.scopeLetLifetimes :
      List (Word × Functions.Block) → List (Word × Functions.Block)
    | [] => []
    | (value, body) :: rest =>
        (value, Block.scopeLetLifetimes body) ::
          CaseList.scopeLetLifetimes rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Default.scopeLetLifetimes :
      Option Functions.Block → Option Functions.Block
    | none => none
    | some body => some (Block.scopeLetLifetimes body)
  termination_by defaultBody => sizeOf defaultBody
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

namespace FunDef

def scopeLetLifetimes (fn : Functions.FunDef) : Functions.FunDef :=
  { fn with body := Block.scopeLetLifetimes fn.body }

end FunDef

namespace Program

def scopeLetLifetimes (program : Functions.Program) :
    Functions.Program :=
  { program with
    functions := program.functions.map FunDef.scopeLetLifetimes
    body := Block.scopeLetLifetimes program.body }

end Program

end FunctionPrep

namespace Object

namespace ItemRef

def objectsFromNat : Nat → List Object → List ObjectItemRef
  | _, [] => []
  | index, _object :: rest =>
      .object index :: objectsFromNat (index + 1) rest

def dataFromNat : Nat → List DataSection → List ObjectItemRef
  | _, [] => []
  | index, _dataSection :: rest =>
      .data index :: dataFromNat (index + 1) rest

end ItemRef

def defaultItems (object : Object) : List ObjectItemRef :=
  ItemRef.objectsFromNat 0 object.objects ++
    ItemRef.dataFromNat 0 object.data

def effectiveItems (object : Object) : List ObjectItemRef :=
  match object.items with
  | [] => object.defaultItems
  | items => items

def dataSizeEntries (object : Object) : List (Name × Word) :=
  DataSection.sizeEntries object.data

def dataOffsetEntriesFromNat (object : Object) (base : Nat) :
    List (Name × Word) :=
  DataSection.offsetEntriesFromNat base object.data

def builtinContext (object : Object) (layout : ObjectLayout) :
    ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := []
    linkerSymbols := [] }

def builtinContextWithLocalDataBase (object : Object) (layout : ObjectLayout)
    (base : Nat) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := object.dataOffsetEntriesFromNat base
    linkerSymbols := [] }

def builtinContextWithLinkerSymbols
    (object : Object) (layout : ObjectLayout)
    (linkerSymbols : List (Name × Word)) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := []
    linkerSymbols := linkerSymbols }

def builtinContextWithLocalDataBaseAndLinkerSymbols
    (object : Object) (layout : ObjectLayout) (base : Nat)
    (linkerSymbols : List (Name × Word)) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := object.dataOffsetEntriesFromNat base
    linkerSymbols := linkerSymbols }

def resolveObjectBuiltinsIn? (object : Object)
    (context : ObjectBuiltinContext) : Option Object := do
  let memoryContract ← MemoryGuard.Object.inferredContract? object
  let context := { context with memoryContract := memoryContract }
  let dispatcher ← Stmt.List.resolveObjectBuiltinsIn? object.dispatcher context
  let functions ←
    FunctionDef.List.resolveObjectBuiltinsIn? object.functions context
  some
    { name := object.name
      dispatcher := dispatcher
      functions := functions
      data := object.data
      objects := object.objects
      items := object.items
      memoryContract := memoryContract
      evmVersion := object.evmVersion }

def resolveObjectBuiltins? (object : Object)
    (layout : ObjectLayout) : Option Object :=
  object.resolveObjectBuiltinsIn? (object.builtinContext layout)

def resolveObjectBuiltinsWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Object :=
  object.resolveObjectBuiltinsIn?
    (object.builtinContextWithLocalDataBase layout base)

def resolveObjectBuiltinsWithLinkerSymbols? (object : Object)
    (layout : ObjectLayout) (linkerSymbols : List (Name × Word)) :
    Option Object :=
  object.resolveObjectBuiltinsIn?
    (object.builtinContextWithLinkerSymbols layout linkerSymbols)

def resolveObjectBuiltinsWithLocalDataBaseAndLinkerSymbols? (object : Object)
    (layout : ObjectLayout) (base : Nat)
    (linkerSymbols : List (Name × Word)) : Option Object :=
  object.resolveObjectBuiltinsIn?
    (object.builtinContextWithLocalDataBaseAndLinkerSymbols
      layout base linkerSymbols)

end Object

structure ObjectImage where
  name : Name
  bytes : List UInt8
  immutableReferences : List (Name × List ImmutableReference) := []
  layoutEntries : List ObjectLayout.Entry := []
  dataSizeEntries : List (Name × Word) := []
  dataOffsetEntries : List (Name × Word) := []
  deriving Inhabited, Repr

namespace ObjectImage

def size (image : ObjectImage) : Nat :=
  image.bytes.length

def layoutEntryFromNat (base : Nat) (image : ObjectImage) :
    ObjectLayout.Entry :=
  { name := image.name
    offset := EvmYul.UInt256.ofNat base
    size := EvmYul.UInt256.ofNat image.size }

def layoutEntriesFromNatForPath (base : Nat) (image : ObjectImage) :
    List ObjectLayout.Entry :=
  if Name.objectPathComponent? image.name then
    image.layoutEntryFromNat base ::
      image.layoutEntries.map
        (ObjectLayout.Entry.addBaseAndPrefix base image.name)
  else
    []

def dataSizeEntriesForPath (image : ObjectImage) :
    List (Name × Word) :=
  if Name.objectPathComponent? image.name then
    image.dataSizeEntries.map
      (fun entry => (Name.objectPath image.name entry.fst, entry.snd))
  else
    []

def dataOffsetEntriesFromNatForPath (base : Nat) (image : ObjectImage) :
    List (Name × Word) :=
  if Name.objectPathComponent? image.name then
    image.dataOffsetEntries.map
      (fun entry =>
        ( Name.objectPath image.name entry.fst
        , EvmYul.UInt256.ofNat (base + entry.snd.toNat) ))
  else
    []

def immutableReferenceEntriesFromNat (base : Nat) (image : ObjectImage) :
    List (Name × List ImmutableReference) :=
  ImmutableReference.shiftEntries base image.immutableReferences

def layoutEntriesFromNat : Nat → List ObjectImage → List ObjectLayout.Entry
  | _, [] => []
  | base, image :: rest =>
      image.layoutEntryFromNat base ::
        layoutEntriesFromNat (base + image.size) rest

def bytesAll (images : List ObjectImage) : List UInt8 :=
  Bytecode.concat (images.map (fun image => image.bytes))

def totalSize (images : List ObjectImage) : Nat :=
  images.foldl (fun acc image => acc + image.size) 0

def immutableReferenceEntries : List ObjectImage →
    List (Name × List ImmutableReference)
  | [] => []
  | image :: rest =>
      image.immutableReferences ++ immutableReferenceEntries rest

end ObjectImage

namespace ObjectItemRef

def inBounds? (dataSections : List DataSection)
    (objectImages : List ObjectImage) : ObjectItemRef → Bool
  | .data index => decide (index < dataSections.length)
  | .object index => decide (index < objectImages.length)

def isMetadata? (dataSections : List DataSection) : ObjectItemRef → Bool
  | .data index =>
      match dataSections[index]? with
      | some dataSection => dataSection.name? == some ".metadata"
      | none => false
  | .object _ => false

def payloadSize? (dataSections : List DataSection)
    (objectImages : List ObjectImage) : ObjectItemRef → Option Nat
  | .data index => do
      let dataSection ← dataSections[index]?
      some dataSection.bytes.length
  | .object index => do
      let image ← objectImages[index]?
      some image.size

def payloadBytes? (dataSections : List DataSection)
    (objectImages : List ObjectImage) : ObjectItemRef → Option (List UInt8)
  | .data index => do
      let dataSection ← dataSections[index]?
      some dataSection.bytes
  | .object index => do
      let image ← objectImages[index]?
      some image.bytes

namespace List

def noDuplicates? : List ObjectItemRef → Bool
  | [] => true
  | item :: rest => !rest.contains item && noDuplicates? rest

def sameMembers? (left right : List ObjectItemRef) : Bool :=
  left.all (fun item => right.contains item) &&
    right.all (fun item => left.contains item)

def validFor? (expected items : List ObjectItemRef) : Bool :=
  noDuplicates? items && sameMembers? expected items

def moveMetadataLast (dataSections : List DataSection)
    (items : List ObjectItemRef) : List ObjectItemRef :=
  items.filter (fun item => !item.isMetadata? dataSections) ++
    items.filter (fun item => item.isMetadata? dataSections)

def objectLayoutEntriesFromNat? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    Nat → List ObjectItemRef → Option (List ObjectLayout.Entry)
  | _, [] => some []
  | base, item :: rest => do
      let itemSize ← item.payloadSize? dataSections objectImages
      let tail ←
        objectLayoutEntriesFromNat?
          dataSections objectImages (base + itemSize) rest
      match item with
      | .data _ => some tail
      | .object index => do
          let image ← objectImages[index]?
          some (image.layoutEntriesFromNatForPath base ++ tail)

def dataSizeEntries? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    List ObjectItemRef → Option (List (Name × Word))
  | [] => some []
  | item :: rest => do
      let tail ← dataSizeEntries? dataSections objectImages rest
      match item with
      | .data index => do
          let dataSection ← dataSections[index]?
          match dataSection.sizeEntry? with
          | some entry => some (entry :: tail)
          | none => some tail
      | .object index => do
          let image ← objectImages[index]?
          some (image.dataSizeEntriesForPath ++ tail)

def dataOffsetEntriesFromNat? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    Nat → List ObjectItemRef → Option (List (Name × Word))
  | _, [] => some []
  | base, item :: rest => do
      let itemSize ← item.payloadSize? dataSections objectImages
      let tail ←
        dataOffsetEntriesFromNat?
          dataSections objectImages (base + itemSize) rest
      match item with
      | .object index => do
          let image ← objectImages[index]?
          some (image.dataOffsetEntriesFromNatForPath base ++ tail)
      | .data index => do
          let dataSection ← dataSections[index]?
          match dataSection.offsetEntryFromNat? base with
          | some entry => some (entry :: tail)
          | none => some tail

def payloadBytes? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    List ObjectItemRef → Option (List UInt8)
  | [] => some []
  | item :: rest => do
      let head ← item.payloadBytes? dataSections objectImages
      let tail ← payloadBytes? dataSections objectImages rest
      some (head ++ tail)

def immutableReferenceEntriesFromNat? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    Nat → List ObjectItemRef → Option (List (Name × List ImmutableReference))
  | _, [] => some []
  | base, item :: rest => do
      let itemSize ← item.payloadSize? dataSections objectImages
      let tail ←
        immutableReferenceEntriesFromNat?
          dataSections objectImages (base + itemSize) rest
      match item with
      | .data _ => some tail
      | .object index => do
          let image ← objectImages[index]?
          some (image.immutableReferenceEntriesFromNat base ++ tail)

end List
end ObjectItemRef

namespace Object

def payloadItems? (object : Object) (_objectImages : List ObjectImage) :
    Option (List ObjectItemRef) :=
  let expected := object.defaultItems
  let items := object.effectiveItems
  if ObjectItemRef.List.validFor? expected items then
    some (ObjectItemRef.List.moveMetadataLast object.data items)
  else
    none

end Object

namespace Object

def functionMap (entries : List (Name × AstFunctionDefinition)) :
    Finmap (fun (_ : EvmYul.Yul.Ast.YulFunctionName) =>
      AstFunctionDefinition) :=
  Yul.FunctionList.functionMap entries

def toYulContractWithFunctionEntries? (object : Object) :
    Option (AstContract × List (Name × AstFunctionDefinition)) := do
  let dispatcher ← Stmt.toYul? (.block object.dispatcher)
  let functions ← FunctionDef.List.toYul? object.functions
  some
    ( { dispatcher := dispatcher
        functions := functionMap functions }
    , functions )

def toYulContract? (object : Object) : Option AstContract := do
  let (contract, _functions) ← object.toYulContractWithFunctionEntries?
  some contract

def toYulProgram? (object : Object) : Option Yul.Program := do
  let contract ← Object.toYulContract? object
  some
    { contract := contract
      memoryContract := object.memoryContract }

theorem toYulProgram?_memoryContract
    {object : Object} {program : Yul.Program}
    (hConvert : object.toYulProgram? = some program) :
    program.memoryContract = object.memoryContract := by
  unfold toYulProgram? at hConvert
  cases hContract : Object.toYulContract? object with
  | none => simp [hContract] at hConvert
  | some contract =>
      simp [hContract] at hConvert
      subst program
      rfl

def toSolcYulProgram? (object : Object) :
    Option Yul.Program := do
  let (contract, functions) ← object.toYulContractWithFunctionEntries?
  if object.forkSpellingOk? then
    if Yul.SolcValidation.ContractOkWithEntries?
        object.dialectProfile contract functions then
      some
        { contract := contract
          memoryContract := object.memoryContract }
    else
      none
  else
    none

def toSolcYulOrderedProgram? (object : Object) :
    Option Yul.OrderedProgram := do
  let (contract, functions) ← object.toYulContractWithFunctionEntries?
  if object.forkSpellingOk? then
    if Yul.SolcValidation.ContractOkWithEntries?
        object.dialectProfile contract functions then
      some
        { program :=
            { contract := contract
              memoryContract := object.memoryContract }
          functionEntries := functions }
    else
      none
  else
    none

theorem toSolcYulOrderedProgram?_source
    {object : Object} {ordered : Yul.OrderedProgram}
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
      ordered.RepresentsSource ∧
      ordered.FunctionNamesNodup ∧
      Yul.SolcValidation.ContractOkWithEntries?
          object.dialectProfile
          ordered.program.contract ordered.functionEntries = true ∧
      ordered.program.memoryContract = object.memoryContract := by
  unfold toSolcYulOrderedProgram? at hConvert
  cases hContract : object.toYulContractWithFunctionEntries? with
  | none => simp [hContract] at hConvert
  | some result =>
      rcases result with ⟨contract, functions⟩
      cases hValid :
          Yul.SolcValidation.ContractOkWithEntries?
            object.dialectProfile contract functions <;>
        simp [hContract, hValid] at hConvert
      rcases hConvert with ⟨_hSpelling, hConvert⟩
      subst ordered
      refine ⟨?_, ?_, hValid, rfl⟩
      · unfold Yul.OrderedProgram.RepresentsSource
        unfold toYulContractWithFunctionEntries? at hContract
        cases hDispatcher : Stmt.toYul? (.block object.dispatcher) with
        | none => simp [hDispatcher] at hContract
        | some dispatcher =>
            cases hFunctions : FunctionDef.List.toYul? object.functions with
            | none => simp [hDispatcher, hFunctions] at hContract
            | some entries =>
                simp [hDispatcher, hFunctions] at hContract
                rcases hContract with ⟨rfl, rfl⟩
                rfl
      · unfold Yul.OrderedProgram.FunctionNamesNodup
        have hNames :
            Yul.SolcValidation.FunctionNamesOk?
                (functions.map Prod.fst) = true := by
          have hParts := hValid
          simp [Yul.SolcValidation.ContractOkWithEntries?] at hParts
          exact hParts.1
        have hParts := hNames
        simp [Yul.SolcValidation.FunctionNamesOk?,
          Yul.SolcValidation.namesNodup?] at hParts
        exact hParts.2

theorem toSolcYulOrderedProgram?_forkSpellingOk
    {object : Object} {ordered : Yul.OrderedProgram}
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    object.forkSpellingOk? = true := by
  unfold toSolcYulOrderedProgram? at hConvert
  cases hContract : object.toYulContractWithFunctionEntries? with
  | none => simp [hContract] at hConvert
  | some result =>
      rcases result with ⟨contract, functions⟩
      cases hValid :
          Yul.SolcValidation.ContractOkWithEntries?
            object.dialectProfile contract functions <;>
        simp [hContract, hValid] at hConvert
      exact hConvert.1

theorem toSolcYulOrderedProgram?_programOkWithEntries
    {object : Object} {ordered : Yul.OrderedProgram}
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    Yul.SolcValidation.ProgramOkWithEntries?
        object.dialectProfile ordered.program
        ordered.functionEntries = true := by
  exact (toSolcYulOrderedProgram?_source hConvert).2.2.1

theorem toSolcYulProgram?_memoryContract
    {object : Object} {program : Yul.Program}
    (hConvert : object.toSolcYulProgram? = some program) :
    program.memoryContract = object.memoryContract := by
  unfold toSolcYulProgram? at hConvert
  cases hContract : object.toYulContractWithFunctionEntries? with
  | none => simp [hContract] at hConvert
  | some result =>
      rcases result with ⟨contract, functions⟩
      by_cases hValid :
          Yul.SolcValidation.ContractOkWithEntries?
            object.dialectProfile contract functions
      · simp [hContract, hValid] at hConvert
        rcases hConvert with ⟨_hSpelling, hConvert⟩
        subst program
        rfl
      · simp [hContract, hValid] at hConvert

def toYulProgramWithLayout? (object : Object) (layout : ObjectLayout) :
    Option Yul.Program := do
  let resolved ← object.resolveObjectBuiltins? layout
  Object.toYulProgram? resolved

def toYulProgramWithLocalDataBase? (object : Object) (layout : ObjectLayout)
    (base : Nat) : Option Yul.Program := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  Object.toYulProgram? resolved

noncomputable def lowerCode? (object : Object) :
    Option Functions.Program := do
  let program ← object.toSolcYulProgram?
  let lower ← Yul.Program.toObjects? program
  some lower.root.code

theorem toSolcYulProgram?_eq_some {object : Object}
    {program : Yul.Program}
    (hProgram : object.toSolcYulProgram? = some program) :
    ∃ functions : List (Name × AstFunctionDefinition),
      object.toYulProgram? = some program ∧
        FunctionDef.List.toYul? object.functions = some functions ∧
          Yul.SolcValidation.ContractOkWithEntries?
            object.dialectProfile
            program.contract functions = true := by
  unfold toSolcYulProgram? toYulContractWithFunctionEntries? at hProgram
  unfold toYulProgram? toYulContract? toYulContractWithFunctionEntries?
  cases hDispatcher : Stmt.toYul? (.block object.dispatcher) with
  | none =>
      simp [hDispatcher] at hProgram
  | some dispatcher =>
      cases hFunctions : FunctionDef.List.toYul? object.functions with
      | none =>
          simp [hDispatcher, hFunctions] at hProgram
      | some functions =>
          cases hValid :
              Yul.SolcValidation.ContractOkWithEntries?
                object.dialectProfile
                { dispatcher := dispatcher
                  functions := functionMap functions }
                functions <;>
            simp [hDispatcher, hFunctions, hValid] at hProgram
          rcases hProgram with ⟨_hSpelling, hProgram⟩
          subst program
          exact
            ⟨functions, by simp, rfl, hValid⟩

theorem lowerCode?_some_solc_valid {object : Object}
    {code : Functions.Program}
    (hLower : object.lowerCode? = some code) :
    ∃ yulProgram : Yul.Program, ∃ lower : Objects.Program,
      object.toSolcYulProgram? = some yulProgram ∧
        Yul.Program.toObjects? yulProgram = some lower ∧
          lower.root.code = code := by
  unfold lowerCode? at hLower
  cases hYul : object.toSolcYulProgram? with
  | none =>
      simp [hYul] at hLower
  | some yulProgram =>
      cases hObjects : Yul.Program.toObjects? yulProgram with
      | none =>
          simp [hYul, hObjects] at hLower
      | some lower =>
          simp [hYul, hObjects] at hLower
          subst code
          exact ⟨yulProgram, lower, rfl, hObjects, rfl⟩

def lowerCodeUnchecked? (object : Object) :
    Option Functions.Program := do
  let ordered ← object.toSolcYulOrderedProgram?
  let lower ← ordered.toObjects?
  some lower.root.code

theorem lowerCodeUnchecked?_some
    {object : Object} {code : Functions.Program}
    (hLower : object.lowerCodeUnchecked? = some code) :
    ∃ ordered : Yul.OrderedProgram, ∃ lower : Objects.Program,
      object.toSolcYulOrderedProgram? = some ordered ∧
        ordered.toObjects? = some lower ∧
        lower.root.code = code := by
  unfold lowerCodeUnchecked? at hLower
  cases hOrdered : object.toSolcYulOrderedProgram? with
  | none => simp [hOrdered] at hLower
  | some ordered =>
      cases hObjects : ordered.toObjects? with
      | none => simp [hOrdered, hObjects] at hLower
      | some lower =>
          simp [hOrdered, hObjects] at hLower
          subst code
          exact ⟨ordered, lower, rfl, hObjects, rfl⟩

def lowerCodeUncheckedWithLayout? (object : Object)
    (layout : ObjectLayout) : Option Functions.Program := do
  let resolved ← object.resolveObjectBuiltins? layout
  resolved.lowerCodeUnchecked?

def lowerCodeUncheckedWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Functions.Program := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  resolved.lowerCodeUnchecked?

/-- Resolved frontend code compiled by the checked stack allocator. -/
structure VerifiedStackCodeArtifact where
  resolved : Object
  ordered : Yul.OrderedProgram
  lower : Objects.Program
  compiled : Compiler.StackArtifact.Artifact
  compact : Assembly.Compact.Artifact
  bytes : List UInt8
  immutableMarkerBytes : List UInt8

structure ImmutablePushPlan where
  pinnedPushPcs : List Nat
  markerTarget? : Option Assembly.Program

/-- Compute the physical push sites whose compact width must remain stable when
Solidity patches immutable values. The marker program is produced by the same
checked frontend and stack allocator; the Assembly owner accepts pins only
when both prepared programs have identical instruction shape. -/
def immutablePushPlanFor? (object : Object)
    (context : ObjectBuiltinContext) (actual : Assembly.Program) :
    Option ImmutablePushPlan :=
  let immutableNames := object.loadImmutableNames
  match immutableNames with
  | [] => some { pinnedPushPcs := [], markerTarget? := none }
  | _ :: _ => do
      let markerImmutableValues :=
        ImmutableReference.markerEntriesFromNat 0 immutableNames
      if context.immutableValues = markerImmutableValues then
        some { pinnedPushPcs := [], markerTarget? := none }
      else
        let markerContext : ObjectBuiltinContext :=
          { context with immutableValues := markerImmutableValues }
        let resolved ← object.resolveObjectBuiltinsIn? markerContext
        let ordered ← resolved.toSolcYulOrderedProgram?
        let lower ← ordered.toObjects?
        let compiled ← Compiler.StackArtifact.compile? lower.toFunctions
        let pinnedPushPcs ← Assembly.Compact.differingPushPcs?
          actual compiled.certified.target
        some
          { pinnedPushPcs := pinnedPushPcs
            markerTarget? := some compiled.certified.target }

def verifiedCodeSentinel : List UInt8 :=
  Assembly.Compact.encodeInstr (.prim .invalid)

def compileImmutableMarkerBytes? (plan : ImmutablePushPlan)
    (actualCompact : Assembly.Compact.Artifact) : Option (List UInt8) :=
  match plan.markerTarget? with
  | none => some (actualCompact.bytes.toList ++ verifiedCodeSentinel)
  | some markerTarget => do
      let markerCompact ←
        Assembly.Compact.compile? markerTarget plan.pinnedPushPcs
      some (markerCompact.bytes.toList ++ verifiedCodeSentinel)

def compileVerifiedStackCodeArtifactIn? (object : Object)
    (context : ObjectBuiltinContext) : Option VerifiedStackCodeArtifact := do
  let resolved ← object.resolveObjectBuiltinsIn? context
  let ordered ← resolved.toSolcYulOrderedProgram?
  let lower ← ordered.toObjects?
  let compiled ← Compiler.StackArtifact.compile? lower.toFunctions
  let pushPlan ←
    object.immutablePushPlanFor? context compiled.certified.target
  let compact ←
    Assembly.Compact.compile? compiled.certified.target pushPlan.pinnedPushPcs
  let bytes := compact.bytes.toList ++ verifiedCodeSentinel
  let immutableMarkerBytes ← compileImmutableMarkerBytes? pushPlan compact
  some
    { resolved, ordered, lower, compiled, compact, bytes,
      immutableMarkerBytes }

theorem compileVerifiedStackCodeArtifactIn?_parts
    {object : Object} {context : ObjectBuiltinContext}
    {artifact : VerifiedStackCodeArtifact}
    (hCompile : object.compileVerifiedStackCodeArtifactIn? context =
      some artifact) :
    object.resolveObjectBuiltinsIn? context = some artifact.resolved ∧
      artifact.resolved.toSolcYulOrderedProgram? = some artifact.ordered ∧
      artifact.ordered.toObjects? = some artifact.lower ∧
      Compiler.StackArtifact.compile? artifact.lower.toFunctions =
        some artifact.compiled ∧
      ∃ pushPlan,
        object.immutablePushPlanFor? context artifact.compiled.certified.target =
          some pushPlan ∧
        Assembly.Compact.compile? artifact.compiled.certified.target
            pushPlan.pinnedPushPcs = some artifact.compact ∧
        artifact.bytes =
          artifact.compact.bytes.toList ++ verifiedCodeSentinel ∧
        compileImmutableMarkerBytes? pushPlan artifact.compact =
          some artifact.immutableMarkerBytes := by
  unfold compileVerifiedStackCodeArtifactIn? at hCompile
  cases hResolved : object.resolveObjectBuiltinsIn? context with
  | none => simp [hResolved] at hCompile
  | some resolved =>
      cases hOrdered : resolved.toSolcYulOrderedProgram? with
      | none => simp [hResolved, hOrdered] at hCompile
      | some ordered =>
          cases hLower : ordered.toObjects? with
          | none => simp [hResolved, hOrdered, hLower] at hCompile
          | some lower =>
              cases hCompiled :
                  Compiler.StackArtifact.compile? lower.toFunctions with
              | none =>
                  simp [hResolved, hOrdered, hLower, hCompiled] at hCompile
              | some compiled =>
                  cases hPlan :
                      object.immutablePushPlanFor? context
                        compiled.certified.target with
                  | none =>
                      simp [hResolved, hOrdered, hLower, hCompiled, hPlan]
                        at hCompile
                  | some pushPlan =>
                      cases hCompact :
                          Assembly.Compact.compile? compiled.certified.target
                            pushPlan.pinnedPushPcs with
                      | none =>
                          simp [hResolved, hOrdered, hLower, hCompiled, hPlan,
                            hCompact] at hCompile
                      | some compact =>
                          cases hMarker :
                              compileImmutableMarkerBytes? pushPlan compact with
                          | none =>
                              simp [hResolved, hOrdered, hLower, hCompiled,
                                hPlan, hCompact, hMarker] at hCompile
                          | some immutableMarkerBytes =>
                              simp [hResolved, hOrdered, hLower, hCompiled,
                                hPlan, hCompact, hMarker] at hCompile
                              subst artifact
                              exact
                                ⟨by simpa using hResolved,
                                  by simpa using hOrdered,
                                  by simpa using hLower,
                                  by simpa using hCompiled,
                                  pushPlan, by simpa using hPlan,
                                  by simpa using hCompact, by simp,
                                  by simpa using hMarker⟩

theorem compileVerifiedStackCodeArtifactIn?_decodingCorrect
    {object : Object} {context : ObjectBuiltinContext}
    {artifact : VerifiedStackCodeArtifact}
    (hCompile : object.compileVerifiedStackCodeArtifactIn? context =
      some artifact) :
    Assembly.Compact.DecodingCorrect artifact.compact.program
      artifact.compact.bytes := by
  obtain ⟨_hResolved, _hOrdered, _hLower, _hArtifact, _pushPlan,
      _hPlan, hCompact, _hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCompile
  exact Assembly.Compact.compile?_decodingCorrect hCompact

mutual
  noncomputable def toObjects? (object : Object) :
      Option Objects.Object := do
    let code ← object.lowerCode?
    let objects ← List.toObjects? object.objects
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  noncomputable def List.toObjects? (objects : List Object) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjects? object
        let tail ← List.toObjects? rest
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def toObjectsUnchecked? (object : Object) :
      Option Objects.Object := do
    let code ← object.lowerCodeUnchecked?
    let objects ← List.toObjectsUnchecked? object.objects
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  def List.toObjectsUnchecked? (objects : List Object) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjectsUnchecked? object
        let tail ← List.toObjectsUnchecked? rest
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  noncomputable def toObjectsWithLayout? (object : Object)
      (layout : ObjectLayout) : Option Objects.Object := do
    let resolved ← object.resolveObjectBuiltins? layout
    let code ← resolved.lowerCode?
    let objects ← List.toObjectsWithLayout? object.objects layout
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  noncomputable def List.toObjectsWithLayout?
      (objects : List Object) (layout : ObjectLayout) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjectsWithLayout? object layout
        let tail ← List.toObjectsWithLayout? rest layout
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def toObjectsUncheckedWithLayout? (object : Object)
      (layout : ObjectLayout) : Option Objects.Object := do
    let resolved ← object.resolveObjectBuiltins? layout
    let code ← resolved.lowerCodeUnchecked?
    let objects ← List.toObjectsUncheckedWithLayout? object.objects layout
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  def List.toObjectsUncheckedWithLayout?
      (objects : List Object) (layout : ObjectLayout) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjectsUncheckedWithLayout? object layout
        let tail ← List.toObjectsUncheckedWithLayout? rest layout
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

noncomputable def toObjectsWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Object := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  let code ← resolved.lowerCode?
  let objects ← List.toObjectsWithLayout? object.objects layout
  some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)

def toObjectsUncheckedWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Object := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  let code ← resolved.lowerCodeUnchecked?
  let objects ← List.toObjectsUncheckedWithLayout? object.objects layout
  some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)

structure ObjectComputedObjectData where
  childImages : List ObjectImage
  items : List ObjectItemRef
  dataSizes : List (Name × Word)
  dataOffsets : List (Name × Word)
  payload : List UInt8
  codeBase : Nat
  context : ObjectBuiltinContext
  code : List UInt8
  markerCode : List UInt8
  deriving Inhabited, Repr

structure ObjectArtifactPlan where
  childImages : List ObjectImage
  immutableNames : List Name
  markerImmutableValues : List (Name × Word)
  items : List ObjectItemRef
  dataSizes : List (Name × Word)
  dataOffsets : List (Name × Word)
  payload : List UInt8
  codeBase : Nat
  layout : List ObjectLayout.Entry
  context : ObjectBuiltinContext

structure ObjectCodeBasePlan where
  codeBase : Nat
  layout : List ObjectLayout.Entry
  dataOffsets : List (Name × Word)
  context : ObjectBuiltinContext

def stabilizeObjectCodeBase? (object : Object)
    (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (childImmutableReferences : List (Name × List ImmutableReference))
    (immutableValues : List (Name × Word))
    (dataSizes : List (Name × Word)) (items : List ObjectItemRef)
    (payload : List UInt8)
    (compileBytesIn? : ObjectBuiltinContext → Option (List UInt8)) :
    Nat → Nat → Option ObjectCodeBasePlan
  | fuel, candidate => do
      let layout ←
        ObjectItemRef.List.objectLayoutEntriesFromNat?
          object.data childImages candidate items
      let dataOffsets ←
        ObjectItemRef.List.dataOffsetEntriesFromNat?
          object.data childImages candidate items
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      if !context.objectDataNamesUnique? then
        none
      else
        let bytes ← compileBytesIn? context
        if bytes.length == candidate then
          some { codeBase := candidate, layout, dataOffsets, context }
        else
          match fuel with
          | 0 => none
          | fuel + 1 =>
              stabilizeObjectCodeBase? object linkerSymbols childImages
                childImmutableReferences immutableValues dataSizes items
                payload compileBytesIn? fuel bytes.length
termination_by fuel candidate => fuel

/-- Artifact-retaining variant of code-base stabilization. This avoids
recompiling the final fixed-point context after the planner has already checked
it, while leaving the generic byte-only planner above unchanged. -/
def stabilizeObjectCodeBaseArtifact? {α : Type}
    (object : Object) (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (childImmutableReferences : List (Name × List ImmutableReference))
    (immutableValues : List (Name × Word))
    (dataSizes : List (Name × Word)) (items : List ObjectItemRef)
    (payload : List UInt8)
    (compileArtifactIn? : ObjectBuiltinContext → Option α)
    (artifactBytes : α → List UInt8) :
    Nat → Nat → Option (ObjectCodeBasePlan × α)
  | fuel, candidate => do
      let layout ←
        ObjectItemRef.List.objectLayoutEntriesFromNat?
          object.data childImages candidate items
      let dataOffsets ←
        ObjectItemRef.List.dataOffsetEntriesFromNat?
          object.data childImages candidate items
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      if !context.objectDataNamesUnique? then
        none
      else
        let artifact ← compileArtifactIn? context
        let bytes := artifactBytes artifact
        if bytes.length == candidate then
          some ({ codeBase := candidate, layout, dataOffsets, context }, artifact)
        else
          match fuel with
          | 0 => none
          | fuel + 1 =>
              stabilizeObjectCodeBaseArtifact? object linkerSymbols childImages
                childImmutableReferences immutableValues dataSizes items
                payload compileArtifactIn? artifactBytes fuel bytes.length
termination_by fuel candidate => fuel

theorem stabilizeObjectCodeBaseArtifact?_compiled {α : Type}
    (object : Object) (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (childImmutableReferences : List (Name × List ImmutableReference))
    (immutableValues : List (Name × Word))
    (dataSizes : List (Name × Word)) (items : List ObjectItemRef)
    (payload : List UInt8)
    (compileArtifactIn? : ObjectBuiltinContext → Option α)
    (artifactBytes : α → List UInt8)
    {fuel candidate : Nat} {plan : ObjectCodeBasePlan} {artifact : α}
    (hStabilize :
      stabilizeObjectCodeBaseArtifact? object linkerSymbols childImages
        childImmutableReferences immutableValues dataSizes items payload
        compileArtifactIn? artifactBytes fuel candidate =
          some (plan, artifact)) :
    compileArtifactIn? plan.context = some artifact := by
  induction fuel generalizing candidate with
  | zero =>
      unfold stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, _hLayout, hAfterLayout⟩ :=
        Option.bind_eq_some_iff.mp hStabilize
      obtain ⟨dataOffsets, _hOffsets, hAfterOffsets⟩ :=
        Option.bind_eq_some_iff.mp hAfterLayout
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      change (if (!context.objectDataNamesUnique?) = true then none else
        (compileArtifactIn? context).bind fun compiled =>
          if ((artifactBytes compiled).length == candidate) = true then
            some
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled)
          else none) = some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          exact hCompiled
        · simp [hLength] at hAfterCompiled
      · simp [hUnique] at hAfterOffsets
  | succ fuel ih =>
      unfold stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, _hLayout, hAfterLayout⟩ :=
        Option.bind_eq_some_iff.mp hStabilize
      obtain ⟨dataOffsets, _hOffsets, hAfterOffsets⟩ :=
        Option.bind_eq_some_iff.mp hAfterLayout
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      change (if (!context.objectDataNamesUnique?) = true then none else
        (compileArtifactIn? context).bind fun compiled =>
          if ((artifactBytes compiled).length == candidate) = true then
            some
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled)
          else
            stabilizeObjectCodeBaseArtifact? object linkerSymbols childImages
              childImmutableReferences immutableValues dataSizes items payload
              compileArtifactIn? artifactBytes fuel
                (artifactBytes compiled).length) =
          some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          exact hCompiled
        · simp [hLength] at hAfterCompiled
          exact ih hAfterCompiled
      · simp [hUnique] at hAfterOffsets

def planObjectArtifactFromChildImagesArtifactWith? {α : Type}
    (object : Object) (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (compileArtifactIn? : ObjectBuiltinContext → Option α)
    (artifactBytes : α → List UInt8) :
    Option (ObjectArtifactPlan × α) := do
  let childImmutableReferences :=
    ObjectImage.immutableReferenceEntries childImages
  let immutableNames := object.loadImmutableNames
  let zeroImmutableValues :=
    ImmutableReference.zeroEntries immutableNames
  let markerImmutableValues :=
    ImmutableReference.markerEntriesFromNat 0 immutableNames
  let items ← object.payloadItems? childImages
  let dataSizes ←
    ObjectItemRef.List.dataSizeEntries? object.data childImages items
  let payload ←
    ObjectItemRef.List.payloadBytes? object.data childImages items
  let (stabilized, artifact) ←
    stabilizeObjectCodeBaseArtifact? object linkerSymbols childImages
      childImmutableReferences zeroImmutableValues dataSizes items payload
      compileArtifactIn? artifactBytes 64 0
  some
    ({ childImages := childImages
       immutableNames := immutableNames
       markerImmutableValues := markerImmutableValues
       items := items
       dataSizes := dataSizes
       dataOffsets := stabilized.dataOffsets
       payload := payload
       codeBase := stabilized.codeBase
       layout := stabilized.layout
       context := stabilized.context }, artifact)

theorem planObjectArtifactFromChildImagesArtifactWith?_compiled {α : Type}
    (object : Object) (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (compileArtifactIn? : ObjectBuiltinContext → Option α)
    (artifactBytes : α → List UInt8)
    {plan : ObjectArtifactPlan} {artifact : α}
    (hPlan :
      planObjectArtifactFromChildImagesArtifactWith? object linkerSymbols
        childImages compileArtifactIn? artifactBytes = some (plan, artifact)) :
    compileArtifactIn? plan.context = some artifact := by
  unfold planObjectArtifactFromChildImagesArtifactWith? at hPlan
  obtain ⟨items, _hItems, hAfterItems⟩ :=
    Option.bind_eq_some_iff.mp hPlan
  obtain ⟨dataSizes, _hDataSizes, hAfterDataSizes⟩ :=
    Option.bind_eq_some_iff.mp hAfterItems
  obtain ⟨payload, _hPayload, hAfterPayload⟩ :=
    Option.bind_eq_some_iff.mp hAfterDataSizes
  obtain ⟨stabilizedArtifact, hStabilized, hAfterStabilized⟩ :=
    Option.bind_eq_some_iff.mp hAfterPayload
  rcases stabilizedArtifact with ⟨stabilized, compiled⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hAfterStabilized
  rcases hAfterStabilized with ⟨hPlanEq, hArtifactEq⟩
  subst plan
  subst artifact
  exact
    stabilizeObjectCodeBaseArtifact?_compiled object linkerSymbols childImages
      (ObjectImage.immutableReferenceEntries childImages)
      (ImmutableReference.zeroEntries object.loadImmutableNames)
      dataSizes items payload compileArtifactIn? artifactBytes hStabilized

def planObjectArtifactFromChildImagesWith? (object : Object)
    (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (compileBytesIn? : ObjectBuiltinContext → Option (List UInt8)) :
    Option ObjectArtifactPlan := do
    let childImmutableReferences :=
      ObjectImage.immutableReferenceEntries childImages
    let immutableNames := object.loadImmutableNames
    let zeroImmutableValues :=
      ImmutableReference.zeroEntries immutableNames
    let markerImmutableValues :=
      ImmutableReference.markerEntriesFromNat 0 immutableNames
    let items ← object.payloadItems? childImages
    let dataSizes ←
      ObjectItemRef.List.dataSizeEntries? object.data childImages items
    let payload ←
      ObjectItemRef.List.payloadBytes? object.data childImages items
    let stabilized ←
      stabilizeObjectCodeBase? object linkerSymbols childImages
        childImmutableReferences zeroImmutableValues dataSizes items payload
        compileBytesIn? 64 0
    some
      { childImages := childImages
        immutableNames := immutableNames
        markerImmutableValues := markerImmutableValues
        items := items
        dataSizes := dataSizes
        dataOffsets := stabilized.dataOffsets
        payload := payload
        codeBase := stabilized.codeBase
        layout := stabilized.layout
        context := stabilized.context }

end Object

namespace Program

def toYulProgram? (program : Program) : Option Yul.Program :=
  Object.toYulProgram? program.object

noncomputable def toObjects? (program : Program) : Option Objects.Program := do
  let root ← Object.toObjects? program.object
  some { root := root }

def toObjectsUnchecked? (program : Program) : Option Objects.Program := do
  let root ← Object.toObjectsUnchecked? program.object
  some { root := root }

def resolveObjectBuiltins? (program : Program) (layout : ObjectLayout) :
    Option Program := do
  let object ← Object.resolveObjectBuiltins? program.object layout
  some { source := program.source, contract := program.contract, object := object }

def toYulProgramWithLayout? (program : Program) (layout : ObjectLayout) :
    Option Yul.Program := do
  let resolved ← program.resolveObjectBuiltins? layout
  resolved.toYulProgram?

noncomputable def toObjectsWithLayout? (program : Program)
    (layout : ObjectLayout) : Option Objects.Program := do
  let root ← Object.toObjectsWithLayout? program.object layout
  some { root := root }

def toObjectsUncheckedWithLayout? (program : Program)
    (layout : ObjectLayout) : Option Objects.Program := do
  let root ← Object.toObjectsUncheckedWithLayout? program.object layout
  some { root := root }

def resolveObjectBuiltinsWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Program := do
  let object ←
    Object.resolveObjectBuiltinsWithLocalDataBase?
      program.object layout base
  some { source := program.source, contract := program.contract, object := object }

def toYulProgramWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Yul.Program := do
  let resolved ← program.resolveObjectBuiltinsWithLocalDataBase? layout base
  resolved.toYulProgram?

noncomputable def toObjectsWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Program := do
  let root ← Object.toObjectsWithLocalDataBase? program.object layout base
  some { root := root }

def toObjectsUncheckedWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Program := do
  let root ← Object.toObjectsUncheckedWithLocalDataBase?
    program.object layout base
  some { root := root }

end Program

end Frontend
end Solidity
end EvmCompiler
