import Lean.Data.Json
import EvmCompiler.Solidus.Frontend

/-!
# Frozen source decoder (Solidus Arena freeze cone)

`EvmCompiler.Solidus.compile_correct` asserts `decodeSelectedIr json selection =
.ok selected` and then runs the frozen source semantics on `selected.root`. The
faithfulness of that decoder and of the `Raw.Object`/`Stmt`/`Expr` AST it
produces is therefore load-bearing: if the decoder (formerly in the mutable
18.7k-line `EvmCompiler/Solidity/RawAst.lean`, which is dominated by the
elaborator) returned a trivial object, the whole source-refinement conjunct
would hold vacuously against arbitrary emitted bytecode.

This module relocates exactly the JSON -> source-AST decode layer out of that
file: the pure JSON helpers, the `Raw` source AST, its recursive decoders
(`decodeRootObject` and cone), `walkObjects`, the `Selection`/`SelectedIr`
vocabulary, and `decodeSelectedIr`. It also hosts the pure `EvmVersion` enum
(relocated from the mutable `Yul/SolcValidation.lean`) that `Selection`/
`SelectedIr` are typed against.

The ELABORATOR (`Raw.Object.elaborate?` and friends) stays mutable in the
original file, which now imports this module. All definitions keep their
fully-qualified names and namespaces, so downstream references remain valid.
This module references only `Frontend.Name`/`Word` (frozen), `EvmVersion`
(defined here), `Lean.Json`, and the pinned `EvmYul.UInt256`.
-/

namespace EvmCompiler
namespace Yul
namespace SolcValidation

inductive EvmVersion where
  | frontier
  | homestead
  | byzantium
  | constantinople
  | istanbul
  | london
  | paris
  | shanghai
  | cancun
  | prague
  | osaka
  deriving DecidableEq, Inhabited, Repr

end SolcValidation
end Yul

namespace Solidity
namespace RawAst

abbrev DecodeM := Except String
abbrev Name := Frontend.Name
abbrev Word := Frontend.Word

def maxDecodeFuel : Nat :=
  1000000

def field (json : Lean.Json) (name : String) : DecodeM Lean.Json :=
  match json.getObjVal? name with
  | .ok value => .ok value
  | .error err => .error s!"{name}: {err}"

def optionalField (json : Lean.Json) (name : String) :
    DecodeM (Option Lean.Json) :=
  match json.getObjVal? name with
  | .ok .null => .ok none
  | .ok value => .ok (some value)
  | .error _ => .ok none

def stringField (json : Lean.Json) (name : String) : DecodeM String := do
  (← field json name).getStr?

def optionalStringField (json : Lean.Json) (name : String) :
    DecodeM (Option String) := do
  match ← optionalField json name with
  | none => pure none
  | some value => some <$> value.getStr?

def arrayField (json : Lean.Json) (name : String) :
    DecodeM (Array Lean.Json) := do
  (← field json name).getArr?

def objectEntries (json : Lean.Json) :
    DecodeM (List (String × Lean.Json)) := do
  let object ← json.getObj?
  pure object.toList

def decodeArray {α : Type} (decode : Lean.Json → DecodeM α)
    (json : Lean.Json) : DecodeM (List α) := do
  let values ← json.getArr?
  let mut out : List α := []
  for value in values do
    out := (← decode value) :: out
  pure out.reverse

def decodeArrayField {α : Type} (decode : Lean.Json → DecodeM α)
    (json : Lean.Json) (name : String) : DecodeM (List α) := do
  decodeArray decode (← field json name)

def decodeOptionalArrayField {α : Type} (decode : Lean.Json → DecodeM α)
    (json : Lean.Json) (name : String) : DecodeM (List α) := do
  match ← optionalField json name with
  | none => pure []
  | some value => decodeArray decode value

def decodeTypedNames (nodes : List Lean.Json) (fieldName : String) :
    DecodeM (List Name) := do
  let mut names : List Name := []
  for node in nodes do
    let name ← stringField node "name"
    names := name :: names
  pure names.reverse

def decodeTypedNamesField (json : Lean.Json) (fieldName : String) :
    DecodeM (List Name) := do
  decodeTypedNames (← decodeArray (fun value => pure value) (← field json fieldName))
    fieldName

def decodeOptionalTypedNamesField (json : Lean.Json) (fieldName : String) :
    DecodeM (List Name) := do
  match ← optionalField json fieldName with
  | none => pure []
  | some value =>
      decodeTypedNames (← decodeArray (fun value => pure value) value) fieldName

def dropHexPrefix (value : String) : String :=
  if value.startsWith "0x" || value.startsWith "0X" then
    (value.drop 2).toString
  else
    value

def hexValue? (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n && n ≤ 57 then
    some (n - 48)
  else if 65 ≤ n && n ≤ 70 then
    some (10 + n - 65)
  else if 97 ≤ n && n ≤ 102 then
    some (10 + n - 97)
  else
    none

def parseHexNatAux : List UInt8 → Nat → Option Nat
  | [], acc => some acc
  | byte :: rest, acc => do
      let digit ← hexValue? byte
      parseHexNatAux rest (acc * 16 + digit)

def parseHexNat (value : String) : DecodeM Nat :=
  let digits := (dropHexPrefix value).toUTF8.toList
  match parseHexNatAux digits 0 with
  | some parsed => .ok parsed
  | none => .error s!"expected hex UInt256 literal, got {value}"

def parseUInt256 (value : String) : DecodeM Word := do
  let parsed ←
    if value.startsWith "0x" || value.startsWith "0X" then
      parseHexNat value
    else
      match value.toNat? with
      | some parsed => pure parsed
      | none => .error s!"expected UInt256 literal, got {value}"
  if parsed < 2 ^ (256 : Nat) then
    pure (EvmYul.UInt256.ofNat parsed)
  else
    .error s!"UInt256 literal out of range: {value}"

def parseUInt256Json (value : Lean.Json) : DecodeM Word :=
  match value.getStr? with
  | .ok text => parseUInt256 text
  | .error _ => do
      let n ← value.getNat?
      parseUInt256 (toString n)

def decodeByte (value : Nat) : DecodeM UInt8 :=
  if value < 256 then
    .ok (UInt8.ofNat value)
  else
    .error s!"byte out of range: {value}"

def parseHexBytesAux : List UInt8 → DecodeM (List UInt8)
  | [] => pure []
  | high :: low :: rest => do
      let high ←
        match hexValue? high with
        | some value => pure value
        | none => .error "expected hex byte"
      let low ←
        match hexValue? low with
        | some value => pure value
        | none => .error "expected hex byte"
      let tail ← parseHexBytesAux rest
      pure (UInt8.ofNat (high * 16 + low) :: tail)
  | [_] => .error "hex byte string has odd length"

def parseHexBytes (value what : String) : DecodeM (List UInt8) :=
  match parseHexBytesAux (dropHexPrefix value).toUTF8.toList with
  | .ok bytes => .ok bytes
  | .error err => .error s!"{what}: {err}"

def decodeEvmVersion (value : String) :
    DecodeM Yul.SolcValidation.EvmVersion :=
  match value with
  | "london" => .ok .london
  | "paris" => .ok .paris
  | "shanghai" => .ok .shanghai
  | "cancun" => .ok .cancun
  | "prague" | "pectra" => .ok .prague
  | "osaka" | "fusaka" => .ok .osaka
  | other => .error s!"unsupported frontend evmVersion: {other}"

example : decodeEvmVersion "prague" = .ok .prague := by rfl
example : decodeEvmVersion "pectra" = .ok .prague := by rfl
example : decodeEvmVersion "osaka" = .ok .osaka := by rfl
example : decodeEvmVersion "fusaka" = .ok .osaka := by rfl

def metadataEvmVersion? (contractOutput : Lean.Json) :
    DecodeM (Option Yul.SolcValidation.EvmVersion) := do
  match ← optionalStringField contractOutput "metadata" with
  | none => pure none
  | some text =>
      let metadata ← Lean.Json.parse text
      match ← optionalField metadata "settings" with
      | none => pure none
      | some settings =>
          match ← optionalStringField settings "evmVersion" with
          | none => pure none
          | some version => some <$> decodeEvmVersion version

def parseStandardJsonLibraryAddressNamed (value : Lean.Json)
    (symbolName : String) : DecodeM Word := do
  let text ←
    match value.getStr? with
    | .ok text => pure text
    | .error _ =>
        .error
          s!"malformed Standard JSON metadata settings.libraries entry for {symbolName}: address must be a hex string"
  let address := text.trim
  let digits := dropHexPrefix address
  if digits == "" then
    .error
      s!"malformed Standard JSON metadata settings.libraries entry for {symbolName}: address is empty"
  else if digits.length > 40 then
    .error
      s!"malformed Standard JSON metadata settings.libraries entry for {symbolName}: address is wider than 20 bytes"
  else
    match parseHexNat digits with
    | .ok parsed => pure (EvmYul.UInt256.ofNat parsed)
    | .error _ =>
        .error
          s!"malformed Standard JSON metadata settings.libraries entry for {symbolName}: address must be hex"

def parseStandardJsonLibraryAddress (value : Lean.Json)
    (sourceName libraryName : String) : DecodeM Word :=
  parseStandardJsonLibraryAddressNamed value (sourceName ++ ":" ++ libraryName)

def decodeMetadataLibraries (settings : Lean.Json) :
    DecodeM (List (Name × Word)) := do
  let _ ← settings.getObj?
  match ← optionalField settings "libraries" with
  | none => pure []
  | some libraries => do
      let mut entries : List (Name × Word) := []
      for sourceEntry in ← objectEntries libraries do
        let sourceName := sourceEntry.fst
        match sourceEntry.snd.getStr? with
        | .ok _ =>
            let value ←
              parseStandardJsonLibraryAddressNamed sourceEntry.snd sourceName
            entries := (sourceName, value) :: entries
        | .error _ =>
            let contracts := sourceEntry.snd
            let _ ← contracts.getObj?
            for libraryEntry in ← objectEntries contracts do
              let libraryName := libraryEntry.fst
              let value ←
                parseStandardJsonLibraryAddress
                  libraryEntry.snd sourceName libraryName
              entries := (sourceName ++ ":" ++ libraryName, value) :: entries
      pure entries.reverse

def metadataLinkerSymbols? (contractOutput : Lean.Json) :
    DecodeM (List (Name × Word)) := do
  match ← optionalStringField contractOutput "metadata" with
  | none => pure []
  | some text =>
      let metadata ← Lean.Json.parse text
      let _ ← metadata.getObj?
      match ← optionalField metadata "settings" with
      | none => pure []
      | some settings => decodeMetadataLibraries settings

namespace Raw

inductive Literal where
  | number (value : Word)
  | bool (value : Bool)
  | stringLit (value : String)
  | bytesLit (bytes : List UInt8)
  deriving Inhabited, Repr

mutual
  inductive Expr where
    | literal (value : Literal)
    | identifier (name : Name)
    | functionCall (name : Name) (args : List Expr)
    deriving Inhabited, Repr

  inductive SwitchCaseValue where
    | literal (value : Literal)
    deriving Inhabited, Repr

  inductive Stmt where
    | block (stmts : List Stmt)
    | variableDeclaration (names : List Name) (value? : Option Expr)
    | assignment (names : List Name) (value : Expr)
    | expressionStatement (expr : Expr)
    | functionDefinition (name : Name) (params returns : List Name)
        (body : List Stmt)
    | switch (scrutinee : Expr)
        (cases : List (SwitchCaseValue × List Stmt))
        (default : List Stmt)
    | forLoop (pre : List Stmt) (condition : Expr) (post : List Stmt)
        (body : List Stmt)
    | ifThen (condition : Expr) (body : List Stmt)
    | break
    | continue
    | leave
    deriving Inhabited, Repr
end

mutual
  inductive Object where
    | mk (name : Name) (code? : Option (List Stmt))
        (subObjects : List ObjectItem)
    deriving Inhabited, Repr

  inductive ObjectItem where
    | data (name? : Option Name) (bytes : List UInt8)
    | object (child : Object)
    deriving Inhabited, Repr
end

namespace Object

def name : Object → Name
  | .mk name _ _ => name

def code? : Object → Option (List Stmt)
  | .mk _ code? _ => code?

def subObjects : Object → List ObjectItem
  | .mk _ _ subObjects => subObjects

end Object

def nodeType (json : Lean.Json) : DecodeM String :=
  stringField json "nodeType"

def expectNodeType (json : Lean.Json) (expected : String) : DecodeM Unit := do
  let actual ← nodeType json
  if actual == expected then
    pure ()
  else
    .error s!"expected {expected}, got {actual}"

def decodeLiteral (json : Lean.Json) : DecodeM Literal := do
  expectNodeType json "YulLiteral"
  let kind ← stringField json "kind"
  match kind with
  | "number" =>
      let value ← field json "value"
      .ok (.number (← parseUInt256Json value))
  | "bool" =>
      let value ← field json "value"
      match value.getBool? with
      | .ok bool => .ok (.bool bool)
      | .error _ =>
          match value.getStr? with
          | .ok "true" => .ok (.bool true)
          | .ok "false" => .ok (.bool false)
          | .ok other => .error s!"unsupported bool literal: {other}"
          | .error err => .error err
  | "string" =>
      match ← optionalStringField json "value" with
      | some value => .ok (.stringLit value)
      | none =>
          let hexValue ← stringField json "hexValue"
          .ok (.bytesLit (← parseHexBytes hexValue "Yul hex string literal"))
  | other =>
      .error s!"unsupported Yul literal kind: {other}"

mutual
  def decodeExpr : Nat → Lean.Json → DecodeM Expr
    | 0, _ => .error "raw expression decoder ran out of fuel"
    | fuel + 1, json => do
        match ← nodeType json with
        | "YulLiteral" =>
            .ok (.literal (← decodeLiteral json))
        | "YulIdentifier" =>
            .ok (.identifier (← stringField json "name"))
        | "YulFunctionCall" =>
            let functionName ← field json "functionName"
            let name ← stringField functionName "name"
            let args ← decodeArrayField (decodeExpr fuel) json "arguments"
            .ok (.functionCall name args)
        | other =>
            .error s!"unsupported Yul expression nodeType {other}"

  def decodeSwitchCaseValue : Lean.Json → DecodeM SwitchCaseValue
    | json => .literal <$> decodeLiteral json

  def decodeBlock : Nat → Lean.Json → DecodeM (List Stmt)
    | 0, _ => .error "raw block decoder ran out of fuel"
    | fuel + 1, json => do
        expectNodeType json "YulBlock"
        decodeArrayField (decodeStmt fuel) json "statements"

  def decodeCase : Nat → Lean.Json →
      DecodeM (Option SwitchCaseValue × List Stmt)
    | 0, _ => .error "raw switch-case decoder ran out of fuel"
    | fuel + 1, json => do
        let body ← decodeBlock fuel (← field json "body")
        let value ← field json "value"
        match value.getStr? with
        | .ok "default" => pure (none, body)
        | .ok other => .error s!"unsupported switch case marker: {other}"
        | .error _ =>
            let value ← decodeSwitchCaseValue value
            pure (some value, body)

  def decodeCasesAux : Nat → List Lean.Json →
      DecodeM (List (SwitchCaseValue × List Stmt) × Option (List Stmt))
    | 0, _ => .error "raw switch cases decoder ran out of fuel"
    | _fuel + 1, [] => pure ([], none)
    | fuel + 1, value :: rest => do
        let head ← decodeCase fuel value
        let (cases, defaultBody?) ← decodeCasesAux fuel rest
        match head with
        | (none, body) =>
            match defaultBody? with
            | none => pure (cases, some body)
            | some _ => .error "duplicate Yul switch default case"
        | (some value, body) => pure ((value, body) :: cases, defaultBody?)

  def decodeCases : Nat → List Lean.Json →
      DecodeM (List (SwitchCaseValue × List Stmt) × List Stmt) := fun fuel cases => do
    let (cases, defaultBody?) ← decodeCasesAux fuel cases
    pure (cases, defaultBody?.getD [])

  def decodeStmt : Nat → Lean.Json → DecodeM Stmt
    | 0, _ => .error "raw statement decoder ran out of fuel"
    | fuel + 1, json => do
        match ← nodeType json with
        | "YulBlock" =>
            .block <$> decodeBlock fuel json
        | "YulVariableDeclaration" =>
            let names ← decodeTypedNamesField json "variables"
            let value? ← optionalField json "value"
            let value? ←
              match value? with
              | none => pure none
              | some value => some <$> decodeExpr fuel value
            .ok (.variableDeclaration names value?)
        | "YulAssignment" =>
            let names ← decodeTypedNamesField json "variableNames"
            let value ← decodeExpr fuel (← field json "value")
            .ok (.assignment names value)
        | "YulExpressionStatement" =>
            .expressionStatement <$> decodeExpr fuel (← field json "expression")
        | "YulFunctionDefinition" =>
            let name ← stringField json "name"
            let params ← decodeOptionalTypedNamesField json "parameters"
            let returns ← decodeOptionalTypedNamesField json "returnVariables"
            let body ← decodeBlock fuel (← field json "body")
            .ok (.functionDefinition name params returns body)
        | "YulSwitch" =>
            let scrutinee ← decodeExpr fuel (← field json "expression")
            let rawCases ← decodeArray (fun value => pure value) (← field json "cases")
            let (cases, defaultBody) ← decodeCases fuel rawCases
            .ok (.switch scrutinee cases defaultBody)
        | "YulForLoop" =>
            let pre ← decodeBlock fuel (← field json "pre")
            let condition ← decodeExpr fuel (← field json "condition")
            let post ← decodeBlock fuel (← field json "post")
            let body ← decodeBlock fuel (← field json "body")
            .ok (.forLoop pre condition post body)
        | "YulIf" =>
            let condition ← decodeExpr fuel (← field json "condition")
            let body ← decodeBlock fuel (← field json "body")
            .ok (.ifThen condition body)
        | "YulBreak" => .ok .break
        | "YulContinue" => .ok .continue
        | "YulLeave" => .ok .leave
        | other =>
            .error s!"unsupported Yul statement nodeType {other}"

  def decodeObject : Nat → Lean.Json → DecodeM Object
    | 0, _ => .error "raw object decoder ran out of fuel"
    | fuel + 1, json => do
        expectNodeType json "YulObject"
        let name ← stringField json "name"
        let code? ← optionalField json "code"
        let code? ←
          match code? with
          | none => pure none
          | some code => do
              let block ← field code "block"
              some <$> decodeBlock fuel block
        let subObjects ← decodeOptionalArrayField (decodeObjectItem fuel) json "subObjects"
        .ok (.mk name code? subObjects)

  def decodeObjectItem : Nat → Lean.Json → DecodeM ObjectItem
    | 0, _ => .error "raw object item decoder ran out of fuel"
    | fuel + 1, json => do
        match ← nodeType json with
        | "YulObject" =>
            .object <$> decodeObject fuel json
        | "YulData" =>
            let name? ← optionalStringField json "name"
            let value ← stringField json "value"
            let bytes ← parseHexBytes value "YulData"
            .ok (.data name? bytes)
        | other =>
            .error s!"unsupported Yul subobject nodeType {other}"
end

def decodeRootObject (json : Lean.Json) : DecodeM Object :=
  decodeObject maxDecodeFuel json

def walkObjectsFuel : Nat → Object → List Object
  | 0, obj => [obj]
  | fuel + 1, obj =>
      obj ::
        obj.subObjects.foldr
          (fun item rest =>
            match item with
            | .data _ _ => rest
            | .object child => walkObjectsFuel fuel child ++ rest)
          []

def walkObjects (obj : Object) : List Object :=
  walkObjectsFuel maxDecodeFuel obj


end Raw

inductive ObjectSelector where
  | creation
  | runtime
  | named (name : Name)
  deriving Inhabited, Repr, BEq, DecidableEq

structure Selection where
  source? : Option String := none
  contract? : Option String := none
  objectSelector : ObjectSelector := .creation
  astOutput : String := "irOptimizedAst"
  evmVersion? : Option Yul.SolcValidation.EvmVersion := none
  deriving Inhabited, Repr

structure SelectedIr where
  source : String
  contract : String
  evmVersion : Yul.SolcValidation.EvmVersion
  root : Raw.Object
  deriving Inhabited, Repr

def contractCandidates (json : Lean.Json) (selection : Selection) :
    DecodeM (List (String × String × Lean.Json)) := do
  let contracts ← field json "contracts"
  let mut out : List (String × String × Lean.Json) := []
  for sourceEntry in ← objectEntries contracts do
    let source := sourceEntry.fst
    let sourceContracts := sourceEntry.snd
    if selection.source?.all (fun wanted => wanted == source) then
      for contractEntry in ← objectEntries sourceContracts do
        let contract := contractEntry.fst
        if selection.contract?.all (fun wanted => wanted == contract) then
          out := (source, contract, contractEntry.snd) :: out
  pure out.reverse

def selectUniqueContract (json : Lean.Json) (selection : Selection) :
    DecodeM (String × String × Lean.Json) := do
  let candidates ← contractCandidates json selection
  match candidates with
  | [candidate] => pure candidate
  | [] => .error "no Standard JSON contract matched raw frontend selection"
  | _ :: _ :: _ =>
      .error "raw frontend selection is ambiguous; specify source and contract"

def selectRawObject (root : Raw.Object) (selector : ObjectSelector) :
    DecodeM Raw.Object :=
  match selector with
  | .creation => pure root
  | .runtime =>
      let objects := Raw.walkObjects root
      match objects.find? fun object => object.name != root.name &&
          object.name.endsWith "_deployed" with
      | some object => pure object
      | none => pure root
  | .named name =>
      match (Raw.walkObjects root).find? fun object => object.name == name with
      | some object => pure object
      | none => .error s!"no Yul object named {name}"

def decodeSelectedIr (json : Lean.Json) (selection : Selection) :
    DecodeM SelectedIr := do
  let (source, contract, contractOutput) ← selectUniqueContract json selection
  let astJson ← field contractOutput selection.astOutput
  let root ← Raw.decodeRootObject astJson
  let selected ← selectRawObject root selection.objectSelector
  let evmVersion ←
    match selection.evmVersion? with
    | some version => pure version
    | none =>
        match ← metadataEvmVersion? contractOutput with
        | some version => pure version
        | none =>
            .error "raw frontend selection requires evmVersion metadata"
  pure { source, contract, evmVersion, root := selected }

/-!
## Source-semantics helpers relocated from the mutable `Solidity/RawAst.lean`

`CallClass.classifyCall` and `Elab.ClzHelperModel.reference` are referenced by
the frozen source interpreter (`Solidity.RawAst.Raw.SourceSemantics`) that
`compile_correct` runs. They are pure functions over the frozen frontend spec
types + EvmYul, relocated here (the mutable `Solidity/RawAst.lean` imports this
module) so their meaning is hash-frozen. Names and the full
`Solidity.RawAst.*` namespaces are preserved.
-/

namespace CallClass

def objectBuiltins : List Name :=
  ["datasize", "dataoffset", "datacopy", "setimmutable", "loadimmutable",
    "linkersymbol", "memoryguard"]

def fixedUnsupportedDialectBuiltins : List Name :=
  ["pc", "jump", "jumpi", "jumpdest", "dataloadn", "auxdataloadn",
    "eofcreate", "returncontract", "rjump", "rjumpi", "callf", "retf",
    "jumpf"]

def decimalSuffixInRange? (pref name : String) (lo hi : Nat) : Bool :=
  if name.startsWith pref then
    match (name.drop pref.length).toString.toNat? with
    | some n => lo ≤ n && n ≤ hi
    | none => false
  else
    false

def unsupportedDialectBuiltin? (name : Name) : Bool :=
  fixedUnsupportedDialectBuiltins.contains name ||
    decimalSuffixInRange? "push" name 0 32 ||
    decimalSuffixInRange? "dup" name 1 16 ||
    decimalSuffixInRange? "swap" name 1 16 ||
    name.startsWith "verbatim"

def classifyCall (name : Name) : Frontend.CallKind :=
  match Frontend.Primitive.ofName? name with
  | some _ => .primitive
  | none =>
      if objectBuiltins.contains name then
        .objectBuiltin
      else if unsupportedDialectBuiltin? name then
        .dialectBuiltin
      else
        .user

end CallClass

namespace Elab
namespace ClzHelperModel

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def word (value : Nat) : Word :=
  EvmYul.UInt256.ofNat value

def reference (value : Word) : Word :=
  if value == zero then
    word 256
  else
    word (255 - (EvmYul.UInt256.log2 value).toNat)

end ClzHelperModel
end Elab

end RawAst
end Solidity
end EvmCompiler
