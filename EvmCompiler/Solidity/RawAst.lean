import EvmCompiler.Solidity.Frontend
import Lean.Data.Json

/-!
Lean-owned decoder and elaborator for raw solc Standard JSON Yul IR.

This module intentionally stops at `Solidity.Frontend.Program`.  It is owned by
the Solidity frontend boundary and does not import downstream structured
preservation modules or the Yul end-to-end theorem corridor.
-/

namespace EvmCompiler
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
  | other => .error s!"unsupported frontend evmVersion: {other}"

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

end Raw

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

def reservedBindingName? (name : Name) : Bool :=
  (Frontend.Primitive.ofName? name).isSome ||
    objectBuiltins.contains name ||
    unsupportedDialectBuiltin? name ||
    name == "clz"

theorem classify_primitive_ofName? {name : Name}
    (h : (Frontend.Primitive.ofName? name).isSome) :
    classifyCall name = .primitive := by
  unfold classifyCall
  cases hOp : Frontend.Primitive.ofName? name <;> simp [hOp] at h
  simp [hOp]

end CallClass

namespace Elab

structure State where
  functionScopes : List (List (Name × Name)) := []
  identifierScopes : List (List Name) := []
  hoistedFunctions : List (Name × Frontend.FunctionDef) := []
  usedFunctionNames : List Name := []
  nextGeneratedFunctionId : Nat := 0
  clzHelperName? : Option Name := none
  clzArgName? : Option Name := none
  clzReturnName? : Option Name := none
  deriving Inhabited, Repr

abbrev ElabM := StateT State DecodeM

def throw {α : Type} (message : String) : ElabM α :=
  fun _ => .error message

def pushIdentifierScope : ElabM Unit := do
  modify fun state =>
    { state with identifierScopes := [] :: state.identifierScopes }

def popIdentifierScope : ElabM Unit := do
  let state ← get
  match state.identifierScopes with
  | [] => throw "internal frontend error: no identifier scope to pop"
  | _ :: rest => set { state with identifierScopes := rest }

def pushFunctionScope (scope : List (Name × Name)) : ElabM Unit := do
  modify fun state =>
    { state with functionScopes := scope :: state.functionScopes }

def popFunctionScope : ElabM Unit := do
  let state ← get
  match state.functionScopes with
  | [] => throw "internal frontend error: no function scope to pop"
  | _ :: rest => set { state with functionScopes := rest }

def identifierVisibleIn (name : Name) (scopes : List (List Name)) : Bool :=
  scopes.any fun scope => scope.contains name

def identifierVisible (name : Name) : ElabM Bool := do
  let state ← get
  pure (identifierVisibleIn name state.identifierScopes)

def requireIdentifierVisible (name : Name) (what : String) : ElabM Unit := do
  if ← identifierVisible name then
    pure ()
  else
    throw s!"unknown Yul identifier {name} in {what}"

def requireIdentifiersVisible : List Name → String → ElabM Unit
  | [], _ => pure ()
  | name :: rest, what => do
      requireIdentifierVisible name what
      requireIdentifiersVisible rest what

def asciiAlpha (n : Nat) : Bool :=
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)

def asciiDigit (n : Nat) : Bool :=
  48 ≤ n && n ≤ 57

def asciiIdentifierStart (byte : UInt8) : Bool :=
  let n := byte.toNat
  asciiAlpha n || n == 95 || n == 36

def asciiIdentifierRest (byte : UInt8) : Bool :=
  let n := byte.toNat
  asciiAlpha n || asciiDigit n || n == 95 || n == 36

def validYulIdentifierBytes : List UInt8 → Bool
  | [] => false
  | first :: rest =>
      if !asciiIdentifierStart first then
        false
      else
        let rec loop : List UInt8 → Bool → Bool
          | [], previousDot => !previousDot
          | byte :: rest, previousDot =>
              if byte.toNat == 46 then
                if previousDot then false else loop rest true
              else if asciiIdentifierRest byte then
                loop rest false
              else
                false
        loop rest false

def validYulIdentifier? (name : Name) : Bool :=
  validYulIdentifierBytes name.toUTF8.toList

def bindingNameOk? (name : Name) : Bool :=
  validYulIdentifier? name &&
    !CallClass.reservedBindingName? name &&
    !name.startsWith "verbatim"

def collectDeclaredIdentifiers (names : List Name) (description : String)
    (scopes : List (List Name)) : DecodeM (List Name) :=
  let rec loop : List Name → List Name → DecodeM (List Name)
    | [], seen => .ok seen.reverse
    | name :: rest, seen => do
        if !bindingNameOk? name then
          .error s!"invalid Yul {description} name {name}"
        if seen.contains name then
          .error s!"duplicate Yul {description} name {name}"
        if identifierVisibleIn name scopes then
          .error s!"Yul {description} name {name} already taken in this scope"
        loop rest (name :: seen)
  loop names []

def declareIdentifiers (names : List Name) (description : String) :
    ElabM Unit := do
  let state ← get
  let scopes :=
    match state.identifierScopes with
    | [] => [[]]
    | scopes => scopes
  let seen ←
    match collectDeclaredIdentifiers names description scopes with
    | .ok seen => pure seen
    | .error err => throw err
  match state.identifierScopes with
  | [] => set { state with identifierScopes := [seen] }
  | scope :: rest =>
      set { state with identifierScopes := (seen ++ scope) :: rest }

def lookupFunctionInScope (name : Name) :
    List (Name × Name) → Option Name
  | [] => none
  | (source, target) :: rest =>
      if source == name then some target else lookupFunctionInScope name rest

def resolveFunctionIn (name : Name) :
    List (List (Name × Name)) → Option Name
  | [] => none
  | scope :: rest =>
      match lookupFunctionInScope name scope with
      | some resolved => some resolved
      | none => resolveFunctionIn name rest

def resolveFunction (name : Name) : ElabM Name := do
  let state ← get
  match resolveFunctionIn name state.functionScopes with
  | some resolved => pure resolved
  | none => throw s!"unknown Yul function {name}"

def generatedIdentifierPart (name : Name) : String :=
  let chars :=
    name.toUTF8.toList.filterMap fun byte =>
      let n := byte.toNat
      if asciiAlpha n || asciiDigit n || n == 95 || n == 36 then
        some (Char.ofNat n)
      else if n == 46 then
        some '_'
      else
        none
  let text := String.mk chars
  if text.isEmpty then "fn" else text

def freshGeneratedFunctionNameFrom (stem : Name) : Nat → ElabM Name
  | 0 => throw "could not allocate fresh generated Yul function name"
  | fuel + 1 => do
      let state ← get
      let candidate :=
        "__yul_gen_" ++ toString state.nextGeneratedFunctionId ++ "_" ++ stem
      set { state with nextGeneratedFunctionId := state.nextGeneratedFunctionId + 1 }
      let state ← get
      if state.usedFunctionNames.contains candidate then
        freshGeneratedFunctionNameFrom stem fuel
      else
        set { state with usedFunctionNames := candidate :: state.usedFunctionNames }
        pure candidate

def freshGeneratedFunctionName (base : Name) : ElabM Name :=
  freshGeneratedFunctionNameFrom (generatedIdentifierPart base) maxDecodeFuel

def freshNonFunctionBindingNameFrom (stem : Name) (index : Nat) :
    Nat → ElabM Name
  | 0 => throw "could not allocate fresh generated Yul binding name"
  | fuel + 1 => do
      let candidate :=
        if index == 0 then "__yul_" ++ stem else
          "__yul_" ++ stem ++ "_" ++ toString index
      let state ← get
      if state.usedFunctionNames.contains candidate then
        freshNonFunctionBindingNameFrom stem (index + 1) fuel
      else
        set { state with usedFunctionNames := candidate :: state.usedFunctionNames }
        pure candidate

def freshNonFunctionBindingName (base : Name) : ElabM Name :=
  freshNonFunctionBindingNameFrom (generatedIdentifierPart base) 0 maxDecodeFuel

def ensureClzHelper : ElabM Name := do
  let state ← get
  match state.clzHelperName? with
  | some name => pure name
  | none =>
      let helper ← freshGeneratedFunctionName "clz"
      let arg ← freshNonFunctionBindingName "clz_arg"
      let ret ← freshNonFunctionBindingName "clz_ret"
      modify fun state =>
        { state with
          clzHelperName? := some helper
          clzArgName? := some arg
          clzReturnName? := some ret }
      pure helper

def clzPrim (name : Name) (args : List Frontend.Expr) : Frontend.Expr :=
  Frontend.Expr.call .primitive name args

def clzValue (name : Name) : Frontend.Expr :=
  Frontend.Expr.var name

def clzWord (value : Nat) : Frontend.Expr :=
  Frontend.Expr.lit (EvmYul.UInt256.ofNat value)

def clzHelperStepSchedule : List (Nat × Nat) :=
  [(128, 128), (192, 64), (224, 32), (240, 16), (248, 8),
    (252, 4), (254, 2), (255, 1)]

def clzHelperStepScheduleOk? : Bool :=
  clzHelperStepSchedule.all fun step => step.fst + step.snd == 256

theorem clzHelperStepScheduleOk :
    clzHelperStepScheduleOk? = true := by
  rfl

namespace ClzHelperModel

structure State where
  arg : Word
  ret : Word
  deriving BEq, Repr

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def word (value : Nat) : Word :=
  EvmYul.UInt256.ofNat value

def shouldRunStep (checkShift : Nat) (state : State) : Bool :=
  EvmYul.UInt256.isZero
      (EvmYul.UInt256.shiftRight state.arg (word checkShift)) != zero

def applyStepBody (addend : Nat) (state : State) : State :=
  let ret := EvmYul.UInt256.add state.ret (word addend)
  let arg :=
    if addend == 1 then state.arg
    else EvmYul.UInt256.shiftLeft state.arg (word addend)
  { arg, ret }

def applyStep (state : State) (step : Nat × Nat) : State :=
  if shouldRunStep step.fst state then
    applyStepBody step.snd state
  else
    state

def runNonzero (value : Word) : State :=
  clzHelperStepSchedule.foldl applyStep
    { arg := value, ret := word 0 }

def run (value : Word) : Word :=
  if value == zero then
    word 256
  else
    (runNonzero value).ret

def reference (value : Word) : Word :=
  if value == zero then
    word 256
  else
    word (255 - (EvmYul.UInt256.log2 value).toNat)

theorem word_toNat_of_lt {value : Nat} (h : value < 256) :
    (word value).toNat = value := by
  unfold word EvmYul.UInt256.toNat EvmYul.UInt256.ofNat
  change (Fin.ofNat EvmYul.UInt256.size value).val = value
  rw [Fin.val_ofNat]
  apply Nat.mod_eq_of_lt
  have : 256 < EvmYul.UInt256.size := by decide
  exact Nat.lt_trans h this

theorem add_word_eq_of_lt {a b : Nat} (h : a + b < 256) :
    EvmYul.UInt256.add (word a) (word b) = word (a + b) := by
  unfold EvmYul.UInt256.add word EvmYul.UInt256.ofNat
  congr
  apply Fin.ext
  simp only [Fin.val_add, Id.run]
  rw [Fin.val_ofNat, Fin.val_ofNat]
  have hlt : a + b < EvmYul.UInt256.size := by
    have : 256 < EvmYul.UInt256.size := by decide
    exact Nat.lt_trans h this
  have ha : a < EvmYul.UInt256.size := by omega
  have hb : b < EvmYul.UInt256.size := by omega
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hlt]
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt hlt]

theorem toNat_eq_zero_iff (value : Word) :
    value.toNat = 0 ↔ value = zero := by
  constructor
  · intro hz
    cases value with
    | mk val =>
        unfold zero EvmYul.UInt256.ofNat
        apply congrArg EvmYul.UInt256.mk
        apply Fin.ext
        simpa [EvmYul.UInt256.toNat] using hz
  · intro h
    rw [h]
    exact word_toNat_of_lt (by decide : 0 < 256)

theorem log2_toNat_eq (value : Word) :
    (EvmYul.UInt256.log2 value).toNat = value.toNat.log2 := by
  rfl

theorem log2_toNat_lt_256_of_ne_zero
    {value : Word} (hValue : value ≠ zero) :
    (EvmYul.UInt256.log2 value).toNat < 256 := by
  have hValLt : value.toNat < 2 ^ 256 := by
    have hv : value.toNat < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.toNat
      exact value.val.isLt
    simpa [EvmYul.UInt256.size] using hv
  have hValNe : value.toNat ≠ 0 := by
    intro hz
    exact hValue ((toNat_eq_zero_iff value).mp hz)
  have hLogBound : value.toNat.log2 + 1 ≤ 256 := by
    by_contra hnot
    have hle : 256 ≤ value.toNat.log2 := by omega
    have hpows : 2 ^ 256 ≤ 2 ^ value.toNat.log2 := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have hleVal : 2 ^ value.toNat.log2 ≤ value.toNat := by
      exact Nat.log2_self_le hValNe
    exact Nat.not_le_of_gt hValLt (Nat.le_trans hpows hleVal)
  have : value.toNat.log2 < 256 := Nat.lt_of_succ_le hLogBound
  simpa [log2_toNat_eq] using this

theorem shiftRight_word_toNat (value : Word) {shift : Nat}
    (hShift : shift < 256) :
    (EvmYul.UInt256.shiftRight value (word shift)).toNat =
      value.toNat >>> shift := by
  have hWord : (word shift).toNat = shift := word_toNat_of_lt hShift
  have hWordVal : (word shift).val.val = shift := by
    simpa [EvmYul.UInt256.toNat] using hWord
  have hBranch :
      ¬ (word shift).val ≥ (256 : Fin EvmYul.UInt256.size) := by
    change ¬ (256 : Fin EvmYul.UInt256.size).val ≤ (word shift).val.val
    have h256 : (256 : Fin EvmYul.UInt256.size).val = 256 := by decide
    rw [h256, hWordVal]
    exact Nat.not_le_of_gt hShift
  unfold EvmYul.UInt256.shiftRight EvmYul.UInt256.toNat
  simp [hBranch]
  rw [hWordVal]

theorem shiftRight_word_eq_zero_iff_log2_lt
    (value : Word) {shift : Nat}
    (hValue : value ≠ zero) (hShift : shift < 256) :
    EvmYul.UInt256.shiftRight value (word shift) = zero ↔
      value.toNat.log2 < shift := by
  have hValueNat : value.toNat ≠ 0 := by
    intro hz
    exact hValue ((toNat_eq_zero_iff value).mp hz)
  constructor
  · intro hZero
    have hNatZero :
        (EvmYul.UInt256.shiftRight value (word shift)).toNat = 0 := by
      rw [hZero]
      exact word_toNat_of_lt (by decide : 0 < 256)
    have hDivZero : value.toNat >>> shift = 0 := by
      simpa [shiftRight_word_toNat value hShift] using hNatZero
    have hLtPow : value.toNat < 2 ^ shift := by
      rw [Nat.shiftRight_eq_div_pow] at hDivZero
      exact Nat.lt_of_div_eq_zero (Nat.pow_pos (by decide : 0 < 2))
        hDivZero
    exact (Nat.log2_lt hValueNat).mpr hLtPow
  · intro hLogLt
    have hLtPow : value.toNat < 2 ^ shift :=
      (Nat.log2_lt hValueNat).mp hLogLt
    apply (toNat_eq_zero_iff _).mp
    rw [shiftRight_word_toNat value hShift, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hLtPow

theorem shiftLeft_word_toNat_of_lt (value : Word) {shift : Nat}
    (hShift : shift < 256)
    (hNoOverflow : value.toNat <<< shift < EvmYul.UInt256.size) :
    (EvmYul.UInt256.shiftLeft value (word shift)).toNat =
      value.toNat <<< shift := by
  have hWord : (word shift).toNat = shift := word_toNat_of_lt hShift
  have hWordVal : (word shift).val.val = shift := by
    simpa [EvmYul.UInt256.toNat] using hWord
  have hBranch :
      ¬ (word shift).val ≥ (256 : Fin EvmYul.UInt256.size) := by
    change ¬ (256 : Fin EvmYul.UInt256.size).val ≤ (word shift).val.val
    have h256 : (256 : Fin EvmYul.UInt256.size).val = 256 := by decide
    rw [h256, hWordVal]
    exact Nat.not_le_of_gt hShift
  unfold EvmYul.UInt256.shiftLeft EvmYul.UInt256.toNat
  simp [hBranch]
  rw [hWordVal]
  exact Nat.mod_eq_of_lt hNoOverflow

theorem log2_shiftLeft_word_toNat
    (value : Word) {shift : Nat}
    (hValue : value ≠ zero) (hShift : shift < 256)
    (hNoOverflow : value.toNat <<< shift < EvmYul.UInt256.size) :
    (EvmYul.UInt256.log2
      (EvmYul.UInt256.shiftLeft value (word shift))).toNat =
      value.toNat.log2 + shift := by
  have hValueNat : value.toNat ≠ 0 := by
    intro hz
    exact hValue ((toNat_eq_zero_iff value).mp hz)
  have hShiftToNat := shiftLeft_word_toNat_of_lt value hShift hNoOverflow
  have hLow : 2 ^ (value.toNat.log2 + shift) ≤
      value.toNat <<< shift := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hValueNat)
  have hHigh : value.toNat <<< shift <
      2 ^ (value.toNat.log2 + shift + 1) := by
    rw [Nat.shiftLeft_eq]
    have hMul := Nat.mul_lt_mul_of_pos_right
      (Nat.lt_log2_self (n := value.toNat))
      (Nat.pow_pos (by decide : 0 < 2) (n := shift))
    simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMul
  have hLog :
      Nat.log 2 (value.toNat <<< shift) =
        value.toNat.log2 + shift := by
    exact Nat.log_eq_of_pow_le_of_lt_pow hLow hHigh
  rw [log2_toNat_eq, hShiftToNat]
  rw [Nat.log2_eq_log_two]
  exact hLog

theorem shiftLeft_noOverflow_of_log2_add_lt
    (value : Word) {shift : Nat}
    (hValue : value ≠ zero)
    (hBound : value.toNat.log2 + shift < 256) :
    value.toNat <<< shift < EvmYul.UInt256.size := by
  have hValueNat : value.toNat ≠ 0 := by
    intro hz
    exact hValue ((toNat_eq_zero_iff value).mp hz)
  rw [Nat.shiftLeft_eq]
  have hValLt : value.toNat < 2 ^ (value.toNat.log2 + 1) :=
    Nat.lt_log2_self (n := value.toNat)
  have hMulLt : value.toNat * 2 ^ shift <
      2 ^ (value.toNat.log2 + 1) * 2 ^ shift :=
    Nat.mul_lt_mul_of_pos_right hValLt
      (Nat.pow_pos (by decide : 0 < 2) (n := shift))
  have hPowEq : 2 ^ (value.toNat.log2 + 1) * 2 ^ shift =
      2 ^ (value.toNat.log2 + shift + 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hPowLe : 2 ^ (value.toNat.log2 + shift + 1) ≤ 2 ^ 256 := by
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    omega
  have hLtPow : value.toNat * 2 ^ shift < 2 ^ 256 :=
    lt_of_lt_of_le (by simpa [hPowEq] using hMulLt) hPowLe
  simpa [EvmYul.UInt256.size] using hLtPow

theorem isZero_truthy_iff (value : Word) :
    (EvmYul.UInt256.isZero value != zero) = true ↔ value = zero := by
  constructor
  · intro h
    by_cases hz : value = zero
    · exact hz
    · have hEq0 : EvmYul.UInt256.eq0 value = false := by
        cases value with
        | mk value =>
            simp [EvmYul.UInt256.eq0, EvmYul.instBEqUInt256,
              EvmYul.instBEqUInt256.beq, zero, EvmYul.UInt256.ofNat,
              Id.run] at hz ⊢
            exact hz
      have hIszeroZero : EvmYul.UInt256.isZero value = zero := by
        simp [EvmYul.UInt256.isZero, hEq0, EvmYul.UInt256.fromBool,
          zero]
      simp [hIszeroZero, zero, bne, EvmYul.instBEqUInt256,
        EvmYul.instBEqUInt256.beq, EvmYul.UInt256.ofNat, Id.run] at h
  · intro hz
    subst hz
    simp [EvmYul.UInt256.isZero, EvmYul.UInt256.eq0,
      EvmYul.UInt256.fromBool, Bool.toUInt256, zero, bne,
      EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq,
      EvmYul.UInt256.ofNat, Id.run]
    decide

theorem shouldRunStep_eq_log2_lt (value ret : Word)
    {checkShift : Nat} (hValue : value ≠ zero) (hShift : checkShift < 256) :
    shouldRunStep checkShift { arg := value, ret := ret } =
      decide (value.toNat.log2 < checkShift) := by
  by_cases hLog : value.toNat.log2 < checkShift
  · have hShiftZero :
        EvmYul.UInt256.shiftRight value (word checkShift) = zero :=
      (shiftRight_word_eq_zero_iff_log2_lt value hValue hShift).mpr hLog
    simp [hLog, shouldRunStep, (isZero_truthy_iff _).mpr hShiftZero]
  · have hShiftNonzero :
        EvmYul.UInt256.shiftRight value (word checkShift) ≠ zero := by
      intro hZero
      exact hLog
        ((shiftRight_word_eq_zero_iff_log2_lt value hValue hShift).mp hZero)
    have hBoolFalse :
        (EvmYul.UInt256.isZero
          (EvmYul.UInt256.shiftRight value (word checkShift)) != zero) =
          false := by
      have hNotTrue :
          ¬ (EvmYul.UInt256.isZero
            (EvmYul.UInt256.shiftRight value (word checkShift)) != zero) =
              true := by
        intro hTrue
        exact hShiftNonzero ((isZero_truthy_iff _).mp hTrue)
      exact Bool.eq_false_of_not_eq_true hNotTrue
    simp [hLog, shouldRunStep, hBoolFalse]

def applyHighestBitStep (highestBit ret : Nat) (step : Nat × Nat) : Nat :=
  if highestBit + ret < step.fst then ret + step.snd else ret

def runHighestBit (highestBit : Nat) : Nat :=
  clzHelperStepSchedule.foldl (applyHighestBitStep highestBit) 0

theorem applyStep_prefix_refines
    {state : State} {highest ret checkShift addend : Nat}
    (hArg : state.arg ≠ zero)
    (hRet : state.ret = word ret)
    (hLog : state.arg.toNat.log2 = highest + ret)
    (hBound : highest + ret < 256)
    (hCheck : checkShift < 256)
    (hAdd : addend < 256)
    (hStep : checkShift + addend = 256)
    (hAddNeOne : addend ≠ 1) :
    let state' := applyStep state (checkShift, addend)
    state'.ret = word (applyHighestBitStep highest ret (checkShift, addend)) ∧
      state'.arg ≠ zero ∧
      state'.arg.toNat.log2 =
        highest + applyHighestBitStep highest ret (checkShift, addend) ∧
      highest + applyHighestBitStep highest ret (checkShift, addend) < 256 := by
  dsimp only
  have hShould := shouldRunStep_eq_log2_lt state.arg state.ret hArg hCheck
  rw [hLog] at hShould
  by_cases hRun : highest + ret < checkShift
  · have hRetAddBound : ret + addend < 256 := by omega
    have hLogAddBound : state.arg.toNat.log2 + addend < 256 := by omega
    have hNoOverflow :=
      shiftLeft_noOverflow_of_log2_add_lt state.arg hArg hLogAddBound
    have hShiftLog :=
      log2_shiftLeft_word_toNat state.arg hArg hAdd hNoOverflow
    have hShiftLogNat :
        (EvmYul.UInt256.shiftLeft state.arg (word addend)).toNat.log2 =
          state.arg.toNat.log2 + addend := by
      simpa [log2_toNat_eq] using hShiftLog
    have hShiftNat := shiftLeft_word_toNat_of_lt state.arg hAdd hNoOverflow
    have hShiftNe :
        EvmYul.UInt256.shiftLeft state.arg (word addend) ≠ zero := by
      intro hZero
      have hNatZero :
          (EvmYul.UInt256.shiftLeft state.arg (word addend)).toNat = 0 :=
        (toNat_eq_zero_iff _).mpr hZero
      have hArgNatNe : state.arg.toNat ≠ 0 := by
        intro hz
        exact hArg ((toNat_eq_zero_iff state.arg).mp hz)
      rw [hShiftNat, Nat.shiftLeft_eq] at hNatZero
      exact Nat.mul_ne_zero hArgNatNe
        (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2) (n := addend)))
        hNatZero
    have hRetAdd := add_word_eq_of_lt (a := ret) (b := addend)
      hRetAddBound
    simp [applyStep, hShould, hRun, applyStepBody, applyHighestBitStep,
      hAddNeOne, hRet, hRetAdd, hShiftNe, hShiftLogNat]
    omega
  · simp [applyStep, hShould, hRun, applyHighestBitStep, hRet, hArg, hLog,
      hBound]

theorem applyStep_final_ret_refines
    {state : State} {highest ret : Nat}
    (hArg : state.arg ≠ zero)
    (hRet : state.ret = word ret)
    (hLog : state.arg.toNat.log2 = highest + ret)
    (hBound : highest + ret < 256) :
    (applyStep state (255, 1)).ret =
      word (applyHighestBitStep highest ret (255, 1)) := by
  have hShould := shouldRunStep_eq_log2_lt state.arg state.ret hArg
    (by decide : 255 < 256)
  rw [hLog] at hShould
  by_cases hRun : highest + ret < 255
  · have hRetAddBound : ret + 1 < 256 := by omega
    have hRetAdd := add_word_eq_of_lt (a := ret) (b := 1) hRetAddBound
    simp [applyStep, hShould, hRun, applyStepBody, applyHighestBitStep,
      hRet, hRetAdd]
  · simp [applyStep, hShould, hRun, applyHighestBitStep, hRet]

set_option maxRecDepth 10000 in
theorem runHighestBit_eq_reference :
    ∀ highestBit : Fin 256,
      runHighestBit highestBit.val = 255 - highestBit.val := by
  decide

theorem runNonzero_ret_eq_runHighestBit
    (value : Word) (hValue : value ≠ zero) :
    (runNonzero value).ret = word (runHighestBit value.toNat.log2) := by
  let highest := value.toNat.log2
  have hHighest : highest < 256 := by
    have h := log2_toNat_lt_256_of_ne_zero hValue
    simpa [highest, log2_toNat_eq] using h
  let state0 : State := { arg := value, ret := word 0 }
  let ret0 : Nat := 0
  have h0Arg : state0.arg ≠ zero := by simpa [state0] using hValue
  have h0Ret : state0.ret = word ret0 := by rfl
  have h0Log : state0.arg.toNat.log2 = highest + ret0 := by
    simp [state0, highest, ret0]
  have h0Bound : highest + ret0 < 256 := by simpa [ret0] using hHighest
  let ret1 := applyHighestBitStep highest ret0 (128, 128)
  let state1 := applyStep state0 (128, 128)
  have step1 := applyStep_prefix_refines (state := state0)
    (highest := highest) (ret := ret0) (checkShift := 128) (addend := 128)
    h0Arg h0Ret h0Log h0Bound (by decide) (by decide) (by decide)
    (by decide)
  have h1Ret : state1.ret = word ret1 := by
    simpa [state1, ret1] using step1.1
  have h1Arg : state1.arg ≠ zero := by
    simpa [state1] using step1.2.1
  have h1Log : state1.arg.toNat.log2 = highest + ret1 := by
    simpa [state1, ret1] using step1.2.2.1
  have h1Bound : highest + ret1 < 256 := by
    simpa [ret1] using step1.2.2.2
  let ret2 := applyHighestBitStep highest ret1 (192, 64)
  let state2 := applyStep state1 (192, 64)
  have step2 := applyStep_prefix_refines (state := state1)
    (highest := highest) (ret := ret1) (checkShift := 192) (addend := 64)
    h1Arg h1Ret h1Log h1Bound (by decide) (by decide) (by decide)
    (by decide)
  have h2Ret : state2.ret = word ret2 := by
    simpa [state2, ret2] using step2.1
  have h2Arg : state2.arg ≠ zero := by
    simpa [state2] using step2.2.1
  have h2Log : state2.arg.toNat.log2 = highest + ret2 := by
    simpa [state2, ret2] using step2.2.2.1
  have h2Bound : highest + ret2 < 256 := by
    simpa [ret2] using step2.2.2.2
  let ret3 := applyHighestBitStep highest ret2 (224, 32)
  let state3 := applyStep state2 (224, 32)
  have step3 := applyStep_prefix_refines (state := state2)
    (highest := highest) (ret := ret2) (checkShift := 224) (addend := 32)
    h2Arg h2Ret h2Log h2Bound (by decide) (by decide) (by decide)
    (by decide)
  have h3Ret : state3.ret = word ret3 := by
    simpa [state3, ret3] using step3.1
  have h3Arg : state3.arg ≠ zero := by
    simpa [state3] using step3.2.1
  have h3Log : state3.arg.toNat.log2 = highest + ret3 := by
    simpa [state3, ret3] using step3.2.2.1
  have h3Bound : highest + ret3 < 256 := by
    simpa [ret3] using step3.2.2.2
  let ret4 := applyHighestBitStep highest ret3 (240, 16)
  let state4 := applyStep state3 (240, 16)
  have step4 := applyStep_prefix_refines (state := state3)
    (highest := highest) (ret := ret3) (checkShift := 240) (addend := 16)
    h3Arg h3Ret h3Log h3Bound (by decide) (by decide) (by decide)
    (by decide)
  have h4Ret : state4.ret = word ret4 := by
    simpa [state4, ret4] using step4.1
  have h4Arg : state4.arg ≠ zero := by
    simpa [state4] using step4.2.1
  have h4Log : state4.arg.toNat.log2 = highest + ret4 := by
    simpa [state4, ret4] using step4.2.2.1
  have h4Bound : highest + ret4 < 256 := by
    simpa [ret4] using step4.2.2.2
  let ret5 := applyHighestBitStep highest ret4 (248, 8)
  let state5 := applyStep state4 (248, 8)
  have step5 := applyStep_prefix_refines (state := state4)
    (highest := highest) (ret := ret4) (checkShift := 248) (addend := 8)
    h4Arg h4Ret h4Log h4Bound (by decide) (by decide) (by decide)
    (by decide)
  have h5Ret : state5.ret = word ret5 := by
    simpa [state5, ret5] using step5.1
  have h5Arg : state5.arg ≠ zero := by
    simpa [state5] using step5.2.1
  have h5Log : state5.arg.toNat.log2 = highest + ret5 := by
    simpa [state5, ret5] using step5.2.2.1
  have h5Bound : highest + ret5 < 256 := by
    simpa [ret5] using step5.2.2.2
  let ret6 := applyHighestBitStep highest ret5 (252, 4)
  let state6 := applyStep state5 (252, 4)
  have step6 := applyStep_prefix_refines (state := state5)
    (highest := highest) (ret := ret5) (checkShift := 252) (addend := 4)
    h5Arg h5Ret h5Log h5Bound (by decide) (by decide) (by decide)
    (by decide)
  have h6Ret : state6.ret = word ret6 := by
    simpa [state6, ret6] using step6.1
  have h6Arg : state6.arg ≠ zero := by
    simpa [state6] using step6.2.1
  have h6Log : state6.arg.toNat.log2 = highest + ret6 := by
    simpa [state6, ret6] using step6.2.2.1
  have h6Bound : highest + ret6 < 256 := by
    simpa [ret6] using step6.2.2.2
  let ret7 := applyHighestBitStep highest ret6 (254, 2)
  let state7 := applyStep state6 (254, 2)
  have step7 := applyStep_prefix_refines (state := state6)
    (highest := highest) (ret := ret6) (checkShift := 254) (addend := 2)
    h6Arg h6Ret h6Log h6Bound (by decide) (by decide) (by decide)
    (by decide)
  have h7Ret : state7.ret = word ret7 := by
    simpa [state7, ret7] using step7.1
  have h7Arg : state7.arg ≠ zero := by
    simpa [state7] using step7.2.1
  have h7Log : state7.arg.toNat.log2 = highest + ret7 := by
    simpa [state7, ret7] using step7.2.2.1
  have h7Bound : highest + ret7 < 256 := by
    simpa [ret7] using step7.2.2.2
  let ret8 := applyHighestBitStep highest ret7 (255, 1)
  let state8 := applyStep state7 (255, 1)
  have step8 := applyStep_final_ret_refines (state := state7)
    (highest := highest) (ret := ret7) h7Arg h7Ret h7Log h7Bound
  have h8Ret : state8.ret = word ret8 := by
    simpa [state8, ret8] using step8
  simpa [runNonzero, runHighestBit, clzHelperStepSchedule, state0, state1,
    state2, state3, state4, state5, state6, state7, state8, ret0, ret1,
    ret2, ret3, ret4, ret5, ret6, ret7, ret8, highest] using h8Ret

theorem run_eq_reference (value : Word) :
    run value = reference value := by
  by_cases hValue : value = zero
  · subst hValue
    simp [run, reference, zero, EvmYul.instBEqUInt256,
      EvmYul.instBEqUInt256.beq, EvmYul.UInt256.ofNat, Id.run]
  · have hValueBool : (value == zero) = false := by
      cases value with
      | mk valueFin =>
          simp [zero, EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq,
            EvmYul.UInt256.ofNat, Id.run] at hValue ⊢
          exact hValue
    have hRet := runNonzero_ret_eq_runHighestBit value hValue
    have hHighestNat : value.toNat.log2 < 256 := by
      have h := log2_toNat_lt_256_of_ne_zero hValue
      simpa [log2_toNat_eq] using h
    have hRunHighest :
        runHighestBit value.toNat.log2 = 255 - value.toNat.log2 :=
      runHighestBit_eq_reference ⟨value.toNat.log2, hHighestNat⟩
    rw [run, reference, hValueBool]
    rw [hRet, hRunHighest]
    simp [log2_toNat_eq]

def powerOfTwoInputsMatchReference? : Bool :=
  (List.range 256).all fun highestBit =>
    run (word (2 ^ highestBit)) == reference (word (2 ^ highestBit))

set_option maxRecDepth 10000 in
theorem powerOfTwoInputsMatchReference :
    powerOfTwoInputsMatchReference? = true := by
  decide

def boundaryInputs : List Word :=
  [ word 0
  , word 1
  , word 2
  , word (2 ^ 64)
  , word (2 ^ 127)
  , word (2 ^ 128)
  , word (2 ^ 254)
  , word (2 ^ 255)
  , word (EvmYul.UInt256.size - 1)
  ]

def boundaryInputsMatchReference? : Bool :=
  boundaryInputs.all fun value => run value == reference value

theorem run_zero :
    run zero = word 256 := by
  decide

theorem boundaryInputsMatchReference :
    boundaryInputsMatchReference? = true := by
  decide

end ClzHelperModel

def clzHelperStepBody (argName returnName : Name)
    (addend : Nat) : List Frontend.Stmt :=
  let stepBody : List Frontend.Stmt :=
    [Frontend.Stmt.assign [returnName]
      (clzPrim "add" [clzValue returnName, clzWord addend])]
  if addend == 1 then
    stepBody
  else
    stepBody ++
      [Frontend.Stmt.assign [argName]
        (clzPrim "shl" [clzWord addend, clzValue argName])]

def clzHelperAppendStep (argName returnName : Name)
    (body : List Frontend.Stmt) (step : Nat × Nat) : List Frontend.Stmt :=
  let checkShift := step.fst
  let addend := step.snd
  body ++
    [Frontend.Stmt.ifThen
      (clzPrim "iszero"
        [clzPrim "shr" [clzWord checkShift, clzValue argName]])
      (clzHelperStepBody argName returnName addend)]

def clzHelperNonzeroBody (argName returnName : Name) :
    List Frontend.Stmt :=
  clzHelperStepSchedule.foldl
    (clzHelperAppendStep argName returnName)
    [Frontend.Stmt.assign [returnName] (clzWord 0)]

def clzHelperBody (argName returnName : Name) :
    List Frontend.Stmt :=
  [Frontend.Stmt.assign [returnName] (clzWord 256),
    Frontend.Stmt.ifThen (clzValue argName)
      (clzHelperNonzeroBody argName returnName)]

def clzHelperFunctionDef (argName returnName : Name) :
    Frontend.FunctionDef :=
  { params := [argName]
    returns := [returnName]
    body := clzHelperBody argName returnName }

structure ClzHelperSpec (fn : Frontend.FunctionDef)
    (argName returnName : Name) : Prop where
  params_eq : fn.params = [argName]
  returns_eq : fn.returns = [returnName]
  body_eq : fn.body = clzHelperBody argName returnName
  schedule_ok : clzHelperStepScheduleOk? = true

theorem clzHelperFunctionDef_spec (argName returnName : Name) :
    ClzHelperSpec (clzHelperFunctionDef argName returnName)
      argName returnName := by
  exact
    { params_eq := rfl
      returns_eq := rfl
      body_eq := rfl
      schedule_ok := clzHelperStepScheduleOk }

theorem clzHelperFunctionDef_shape (argName returnName : Name) :
    (clzHelperFunctionDef argName returnName).params = [argName] ∧
      (clzHelperFunctionDef argName returnName).returns = [returnName] := by
  have hSpec := clzHelperFunctionDef_spec argName returnName
  exact ⟨hSpec.params_eq, hSpec.returns_eq⟩

theorem clzHelperFunctionDef_toYul?_some (argName returnName : Name) :
    ∃ body,
      Frontend.FunctionDef.toYul? (clzHelperFunctionDef argName returnName) =
        some (.Def [argName] [returnName] body) := by
  unfold clzHelperFunctionDef clzHelperBody clzHelperNonzeroBody
    clzHelperAppendStep clzHelperStepBody clzHelperStepSchedule clzPrim
    clzValue clzWord Frontend.FunctionDef.toYul?
  simp [Frontend.Stmt.List.toYul?, Frontend.Stmt.toYul?,
    Frontend.Expr.toYul?, Frontend.Expr.List.toYul?,
    Frontend.Primitive.ofName?]

namespace ClzHelperExecution

def truthy (value : Word) : Bool :=
  value != ClzHelperModel.zero

def readName? (argName returnName name : Name)
    (state : ClzHelperModel.State) : Option Word :=
  if name = argName then
    some state.arg
  else if name = returnName then
    some state.ret
  else
    none

def writeName? (argName returnName name : Name) (value : Word)
    (state : ClzHelperModel.State) : Option ClzHelperModel.State :=
  if name = argName then
    some { state with arg := value }
  else if name = returnName then
    some { state with ret := value }
  else
    none

def evalPrimitive? (callee : Name) (args : List Word) : Option Word :=
  match callee, args with
  | "add", [left, right] => some (EvmYul.UInt256.add left right)
  | "shl", [shift, value] => some (EvmYul.UInt256.shiftLeft value shift)
  | "shr", [shift, value] => some (EvmYul.UInt256.shiftRight value shift)
  | "iszero", [value] => some (EvmYul.UInt256.isZero value)
  | _, _ => none

mutual
  def evalExpr? (argName returnName : Name)
      (state : ClzHelperModel.State) : Frontend.Expr → Option Word
    | .lit value => some value
    | .var name => readName? argName returnName name state
    | .call .primitive callee args => do
        let values ← evalExprList? argName returnName state args
        evalPrimitive? callee values
    | _ => none

  def evalExprList? (argName returnName : Name)
      (state : ClzHelperModel.State) :
      List Frontend.Expr → Option (List Word)
    | [] => some []
    | expr :: rest => do
        let head ← evalExpr? argName returnName state expr
        let tail ← evalExprList? argName returnName state rest
        some (head :: tail)
end

mutual
  def execStmt? (argName returnName : Name)
      (state : ClzHelperModel.State) : Frontend.Stmt →
      Option ClzHelperModel.State
    | .block stmts => execStmts? argName returnName state stmts
    | .assign [name] value => do
        let value' ← evalExpr? argName returnName state value
        writeName? argName returnName name value' state
    | .ifThen condition body => do
        let value ← evalExpr? argName returnName state condition
        if truthy value then
          execStmts? argName returnName state body
        else
          some state
    | _ => none

  def execStmts? (argName returnName : Name)
      (state : ClzHelperModel.State) :
      List Frontend.Stmt → Option ClzHelperModel.State
    | [] => some state
    | stmt :: rest => do
        let state' ← execStmt? argName returnName state stmt
        execStmts? argName returnName state' rest
end

theorem execStmts_append_some
    {argName returnName : Name}
    {pre suffix : List Frontend.Stmt}
    {state mid : ClzHelperModel.State}
    (hPre : execStmts? argName returnName state pre = some mid) :
    execStmts? argName returnName state (pre ++ suffix) =
      execStmts? argName returnName mid suffix := by
  induction pre generalizing state with
  | nil =>
      simp [execStmts?] at hPre ⊢
      exact hPre ▸ rfl
  | cons stmt rest ih =>
      simp [execStmts?] at hPre ⊢
      cases hStmt : execStmt? argName returnName state stmt with
      | none =>
          simp [hStmt] at hPre
      | some after =>
          simp [hStmt] at hPre ⊢
          exact ih hPre

theorem exec_clzHelperStepBody_eq_applyStepBody
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (state : ClzHelperModel.State) (addend : Nat) :
    execStmts? argName returnName state
        (clzHelperStepBody argName returnName addend) =
      some (ClzHelperModel.applyStepBody addend state) := by
  by_cases hAdd : addend == 1
  · simp [clzHelperStepBody, ClzHelperModel.applyStepBody, hAdd,
      execStmts?, execStmt?, evalExpr?, evalExprList?, evalPrimitive?,
      readName?, writeName?, clzPrim, clzValue, clzWord, ClzHelperModel.word,
      hNames, Ne.symm hNames]
  · simp [clzHelperStepBody, ClzHelperModel.applyStepBody, hAdd,
      execStmts?, execStmt?, evalExpr?, evalExprList?, evalPrimitive?,
      readName?, writeName?, clzPrim, clzValue, clzWord, ClzHelperModel.word,
      hNames, Ne.symm hNames]

theorem exec_clzHelperStep_eq_applyStep
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (state : ClzHelperModel.State) (step : Nat × Nat) :
    execStmts? argName returnName state
        [Frontend.Stmt.ifThen
          (clzPrim "iszero"
            [clzPrim "shr" [clzWord step.fst, clzValue argName]])
          (clzHelperStepBody argName returnName step.snd)] =
      some (ClzHelperModel.applyStep state step) := by
  cases step with
  | mk checkShift addend =>
      by_cases hCond :
          (EvmYul.UInt256.isZero
              (EvmYul.UInt256.shiftRight state.arg
                (EvmYul.UInt256.ofNat checkShift)) !=
            ClzHelperModel.zero) = true
      · simp [execStmts?, execStmt?, evalExpr?, evalExprList?,
          evalPrimitive?, readName?, writeName?, truthy,
          ClzHelperModel.applyStep, ClzHelperModel.shouldRunStep,
          clzPrim, clzValue, clzWord, ClzHelperModel.word,
          hNames, Ne.symm hNames, hCond,
          exec_clzHelperStepBody_eq_applyStepBody]
      · simp [execStmts?, execStmt?, evalExpr?, evalExprList?,
          evalPrimitive?, readName?, writeName?, truthy,
          ClzHelperModel.applyStep, ClzHelperModel.shouldRunStep,
          clzPrim, clzValue, clzWord, ClzHelperModel.word,
          hNames, Ne.symm hNames, hCond,
          exec_clzHelperStepBody_eq_applyStepBody]

theorem exec_clzHelperAppendStep_eq_applyStep
    (argName returnName : Name) (hNames : argName ≠ returnName)
    {body : List Frontend.Stmt} {state mid : ClzHelperModel.State}
    (step : Nat × Nat)
    (hBody : execStmts? argName returnName state body = some mid) :
    execStmts? argName returnName state
        (clzHelperAppendStep argName returnName body step) =
      some (ClzHelperModel.applyStep mid step) := by
  cases step with
  | mk checkShift addend =>
      unfold clzHelperAppendStep
      rw [execStmts_append_some hBody]
      exact exec_clzHelperStep_eq_applyStep argName returnName hNames mid
        (checkShift, addend)

theorem exec_clzHelperStepFold_eq_model
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (steps : List (Nat × Nat)) {body : List Frontend.Stmt}
    {state mid : ClzHelperModel.State}
    (hBody : execStmts? argName returnName state body = some mid) :
    execStmts? argName returnName state
        (steps.foldl (clzHelperAppendStep argName returnName) body) =
      some (steps.foldl ClzHelperModel.applyStep mid) := by
  induction steps generalizing body mid with
  | nil =>
      simpa using hBody
  | cons step rest ih =>
      exact ih
        (body := clzHelperAppendStep argName returnName body step)
        (mid := ClzHelperModel.applyStep mid step)
        (exec_clzHelperAppendStep_eq_applyStep argName returnName hNames
          step hBody)

theorem exec_clzHelperNonzeroBody_eq_runNonzero
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (value : Word) (initialRet : Word) :
    execStmts? argName returnName
        { arg := value, ret := initialRet }
        (clzHelperNonzeroBody argName returnName) =
      some (ClzHelperModel.runNonzero value) := by
  unfold clzHelperNonzeroBody ClzHelperModel.runNonzero
  exact exec_clzHelperStepFold_eq_model argName returnName hNames
    clzHelperStepSchedule
    (body := [Frontend.Stmt.assign [returnName] (clzWord 0)])
    (state := { arg := value, ret := initialRet })
    (mid := { arg := value, ret := ClzHelperModel.word 0 })
    (by
      simp [execStmts?, execStmt?, evalExpr?, readName?, writeName?,
        clzWord, ClzHelperModel.word, hNames, Ne.symm hNames])

def expectedFinalState (value : Word) : ClzHelperModel.State :=
  if truthy value then
    ClzHelperModel.runNonzero value
  else
    { arg := value, ret := ClzHelperModel.word 256 }

theorem exec_clzHelperBody_eq_expectedFinalState
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (value initialRet : Word) :
    execStmts? argName returnName
        { arg := value, ret := initialRet }
        (clzHelperBody argName returnName) =
      some (expectedFinalState value) := by
  by_cases hTruthy : truthy value
  · simp [clzHelperBody, expectedFinalState, hTruthy,
      execStmts?, execStmt?, evalExpr?, readName?, writeName?, clzWord,
      clzValue, hNames, Ne.symm hNames,
      exec_clzHelperNonzeroBody_eq_runNonzero]
  · simp [clzHelperBody, expectedFinalState, hTruthy,
      execStmts?, execStmt?, evalExpr?, readName?, writeName?, clzWord,
      clzValue, ClzHelperModel.word, hNames, Ne.symm hNames]

theorem expectedFinalState_ret_eq_run (value : Word) :
    (expectedFinalState value).ret = ClzHelperModel.run value := by
  by_cases hZero : value == ClzHelperModel.zero
  · have hTruthy : truthy value = false := by
      simp [truthy, bne, hZero]
    simp [expectedFinalState, ClzHelperModel.run, hZero, hTruthy]
  · have hTruthy : truthy value = true := by
      have hEqFalse :
          (value == ClzHelperModel.zero) = false :=
        Bool.eq_false_of_not_eq_true hZero
      simp [truthy, bne, hEqFalse]
    simp [expectedFinalState, ClzHelperModel.run, hZero, hTruthy]

theorem exec_clzHelperBody_ret_eq_run
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (value initialRet : Word) :
    (execStmts? argName returnName
        { arg := value, ret := initialRet }
        (clzHelperBody argName returnName)).map (fun state => state.ret) =
      some (ClzHelperModel.run value) := by
  rw [exec_clzHelperBody_eq_expectedFinalState argName returnName hNames]
  simp [expectedFinalState_ret_eq_run]

theorem exec_clzHelperSpec_ret_eq_run
    {fn : Frontend.FunctionDef} {argName returnName : Name}
    (hSpec : ClzHelperSpec fn argName returnName)
    (hNames : argName ≠ returnName)
    (value initialRet : Word) :
    (execStmts? argName returnName
        { arg := value, ret := initialRet }
        fn.body).map (fun state => state.ret) =
      some (ClzHelperModel.run value) := by
  rw [hSpec.body_eq]
  exact exec_clzHelperBody_ret_eq_run argName returnName hNames value
    initialRet

end ClzHelperExecution

namespace ClzCallReplacement

abbrev Env := Name → Option Word

def clzModel (value : Word) : Word :=
  ClzHelperModel.run value

theorem clzModel_eq_reference (value : Word) :
    clzModel value = ClzHelperModel.reference value := by
  unfold clzModel
  exact ClzHelperModel.run_eq_reference value

mutual
  def evalPureExpr? (env : Env) : Frontend.Expr → Option Word
    | .lit value => some value
    | .var name => env name
    | .call .primitive callee args => do
        let values ← evalPureExprList? env args
        ClzHelperExecution.evalPrimitive? callee values
    | _ => none

  def evalPureExprList? (env : Env) :
      List Frontend.Expr → Option (List Word)
    | [] => some []
    | expr :: rest => do
        let head ← evalPureExpr? env expr
        let tail ← evalPureExprList? env rest
        some (head :: tail)
end

def evalGeneratedHelperCall? (argName returnName : Name)
    (fn : Frontend.FunctionDef) (value initialRet : Word) : Option Word :=
  (ClzHelperExecution.execStmts? argName returnName
      { arg := value, ret := initialRet }
      fn.body).map (fun state => state.ret)

def evalHelperCallExpr? (helper argName returnName : Name)
    (fn : Frontend.FunctionDef) (env : Env)
    (expr : Frontend.Expr) (initialRet : Word) : Option Word :=
  match expr with
  | .call .user callee [argExpr] =>
      if callee = helper then do
        let value ← evalPureExpr? env argExpr
        evalGeneratedHelperCall? argName returnName fn value initialRet
      else
        none
  | _ => none

theorem evalGeneratedHelperCall_eq_clzModel
    {fn : Frontend.FunctionDef} {argName returnName : Name}
    (hSpec : ClzHelperSpec fn argName returnName)
    (hNames : argName ≠ returnName)
    (value initialRet : Word) :
    evalGeneratedHelperCall? argName returnName fn value initialRet =
      some (clzModel value) := by
  unfold evalGeneratedHelperCall? clzModel
  exact
    ClzHelperExecution.exec_clzHelperSpec_ret_eq_run
      hSpec hNames value initialRet

theorem evalHelperCallExpr_eq_clzModel
    {helper argName returnName : Name} {fn : Frontend.FunctionDef}
    {env : Env} {argExpr : Frontend.Expr} {value initialRet : Word}
    (hSpec : ClzHelperSpec fn argName returnName)
    (hNames : argName ≠ returnName)
    (hArg : evalPureExpr? env argExpr = some value) :
    evalHelperCallExpr? helper argName returnName fn env
        (.call .user helper [argExpr]) initialRet =
      some (clzModel value) := by
  simp [evalHelperCallExpr?, hArg,
    evalGeneratedHelperCall_eq_clzModel hSpec hNames, clzModel]

theorem evalGeneratedHelperCall_eq_reference
    {fn : Frontend.FunctionDef} {argName returnName : Name}
    (hSpec : ClzHelperSpec fn argName returnName)
    (hNames : argName ≠ returnName)
    (value initialRet : Word) :
    evalGeneratedHelperCall? argName returnName fn value initialRet =
      some (ClzHelperModel.reference value) := by
  rw [evalGeneratedHelperCall_eq_clzModel hSpec hNames]
  simp [clzModel_eq_reference]

theorem evalHelperCallExpr_eq_reference
    {helper argName returnName : Name} {fn : Frontend.FunctionDef}
    {env : Env} {argExpr : Frontend.Expr} {value initialRet : Word}
    (hSpec : ClzHelperSpec fn argName returnName)
    (hNames : argName ≠ returnName)
    (hArg : evalPureExpr? env argExpr = some value) :
    evalHelperCallExpr? helper argName returnName fn env
        (.call .user helper [argExpr]) initialRet =
      some (ClzHelperModel.reference value) := by
  rw [evalHelperCallExpr_eq_clzModel hSpec hNames hArg]
  simp [clzModel_eq_reference]

end ClzCallReplacement

mutual
  def Literal.elaborate : Raw.Literal → DecodeM Frontend.Expr
    | .number value => .ok (.lit value)
    | .bool value => .ok (.lit (EvmYul.UInt256.ofNat (if value then 1 else 0)))
    | .stringLit value => .ok (.stringLit value)
    | .bytesLit bytes => .ok (.bytesLit bytes)

  def SwitchCaseValue.elaborate :
      Raw.SwitchCaseValue → DecodeM Frontend.SwitchCaseValue
    | .literal (.number value) => .ok (.word value)
    | .literal (.bool value) => .ok (.boolLit value)
    | .literal (.stringLit value) => .ok (.stringLit value)
    | .literal (.bytesLit bytes) => .ok (.bytesLit bytes)

  def Expr.elaborate : Raw.Expr → ElabM Frontend.Expr
    | .literal literal =>
        match Literal.elaborate literal with
        | .ok expr => pure expr
        | .error err => throw err
    | .identifier name => do
        requireIdentifierVisible name "expression"
        pure (.var name)
    | .functionCall "memoryguard" args => do
        match args with
        | [arg] =>
            let arg ← Expr.elaborate arg
            pure (.call .objectBuiltin "memoryguard" [arg])
        | _ => throw "memoryguard expects one argument"
    | .functionCall "clz" args => do
        match args with
        | [arg] =>
            let arg ← Expr.elaborate arg
            let helper ← ensureClzHelper
            pure (.call .user helper [arg])
        | _ => throw "clz expects one argument"
    | .functionCall name args => do
        let args ← Expr.List.elaborate args
        let kind := CallClass.classifyCall name
        let callee ←
          match kind with
          | .user => resolveFunction name
          | _ => pure name
        pure (.call kind callee args)

  def Expr.List.elaborate : List Raw.Expr → ElabM (List Frontend.Expr)
    | [] => pure []
    | expr :: rest => do
        let head ← Expr.elaborate expr
        let tail ← Expr.List.elaborate rest
        pure (head :: tail)

  def Stmt.elaborate : Raw.Stmt → ElabM Frontend.Stmt
    | .block stmts => do
        let stmts ← Stmt.List.elaborateBlock stmts true
        pure (.block stmts)
    | .variableDeclaration names value? => do
        let value? ←
          match value? with
          | none => pure none
          | some value => some <$> Expr.elaborate value
        declareIdentifiers names "variable"
        pure (.letDecl names value?)
    | .assignment names value => do
        requireIdentifiersVisible names "assignment"
        let value ← Expr.elaborate value
        pure (.assign names value)
    | .expressionStatement expr => do
        let expr ← Expr.elaborate expr
        pure (.exprStmt expr)
    | .functionDefinition name params returns body => do
        let generated ← resolveFunction name
        let fn ← FunctionDef.elaborate params returns body
        pure (.functionDef generated params returns fn.body)
    | .switch scrutinee cases defaultBody => do
        let scrutinee ← Expr.elaborate scrutinee
        let cases ← Stmt.CaseList.elaborate cases
        let defaultBody ← Stmt.List.elaborateBlock defaultBody true
        pure (.switch scrutinee cases defaultBody)
    | .forLoop pre condition post body => do
        pushIdentifierScope
        let preHasFunctions := Stmt.List.hasImmediateFunctionDefinition pre
        let pre ←
          if preHasFunctions then
            Stmt.List.elaborateForInitBlockWithScope pre
          else
            Stmt.List.elaborateBlock pre false
        let condition ← Expr.elaborate condition
        let post ← Stmt.List.elaborateBlock post true
        let body ← Stmt.List.elaborateBlock body true
        if preHasFunctions then
          popFunctionScope
        popIdentifierScope
        pure (.forLoop pre condition post body)
    | .ifThen condition body => do
        let condition ← Expr.elaborate condition
        let body ← Stmt.List.elaborateBlock body true
        pure (.ifThen condition body)
    | .break => pure .break
    | .continue => pure .continue
    | .leave => pure .leave

  def Stmt.List.hasImmediateFunctionDefinition : List Raw.Stmt → Bool
    | [] => false
    | .functionDefinition _ _ _ _ :: _ => true
    | _ :: rest => Stmt.List.hasImmediateFunctionDefinition rest

  def Stmt.List.localFunctionScope :
      List Raw.Stmt → ElabM (List (Name × Name))
    | [] => pure []
    | stmt :: rest => do
        match stmt with
        | .functionDefinition name _ _ _ =>
            let tail ← Stmt.List.localFunctionScope rest
            if tail.any fun entry => entry.fst == name then
              throw s!"duplicate Yul function {name} in block"
            declareIdentifiers [name] "function"
            let generated ← freshGeneratedFunctionName name
            pure ((name, generated) :: tail)
        | _ => Stmt.List.localFunctionScope rest

  def Stmt.List.hoistLocalFunctions :
      List Raw.Stmt → List (Name × Name) → ElabM Unit
    | [], _ => pure ()
    | stmt :: rest, scope => do
        match stmt with
        | .functionDefinition name params returns body =>
            let generated ←
              match lookupFunctionInScope name scope with
              | some generated => pure generated
              | none => throw s!"internal frontend error: missing generated name for {name}"
            let fn ← FunctionDef.elaborate params returns body
            modify fun state =>
              { state with
                hoistedFunctions :=
                  (generated, fn) :: state.hoistedFunctions }
            Stmt.List.hoistLocalFunctions rest scope
        | _ => Stmt.List.hoistLocalFunctions rest scope

  def Stmt.List.elaborateBlock (stmts : List Raw.Stmt)
      (createsScope : Bool) : ElabM (List Frontend.Stmt) := do
    if createsScope then
      pushIdentifierScope
    let scope ← Stmt.List.localFunctionScope stmts
    pushFunctionScope scope
    Stmt.List.hoistLocalFunctions stmts scope
    let result ← Stmt.List.elaborate stmts
    popFunctionScope
    if createsScope then
      popIdentifierScope
    pure result

  def Stmt.List.elaborateForInitBlockWithScope
      (stmts : List Raw.Stmt) : ElabM (List Frontend.Stmt) := do
    let scope ← Stmt.List.localFunctionScope stmts
    pushFunctionScope scope
    Stmt.List.hoistLocalFunctions stmts scope
    Stmt.List.elaborate stmts

  def Stmt.List.elaborate : List Raw.Stmt → ElabM (List Frontend.Stmt)
    | [] => pure []
    | stmt :: rest => do
        let head ← Stmt.elaborate stmt
        let tail ← Stmt.List.elaborate rest
        pure (head :: tail)

  def Stmt.CaseList.elaborate :
      List (Raw.SwitchCaseValue × List Raw.Stmt) →
        ElabM (List (Frontend.SwitchCaseValue × List Frontend.Stmt))
    | [] => pure []
    | (value, body) :: rest => do
        let value ←
          match SwitchCaseValue.elaborate value with
          | .ok value => pure value
          | .error err => throw err
        let body ← Stmt.List.elaborateBlock body true
        let rest ← Stmt.CaseList.elaborate rest
        pure ((value, body) :: rest)

  def FunctionDef.elaborate (params returns : List Name)
      (body : List Raw.Stmt) : ElabM Frontend.FunctionDef := do
    pushIdentifierScope
    declareIdentifiers (params ++ returns) "function parameter/result"
    let body ← Stmt.List.elaborateBlock body true
    popIdentifierScope
    pure { params, returns, body }
end

def PreservesHoisted {α : Type} (action : ElabM α) : Prop :=
  ∀ {state state' : State} {value : α}
      {entry : Name × Frontend.FunctionDef},
    action.run state = .ok (value, state') →
      entry ∈ state.hoistedFunctions →
        entry ∈ state'.hoistedFunctions

theorem PreservesHoisted.bind {α β : Type}
    {action : ElabM α} {next : α → ElabM β}
    (hAction : PreservesHoisted action)
    (hNext : ∀ value, PreservesHoisted (next value)) :
    PreservesHoisted (action >>= next) := by
  intro state state' value entry hRun hEntry
  simp [StateT.run_bind] at hRun
  cases hActionRun : action.run state with
  | error _ =>
      simp [hActionRun] at hRun
  | ok result =>
      rcases result with ⟨midValue, midState⟩
      have hMid : entry ∈ midState.hoistedFunctions :=
        hAction hActionRun hEntry
      simp [hActionRun] at hRun
      exact hNext midValue hRun hMid

theorem PreservesHoisted.map {α β : Type} {action : ElabM α}
    (f : α → β) (hAction : PreservesHoisted action) :
    PreservesHoisted (f <$> action) := by
  intro state state' value entry hRun hEntry
  simp [StateT.run_map] at hRun
  cases hActionRun : action.run state with
  | error _ =>
      simp [hActionRun] at hRun
  | ok result =>
      rcases result with ⟨_midValue, midState⟩
      have hMid : entry ∈ midState.hoistedFunctions :=
        hAction hActionRun hEntry
      simp [hActionRun] at hRun
      rcases hRun with ⟨_hValue, hState⟩
      subst state'
      exact hMid

theorem PreservesHoisted.pure {α : Type} (value : α) :
    PreservesHoisted (pure value : ElabM α) := by
  intro state state' result entry hRun hEntry
  simp [StateT.run_pure] at hRun
  cases hRun
  exact hEntry

theorem PreservesHoisted.throw {α : Type} (message : String) :
    PreservesHoisted (throw message : ElabM α) := by
  intro state state' value entry hRun hEntry
  unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
  change (Except.error message : DecodeM (α × State)) =
    .ok (value, state') at hRun
  cases hRun

theorem requireIdentifierVisible_preserves_hoistedFunction_mem
    (name : Name) (what : String) :
    PreservesHoisted (requireIdentifierVisible name what) := by
  intro state state' value entry hRun hEntry
  unfold requireIdentifierVisible identifierVisible at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hVisible : identifierVisibleIn name state.identifierScopes with
  | false =>
      simp [hVisible] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error s!"unknown Yul identifier {name} in {what}" :
        DecodeM (Unit × State)) = .ok (value, state') at hRun
      cases hRun
  | true =>
      simp [hVisible] at hRun
      cases hRun
      exact hEntry

theorem requireIdentifiersVisible_preserves_hoistedFunction_mem
    (names : List Name) (what : String) :
    PreservesHoisted (requireIdentifiersVisible names what) := by
  induction names with
  | nil =>
      simp [requireIdentifiersVisible]
      exact PreservesHoisted.pure ()
  | cons name rest ih =>
      change PreservesHoisted
        (requireIdentifierVisible name what >>= fun _ =>
          requireIdentifiersVisible rest what)
      exact
        PreservesHoisted.bind
          (requireIdentifierVisible_preserves_hoistedFunction_mem name what)
          (fun _ => ih)

theorem declareIdentifiers_preserves_hoistedFunction_mem
    (names : List Name) (description : String) :
    PreservesHoisted (declareIdentifiers names description) := by
  intro state state' value entry hRun hEntry
  unfold declareIdentifiers at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hScopes : state.identifierScopes with
  | nil =>
      cases hCollect : collectDeclaredIdentifiers names description [[]] with
      | error err =>
          simp [hScopes, hCollect] at hRun
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
          change (Except.error err : DecodeM (Unit × State)) =
            .ok (value, state') at hRun
          cases hRun
      | ok seen =>
          simp [hScopes, hCollect, StateT.run_set] at hRun
          cases hRun
          exact hEntry
  | cons scope rest =>
      cases hCollect :
          collectDeclaredIdentifiers names description (scope :: rest) with
      | error err =>
          simp [hScopes, hCollect] at hRun
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
          change (Except.error err : DecodeM (Unit × State)) =
            .ok (value, state') at hRun
          cases hRun
      | ok seen =>
          simp [hScopes, hCollect, StateT.run_set] at hRun
          cases hRun
          exact hEntry

theorem hoistFunctionEntry_preserves_hoistedFunction_mem
    (generated : Name) (fn : Frontend.FunctionDef) :
    PreservesHoisted (modify fun state =>
      { state with hoistedFunctions := (generated, fn) ::
        state.hoistedFunctions }) := by
  intro state state' value entry hRun hEntry
  simp [StateT.run_modify] at hRun
  cases hRun
  exact List.mem_cons_of_mem (generated, fn) hEntry

theorem pushIdentifierScope_preserves_hoistedFunction_mem :
    PreservesHoisted pushIdentifierScope := by
  intro state state' value entry hRun hEntry
  unfold pushIdentifierScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  exact hEntry

theorem popIdentifierScope_preserves_hoistedFunction_mem :
    PreservesHoisted popIdentifierScope := by
  intro state state' value entry hRun hEntry
  unfold popIdentifierScope at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hScopes : state.identifierScopes with
  | nil =>
      simp [hScopes] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "internal frontend error: no identifier scope to pop" :
          DecodeM (Unit × State)) = .ok (value, state') at hRun
      cases hRun
  | cons _ rest =>
      simp [hScopes, StateT.run_set] at hRun
      cases hRun
      exact hEntry

theorem pushFunctionScope_preserves_hoistedFunction_mem
    (scope : List (Name × Name)) :
    PreservesHoisted (pushFunctionScope scope) := by
  intro state state' value entry hRun hEntry
  unfold pushFunctionScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  exact hEntry

theorem popFunctionScope_preserves_hoistedFunction_mem :
    PreservesHoisted popFunctionScope := by
  intro state state' value entry hRun hEntry
  unfold popFunctionScope at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hScopes : state.functionScopes with
  | nil =>
      simp [hScopes] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "internal frontend error: no function scope to pop" :
          DecodeM (Unit × State)) = .ok (value, state') at hRun
      cases hRun
  | cons _ rest =>
      simp [hScopes, StateT.run_set] at hRun
      cases hRun
      exact hEntry

theorem resolveFunction_preserves_hoistedFunction_mem (name : Name) :
    PreservesHoisted (resolveFunction name) := by
  intro state state' value entry hRun hEntry
  unfold resolveFunction at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hResolve : resolveFunctionIn name state.functionScopes with
  | none =>
      simp [hResolve] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error s!"unknown Yul function {name}" :
        DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | some _ =>
      simp [hResolve] at hRun
      cases hRun
      exact hEntry

theorem freshGeneratedFunctionNameFrom_preserves_hoistedFunction_mem
    (stem : Name) (fuel : Nat) :
    PreservesHoisted (freshGeneratedFunctionNameFrom stem fuel) := by
  induction fuel with
  | zero =>
      intro state state' value entry hRun hEntry
      unfold freshGeneratedFunctionNameFrom at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "could not allocate fresh generated Yul function name" :
          DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | succ fuel ih =>
      intro state state' value entry hRun hEntry
      unfold freshGeneratedFunctionNameFrom at hRun
      simp [StateT.run_bind, StateT.run_get, StateT.run_set] at hRun
      let candidate : Name :=
        "__yul_gen_" ++ toString state.nextGeneratedFunctionId ++ "_" ++ stem
      let bumpedState : State :=
        { state with
          nextGeneratedFunctionId := state.nextGeneratedFunctionId + 1 }
      change StateT.run
          (if candidate ∈ state.usedFunctionNames then
            freshGeneratedFunctionNameFrom stem fuel
          else
            (fun _ => candidate) <$> set
              { bumpedState with
                usedFunctionNames := candidate :: state.usedFunctionNames })
          bumpedState = .ok (value, state') at hRun
      by_cases hContains : candidate ∈ state.usedFunctionNames
      · simp [hContains] at hRun
        exact ih hRun hEntry
      · simp [hContains, StateT.run_map, StateT.run_set] at hRun
        simp [pure, Except.pure] at hRun
        rcases hRun with ⟨_hValue, hState⟩
        subst state'
        exact hEntry

theorem freshGeneratedFunctionName_preserves_hoistedFunction_mem
    (base : Name) :
    PreservesHoisted (freshGeneratedFunctionName base) := by
  unfold freshGeneratedFunctionName
  exact
    freshGeneratedFunctionNameFrom_preserves_hoistedFunction_mem
      (generatedIdentifierPart base) maxDecodeFuel

theorem freshNonFunctionBindingNameFrom_preserves_hoistedFunction_mem
    (stem : Name) (index fuel : Nat) :
    PreservesHoisted (freshNonFunctionBindingNameFrom stem index fuel) := by
  induction fuel generalizing index with
  | zero =>
      intro state state' value entry hRun hEntry
      unfold freshNonFunctionBindingNameFrom at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "could not allocate fresh generated Yul binding name" :
          DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | succ fuel ih =>
      intro state state' value entry hRun hEntry
      unfold freshNonFunctionBindingNameFrom at hRun
      simp [StateT.run_bind, StateT.run_get] at hRun
      let candidate : Name :=
        if index = 0 then "__yul_" ++ stem else
          "__yul_" ++ stem ++ "_" ++ toString index
      change StateT.run
          (if candidate ∈ state.usedFunctionNames then
            freshNonFunctionBindingNameFrom stem (index + 1) fuel
          else
            (fun _ => candidate) <$> set
              { state with
                usedFunctionNames := candidate :: state.usedFunctionNames })
          state = .ok (value, state') at hRun
      by_cases hContains : candidate ∈ state.usedFunctionNames
      · simp [hContains] at hRun
        exact ih (index + 1) hRun hEntry
      · simp [hContains, StateT.run_map, StateT.run_set] at hRun
        simp [pure, Except.pure] at hRun
        rcases hRun with ⟨_hValue, hState⟩
        subst state'
        exact hEntry

theorem freshNonFunctionBindingName_preserves_hoistedFunction_mem
    (base : Name) :
    PreservesHoisted (freshNonFunctionBindingName base) := by
  unfold freshNonFunctionBindingName
  exact
    freshNonFunctionBindingNameFrom_preserves_hoistedFunction_mem
      (generatedIdentifierPart base) 0 maxDecodeFuel

theorem ensureClzHelper_preserves_hoistedFunction_mem :
    PreservesHoisted ensureClzHelper := by
  intro state state' value entry hRun hEntry
  unfold ensureClzHelper at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hHelper : state.clzHelperName? with
  | some _ =>
      simp [hHelper] at hRun
      cases hRun
      exact hEntry
  | none =>
      simp [hHelper] at hRun
      cases hFreshHelper :
          (freshGeneratedFunctionName "clz").run state with
      | error _ =>
          simp [hFreshHelper] at hRun
      | ok helperResult =>
          rcases helperResult with ⟨helper, helperState⟩
          have hEntryHelper :
              entry ∈ helperState.hoistedFunctions :=
            freshGeneratedFunctionName_preserves_hoistedFunction_mem
              "clz" hFreshHelper hEntry
          simp [hFreshHelper] at hRun
          cases hFreshArg :
              (freshNonFunctionBindingName "clz_arg").run helperState with
          | error _ =>
              simp [hFreshArg] at hRun
          | ok argResult =>
              rcases argResult with ⟨arg, argState⟩
              have hEntryArg :
                  entry ∈ argState.hoistedFunctions :=
                freshNonFunctionBindingName_preserves_hoistedFunction_mem
                  "clz_arg" hFreshArg hEntryHelper
              simp [hFreshArg] at hRun
              cases hFreshRet :
                  (freshNonFunctionBindingName "clz_ret").run argState with
              | error _ =>
                  simp [hFreshRet] at hRun
              | ok retResult =>
                  rcases retResult with ⟨ret, retState⟩
                  have hEntryRet :
                      entry ∈ retState.hoistedFunctions :=
                    freshNonFunctionBindingName_preserves_hoistedFunction_mem
                      "clz_ret" hFreshRet hEntryArg
                  simp [hFreshRet, StateT.run_modify] at hRun
                  rcases hRun with ⟨_hValue, hState⟩
                  subst state'
                  simpa using hEntryRet

namespace Expr

mutual

theorem elaborate_preserves_hoistedFunction_mem
    (expr : Raw.Expr) : PreservesHoisted (Expr.elaborate expr) := by
  intro state state' value entry hRun hEntry
  cases expr with
  | literal literal =>
      cases literal <;>
        simp [Expr.elaborate, Literal.elaborate] at hRun <;>
        cases hRun <;>
        exact hEntry
  | identifier name =>
      unfold Expr.elaborate at hRun
      exact
        PreservesHoisted.map (fun _ => Frontend.Expr.var name)
          (requireIdentifierVisible_preserves_hoistedFunction_mem
            name "expression") hRun hEntry
  | functionCall name args =>
      by_cases hMemoryguard : name = "memoryguard"
      · subst name
        cases args with
        | nil =>
            unfold Expr.elaborate at hRun
            exact PreservesHoisted.throw
              "memoryguard expects one argument" hRun hEntry
        | cons arg rest =>
            cases rest with
            | nil =>
                unfold Expr.elaborate at hRun
                exact
                  PreservesHoisted.map
                    (fun arg =>
                      Frontend.Expr.call .objectBuiltin "memoryguard" [arg])
                    (elaborate_preserves_hoistedFunction_mem arg)
                    hRun hEntry
            | cons _ _ =>
                unfold Expr.elaborate at hRun
                exact PreservesHoisted.throw
                  "memoryguard expects one argument" hRun hEntry
      · by_cases hClz : name = "clz"
        · subst name
          cases args with
          | nil =>
              unfold Expr.elaborate at hRun
              exact PreservesHoisted.throw "clz expects one argument"
                hRun hEntry
          | cons arg rest =>
              cases rest with
              | nil =>
                  unfold Expr.elaborate at hRun
                  exact
                    PreservesHoisted.bind
                      (elaborate_preserves_hoistedFunction_mem arg)
                      (fun arg =>
                        PreservesHoisted.bind
                          ensureClzHelper_preserves_hoistedFunction_mem
                          (fun helper => PreservesHoisted.pure
                            (Frontend.Expr.call .user helper [arg])))
                      hRun hEntry
              | cons _ _ =>
                  unfold Expr.elaborate at hRun
                  exact PreservesHoisted.throw "clz expects one argument"
                    hRun hEntry
        · unfold Expr.elaborate at hRun
          simp [hMemoryguard, hClz, StateT.run_bind] at hRun
          cases hArgs : (Expr.List.elaborate args).run state with
          | error _ =>
              simp [hArgs] at hRun
          | ok result =>
              rcases result with ⟨args', argState⟩
              have hEntryArgs :
                  entry ∈ argState.hoistedFunctions :=
                List.elaborate_preserves_hoistedFunction_mem
                  args hArgs hEntry
              simp [hArgs] at hRun
              cases hClass : CallClass.classifyCall name with
              | primitive =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hEntryArgs
              | user =>
                  simp [hClass] at hRun
                  exact
                    PreservesHoisted.map
                      (fun callee =>
                        Frontend.Expr.call .user callee args')
                      (resolveFunction_preserves_hoistedFunction_mem name)
                      hRun hEntryArgs
              | objectBuiltin =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hEntryArgs
              | dialectBuiltin =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hEntryArgs
  termination_by 2 * sizeOf expr
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem List.elaborate_preserves_hoistedFunction_mem
    (exprs : List Raw.Expr) :
    PreservesHoisted (Expr.List.elaborate exprs) := by
  cases exprs with
  | nil =>
      intro state state' value entry hRun hEntry
      unfold Expr.List.elaborate at hRun
      simp [StateT.run_pure] at hRun
      cases hRun
      exact hEntry
  | cons expr rest =>
      intro state state' value entry hRun hEntry
      unfold Expr.List.elaborate at hRun
      exact
        PreservesHoisted.bind
          (elaborate_preserves_hoistedFunction_mem expr)
          (fun head =>
            PreservesHoisted.bind
              (List.elaborate_preserves_hoistedFunction_mem rest)
              (fun tail => PreservesHoisted.pure (head :: tail)))
          hRun hEntry
  termination_by 2 * sizeOf exprs + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end

theorem elaborate_user_call_resolved
    {state argState : State} {name generated : Name}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hArgs :
      (Expr.List.elaborate args).run state = .ok (args', argState))
    (hClass : CallClass.classifyCall name = .user)
    (hResolve :
      resolveFunctionIn name argState.functionScopes = some generated) :
    (Expr.elaborate (.functionCall name args)).run state =
      .ok (.call .user generated args', argState) := by
  simp [Expr.elaborate, hNotMemoryguard, hNotClz, hArgs, hClass,
    resolveFunction, hResolve]
  rfl

end Expr

namespace Stmt

theorem elaborate_functionDefinition_resolved_stub
    {state state' : State} {name : Name} {params returns : List Name}
    {generated : Name} {body : List Raw.Stmt} {fn : Frontend.FunctionDef}
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hFn :
      (FunctionDef.elaborate params returns body).run state =
        .ok (fn, state')) :
    (Stmt.elaborate (.functionDefinition name params returns body)).run
      state =
        .ok (.functionDef generated params returns fn.body, state') := by
  simp [Stmt.elaborate, resolveFunction, hResolve, hFn]

end Stmt

namespace Stmt.List

theorem localFunctionScope_single_functionDefinition
    {state declaredState state' : State}
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    (hDeclare :
      (declareIdentifiers [name] "function").run state =
        .ok ((), declaredState))
    (hFresh :
      (freshGeneratedFunctionName name).run declaredState =
        .ok (generated, state')) :
    (Stmt.List.localFunctionScope
      [.functionDefinition name params returns body]).run state =
        .ok ([(name, generated)], state') := by
  change declareIdentifiers [name] "function" state =
    .ok ((), declaredState) at hDeclare
  change freshGeneratedFunctionName name declaredState =
    .ok (generated, state') at hFresh
  simp [Stmt.List.localFunctionScope, hDeclare, hFresh, StateT.run,
    StateT.instMonad, StateT.bind, StateT.pure, pure, Except.pure]

theorem localFunctionScope_cons_functionDefinition
    {state tailState declaredState state' : State}
    {name generated : Name} {params returns : List Name}
    {body rest : List Raw.Stmt} {tailScope : List (Name × Name)}
    (hTail :
      (Stmt.List.localFunctionScope rest).run state =
        .ok (tailScope, tailState))
    (hNoDuplicate :
      (tailScope.any fun entry => entry.fst == name) = false)
    (hDeclare :
      (declareIdentifiers [name] "function").run tailState =
        .ok ((), declaredState))
    (hFresh :
      (freshGeneratedFunctionName name).run declaredState =
        .ok (generated, state')) :
    (Stmt.List.localFunctionScope
      (.functionDefinition name params returns body :: rest)).run state =
        .ok ((name, generated) :: tailScope, state') := by
  change Stmt.List.localFunctionScope rest state =
    .ok (tailScope, tailState) at hTail
  change declareIdentifiers [name] "function" tailState =
    .ok ((), declaredState) at hDeclare
  change freshGeneratedFunctionName name declaredState =
    .ok (generated, state') at hFresh
  simp [Stmt.List.localFunctionScope, hTail, hNoDuplicate, hDeclare, hFresh,
    StateT.run, StateT.instMonad, StateT.bind, StateT.pure, pure, Except.pure]

theorem localFunctionScope_preserves_hoistedFunction_mem
    (stmts : List Raw.Stmt) :
    PreservesHoisted (Stmt.List.localFunctionScope stmts) := by
  induction stmts with
  | nil =>
      simp [Stmt.List.localFunctionScope]
      exact PreservesHoisted.pure []
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          change PreservesHoisted
            (Stmt.List.localFunctionScope rest >>= fun tail =>
              if tail.any fun entry => entry.fst == name then
                throw s!"duplicate Yul function {name} in block"
              else
                declareIdentifiers [name] "function" >>= fun _ =>
                  freshGeneratedFunctionName name >>= fun generated =>
                    pure ((name, generated) :: tail))
          exact
            PreservesHoisted.bind ih (fun tail => by
              cases hDuplicate :
                  (tail.any fun entry => entry.fst == name) with
              | false =>
                  simp [hDuplicate]
                  exact
                    PreservesHoisted.bind
                      (declareIdentifiers_preserves_hoistedFunction_mem
                        [name] "function")
                      (fun _ =>
                        PreservesHoisted.bind
                          (freshGeneratedFunctionName_preserves_hoistedFunction_mem
                            name)
                          (fun generated =>
                            PreservesHoisted.pure
                              ((name, generated) :: tail)))
              | true =>
                  simp [hDuplicate]
                  exact PreservesHoisted.throw
                    s!"duplicate Yul function {name} in block")
      | block stmts =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | variableDeclaration names value? =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | assignment names value =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | expressionStatement expr =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | switch scrutinee cases default =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | forLoop pre condition post body =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | ifThen condition body =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | «break» =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | «continue» =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih
      | «leave» =>
          change PreservesHoisted (Stmt.List.localFunctionScope rest)
          exact ih

theorem hoistLocalFunctions_single_functionDefinition_resolved
    {state state' : State} {scope : List (Name × Name)}
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt} {fn : Frontend.FunctionDef}
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hFn :
      (FunctionDef.elaborate params returns body).run state =
        .ok (fn, state')) :
    (Stmt.List.hoistLocalFunctions
      [.functionDefinition name params returns body] scope).run state =
        .ok ((), { state' with
          hoistedFunctions := (generated, fn) :: state'.hoistedFunctions }) := by
  change FunctionDef.elaborate params returns body state =
    .ok (fn, state') at hFn
  simp [Stmt.List.hoistLocalFunctions, hLookup, hFn, StateT.run,
    StateT.instMonad, StateT.bind, StateT.pure, modify, MonadStateOf.modifyGet,
    MonadState.modifyGet, instMonadStateOfMonadStateOf,
    instMonadStateOfStateTOfMonad, StateT.modifyGet, pure, Except.pure]

theorem lookupFunctionInScope_cons_self
    (name generated : Name) (tail : List (Name × Name)) :
    lookupFunctionInScope name ((name, generated) :: tail) = some generated := by
  simp [lookupFunctionInScope]

theorem resolveFunctionIn_cons_scope_self
    (name generated : Name) (tail : List (Name × Name))
    (outer : List (List (Name × Name))) :
    resolveFunctionIn name (((name, generated) :: tail) :: outer) =
      some generated := by
  simp [resolveFunctionIn, lookupFunctionInScope_cons_self]

theorem resolveFunctionIn_of_scope_lookup
    {name generated : Name} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    (hLookup : lookupFunctionInScope name scope = some generated) :
    resolveFunctionIn name (scope :: outer) = some generated := by
  simp [resolveFunctionIn, hLookup]

theorem hoistLocalFunctions_single_functionDefinition_preserves_body_entry
    {state bodyState finalState : State} {scope : List (Name × Name)}
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt} {fn : Frontend.FunctionDef}
    {entry : Name × Frontend.FunctionDef}
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hFn :
      (FunctionDef.elaborate params returns body).run state =
        .ok (fn, bodyState))
    (hHoist :
      (Stmt.List.hoistLocalFunctions
        [.functionDefinition name params returns body] scope).run state =
        .ok ((), finalState))
    (hEntry : entry ∈ bodyState.hoistedFunctions) :
    entry ∈ finalState.hoistedFunctions := by
  have hEq :=
    hoistLocalFunctions_single_functionDefinition_resolved
      (state := state) (state' := bodyState) (scope := scope)
      (name := name) (generated := generated) (params := params)
      (returns := returns) (body := body) (fn := fn) hLookup hFn
  rw [hEq] at hHoist
  cases hHoist
  exact List.mem_cons_of_mem (generated, fn) hEntry

end Stmt.List

mutual

theorem Stmt.elaborate_preserves_hoistedFunction_mem
    (stmt : Raw.Stmt) : PreservesHoisted (Stmt.elaborate stmt) := by
  cases stmt with
  | block stmts =>
      simp only [Stmt.elaborate]
      exact
        PreservesHoisted.bind
          (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
            stmts true)
          (fun stmts => PreservesHoisted.pure (Frontend.Stmt.block stmts))
  | variableDeclaration names value? =>
      cases value? with
      | none =>
          simp only [Stmt.elaborate]
          exact
            PreservesHoisted.map
              (fun _ => Frontend.Stmt.letDecl names none)
              (declareIdentifiers_preserves_hoistedFunction_mem
                names "variable")
      | some value =>
          simp only [Stmt.elaborate]
          exact
            PreservesHoisted.bind
              (PreservesHoisted.map some
                (Expr.elaborate_preserves_hoistedFunction_mem value))
              (fun value? =>
                PreservesHoisted.bind
                  (declareIdentifiers_preserves_hoistedFunction_mem
                    names "variable")
                  (fun _ => PreservesHoisted.pure
                    (Frontend.Stmt.letDecl names value?)))
  | assignment names value =>
      simp only [Stmt.elaborate]
      exact
        PreservesHoisted.bind
          (requireIdentifiersVisible_preserves_hoistedFunction_mem
            names "assignment")
          (fun _ =>
            PreservesHoisted.bind
              (Expr.elaborate_preserves_hoistedFunction_mem value)
              (fun value => PreservesHoisted.pure
                (Frontend.Stmt.assign names value)))
  | expressionStatement expr =>
      simp only [Stmt.elaborate]
      exact
        PreservesHoisted.bind
          (Expr.elaborate_preserves_hoistedFunction_mem expr)
          (fun expr => PreservesHoisted.pure
            (Frontend.Stmt.exprStmt expr))
  | functionDefinition name params returns body =>
      simp only [Stmt.elaborate]
      exact
        PreservesHoisted.bind
          (resolveFunction_preserves_hoistedFunction_mem name)
          (fun generated =>
            PreservesHoisted.bind
              (FunctionDef.elaborate_preserves_hoistedFunction_mem
                params returns body)
              (fun fn => PreservesHoisted.pure
                (Frontend.Stmt.functionDef generated params returns fn.body)))
  | switch scrutinee cases defaultBody =>
      simp only [Stmt.elaborate]
      exact
        PreservesHoisted.bind
          (Expr.elaborate_preserves_hoistedFunction_mem scrutinee)
          (fun scrutinee =>
            PreservesHoisted.bind
              (Stmt.CaseList.elaborate_preserves_hoistedFunction_mem cases)
              (fun cases =>
                PreservesHoisted.bind
                  (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                    defaultBody true)
                  (fun defaultBody => PreservesHoisted.pure
                    (Frontend.Stmt.switch scrutinee cases defaultBody))))
  | forLoop pre condition post body =>
      cases hPre : Stmt.List.hasImmediateFunctionDefinition pre with
      | false =>
          simp only [Stmt.elaborate, hPre, Bool.false_eq_true, ↓reduceIte]
          exact
            PreservesHoisted.bind
              pushIdentifierScope_preserves_hoistedFunction_mem
              (fun _ =>
                PreservesHoisted.bind
                  (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                    pre false)
                  (fun pre =>
                    PreservesHoisted.bind
                      (Expr.elaborate_preserves_hoistedFunction_mem condition)
                      (fun condition =>
                        PreservesHoisted.bind
                          (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                            post true)
                          (fun post =>
                            PreservesHoisted.bind
                              (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                                body true)
                              (fun body =>
                                PreservesHoisted.bind
                                  popIdentifierScope_preserves_hoistedFunction_mem
                                  (fun _ => PreservesHoisted.pure
                                    (Frontend.Stmt.forLoop
                                      pre condition post body)))))))
      | true =>
          simp only [Stmt.elaborate, hPre, Bool.true_eq_false, ↓reduceIte]
          exact
            PreservesHoisted.bind
              pushIdentifierScope_preserves_hoistedFunction_mem
              (fun _ =>
                PreservesHoisted.bind
                  (Stmt.List.elaborateForInitBlockWithScope_preserves_hoistedFunction_mem
                    pre)
                  (fun pre =>
                    PreservesHoisted.bind
                      (Expr.elaborate_preserves_hoistedFunction_mem condition)
                      (fun condition =>
                        PreservesHoisted.bind
                          (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                            post true)
                          (fun post =>
                            PreservesHoisted.bind
                              (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                                body true)
                              (fun body =>
                                PreservesHoisted.bind
                                  popFunctionScope_preserves_hoistedFunction_mem
                                  (fun _ =>
                                    PreservesHoisted.bind
                                      popIdentifierScope_preserves_hoistedFunction_mem
                                      (fun _ => PreservesHoisted.pure
                                        (Frontend.Stmt.forLoop
                                          pre condition post body))))))))
  | ifThen condition body =>
      simp only [Stmt.elaborate]
      exact
        PreservesHoisted.bind
          (Expr.elaborate_preserves_hoistedFunction_mem condition)
          (fun condition =>
            PreservesHoisted.bind
              (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                body true)
              (fun body => PreservesHoisted.pure
                (Frontend.Stmt.ifThen condition body)))
  | «break» =>
      simp only [Stmt.elaborate]
      exact PreservesHoisted.pure Frontend.Stmt.break
  | «continue» =>
      simp only [Stmt.elaborate]
      exact PreservesHoisted.pure Frontend.Stmt.continue
  | «leave» =>
      simp only [Stmt.elaborate]
      exact PreservesHoisted.pure Frontend.Stmt.leave
  termination_by 20 * sizeOf stmt + 18
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborate_preserves_hoistedFunction_mem
    (stmts : List Raw.Stmt) :
    PreservesHoisted (Stmt.List.elaborate stmts) := by
  cases stmts with
  | nil =>
      simp [Stmt.List.elaborate]
      exact PreservesHoisted.pure []
  | cons stmt rest =>
      simp [Stmt.List.elaborate]
      exact
        PreservesHoisted.bind
          (Stmt.elaborate_preserves_hoistedFunction_mem stmt)
          (fun head =>
            PreservesHoisted.bind
              (Stmt.List.elaborate_preserves_hoistedFunction_mem rest)
              (fun tail => PreservesHoisted.pure (head :: tail)))
  termination_by 20 * sizeOf stmts + 10
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
    (stmts : List Raw.Stmt) (scope : List (Name × Name)) :
    PreservesHoisted (Stmt.List.hoistLocalFunctions stmts scope) := by
  cases stmts with
  | nil =>
      simp [Stmt.List.hoistLocalFunctions]
      exact PreservesHoisted.pure ()
  | cons stmt rest =>
      cases stmt with
      | functionDefinition name params returns body =>
          cases hLookup : lookupFunctionInScope name scope with
          | none =>
              simp [Stmt.List.hoistLocalFunctions, hLookup]
              exact PreservesHoisted.throw
                s!"internal frontend error: missing generated name for {name}"
          | some generated =>
              simp [Stmt.List.hoistLocalFunctions, hLookup]
              exact
                PreservesHoisted.bind
                  (FunctionDef.elaborate_preserves_hoistedFunction_mem
                    params returns body)
                  (fun fn =>
                    PreservesHoisted.bind
                      (hoistFunctionEntry_preserves_hoistedFunction_mem
                        generated fn)
                      (fun _ =>
                        Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
                          rest scope))
      | block stmts =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | variableDeclaration names value? =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | assignment names value =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | expressionStatement expr =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | switch scrutinee cases default =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | forLoop pre condition post body =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | ifThen condition body =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | «break» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | «continue» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
      | «leave» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
              rest scope
  termination_by 20 * sizeOf stmts + 12
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
    (stmts : List Raw.Stmt) (createsScope : Bool) :
    PreservesHoisted (Stmt.List.elaborateBlock stmts createsScope) := by
  cases createsScope with
  | false =>
      simp [Stmt.List.elaborateBlock]
      exact
        PreservesHoisted.bind
          (Stmt.List.localFunctionScope_preserves_hoistedFunction_mem stmts)
          (fun scope =>
            PreservesHoisted.bind
              (pushFunctionScope_preserves_hoistedFunction_mem scope)
              (fun _ =>
                PreservesHoisted.bind
                  (Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
                    stmts scope)
                  (fun _ =>
                    PreservesHoisted.bind
                      (Stmt.List.elaborate_preserves_hoistedFunction_mem stmts)
                      (fun result =>
                        PreservesHoisted.bind
                          popFunctionScope_preserves_hoistedFunction_mem
                          (fun _ => PreservesHoisted.pure result)))))
  | true =>
      simp [Stmt.List.elaborateBlock]
      exact
        PreservesHoisted.bind
          pushIdentifierScope_preserves_hoistedFunction_mem
          (fun _ =>
            PreservesHoisted.bind
              (Stmt.List.localFunctionScope_preserves_hoistedFunction_mem
                stmts)
              (fun scope =>
                PreservesHoisted.bind
                  (pushFunctionScope_preserves_hoistedFunction_mem scope)
                  (fun _ =>
                    PreservesHoisted.bind
                      (Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
                        stmts scope)
                      (fun _ =>
                        PreservesHoisted.bind
                          (Stmt.List.elaborate_preserves_hoistedFunction_mem
                            stmts)
                          (fun result =>
                            PreservesHoisted.bind
                              popFunctionScope_preserves_hoistedFunction_mem
                              (fun _ =>
                                PreservesHoisted.bind
                                  popIdentifierScope_preserves_hoistedFunction_mem
                                  (fun _ =>
                                    PreservesHoisted.pure result)))))))
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateForInitBlockWithScope_preserves_hoistedFunction_mem
    (stmts : List Raw.Stmt) :
    PreservesHoisted (Stmt.List.elaborateForInitBlockWithScope stmts) := by
  simp [Stmt.List.elaborateForInitBlockWithScope]
  exact
    PreservesHoisted.bind
      (Stmt.List.localFunctionScope_preserves_hoistedFunction_mem stmts)
      (fun scope =>
        PreservesHoisted.bind
          (pushFunctionScope_preserves_hoistedFunction_mem scope)
          (fun _ =>
            PreservesHoisted.bind
              (Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
                stmts scope)
              (fun _ =>
                Stmt.List.elaborate_preserves_hoistedFunction_mem stmts)))
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.CaseList.elaborate_preserves_hoistedFunction_mem
    (cases : List (Raw.SwitchCaseValue × List Raw.Stmt)) :
    PreservesHoisted (Stmt.CaseList.elaborate cases) := by
  cases cases with
  | nil =>
      simp [Stmt.CaseList.elaborate]
      exact PreservesHoisted.pure []
  | cons head rest =>
      rcases head with ⟨value, body⟩
      cases value with
      | literal literal =>
          cases literal with
          | number value =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesHoisted.bind
                  (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                    body true)
                  (fun body =>
                    PreservesHoisted.bind
                      (Stmt.CaseList.elaborate_preserves_hoistedFunction_mem
                        rest)
                      (fun rest => PreservesHoisted.pure
                        ((Frontend.SwitchCaseValue.word value, body) ::
                          rest)))
          | bool value =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesHoisted.bind
                  (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                    body true)
                  (fun body =>
                    PreservesHoisted.bind
                      (Stmt.CaseList.elaborate_preserves_hoistedFunction_mem
                        rest)
                      (fun rest => PreservesHoisted.pure
                        ((Frontend.SwitchCaseValue.boolLit value, body) ::
                          rest)))
          | stringLit value =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesHoisted.bind
                  (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                    body true)
                  (fun body =>
                    PreservesHoisted.bind
                      (Stmt.CaseList.elaborate_preserves_hoistedFunction_mem
                        rest)
                      (fun rest => PreservesHoisted.pure
                        ((Frontend.SwitchCaseValue.stringLit value, body) ::
                          rest)))
          | bytesLit bytes =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesHoisted.bind
                  (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                    body true)
                  (fun body =>
                    PreservesHoisted.bind
                      (Stmt.CaseList.elaborate_preserves_hoistedFunction_mem
                        rest)
                      (fun rest => PreservesHoisted.pure
                        ((Frontend.SwitchCaseValue.bytesLit bytes, body) ::
                          rest)))
  termination_by 20 * sizeOf cases + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem FunctionDef.elaborate_preserves_hoistedFunction_mem
    (params returns : List Name) (body : List Raw.Stmt) :
    PreservesHoisted (FunctionDef.elaborate params returns body) := by
  simp [FunctionDef.elaborate]
  exact
    PreservesHoisted.bind
      pushIdentifierScope_preserves_hoistedFunction_mem
      (fun _ =>
        PreservesHoisted.bind
          (declareIdentifiers_preserves_hoistedFunction_mem
            (params ++ returns) "function parameter/result")
          (fun _ =>
            PreservesHoisted.bind
              (Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                body true)
              (fun body =>
                PreservesHoisted.bind
                  popIdentifierScope_preserves_hoistedFunction_mem
                  (fun _ => PreservesHoisted.pure
                    ({ params, returns, body } : Frontend.FunctionDef)))))
  termination_by 20 * sizeOf body + 16
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end

namespace Stmt.List

theorem localFunctionScope_lookup_functionDefinition
    {stmts : List Raw.Stmt} {state scopeState : State}
    {scope : List (Name × Name)} {name generated : Name}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hLookup : lookupFunctionInScope name scope = some generated) :
    ∃ params returns body,
      .functionDefinition name params returns body ∈ stmts := by
  induction stmts generalizing state scopeState scope with
  | nil =>
      simp [Stmt.List.localFunctionScope] at hScope
      cases hScope
      simp [lookupFunctionInScope] at hLookup
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition head params returns body =>
          unfold Stmt.List.localFunctionScope at hScope
          simp [StateT.run_bind] at hScope
          cases hTail : (Stmt.List.localFunctionScope rest).run state with
          | error err =>
              simp [hTail] at hScope
          | ok tailResult =>
              rcases tailResult with ⟨tailScope, tailState⟩
              simp [hTail] at hScope
              cases hDuplicate :
                  (tailScope.any fun entry => entry.fst == head) with
              | true =>
                  simp [hDuplicate] at hScope
                  unfold EvmCompiler.Solidity.RawAst.Elab.throw at hScope
                  cases hScope
              | false =>
                  simp [hDuplicate] at hScope
                  cases hDeclare :
                      (declareIdentifiers [head] "function").run tailState with
                  | error err =>
                      simp [hDeclare] at hScope
                  | ok declareResult =>
                      rcases declareResult with ⟨_, declaredState⟩
                      simp [hDeclare] at hScope
                      cases hFresh :
                          (freshGeneratedFunctionName head).run declaredState with
                      | error err =>
                          simp [hFresh] at hScope
                      | ok freshResult =>
                          rcases freshResult with ⟨headGenerated, freshState⟩
                          simp [hFresh] at hScope
                          rcases hScope with ⟨hScopeEq, _hStateEq⟩
                          subst scope
                          by_cases hName : head = name
                          · subst name
                            simp [lookupFunctionInScope] at hLookup
                            exact ⟨params, returns, body, by simp⟩
                          · simp [lookupFunctionInScope, hName] at hLookup
                            rcases ih hTail hLookup with
                              ⟨tailParams, tailReturns, tailBody, hMem⟩
                            exact
                              ⟨tailParams, tailReturns, tailBody,
                                List.mem_cons_of_mem _ hMem⟩
      | block stmts =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | variableDeclaration names value? =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | assignment names value =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | expressionStatement expr =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | switch scrutinee cases default =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | forLoop pre condition post body =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | ifThen condition body =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | «break» =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | «continue» =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩
      | «leave» =>
          unfold Stmt.List.localFunctionScope at hScope
          rcases ih hScope hLookup with ⟨params, returns, body, hMem⟩
          exact ⟨params, returns, body, List.mem_cons_of_mem _ hMem⟩

theorem hoistLocalFunctions_functionDefinition_entry
    {stmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state finalState : State}
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    (hMem :
      .functionDefinition name params returns body ∈ stmts)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hHoist :
      (Stmt.List.hoistLocalFunctions stmts scope).run state =
        .ok ((), finalState)) :
    ∃ fn, (generated, fn) ∈ finalState.hoistedFunctions := by
  induction stmts generalizing state finalState with
  | nil =>
      simp at hMem
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition head headParams headReturns headBody =>
          simp at hMem
          rcases hMem with hHead | hTail
          · rcases hHead with
              ⟨hName, hParams, hReturns, hBody⟩
            subst head
            subst headParams
            subst headReturns
            subst headBody
            unfold Stmt.List.hoistLocalFunctions at hHoist
            simp [hLookup, StateT.run_bind] at hHoist
            cases hFn :
                (FunctionDef.elaborate params returns body).run state with
            | error err =>
                simp [hFn] at hHoist
            | ok fnResult =>
                rcases fnResult with ⟨fn, fnState⟩
                simp [hFn, StateT.run_modify] at hHoist
                refine ⟨fn, ?_⟩
                exact
                  Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
                    rest scope hHoist
                    (by simp)
          · unfold Stmt.List.hoistLocalFunctions at hHoist
            simp [StateT.run_bind] at hHoist
            cases hHeadLookup : lookupFunctionInScope head scope with
            | none =>
                simp [hHeadLookup] at hHoist
                unfold EvmCompiler.Solidity.RawAst.Elab.throw at hHoist
                cases hHoist
            | some headGenerated =>
                simp [hHeadLookup] at hHoist
                cases hFn :
                    (FunctionDef.elaborate
                      headParams headReturns headBody).run state with
                | error err =>
                    rw [hFn] at hHoist
                    cases hHoist
                | ok fnResult =>
                    rcases fnResult with ⟨fn, fnState⟩
                    simp [hFn, StateT.run_modify] at hHoist
                    exact ih hTail hHoist
      | block stmts =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | variableDeclaration names value? =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | assignment names value =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | expressionStatement expr =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | switch scrutinee cases default =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | forLoop pre condition post body =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | ifThen condition body =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | «break» =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | «continue» =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist
      | «leave» =>
          unfold Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist

theorem localFunctionScope_hoistLocalFunctions_lookup_entry
    {stmts : List Raw.Stmt} {state scopeState finalState : State}
    {scope : List (Name × Name)} {name generated : Name}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hHoist :
      (Stmt.List.hoistLocalFunctions stmts scope).run scopeState =
        .ok ((), finalState))
    (hLookup : lookupFunctionInScope name scope = some generated) :
    ∃ params returns body fn,
      .functionDefinition name params returns body ∈ stmts ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases localFunctionScope_lookup_functionDefinition hScope hLookup with
    ⟨params, returns, body, hMem⟩
  rcases hoistLocalFunctions_functionDefinition_entry
      hMem hLookup hHoist with ⟨fn, hEntry⟩
  exact ⟨params, returns, body, fn, hMem, hEntry⟩

theorem localFunctionScope_hoistLocalFunctions_elaborate_user_call_entry
    {stmts : List Raw.Stmt}
    {scopeInit scopeState hoistState callState argState : State}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {name generated : Name}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hScope :
      (Stmt.List.localFunctionScope stmts).run scopeInit =
        .ok (scope, scopeState))
    (hHoist :
      (Stmt.List.hoistLocalFunctions stmts scope).run scopeState =
        .ok ((), hoistState))
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hArgs :
      (Expr.List.elaborate args).run callState = .ok (args', argState))
    (hArgScopes : argState.functionScopes = scope :: outer)
    (hClass : CallClass.classifyCall name = .user) :
    (Expr.elaborate (.functionCall name args)).run callState =
        .ok (.call .user generated args', argState) ∧
      ∃ params returns body fn,
        .functionDefinition name params returns body ∈ stmts ∧
          (generated, fn) ∈ hoistState.hoistedFunctions := by
  have hResolve :
      resolveFunctionIn name argState.functionScopes = some generated := by
    rw [hArgScopes]
    exact resolveFunctionIn_of_scope_lookup hLookup
  constructor
  · exact
      Expr.elaborate_user_call_resolved
        hNotMemoryguard hNotClz hArgs hClass hResolve
  · exact
      localFunctionScope_hoistLocalFunctions_lookup_entry
        hScope hHoist hLookup

end Stmt.List

def collectTopFunctions : List Raw.Stmt → ElabM (List (Name × Name))
  | [] => pure []
  | stmt :: rest => do
      match stmt with
      | .functionDefinition name _ _ _ =>
          let tail ← collectTopFunctions rest
          if tail.any fun entry => entry.fst == name then
            throw s!"duplicate top-level Yul function {name}"
          declareIdentifiers [name] "function"
          modify fun state =>
            { state with usedFunctionNames := name :: state.usedFunctionNames }
          pure ((name, name) :: tail)
      | _ => collectTopFunctions rest

def elaborateCodeAction (stmts : List Raw.Stmt) :
    ElabM (List Frontend.Stmt) := do
  pushIdentifierScope
  let topScope ← collectTopFunctions stmts
  pushFunctionScope topScope
  let mut dispatcher : List Frontend.Stmt := []
  let mut topFunctions : List (Name × Frontend.FunctionDef) := []
  for stmt in stmts do
    match stmt with
    | .functionDefinition name params returns body =>
        let fn ← FunctionDef.elaborate params returns body
        topFunctions := (name, fn) :: topFunctions
    | _ =>
        let stmt ← Stmt.elaborate stmt
        dispatcher := stmt :: dispatcher
  popFunctionScope
  popIdentifierScope
  modify fun state =>
    { state with hoistedFunctions := state.hoistedFunctions ++ topFunctions }
  pure dispatcher.reverse

def elaborateCodeCore (stmts : List Raw.Stmt) :
    DecodeM (List Frontend.Stmt × State) :=
  (elaborateCodeAction stmts).run {}

def finalFunctions (state : State) : List (Name × Frontend.FunctionDef) :=
  let functions := state.hoistedFunctions.reverse
  match state.clzHelperName?, state.clzArgName?, state.clzReturnName? with
  | some helper, some arg, some ret =>
      functions ++ [(helper, clzHelperFunctionDef arg ret)]
  | none, none, none => functions
  | _, _, _ => functions

def ClzExpansionOk (functions : List (Name × Frontend.FunctionDef))
    (helper? arg? ret? : Option Name) : Prop :=
  match helper?, arg?, ret? with
  | some helper, some arg, some ret =>
      (helper, clzHelperFunctionDef arg ret) ∈ functions
  | _, _, _ => True

theorem finalFunctions_clzExpansionOk (state : State) :
    ClzExpansionOk (finalFunctions state) state.clzHelperName?
      state.clzArgName? state.clzReturnName? := by
  unfold finalFunctions ClzExpansionOk
  cases state.clzHelperName? <;>
    cases state.clzArgName? <;>
      cases state.clzReturnName? <;>
        simp

theorem finalFunctions_hoistedFunction_mem (state : State)
    {entry : Name × Frontend.FunctionDef}
    (hEntry : entry ∈ state.hoistedFunctions) :
    entry ∈ finalFunctions state := by
  unfold finalFunctions
  have hReverse : entry ∈ state.hoistedFunctions.reverse := by
    simpa using hEntry
  cases state.clzHelperName? <;>
    cases state.clzArgName? <;>
      cases state.clzReturnName? <;>
        simp [hReverse]

def elaborateCode (stmts : List Raw.Stmt) :
    DecodeM (List Frontend.Stmt × List (Name × Frontend.FunctionDef) ×
      Option Name × Option Name × Option Name) := do
  let (dispatcher, state) ← elaborateCodeCore stmts
  let functions := finalFunctions state
  pure (dispatcher, functions, state.clzHelperName?, state.clzArgName?,
    state.clzReturnName?)

theorem elaborateCode_parts
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper? arg? ret? : Option Name}
    (hElab :
      elaborateCode stmts = .ok (dispatcher, functions, helper?, arg?, ret?)) :
    ∃ state,
      elaborateCodeCore stmts = .ok (dispatcher, state) ∧
        functions = finalFunctions state ∧
          helper? = state.clzHelperName? ∧
            arg? = state.clzArgName? ∧
              ret? = state.clzReturnName? := by
  unfold elaborateCode at hElab
  cases hRun : elaborateCodeCore stmts with
  | error err =>
      simp [hRun] at hElab
  | ok result =>
      rcases result with ⟨dispatcher', state⟩
      simp [hRun] at hElab
      rcases hElab with ⟨hDispatcher, hFunctions, hHelper, hArg, hRet⟩
      refine
        ⟨state, ?_, hFunctions.symm, hHelper.symm, hArg.symm, hRet.symm⟩
      simp [hDispatcher]

theorem elaborateCode_clzExpansionOk
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper? arg? ret? : Option Name}
    (hElab :
      elaborateCode stmts = .ok (dispatcher, functions, helper?, arg?, ret?)) :
    ClzExpansionOk functions helper? arg? ret? := by
  rcases elaborateCode_parts hElab with
    ⟨state, _hCore, hFunctions, hHelper, hArg, hRet⟩
  rw [hFunctions, hHelper, hArg, hRet]
  exact finalFunctions_clzExpansionOk state

theorem elaborateCode_clzHelper_mem
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper arg ret : Name}
    (hElab :
      elaborateCode stmts = .ok
        (dispatcher, functions, some helper, some arg, some ret)) :
    (helper, clzHelperFunctionDef arg ret) ∈ functions := by
  exact elaborateCode_clzExpansionOk hElab

theorem elaborateCode_clzHelper_shape
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper arg ret : Name}
    (hElab :
      elaborateCode stmts = .ok
        (dispatcher, functions, some helper, some arg, some ret)) :
    ∃ fn,
      (helper, fn) ∈ functions ∧
        fn.params = [arg] ∧
          fn.returns = [ret] := by
  refine
    ⟨clzHelperFunctionDef arg ret,
      elaborateCode_clzHelper_mem hElab, ?_, ?_⟩
  · exact (clzHelperFunctionDef_shape arg ret).1
  · exact (clzHelperFunctionDef_shape arg ret).2

theorem elaborateCode_clzHelper_spec
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper arg ret : Name}
    (hElab :
      elaborateCode stmts = .ok
        (dispatcher, functions, some helper, some arg, some ret)) :
    ∃ fn,
      (helper, fn) ∈ functions ∧
        ClzHelperSpec fn arg ret := by
  exact
    ⟨clzHelperFunctionDef arg ret,
      elaborateCode_clzHelper_mem hElab,
      clzHelperFunctionDef_spec arg ret⟩

theorem elaborateCode_clzHelper_exec_ret_eq_run
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper arg ret : Name}
    (hElab :
      elaborateCode stmts = .ok
        (dispatcher, functions, some helper, some arg, some ret))
    (hNames : arg ≠ ret) :
    ∃ fn,
      (helper, fn) ∈ functions ∧
        ∀ value initialRet : Word,
          (ClzHelperExecution.execStmts? arg ret
              { arg := value, ret := initialRet }
              fn.body).map (fun state => state.ret) =
            some (ClzHelperModel.run value) := by
  rcases elaborateCode_clzHelper_spec hElab with ⟨fn, hMem, hSpec⟩
  exact
    ⟨fn, hMem, fun value initialRet =>
      ClzHelperExecution.exec_clzHelperSpec_ret_eq_run hSpec hNames value
        initialRet⟩

theorem elaborateCode_clzHelper_toYul?_some
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper arg ret : Name}
    (hElab :
      elaborateCode stmts = .ok
        (dispatcher, functions, some helper, some arg, some ret)) :
    ∃ body,
      (helper, clzHelperFunctionDef arg ret) ∈ functions ∧
        Frontend.FunctionDef.toYul? (clzHelperFunctionDef arg ret) =
          some (.Def [arg] [ret] body) := by
  rcases clzHelperFunctionDef_toYul?_some arg ret with ⟨body, hYul⟩
  exact ⟨body, elaborateCode_clzHelper_mem hElab, hYul⟩

theorem elaborateCode_hoistedFunction_mem
    {stmts : List Raw.Stmt}
    {dispatcher coreDispatcher : List Frontend.Stmt}
    {state : State}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper? arg? ret? : Option Name}
    {entry : Name × Frontend.FunctionDef}
    (hCore : elaborateCodeCore stmts = .ok (coreDispatcher, state))
    (hElab :
      elaborateCode stmts = .ok (dispatcher, functions, helper?, arg?, ret?))
    (hEntry : entry ∈ state.hoistedFunctions) :
    entry ∈ functions := by
  rcases elaborateCode_parts hElab with
    ⟨state', hCore', hFunctions, _hHelper, _hArg, _hRet⟩
  have hState : state' = state := by
    cases hCore.symm.trans hCore'
    rfl
  subst state'
  rw [hFunctions]
  exact finalFunctions_hoistedFunction_mem state hEntry

end Elab

namespace Raw

mutual
  def ObjectItem.elaborateFuel? (fuel : Nat) (item : ObjectItem)
      (evmVersion : Yul.SolcValidation.EvmVersion) :
      DecodeM (Sum Frontend.DataSection Frontend.Object) :=
    match fuel with
    | 0 => .error "raw object elaborator ran out of fuel"
    | fuel + 1 =>
        match item with
        | .data name? bytes => .ok (.inl { name? := name?, bytes := bytes })
        | .object child => .inr <$> Object.elaborateFuel? fuel child evmVersion

  def Object.elaborateItemsFuel? (fuel : Nat) (items : List ObjectItem)
      (evmVersion : Yul.SolcValidation.EvmVersion) :
      DecodeM
        (List Frontend.DataSection × List Frontend.Object ×
          List Frontend.ObjectItemRef) := do
    match fuel with
    | 0 => .error "raw object item elaborator ran out of fuel"
    | fuel + 1 =>
        let mut data : List Frontend.DataSection := []
        let mut objects : List Frontend.Object := []
        let mut refs : List Frontend.ObjectItemRef := []
        for item in items do
          match ← ObjectItem.elaborateFuel? fuel item evmVersion with
          | .inl sect =>
              refs := .data data.length :: refs
              data := sect :: data
          | .inr child =>
              refs := .object objects.length :: refs
              objects := child :: objects
        pure (data.reverse, objects.reverse, refs.reverse)

  def Object.elaborateFuel? (fuel : Nat) (obj : Object)
      (evmVersion : Yul.SolcValidation.EvmVersion) :
      DecodeM Frontend.Object := do
    match fuel with
    | 0 => .error "raw object elaborator ran out of fuel"
    | fuel + 1 =>
        let dispatcherAndFunctions ←
          match obj.code? with
          | none => pure ([], [], none, none, none)
          | some code => Elab.elaborateCode code
        let (dispatcher, functions, _clzName?, _clzArg?, _clzRet?) :=
          dispatcherAndFunctions
        let (data, objects, items) ←
          Object.elaborateItemsFuel? fuel obj.subObjects evmVersion
        pure
          { name := obj.name
            dispatcher := dispatcher
            functions := functions
            data := data
            objects := objects
            items := items
            memoryContract := MemoryContract.unrestricted
            evmVersion := evmVersion }
end

def Object.elaborate? (obj : Object)
    (evmVersion : Yul.SolcValidation.EvmVersion) :
    DecodeM Frontend.Object :=
  Object.elaborateFuel? maxDecodeFuel obj evmVersion

theorem Object.elaborateFuel?_parts
    {fuel : Nat} {obj : Object}
    {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab : Object.elaborateFuel? fuel obj evmVersion = .ok frontend) :
    ∃ (itemFuel : Nat) (dispatcher : List Frontend.Stmt)
        (functions : List (Name × Frontend.FunctionDef))
        (helper? arg? ret? : Option Name)
        (data : List Frontend.DataSection)
        (objects : List Frontend.Object)
        (items : List Frontend.ObjectItemRef),
      fuel = itemFuel + 1 ∧
        (match obj.code? with
        | none =>
            dispatcher = [] ∧
              functions = [] ∧
                helper? = none ∧
                  arg? = none ∧
                    ret? = none
        | some code =>
            Elab.elaborateCode code =
              .ok (dispatcher, functions, helper?, arg?, ret?)) ∧
          Object.elaborateItemsFuel? itemFuel obj.subObjects evmVersion =
            .ok (data, objects, items) ∧
            frontend =
              { name := obj.name
                dispatcher := dispatcher
                functions := functions
                data := data
                objects := objects
                items := items
                memoryContract := MemoryContract.unrestricted
                evmVersion := evmVersion } := by
  cases fuel with
  | zero =>
      simp [Object.elaborateFuel?] at hElab
  | succ itemFuel =>
      unfold Object.elaborateFuel? at hElab
      cases hCode : obj.code? with
      | none =>
          cases hItems :
              Object.elaborateItemsFuel? itemFuel obj.subObjects evmVersion with
          | error err =>
              simp [hCode, hItems] at hElab
          | ok result =>
              rcases result with ⟨data, objects, items⟩
              simp [hCode, hItems] at hElab
              subst frontend
              refine
                ⟨itemFuel, [], [], none, none, none, data, objects, items,
                  rfl, ?_, ?_, rfl⟩
              · simp
              · exact hItems
      | some code =>
          cases hCodeElab : Elab.elaborateCode code with
          | error err =>
              simp [hCode, hCodeElab] at hElab
          | ok codeResult =>
              rcases codeResult with ⟨dispatcher, functions, helper?, arg?, ret?⟩
              cases hItems :
                  Object.elaborateItemsFuel? itemFuel obj.subObjects evmVersion with
              | error err =>
                  simp [hCode, hCodeElab, hItems] at hElab
              | ok result =>
                  rcases result with ⟨data, objects, items⟩
                  simp [hCode, hCodeElab, hItems] at hElab
                  subst frontend
                  refine
                    ⟨itemFuel, dispatcher, functions, helper?, arg?, ret?,
                      data, objects, items, rfl, ?_, ?_, rfl⟩
                  · exact hCodeElab
                  · exact hItems

theorem Object.elaborate?_parts
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab : Object.elaborate? obj evmVersion = .ok frontend) :
    ∃ (itemFuel : Nat) (dispatcher : List Frontend.Stmt)
        (functions : List (Name × Frontend.FunctionDef))
        (helper? arg? ret? : Option Name)
        (data : List Frontend.DataSection)
        (objects : List Frontend.Object)
        (items : List Frontend.ObjectItemRef),
      maxDecodeFuel = itemFuel + 1 ∧
        (match obj.code? with
        | none =>
            dispatcher = [] ∧
              functions = [] ∧
                helper? = none ∧
                  arg? = none ∧
                    ret? = none
        | some code =>
            Elab.elaborateCode code =
              .ok (dispatcher, functions, helper?, arg?, ret?)) ∧
          Object.elaborateItemsFuel? itemFuel obj.subObjects evmVersion =
            .ok (data, objects, items) ∧
            frontend =
              { name := obj.name
                dispatcher := dispatcher
                functions := functions
                data := data
                objects := objects
                items := items
                memoryContract := MemoryContract.unrestricted
                evmVersion := evmVersion } := by
  exact Object.elaborateFuel?_parts hElab

def Object.ClzExpansionOk (raw : Object)
    (frontend : Frontend.Object) : Prop :=
  match raw.code? with
  | none => True
  | some code =>
      ∃ (helper? arg? ret? : Option Name),
        Elab.elaborateCode code =
          .ok (frontend.dispatcher, frontend.functions,
            helper?, arg?, ret?) ∧
          Elab.ClzExpansionOk frontend.functions helper? arg? ret?

def Object.ClzHelperSpecOk (raw : Object)
    (frontend : Frontend.Object) : Prop :=
  match raw.code? with
  | none => True
  | some code =>
      ∃ (helper? arg? ret? : Option Name),
        Elab.elaborateCode code =
          .ok (frontend.dispatcher, frontend.functions,
            helper?, arg?, ret?) ∧
          match helper?, arg?, ret? with
          | some helper, some arg, some ret =>
              ∃ fn,
                (helper, fn) ∈ frontend.functions ∧
                  Elab.ClzHelperSpec fn arg ret
          | _, _, _ => True

def Object.clzHelperNamesDistinct? (raw : Object) : Bool :=
  match raw.code? with
  | none => true
  | some code =>
      match Elab.elaborateCode code with
      | .ok (_dispatcher, _functions, some _helper, some arg, some ret) =>
          arg != ret
      | .ok _ => true
      | .error _ => false

theorem Object.clzHelperNamesDistinct?_arg_ne
    {raw : Object} {code : List Raw.Stmt}
    {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper arg ret : Name}
    (hCode : raw.code? = some code)
    (hElab :
      Elab.elaborateCode code =
        .ok (dispatcher, functions, some helper, some arg, some ret))
    (hDistinct : Object.clzHelperNamesDistinct? raw = true) :
    arg ≠ ret := by
  unfold Object.clzHelperNamesDistinct? at hDistinct
  simp [hCode, hElab] at hDistinct
  simpa using hDistinct

def Object.HoistedFunctionsRetained (raw : Object)
    (frontend : Frontend.Object) : Prop :=
  match raw.code? with
  | none => True
  | some code =>
      ∃ (coreDispatcher : List Frontend.Stmt) (state : Elab.State)
          (helper? arg? ret? : Option Name),
        Elab.elaborateCodeCore code = .ok (coreDispatcher, state) ∧
          Elab.elaborateCode code =
            .ok (frontend.dispatcher, frontend.functions,
              helper?, arg?, ret?) ∧
            ∀ entry, entry ∈ state.hoistedFunctions →
              entry ∈ frontend.functions

theorem Object.elaborate?_clzExpansionOk
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab : Object.elaborate? obj evmVersion = .ok frontend) :
    Object.ClzExpansionOk obj frontend := by
  rcases Object.elaborate?_parts hElab with
    ⟨itemFuel, dispatcher, functions, helper?, arg?, ret?, data, objects,
      items, _hFuel, hCode, _hItems, hFrontend⟩
  subst frontend
  cases hRawCode : obj.code? with
  | none =>
      simp [Object.ClzExpansionOk, hRawCode]
  | some code =>
      have hCodeElab :
          Elab.elaborateCode code =
            .ok (dispatcher, functions, helper?, arg?, ret?) := by
        simpa [hRawCode] using hCode
      unfold Object.ClzExpansionOk
      rw [hRawCode]
      exact
        ⟨helper?, arg?, ret?, hCodeElab,
          Elab.elaborateCode_clzExpansionOk hCodeElab⟩

theorem Object.elaborate?_clzHelperSpecOk
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab : Object.elaborate? obj evmVersion = .ok frontend) :
    Object.ClzHelperSpecOk obj frontend := by
  rcases Object.elaborate?_parts hElab with
    ⟨itemFuel, dispatcher, functions, helper?, arg?, ret?, data, objects,
      items, _hFuel, hCode, _hItems, hFrontend⟩
  subst frontend
  cases hRawCode : obj.code? with
  | none =>
      simp [Object.ClzHelperSpecOk, hRawCode]
  | some code =>
      have hCodeElab :
          Elab.elaborateCode code =
            .ok (dispatcher, functions, helper?, arg?, ret?) := by
        simpa [hRawCode] using hCode
      unfold Object.ClzHelperSpecOk
      rw [hRawCode]
      refine ⟨helper?, arg?, ret?, hCodeElab, ?_⟩
      cases helper? <;> cases arg? <;> cases ret? <;> simp
      exact Elab.elaborateCode_clzHelper_spec hCodeElab

theorem Object.elaborate?_hoistedFunctionsRetained
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab : Object.elaborate? obj evmVersion = .ok frontend) :
    Object.HoistedFunctionsRetained obj frontend := by
  rcases Object.elaborate?_parts hElab with
    ⟨itemFuel, dispatcher, functions, helper?, arg?, ret?, data, objects,
      items, _hFuel, hCode, _hItems, hFrontend⟩
  subst frontend
  cases hRawCode : obj.code? with
  | none =>
      simp [Object.HoistedFunctionsRetained, hRawCode]
  | some code =>
      have hCodeElab :
          Elab.elaborateCode code =
            .ok (dispatcher, functions, helper?, arg?, ret?) := by
        simpa [hRawCode] using hCode
      rcases Elab.elaborateCode_parts hCodeElab with
        ⟨state, hCore, _hFunctions, _hHelper, _hArg, _hRet⟩
      unfold Object.HoistedFunctionsRetained
      rw [hRawCode]
      refine ⟨dispatcher, state, helper?, arg?, ret?, hCore, hCodeElab, ?_⟩
      intro entry hEntry
      exact Elab.elaborateCode_hoistedFunction_mem hCore hCodeElab hEntry

namespace ObjectItem

def refShapeAux : Nat → Nat → List ObjectItem → List Frontend.ObjectItemRef
  | _, _, [] => []
  | dataIndex, objectIndex, .data _ _ :: rest =>
      .data dataIndex :: refShapeAux (dataIndex + 1) objectIndex rest
  | dataIndex, objectIndex, .object _ :: rest =>
      .object objectIndex :: refShapeAux dataIndex (objectIndex + 1) rest

def refShape (items : List ObjectItem) : List Frontend.ObjectItemRef :=
  refShapeAux 0 0 items

end ObjectItem

def Object.itemRefsPreserveOrderFuel? :
    Nat → Object → Frontend.Object → Bool
  | 0, _, _ => false
  | fuel + 1, raw, frontend =>
      let rec checkChildren :
          List ObjectItem → List Frontend.Object → Bool
        | [], [] => true
        | [], _ :: _ => false
        | .data _ _ :: rest, fronts => checkChildren rest fronts
        | .object _ :: _, [] => false
        | .object rawChild :: rest, frontChild :: fronts =>
            Object.itemRefsPreserveOrderFuel? fuel rawChild frontChild &&
              checkChildren rest fronts
      (frontend.items == ObjectItem.refShape raw.subObjects) &&
        checkChildren raw.subObjects frontend.objects

def Object.itemRefsPreserveOrder? (raw : Object)
    (frontend : Frontend.Object) : Bool :=
  Object.itemRefsPreserveOrderFuel? maxDecodeFuel raw frontend

def Object.FrontendValidated (raw : Object)
    (frontend : Frontend.Object) : Prop :=
  Object.itemRefsPreserveOrder? raw frontend = true ∧
    Object.clzHelperNamesDistinct? raw = true ∧
      Frontend.Object.noRawClzCall? frontend = true ∧
      Frontend.Object.functionDefStubsRetained? frontend = true ∧
        Frontend.Object.userCallsResolved? frontend = true ∧
          Object.ClzExpansionOk raw frontend ∧
            Object.ClzHelperSpecOk raw frontend ∧
              Object.HoistedFunctionsRetained raw frontend

def Object.elaboratePreservingOrder? (obj : Object)
    (evmVersion : Yul.SolcValidation.EvmVersion) :
    DecodeM Frontend.Object := do
  let frontend ← obj.elaborate? evmVersion
  if Object.itemRefsPreserveOrder? obj frontend then
    if Object.clzHelperNamesDistinct? obj then
      if Frontend.Object.noRawClzCall? frontend then
        if Frontend.Object.functionDefStubsRetained? frontend then
          if Frontend.Object.userCallsResolved? frontend then
            pure frontend
          else
            .error "unresolved Yul user function call"
        else
          .error "hoisted function stub mismatch"
      else
        .error "raw clz call was not normalized"
    else
      .error "clz helper argument/result name collision"
  else
    .error "raw object/data item order mismatch"

theorem Object.elaboratePreservingOrder?_parts
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend) :
    Object.elaborate? obj evmVersion = .ok frontend ∧
      Object.itemRefsPreserveOrder? obj frontend = true := by
  unfold Object.elaboratePreservingOrder? at hElab
  cases hObject : Object.elaborate? obj evmVersion with
  | error err =>
      simp [hObject] at hElab
  | ok object =>
      cases hOrder : Object.itemRefsPreserveOrder? obj object with
      | false =>
          simp [hObject, hOrder] at hElab
      | true =>
          cases hNames : Object.clzHelperNamesDistinct? obj with
          | false =>
              simp [hObject, hOrder, hNames] at hElab
          | true =>
              cases hNoRawClz :
                  Frontend.Object.noRawClzCall? object with
              | false =>
                  simp [hObject, hOrder, hNames, hNoRawClz] at hElab
              | true =>
                  cases hStubs :
                      Frontend.Object.functionDefStubsRetained? object with
                  | false =>
                      simp [hObject, hOrder, hNames, hNoRawClz, hStubs]
                        at hElab
                  | true =>
                      cases hResolved :
                          Frontend.Object.userCallsResolved? object with
                      | false =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved] at hElab
                      | true =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved, pure, Except.pure] at hElab
                          subst object
                          simp [hObject, hOrder]

theorem Object.elaboratePreservingOrder?_clzHelperNamesDistinct
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend) :
    Object.clzHelperNamesDistinct? obj = true := by
  unfold Object.elaboratePreservingOrder? at hElab
  cases hObject : Object.elaborate? obj evmVersion with
  | error err =>
      simp [hObject] at hElab
  | ok object =>
      cases hOrder : Object.itemRefsPreserveOrder? obj object with
      | false =>
          simp [hObject, hOrder] at hElab
      | true =>
          cases hNames : Object.clzHelperNamesDistinct? obj with
          | false =>
              simp [hObject, hOrder, hNames] at hElab
          | true =>
              rfl

theorem Object.elaboratePreservingOrder?_noRawClzCall
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend) :
    Frontend.Object.noRawClzCall? frontend = true := by
  unfold Object.elaboratePreservingOrder? at hElab
  cases hObject : Object.elaborate? obj evmVersion with
  | error err =>
      simp [hObject] at hElab
  | ok object =>
      cases hOrder : Object.itemRefsPreserveOrder? obj object with
      | false =>
          simp [hObject, hOrder] at hElab
      | true =>
          cases hNames : Object.clzHelperNamesDistinct? obj with
          | false =>
              simp [hObject, hOrder, hNames] at hElab
          | true =>
              cases hNoRawClz : Frontend.Object.noRawClzCall? object with
              | false =>
                  simp [hObject, hOrder, hNames, hNoRawClz] at hElab
              | true =>
                  cases hStubs :
                      Frontend.Object.functionDefStubsRetained? object with
                  | false =>
                      simp [hObject, hOrder, hNames, hNoRawClz, hStubs]
                        at hElab
                  | true =>
                      cases hResolved :
                          Frontend.Object.userCallsResolved? object with
                      | false =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved] at hElab
                      | true =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved, pure, Except.pure] at hElab
                          subst frontend
                          exact hNoRawClz

theorem Object.elaboratePreservingOrder?_functionDefStubsRetained
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend) :
    Frontend.Object.functionDefStubsRetained? frontend = true := by
  unfold Object.elaboratePreservingOrder? at hElab
  cases hObject : Object.elaborate? obj evmVersion with
  | error err =>
      simp [hObject] at hElab
  | ok object =>
      cases hOrder : Object.itemRefsPreserveOrder? obj object with
      | false =>
          simp [hObject, hOrder] at hElab
      | true =>
          cases hNames : Object.clzHelperNamesDistinct? obj with
          | false =>
              simp [hObject, hOrder, hNames] at hElab
          | true =>
              cases hNoRawClz : Frontend.Object.noRawClzCall? object with
              | false =>
                  simp [hObject, hOrder, hNames, hNoRawClz] at hElab
              | true =>
                  cases hStubs :
                      Frontend.Object.functionDefStubsRetained? object with
                  | false =>
                      simp [hObject, hOrder, hNames, hNoRawClz, hStubs]
                        at hElab
                  | true =>
                      cases hResolved :
                          Frontend.Object.userCallsResolved? object with
                      | false =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved] at hElab
                      | true =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved, pure, Except.pure] at hElab
                          subst frontend
                          exact hStubs

theorem Object.elaboratePreservingOrder?_userCallsResolved
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend) :
    Frontend.Object.userCallsResolved? frontend = true := by
  unfold Object.elaboratePreservingOrder? at hElab
  cases hObject : Object.elaborate? obj evmVersion with
  | error err =>
      simp [hObject] at hElab
  | ok object =>
      cases hOrder : Object.itemRefsPreserveOrder? obj object with
      | false =>
          simp [hObject, hOrder] at hElab
      | true =>
          cases hNames : Object.clzHelperNamesDistinct? obj with
          | false =>
              simp [hObject, hOrder, hNames] at hElab
          | true =>
              cases hNoRawClz : Frontend.Object.noRawClzCall? object with
              | false =>
                  simp [hObject, hOrder, hNames, hNoRawClz] at hElab
              | true =>
                  cases hStubs :
                      Frontend.Object.functionDefStubsRetained? object with
                  | false =>
                      simp [hObject, hOrder, hNames, hNoRawClz, hStubs]
                        at hElab
                  | true =>
                      cases hResolved :
                          Frontend.Object.userCallsResolved? object with
                      | false =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved] at hElab
                      | true =>
                          simp [hObject, hOrder, hNames, hNoRawClz, hStubs,
                            hResolved, pure, Except.pure] at hElab
                          subst frontend
                          exact hResolved

theorem Object.elaboratePreservingOrder?_frontendValidated
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend) :
    Object.elaborate? obj evmVersion = .ok frontend ∧
      Object.FrontendValidated obj frontend := by
  rcases Object.elaboratePreservingOrder?_parts hElab with
    ⟨hObject, hOrder⟩
  exact
    ⟨hObject, hOrder,
      Object.elaboratePreservingOrder?_clzHelperNamesDistinct hElab,
      Object.elaboratePreservingOrder?_noRawClzCall hElab,
      Object.elaboratePreservingOrder?_functionDefStubsRetained hElab,
      Object.elaboratePreservingOrder?_userCallsResolved hElab,
      Object.elaborate?_clzExpansionOk hObject,
      Object.elaborate?_clzHelperSpecOk hObject,
      Object.elaborate?_hoistedFunctionsRetained hObject⟩

theorem Object.elaboratePreservingOrder?_clzHelper_exec_ret_eq_run
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {code : List Raw.Stmt}
    {helper arg ret : Name}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend)
    (hCode : obj.code? = some code)
    (hCodeElab :
      Elab.elaborateCode code =
        .ok (frontend.dispatcher, frontend.functions,
          some helper, some arg, some ret)) :
    ∃ fn,
      (helper, fn) ∈ frontend.functions ∧
        ∀ value initialRet : Word,
          (Elab.ClzHelperExecution.execStmts? arg ret
              { arg := value, ret := initialRet }
              fn.body).map (fun state => state.ret) =
            some (Elab.ClzHelperModel.run value) := by
  have hDistinctBool :
      Object.clzHelperNamesDistinct? obj = true :=
    Object.elaboratePreservingOrder?_clzHelperNamesDistinct hElab
  have hNames : arg ≠ ret :=
    Object.clzHelperNamesDistinct?_arg_ne hCode hCodeElab hDistinctBool
  exact Elab.elaborateCode_clzHelper_exec_ret_eq_run hCodeElab hNames

theorem Object.elaboratePreservingOrder?_clzHelperCall_eq_clzModel
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {code : List Raw.Stmt}
    {helper arg ret : Name} {env : Elab.ClzCallReplacement.Env}
    {argExpr : Frontend.Expr} {value initialRet : Word}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend)
    (hCode : obj.code? = some code)
    (hCodeElab :
      Elab.elaborateCode code =
        .ok (frontend.dispatcher, frontend.functions,
          some helper, some arg, some ret))
    (hArg :
      Elab.ClzCallReplacement.evalPureExpr? env argExpr = some value) :
    ∃ fn,
      (helper, fn) ∈ frontend.functions ∧
        Elab.ClzCallReplacement.evalHelperCallExpr?
            helper arg ret fn env (.call .user helper [argExpr]) initialRet =
          some (Elab.ClzCallReplacement.clzModel value) := by
  rcases Object.elaboratePreservingOrder?_clzHelper_exec_ret_eq_run
      hElab hCode hCodeElab with
    ⟨fn, hMem, hExec⟩
  refine ⟨fn, hMem, ?_⟩
  simp [Elab.ClzCallReplacement.evalHelperCallExpr?,
    Elab.ClzCallReplacement.evalGeneratedHelperCall?,
    Elab.ClzCallReplacement.clzModel, hArg, hExec]

theorem Object.elaboratePreservingOrder?_clzHelperCall_eq_reference
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {code : List Raw.Stmt}
    {helper arg ret : Name} {env : Elab.ClzCallReplacement.Env}
    {argExpr : Frontend.Expr} {value initialRet : Word}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend)
    (hCode : obj.code? = some code)
    (hCodeElab :
      Elab.elaborateCode code =
        .ok (frontend.dispatcher, frontend.functions,
          some helper, some arg, some ret))
    (hArg :
      Elab.ClzCallReplacement.evalPureExpr? env argExpr = some value) :
    ∃ fn,
      (helper, fn) ∈ frontend.functions ∧
        Elab.ClzCallReplacement.evalHelperCallExpr?
            helper arg ret fn env (.call .user helper [argExpr]) initialRet =
          some (Elab.ClzHelperModel.reference value) := by
  rcases Object.elaboratePreservingOrder?_clzHelperCall_eq_clzModel
      hElab hCode hCodeElab hArg with
    ⟨fn, hMem, hEval⟩
  refine ⟨fn, hMem, ?_⟩
  simpa [Elab.ClzCallReplacement.clzModel_eq_reference] using hEval

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

def decodeSelectedLinkerSymbolsJson (json : Lean.Json)
    (selection : Selection) : DecodeM (List (Name × Word)) := do
  let (_, _, contractOutput) ← selectUniqueContract json selection
  metadataLinkerSymbols? contractOutput

def decodeAndElaborateSolcIrJson (json : Lean.Json)
    (selection : Selection) : DecodeM Frontend.Program := do
  let selected ← decodeSelectedIr json selection
  let object ← selected.root.elaboratePreservingOrder? selected.evmVersion
  pure { source := selected.source, contract := selected.contract, object := object }

theorem decodeAndElaborateSolcIrJson_parts
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ (selected : SelectedIr) (object : Frontend.Object),
      decodeSelectedIr json selection = .ok selected ∧
        selected.root.elaborate? selected.evmVersion = .ok object ∧
          program =
            { source := selected.source
              contract := selected.contract
              object := object } := by
  unfold decodeAndElaborateSolcIrJson at hDecode
  cases hSelected : decodeSelectedIr json selection with
  | error err =>
      simp [hSelected] at hDecode
  | ok selected =>
      cases hObject :
          selected.root.elaboratePreservingOrder? selected.evmVersion with
      | error err =>
          simp [hSelected, hObject] at hDecode
      | ok object =>
          have hRawObject :
              selected.root.elaborate? selected.evmVersion = .ok object :=
            (Raw.Object.elaboratePreservingOrder?_parts hObject).1
          simp [hSelected, hObject] at hDecode
          subst program
          refine ⟨selected, object, ?_, ?_, rfl⟩
          · simp
          · exact hRawObject

theorem decodeAndElaborateSolcIrJson_itemRefsPreserveOrder
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ (selected : SelectedIr) (object : Frontend.Object),
      decodeSelectedIr json selection = .ok selected ∧
        selected.root.elaborate? selected.evmVersion = .ok object ∧
          Raw.Object.itemRefsPreserveOrder? selected.root object = true ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } := by
  unfold decodeAndElaborateSolcIrJson at hDecode
  cases hSelected : decodeSelectedIr json selection with
  | error err =>
      simp [hSelected] at hDecode
  | ok selected =>
      cases hObject :
          selected.root.elaboratePreservingOrder? selected.evmVersion with
      | error err =>
          simp [hSelected, hObject] at hDecode
      | ok object =>
          have hParts :=
            Raw.Object.elaboratePreservingOrder?_parts hObject
          simp [hSelected, hObject] at hDecode
          subst program
          refine ⟨selected, object, ?_, ?_, ?_, rfl⟩
          · simp [hSelected]
          · exact hParts.1
          · exact hParts.2

theorem decodeAndElaborateSolcIrJson_noRawClzCall
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ (selected : SelectedIr) (object : Frontend.Object),
      decodeSelectedIr json selection = .ok selected ∧
        selected.root.elaborate? selected.evmVersion = .ok object ∧
          Frontend.Object.noRawClzCall? object = true ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } := by
  unfold decodeAndElaborateSolcIrJson at hDecode
  cases hSelected : decodeSelectedIr json selection with
  | error err =>
      simp [hSelected] at hDecode
  | ok selected =>
      cases hObject :
          selected.root.elaboratePreservingOrder? selected.evmVersion with
      | error err =>
          simp [hSelected, hObject] at hDecode
      | ok object =>
          have hParts :=
            Raw.Object.elaboratePreservingOrder?_parts hObject
          have hNoRawClz :=
            Raw.Object.elaboratePreservingOrder?_noRawClzCall hObject
          simp [hSelected, hObject] at hDecode
          subst program
          refine ⟨selected, object, ?_, ?_, ?_, rfl⟩
          · simp [hSelected]
          · exact hParts.1
          · exact hNoRawClz

theorem decodeAndElaborateSolcIrJson_functionDefStubsRetained
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ (selected : SelectedIr) (object : Frontend.Object),
      decodeSelectedIr json selection = .ok selected ∧
        selected.root.elaborate? selected.evmVersion = .ok object ∧
          Frontend.Object.functionDefStubsRetained? object = true ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } := by
  unfold decodeAndElaborateSolcIrJson at hDecode
  cases hSelected : decodeSelectedIr json selection with
  | error err =>
      simp [hSelected] at hDecode
  | ok selected =>
      cases hObject :
          selected.root.elaboratePreservingOrder? selected.evmVersion with
      | error err =>
          simp [hSelected, hObject] at hDecode
      | ok object =>
          have hParts :=
            Raw.Object.elaboratePreservingOrder?_parts hObject
          have hStubs :=
            Raw.Object.elaboratePreservingOrder?_functionDefStubsRetained
              hObject
          simp [hSelected, hObject] at hDecode
          subst program
          refine ⟨selected, object, ?_, ?_, ?_, rfl⟩
          · simp [hSelected]
          · exact hParts.1
          · exact hStubs

theorem decodeAndElaborateSolcIrJson_userCallsResolved
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ (selected : SelectedIr) (object : Frontend.Object),
      decodeSelectedIr json selection = .ok selected ∧
        selected.root.elaborate? selected.evmVersion = .ok object ∧
          Frontend.Object.userCallsResolved? object = true ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } := by
  unfold decodeAndElaborateSolcIrJson at hDecode
  cases hSelected : decodeSelectedIr json selection with
  | error err =>
      simp [hSelected] at hDecode
  | ok selected =>
      cases hObject :
          selected.root.elaboratePreservingOrder? selected.evmVersion with
      | error err =>
          simp [hSelected, hObject] at hDecode
      | ok object =>
          have hParts :=
            Raw.Object.elaboratePreservingOrder?_parts hObject
          have hResolved :=
            Raw.Object.elaboratePreservingOrder?_userCallsResolved hObject
          simp [hSelected, hObject] at hDecode
          subst program
          refine ⟨selected, object, ?_, ?_, ?_, rfl⟩
          · simp [hSelected]
          · exact hParts.1
          · exact hResolved

theorem decodeAndElaborateSolcIrJson_clzExpansionOk
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ selected : SelectedIr,
      decodeSelectedIr json selection = .ok selected ∧
        Raw.Object.ClzExpansionOk selected.root program.object := by
  rcases decodeAndElaborateSolcIrJson_parts hDecode with
    ⟨selected, object, hSelected, hObject, hProgram⟩
  subst program
  exact
    ⟨selected, hSelected,
      Raw.Object.elaborate?_clzExpansionOk hObject⟩

theorem decodeAndElaborateSolcIrJson_clzHelperSpecOk
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ selected : SelectedIr,
      decodeSelectedIr json selection = .ok selected ∧
        Raw.Object.ClzHelperSpecOk selected.root program.object := by
  rcases decodeAndElaborateSolcIrJson_parts hDecode with
    ⟨selected, object, hSelected, hObject, hProgram⟩
  subst program
  exact
    ⟨selected, hSelected,
      Raw.Object.elaborate?_clzHelperSpecOk hObject⟩

theorem decodeAndElaborateSolcIrJson_hoistedFunctionsRetained
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ selected : SelectedIr,
      decodeSelectedIr json selection = .ok selected ∧
        Raw.Object.HoistedFunctionsRetained selected.root program.object := by
  rcases decodeAndElaborateSolcIrJson_parts hDecode with
    ⟨selected, object, hSelected, hObject, hProgram⟩
  subst program
  exact
    ⟨selected, hSelected,
      Raw.Object.elaborate?_hoistedFunctionsRetained hObject⟩

theorem decodeAndElaborateSolcIrJson_frontendValidated
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ (selected : SelectedIr) (object : Frontend.Object),
      decodeSelectedIr json selection = .ok selected ∧
        selected.root.elaborate? selected.evmVersion = .ok object ∧
          Raw.Object.FrontendValidated selected.root object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } := by
  unfold decodeAndElaborateSolcIrJson at hDecode
  cases hSelected : decodeSelectedIr json selection with
  | error err =>
      simp [hSelected] at hDecode
  | ok selected =>
      cases hObject :
          selected.root.elaboratePreservingOrder? selected.evmVersion with
      | error err =>
          simp [hSelected, hObject] at hDecode
      | ok object =>
          have hValidated :=
            Raw.Object.elaboratePreservingOrder?_frontendValidated hObject
          simp [hSelected, hObject] at hDecode
          subst program
          refine ⟨selected, object, ?_, ?_, ?_, rfl⟩
          · simp [hSelected]
          · exact hValidated.1
          · exact hValidated.2

theorem decodeAndElaborateSolcIrJson_objectParts
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ (selected : SelectedIr) (itemFuel : Nat)
        (dispatcher : List Frontend.Stmt)
        (functions : List (Name × Frontend.FunctionDef))
        (helper? arg? ret? : Option Name)
        (data : List Frontend.DataSection)
        (objects : List Frontend.Object)
        (items : List Frontend.ObjectItemRef),
      decodeSelectedIr json selection = .ok selected ∧
        maxDecodeFuel = itemFuel + 1 ∧
          (match selected.root.code? with
          | none =>
              dispatcher = [] ∧
                functions = [] ∧
                  helper? = none ∧
                    arg? = none ∧
                      ret? = none
          | some code =>
              Elab.elaborateCode code =
                .ok (dispatcher, functions, helper?, arg?, ret?)) ∧
            Raw.Object.elaborateItemsFuel? itemFuel selected.root.subObjects
              selected.evmVersion = .ok (data, objects, items) ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object :=
                    { name := selected.root.name
                      dispatcher := dispatcher
                      functions := functions
                      data := data
                      objects := objects
                      items := items
                      memoryContract := MemoryContract.unrestricted
                      evmVersion := selected.evmVersion } } := by
  rcases decodeAndElaborateSolcIrJson_parts hDecode with
    ⟨selected, object, hSelected, hObject, hProgram⟩
  rcases Raw.Object.elaborate?_parts hObject with
    ⟨itemFuel, dispatcher, functions, helper?, arg?, ret?, data, objects,
      items, hFuel, hCode, hItems, hFrontend⟩
  subst program
  subst object
  exact
    ⟨selected, itemFuel, dispatcher, functions, helper?, arg?, ret?,
      data, objects, items, hSelected, hFuel, hCode, hItems, rfl⟩

def decodeLinkerSymbolsJson (json : Lean.Json)
    (selection : Selection) : DecodeM (List (Name × Word)) :=
  decodeSelectedLinkerSymbolsJson json selection

def decodeLinkerSymbols? (rawJson : String)
    (selection : Selection) : Option (List (Name × Word)) :=
  match Lean.Json.parse rawJson with
  | .error _ => none
  | .ok json =>
      match decodeLinkerSymbolsJson json selection with
      | .ok symbols => some symbols
      | .error _ => none

def decodeAndElaborateSolcIr? (rawJson : String)
    (selection : Selection) : Option Frontend.Program :=
  match Lean.Json.parse rawJson with
  | .error _ => none
  | .ok json =>
      match decodeAndElaborateSolcIrJson json selection with
      | .ok program => some program
      | .error _ => none

theorem decodeAndElaborateSolcIr?_some
    {rawJson : String} {selection : Selection} {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ json,
      Lean.Json.parse rawJson = .ok json ∧
        decodeAndElaborateSolcIrJson json selection = .ok program := by
  unfold decodeAndElaborateSolcIr? at hDecode
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hDecode
  | ok json =>
      cases hElab : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hElab] at hDecode
      | ok decoded =>
          simp [hParse, hElab] at hDecode
          subst decoded
          refine ⟨json, ?_, ?_⟩
          · simp [hParse]
          · exact hElab

theorem decodeAndElaborateSolcIr?_parts
    {rawJson : String} {selection : Selection} {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_parts hJsonDecode with
    ⟨selected, object, hSelected, hObject, hProgram⟩
  exact ⟨json, selected, object, hParse, hSelected, hObject, hProgram⟩

theorem decodeAndElaborateSolcIr?_itemRefsPreserveOrder
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Raw.Object.itemRefsPreserveOrder? selected.root object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_itemRefsPreserveOrder hJsonDecode with
    ⟨selected, object, hSelected, hObject, hOrder, hProgram⟩
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hOrder, hProgram⟩

theorem decodeAndElaborateSolcIr?_noRawClzCall
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.noRawClzCall? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_noRawClzCall hJsonDecode with
    ⟨selected, object, hSelected, hObject, hNoRawClz, hProgram⟩
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hNoRawClz,
      hProgram⟩

theorem decodeAndElaborateSolcIr?_functionDefStubsRetained
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.functionDefStubsRetained? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_functionDefStubsRetained
      hJsonDecode with
    ⟨selected, object, hSelected, hObject, hStubs, hProgram⟩
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hStubs,
      hProgram⟩

theorem decodeAndElaborateSolcIr?_userCallsResolved
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.userCallsResolved? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_userCallsResolved hJsonDecode with
    ⟨selected, object, hSelected, hObject, hResolved, hProgram⟩
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hResolved,
      hProgram⟩

theorem decodeAndElaborateSolcIr?_clzExpansionOk
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.ClzExpansionOk selected.root program.object := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_clzExpansionOk hJsonDecode with
    ⟨selected, hSelected, hClz⟩
  exact ⟨json, selected, hParse, hSelected, hClz⟩

theorem decodeAndElaborateSolcIr?_clzHelperSpecOk
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.ClzHelperSpecOk selected.root program.object := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_clzHelperSpecOk hJsonDecode with
    ⟨selected, hSelected, hClzSpec⟩
  exact ⟨json, selected, hParse, hSelected, hClzSpec⟩

theorem decodeAndElaborateSolcIr?_hoistedFunctionsRetained
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.HoistedFunctionsRetained selected.root program.object := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_hoistedFunctionsRetained hJsonDecode with
    ⟨selected, hSelected, hHoisted⟩
  exact ⟨json, selected, hParse, hSelected, hHoisted⟩

theorem decodeAndElaborateSolcIr?_frontendValidated
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Raw.Object.FrontendValidated selected.root object ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_frontendValidated hJsonDecode with
    ⟨selected, object, hSelected, hObject, hValidated, hProgram⟩
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hValidated, hProgram⟩

theorem decodeAndElaborateSolcIr?_objectParts
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr) (itemFuel : Nat)
        (dispatcher : List Frontend.Stmt)
        (functions : List (Name × Frontend.FunctionDef))
        (helper? arg? ret? : Option Name)
        (data : List Frontend.DataSection)
        (objects : List Frontend.Object)
        (items : List Frontend.ObjectItemRef),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          maxDecodeFuel = itemFuel + 1 ∧
            (match selected.root.code? with
            | none =>
                dispatcher = [] ∧
                  functions = [] ∧
                    helper? = none ∧
                      arg? = none ∧
                        ret? = none
            | some code =>
                Elab.elaborateCode code =
                  .ok (dispatcher, functions, helper?, arg?, ret?)) ∧
              Raw.Object.elaborateItemsFuel? itemFuel selected.root.subObjects
                selected.evmVersion = .ok (data, objects, items) ∧
                program =
                  { source := selected.source
                    contract := selected.contract
                    object :=
                      { name := selected.root.name
                        dispatcher := dispatcher
                        functions := functions
                        data := data
                        objects := objects
                        items := items
                        memoryContract := MemoryContract.unrestricted
                        evmVersion := selected.evmVersion } } := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json, hParse, hJsonDecode⟩
  rcases decodeAndElaborateSolcIrJson_objectParts hJsonDecode with
    ⟨selected, itemFuel, dispatcher, functions, helper?, arg?, ret?, data,
      objects, items, hSelected, hFuel, hCode, hItems, hProgram⟩
  exact
    ⟨json, selected, itemFuel, dispatcher, functions, helper?, arg?, ret?,
      data, objects, items, hParse, hSelected, hFuel, hCode, hItems, hProgram⟩

end RawAst
end Solidity
end EvmCompiler
