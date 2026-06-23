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
      DecodeM (Option (SwitchCaseValue × List Stmt))
    | 0, _ => .error "raw switch-case decoder ran out of fuel"
    | fuel + 1, json => do
        let body ← decodeBlock fuel (← field json "body")
        let value ← field json "value"
        match value.getStr? with
        | .ok "default" => pure none
        | .ok other => .error s!"unsupported switch case marker: {other}"
        | .error _ =>
            let value ← decodeSwitchCaseValue value
            pure (some (value, body))

  def decodeCases : Nat → List Lean.Json →
      DecodeM (List (SwitchCaseValue × List Stmt) × List Stmt)
    | 0, _ => .error "raw switch cases decoder ran out of fuel"
    | _fuel + 1, [] => pure ([], [])
    | fuel + 1, value :: rest => do
        let head ← decodeCase fuel value
        let (cases, defaultBody) ← decodeCases fuel rest
        match head with
        | none => pure (cases, defaultBody)
        | some case => pure (case :: cases, defaultBody)

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

def declareIdentifiers (names : List Name) (description : String) :
    ElabM Unit := do
  let state ← get
  let state ←
    match state.identifierScopes with
    | [] =>
        let state := { state with identifierScopes := [[]] }
        set state
        pure state
    | _ => pure state
  let mut seen : List Name := []
  for name in names do
    if !bindingNameOk? name then
      throw s!"invalid Yul {description} name {name}"
    if seen.contains name then
      throw s!"duplicate Yul {description} name {name}"
    let state ← get
    if identifierVisibleIn name state.identifierScopes then
      throw s!"Yul {description} name {name} already taken in this scope"
    seen := name :: seen
  let state ← get
  match state.identifierScopes with
  | [] => set { state with identifierScopes := [seen.reverse] }
  | scope :: rest =>
      set { state with identifierScopes := (seen.reverse ++ scope) :: rest }

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

def clzHelperFunctionDef (argName returnName : Name) :
    Frontend.FunctionDef :=
  let prim (name : Name) (args : List Frontend.Expr) :=
    Frontend.Expr.call .primitive name args
  let value (name : Name) := Frontend.Expr.var name
  let word (value : Nat) :=
    Frontend.Expr.lit (EvmYul.UInt256.ofNat value)
  let nonzeroBody :=
    let steps : List (Nat × Nat) :=
      [(128, 128), (192, 64), (224, 32), (240, 16), (248, 8),
        (252, 4), (254, 2), (255, 1)]
    let init : List Frontend.Stmt :=
      [Frontend.Stmt.assign [returnName] (word 0)]
    steps.foldl
      (fun body step =>
        let checkShift := step.fst
        let addend := step.snd
        let stepBody : List Frontend.Stmt :=
          [Frontend.Stmt.assign [returnName]
            (prim "add" [value returnName, word addend])]
        let stepBody :=
          if addend == 1 then
            stepBody
          else
            stepBody ++
              [Frontend.Stmt.assign [argName]
                (prim "shl" [word addend, value argName])]
        body ++
          [Frontend.Stmt.ifThen
            (prim "iszero"
              [prim "shr" [word checkShift, value argName]])
            stepBody])
      init
  { params := [argName]
    returns := [returnName]
    body :=
      [Frontend.Stmt.assign [returnName] (word 256),
        Frontend.Stmt.ifThen (value argName) nonzeroBody] }

theorem clzHelperFunctionDef_shape (argName returnName : Name) :
    (clzHelperFunctionDef argName returnName).params = [argName] ∧
      (clzHelperFunctionDef argName returnName).returns = [returnName] := by
  simp [clzHelperFunctionDef]

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
        for name in names do
          requireIdentifierVisible name "assignment"
        let value ← Expr.elaborate value
        pure (.assign names value)
    | .expressionStatement expr => do
        let expr ← Expr.elaborate expr
        pure (.exprStmt expr)
    | .functionDefinition name params returns body => do
        let fn ← FunctionDef.elaborate params returns body
        pure (.functionDef name params returns fn.body)
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

def elaborateCode (stmts : List Raw.Stmt) :
    DecodeM (List Frontend.Stmt × List (Name × Frontend.FunctionDef) ×
      Option Name × Option Name × Option Name) := do
  let action : ElabM (List Frontend.Stmt) := do
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
      { state with hoistedFunctions := topFunctions.reverse ++ state.hoistedFunctions }
    pure dispatcher.reverse
  let (dispatcher, state) ← action.run {}
  let functions := state.hoistedFunctions.reverse
  let functions :=
    match state.clzHelperName?, state.clzArgName?, state.clzReturnName? with
    | some helper, some arg, some ret =>
        functions ++ [(helper, clzHelperFunctionDef arg ret)]
    | none, none, none => functions
    | _, _, _ => functions
  pure (dispatcher, functions, state.clzHelperName?, state.clzArgName?,
    state.clzReturnName?)

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

def decodeAndElaborateSolcIrJson (json : Lean.Json)
    (selection : Selection) : DecodeM Frontend.Program := do
  let selected ← decodeSelectedIr json selection
  let object ← selected.root.elaborate? selected.evmVersion
  pure { source := selected.source, contract := selected.contract, object := object }

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

end RawAst
end Solidity
end EvmCompiler
