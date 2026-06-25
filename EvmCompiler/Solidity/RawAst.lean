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

namespace Source

/-- Source-facing local function declaration relation for a raw Yul block.

This is intentionally independent of the elaborator state and generated names:
it only records that a raw block syntactically declares a local function with
the given source name, signature, and body.  Successful elaboration later
proves that such a source declaration is realized by a generated callable
frontend entry. -/
inductive LocalFunction :
    List Stmt → Name → List Name → List Name → List Stmt → Prop where
  | here {name params returns body rest} :
      LocalFunction
        (.functionDefinition name params returns body :: rest)
        name params returns body
  | tail {stmt rest name params returns body} :
      LocalFunction rest name params returns body →
        LocalFunction (stmt :: rest) name params returns body

namespace LocalFunction

theorem mem
    {stmts : List Stmt} {name : Name} {params returns : List Name}
    {body : List Stmt}
    (hLocal : LocalFunction stmts name params returns body) :
    .functionDefinition name params returns body ∈ stmts := by
  induction hLocal with
  | here =>
      simp
  | tail hLocal ih =>
      exact List.mem_cons_of_mem _ ih

end LocalFunction

/-- Source-facing absence of a local function declaration with the given name. -/
def NoLocalFunctionNamed (stmts : List Stmt) (name : Name) : Prop :=
  ∀ {params returns body},
    .functionDefinition name params returns body ∈ stmts → False

/-- Source-facing direct expression-statement call occurrence in a raw block.

Like `LocalFunction`, this relation stays independent of generated names and
elaborator state.  It records only the source spelling of a direct
`name(args)` statement in the current raw statement list. -/
inductive LocalCall :
    List Stmt → Name → List Expr → Prop where
  | here {name args rest} :
      LocalCall
        (.expressionStatement (.functionCall name args) :: rest)
        name args
  | tail {stmt rest name args} :
      LocalCall rest name args →
        LocalCall (stmt :: rest) name args

namespace LocalCall

theorem mem
    {stmts : List Stmt} {name : Name} {args : List Expr}
    (hCall : LocalCall stmts name args) :
    .expressionStatement (.functionCall name args) ∈ stmts := by
  induction hCall with
  | here =>
      simp
  | tail hCall ih =>
      exact List.mem_cons_of_mem _ ih

end LocalCall

namespace ExprCall

/-- Source-facing occurrence of an exact raw function-call expression.

This is the expression-level counterpart of `LocalCall`: it names the source
callee spelling and argument list independently of generated frontend names. -/
inductive Direct : Expr → Name → List Expr → Prop where
  | here {name args} :
      Direct (.functionCall name args) name args

/-- Recursive source-facing occurrence of a raw function-call expression. -/
inductive Occurs : Expr → Name → List Expr → Prop where
  | direct {expr name args} :
      Direct expr name args →
        Occurs expr name args
  | arg {callee callArgs arg name args} :
      arg ∈ callArgs →
        Occurs arg name args →
          Occurs (.functionCall callee callArgs) name args

/-- Recursive source-facing occurrence inside a raw expression list. -/
inductive ListOccurs : List Expr → Name → List Expr → Prop where
  | head {expr rest name args} :
      Occurs expr name args →
        ListOccurs (expr :: rest) name args
  | tail {expr rest name args} :
      ListOccurs rest name args →
        ListOccurs (expr :: rest) name args

end ExprCall

namespace StmtExprCall

/--
Source-facing raw call occurrence in a statement expression that is elaborated
under the statement's incoming function scope.

This deliberately excludes nested block bodies and `for` conditions, whose
active function scope can be extended by surrounding block/initializer
elaboration and needs a separate scope-handoff theorem.
-/
inductive IncomingScope : Stmt → Name → List Expr → Prop where
  | variableValue {names value name args} :
      ExprCall.Occurs value name args →
        IncomingScope (.variableDeclaration names (some value)) name args
  | assignmentValue {names value name args} :
      ExprCall.Occurs value name args →
        IncomingScope (.assignment names value) name args
  | expressionStatement {expr name args} :
      ExprCall.Occurs expr name args →
        IncomingScope (.expressionStatement expr) name args
  | switchScrutinee {scrutinee cases default name args} :
      ExprCall.Occurs scrutinee name args →
        IncomingScope (.switch scrutinee cases default) name args
  | ifCondition {condition body name args} :
      ExprCall.Occurs condition name args →
        IncomingScope (.ifThen condition body) name args

end StmtExprCall

mutual

/-- Recursive source-facing raw call occurrence in a statement. -/
inductive StmtCall : Stmt → Name → List Expr → Prop where
  | incoming {stmt name args} :
      StmtExprCall.IncomingScope stmt name args →
        StmtCall stmt name args
  | block {stmts name args} :
      StmtListCall stmts name args →
        StmtCall (.block stmts) name args
  | functionBody {fn params returns body name args} :
      StmtListCall body name args →
        StmtCall (.functionDefinition fn params returns body) name args
  | switchCase {scrutinee cases default name args} :
      CaseListCall cases name args →
        StmtCall (.switch scrutinee cases default) name args
  | switchDefault {scrutinee cases default name args} :
      StmtListCall default name args →
        StmtCall (.switch scrutinee cases default) name args
  | forCondition {pre condition post body name args} :
      ExprCall.Occurs condition name args →
        StmtCall (.forLoop pre condition post body) name args
  | forPre {pre condition post body name args} :
      StmtListCall pre name args →
        StmtCall (.forLoop pre condition post body) name args
  | forPost {pre condition post body name args} :
      StmtListCall post name args →
        StmtCall (.forLoop pre condition post body) name args
  | forBody {pre condition post body name args} :
      StmtListCall body name args →
        StmtCall (.forLoop pre condition post body) name args
  | ifBody {condition body name args} :
      StmtListCall body name args →
        StmtCall (.ifThen condition body) name args

/-- Recursive source-facing raw call occurrence in a statement list. -/
inductive StmtListCall : List Stmt → Name → List Expr → Prop where
  | head {stmt rest name args} :
      StmtCall stmt name args →
        StmtListCall (stmt :: rest) name args
  | tail {stmt rest name args} :
      StmtListCall rest name args →
        StmtListCall (stmt :: rest) name args

/-- Recursive source-facing raw call occurrence in switch case bodies. -/
inductive CaseListCall :
    List (SwitchCaseValue × List Stmt) → Name → List Expr → Prop where
  | head {value body rest name args} :
      StmtListCall body name args →
        CaseListCall ((value, body) :: rest) name args
  | tail {case rest name args} :
      CaseListCall rest name args →
        CaseListCall (case :: rest) name args

end

namespace StmtCall

theorem ofIncoming
    {stmt : Stmt} {name : Name} {args : List Expr}
    (hOccurrence : StmtExprCall.IncomingScope stmt name args) :
    StmtCall stmt name args :=
  .incoming hOccurrence

end StmtCall

namespace StmtListCall

theorem of_mem_stmt
    {stmts : List Stmt} {stmt : Stmt}
    {name : Name} {args : List Expr}
    (hMem : stmt ∈ stmts)
    (hOccurrence : StmtCall stmt name args) :
    StmtListCall stmts name args := by
  induction stmts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp at hMem
      rcases hMem with hHead | hTail
      · subst stmt
        exact .head hOccurrence
      · exact .tail (ih hTail)

theorem of_mem_incoming
    {stmts : List Stmt} {stmt : Stmt}
    {name : Name} {args : List Expr}
    (hMem : stmt ∈ stmts)
    (hOccurrence : StmtExprCall.IncomingScope stmt name args) :
    StmtListCall stmts name args :=
  of_mem_stmt hMem (StmtCall.ofIncoming hOccurrence)

end StmtListCall

namespace CaseListCall

theorem of_mem_body
    {cases : List (SwitchCaseValue × List Stmt)}
    {value : SwitchCaseValue} {body : List Stmt}
    {name : Name} {args : List Expr}
    (hMem : (value, body) ∈ cases)
    (hOccurrence : StmtListCall body name args) :
    CaseListCall cases name args := by
  induction cases with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp at hMem
      rcases hMem with hHead | hTail
      · cases hHead
        exact .head hOccurrence
      · exact .tail (ih hTail)

theorem of_mem_body_incoming
    {cases : List (SwitchCaseValue × List Stmt)}
    {value : SwitchCaseValue} {body : List Stmt}
    {stmt : Stmt} {name : Name} {args : List Expr}
    (hCaseMem : (value, body) ∈ cases)
    (hStmtMem : stmt ∈ body)
    (hOccurrence : StmtExprCall.IncomingScope stmt name args) :
    CaseListCall cases name args :=
  of_mem_body hCaseMem
    (StmtListCall.of_mem_incoming hStmtMem hOccurrence)

end CaseListCall

mutual

/--
Source-facing raw call occurrence along a path where nested local-function
scopes do not shadow the selected source name.

This is the resolver-safe refinement of `StmtCall`: it keeps source syntax
separate from generated names, while recording the no-shadow facts needed for
an outer resolver entry to remain valid through nested block-like statements.
-/
inductive NoShadowStmtCall : Stmt → Name → List Expr → Prop where
  | incoming {stmt name args} :
      StmtExprCall.IncomingScope stmt name args →
        NoShadowStmtCall stmt name args
  | block {stmts name args} :
      NoLocalFunctionNamed stmts name →
        NoShadowStmtListCall stmts name args →
          NoShadowStmtCall (.block stmts) name args
  | functionBody {fn params returns body name args} :
      NoLocalFunctionNamed body name →
        NoShadowStmtListCall body name args →
          NoShadowStmtCall
            (.functionDefinition fn params returns body) name args
  | switchCase {scrutinee cases default name args} :
      NoShadowCaseListCall cases name args →
        NoShadowStmtCall (.switch scrutinee cases default) name args
  | switchDefault {scrutinee cases default name args} :
      NoLocalFunctionNamed default name →
        NoShadowStmtListCall default name args →
          NoShadowStmtCall (.switch scrutinee cases default) name args
  | forCondition {pre condition post body name args} :
      NoLocalFunctionNamed pre name →
      ExprCall.Occurs condition name args →
        NoShadowStmtCall (.forLoop pre condition post body) name args
  | forPre {pre condition post body name args} :
      NoLocalFunctionNamed pre name →
        NoShadowStmtListCall pre name args →
          NoShadowStmtCall (.forLoop pre condition post body) name args
  | forPost {pre condition post body name args} :
      NoLocalFunctionNamed pre name →
      NoLocalFunctionNamed post name →
      NoShadowStmtListCall post name args →
        NoShadowStmtCall (.forLoop pre condition post body) name args
  | forBody {pre condition post body name args} :
      NoLocalFunctionNamed pre name →
      NoLocalFunctionNamed body name →
      NoShadowStmtListCall body name args →
        NoShadowStmtCall (.forLoop pre condition post body) name args
  | ifBody {condition body name args} :
      NoLocalFunctionNamed body name →
        NoShadowStmtListCall body name args →
          NoShadowStmtCall (.ifThen condition body) name args

/-- Resolver-safe recursive source-facing raw call occurrence in a statement list. -/
inductive NoShadowStmtListCall : List Stmt → Name → List Expr → Prop where
  | head {stmt rest name args} :
      NoShadowStmtCall stmt name args →
        NoShadowStmtListCall (stmt :: rest) name args
  | tail {stmt rest name args} :
      NoShadowStmtListCall rest name args →
        NoShadowStmtListCall (stmt :: rest) name args

/-- Resolver-safe recursive source-facing raw call occurrence in switch cases. -/
inductive NoShadowCaseListCall :
    List (SwitchCaseValue × List Stmt) → Name → List Expr → Prop where
  | head {value body rest name args} :
      NoLocalFunctionNamed body name →
        NoShadowStmtListCall body name args →
          NoShadowCaseListCall ((value, body) :: rest) name args
  | tail {case rest name args} :
      NoShadowCaseListCall rest name args →
        NoShadowCaseListCall (case :: rest) name args

end

namespace NoShadowStmtCall

theorem ofIncoming
    {stmt : Stmt} {name : Name} {args : List Expr}
    (hOccurrence : StmtExprCall.IncomingScope stmt name args) :
    NoShadowStmtCall stmt name args :=
  .incoming hOccurrence

end NoShadowStmtCall

namespace NoShadowStmtListCall

theorem of_mem_stmt
    {stmts : List Stmt} {stmt : Stmt}
    {name : Name} {args : List Expr}
    (hMem : stmt ∈ stmts)
    (hOccurrence : NoShadowStmtCall stmt name args) :
    NoShadowStmtListCall stmts name args := by
  induction stmts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp at hMem
      rcases hMem with hHead | hTail
      · subst stmt
        exact .head hOccurrence
      · exact .tail (ih hTail)

theorem of_mem_incoming
    {stmts : List Stmt} {stmt : Stmt}
    {name : Name} {args : List Expr}
    (hMem : stmt ∈ stmts)
    (hOccurrence : StmtExprCall.IncomingScope stmt name args) :
    NoShadowStmtListCall stmts name args :=
  of_mem_stmt hMem (NoShadowStmtCall.ofIncoming hOccurrence)

end NoShadowStmtListCall

namespace NoShadowCaseListCall

theorem of_mem_body
    {cases : List (SwitchCaseValue × List Stmt)}
    {value : SwitchCaseValue} {body : List Stmt}
    {name : Name} {args : List Expr}
    (hMem : (value, body) ∈ cases)
    (hNoShadow : NoLocalFunctionNamed body name)
    (hOccurrence : NoShadowStmtListCall body name args) :
    NoShadowCaseListCall cases name args := by
  induction cases with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp at hMem
      rcases hMem with hHead | hTail
      · cases hHead
        exact .head hNoShadow hOccurrence
      · exact .tail (ih hTail)

theorem of_mem_body_incoming
    {cases : List (SwitchCaseValue × List Stmt)}
    {value : SwitchCaseValue} {body : List Stmt}
    {stmt : Stmt} {name : Name} {args : List Expr}
    (hCaseMem : (value, body) ∈ cases)
    (hNoShadow : NoLocalFunctionNamed body name)
    (hStmtMem : stmt ∈ body)
    (hOccurrence : StmtExprCall.IncomingScope stmt name args) :
    NoShadowCaseListCall cases name args :=
  of_mem_body hCaseMem hNoShadow
    (NoShadowStmtListCall.of_mem_incoming hStmtMem hOccurrence)

end NoShadowCaseListCall

mutual

def noShadowStmtCallToStmtCall (name : Name) (args : List Expr) :
    {stmt : Stmt} → NoShadowStmtCall stmt name args →
      StmtCall stmt name args
  | _, .incoming hIncoming => .incoming hIncoming
  | _, .block _ hList =>
      .block (noShadowStmtListCallToStmtListCall name args hList)
  | _, .functionBody _ hList =>
      .functionBody (noShadowStmtListCallToStmtListCall name args hList)
  | _, .switchCase hCases =>
      .switchCase (noShadowCaseListCallToCaseListCall name args hCases)
  | _, .switchDefault _ hList =>
      .switchDefault (noShadowStmtListCallToStmtListCall name args hList)
  | _, .forCondition _ hCondition => .forCondition hCondition
  | _, .forPre _ hList =>
      .forPre (noShadowStmtListCallToStmtListCall name args hList)
  | _, .forPost _ _ hList =>
      .forPost (noShadowStmtListCallToStmtListCall name args hList)
  | _, .forBody _ _ hList =>
      .forBody (noShadowStmtListCallToStmtListCall name args hList)
  | _, .ifBody _ hList =>
      .ifBody (noShadowStmtListCallToStmtListCall name args hList)

def noShadowCaseListCallToCaseListCall (name : Name) (args : List Expr) :
    {cases : List (SwitchCaseValue × List Stmt)} →
      NoShadowCaseListCall cases name args → CaseListCall cases name args
  | _, .head _ hBody =>
      .head (noShadowStmtListCallToStmtListCall name args hBody)
  | _, .tail hTail =>
      .tail (noShadowCaseListCallToCaseListCall name args hTail)

def noShadowStmtListCallToStmtListCall (name : Name) (args : List Expr) :
    {stmts : List Stmt} → NoShadowStmtListCall stmts name args →
      StmtListCall stmts name args
  | _, .head hHead =>
      .head (noShadowStmtCallToStmtCall name args hHead)
  | _, .tail hTail =>
      .tail (noShadowStmtListCallToStmtListCall name args hTail)

end

theorem NoShadowStmtCall.toStmtCall
    {stmt : Stmt} {name : Name} {args : List Expr}
    (hOccurrence : NoShadowStmtCall stmt name args) :
    StmtCall stmt name args :=
  noShadowStmtCallToStmtCall name args hOccurrence

theorem NoShadowStmtListCall.toStmtListCall
    {stmts : List Stmt} {name : Name} {args : List Expr}
    (hOccurrence : NoShadowStmtListCall stmts name args) :
    StmtListCall stmts name args :=
  noShadowStmtListCallToStmtListCall name args hOccurrence

theorem NoShadowCaseListCall.toCaseListCall
    {cases : List (SwitchCaseValue × List Stmt)}
    {name : Name} {args : List Expr}
    (hOccurrence : NoShadowCaseListCall cases name args) :
    CaseListCall cases name args :=
  noShadowCaseListCallToCaseListCall name args hOccurrence

end Source

end Raw

namespace FrontendOccurrence

/-- Occurrence of a generated frontend user call in a frontend expression. -/
inductive UserCall : Frontend.Expr → Name → List Frontend.Expr → Prop where
  | here {generated args} :
      UserCall (.call .user generated args) generated args
  | arg {kind callee args arg generated generatedArgs} :
      arg ∈ args →
        UserCall arg generated generatedArgs →
          UserCall (.call kind callee args) generated generatedArgs

namespace UserCall

theorem headArg
    {kind : Frontend.CallKind} {callee : Name}
    {arg : Frontend.Expr} {args : List Frontend.Expr}
    {generated : Name} {generatedArgs : List Frontend.Expr}
    (hArg : UserCall arg generated generatedArgs) :
    UserCall (.call kind callee (arg :: args)) generated generatedArgs :=
  .arg (by simp) hArg

theorem objectBuiltinNameArg?_none
    {expr : Frontend.Expr} {generated : Name}
    {args : List Frontend.Expr}
    (hOccurrence : UserCall expr generated args) :
    Frontend.Expr.objectBuiltinNameArg? expr = none := by
  cases hOccurrence <;> rfl

theorem not_lit
    {value : Frontend.Word} {generated : Name}
    {args : List Frontend.Expr} :
    ¬ UserCall (.lit value) generated args := by
  intro hOccurrence
  cases hOccurrence

theorem not_stringLit
    {value : String} {generated : Name}
    {args : List Frontend.Expr} :
    ¬ UserCall (.stringLit value) generated args := by
  intro hOccurrence
  cases hOccurrence

theorem not_bytesLit
    {bytes : List UInt8} {generated : Name}
    {args : List Frontend.Expr} :
    ¬ UserCall (.bytesLit bytes) generated args := by
  intro hOccurrence
  cases hOccurrence

theorem not_var
    {name : Name} {generated : Name}
    {args : List Frontend.Expr} :
    ¬ UserCall (.var name) generated args := by
  intro hOccurrence
  cases hOccurrence

theorem resolveObjectBuiltinsIn?_here
    {generated : Name} {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext} {expr' : Frontend.Expr}
    (hResolve :
      (Frontend.Expr.call .user generated args).resolveObjectBuiltinsIn?
          context =
        some expr') :
    ∃ args',
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context = some args' ∧
        expr' = .call .user generated args' ∧
          UserCall expr' generated args' := by
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgs :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none =>
      simp [hArgs] at hResolve
  | some args' =>
      simp [hArgs] at hResolve
      cases hResolve
      exact ⟨args', by simpa using hArgs, rfl, UserCall.here⟩

theorem resolveObjectBuiltinsIn?_nonObjectBuiltin_call
    {kind : Frontend.CallKind} {callee : Name}
    {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext} {expr' : Frontend.Expr}
    (hKind : kind ≠ .objectBuiltin)
    (hResolve :
      (Frontend.Expr.call kind callee args).resolveObjectBuiltinsIn?
          context =
        some expr') :
    ∃ args',
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context = some args' ∧
        expr' = .call kind callee args' := by
  cases kind with
  | primitive =>
      unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
      cases hArgs :
          Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
      | none =>
          simp [hArgs] at hResolve
      | some args' =>
          simp [hArgs] at hResolve
          cases hResolve
          exact ⟨args', by simpa using hArgs, rfl⟩
  | user =>
      unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
      cases hArgs :
          Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
      | none =>
          simp [hArgs] at hResolve
      | some args' =>
          simp [hArgs] at hResolve
          cases hResolve
          exact ⟨args', by simpa using hArgs, rfl⟩
  | objectBuiltin =>
      exact False.elim (hKind rfl)
  | dialectBuiltin =>
      unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
      cases hArgs :
          Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
      | none =>
          simp [hArgs] at hResolve
      | some args' =>
          simp [hArgs] at hResolve
          cases hResolve
          exact ⟨args', by simpa using hArgs, rfl⟩

mutual

theorem resolveObjectBuiltinsIn?_occurrence
    {expr expr' : Frontend.Expr} {generated : Name}
    {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext}
    (hResolve : Frontend.Expr.resolveObjectBuiltinsIn? expr context = some expr')
    (hOccurrence : UserCall expr generated args) :
    ∃ args',
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context = some args' ∧
        UserCall expr' generated args' := by
  cases expr with
  | lit value =>
      cases hOccurrence
  | stringLit value =>
      cases hOccurrence
  | bytesLit bytes =>
      cases hOccurrence
  | var name =>
      cases hOccurrence
  | call kind callee callArgs =>
      cases hOccurrence with
      | here =>
          rcases resolveObjectBuiltinsIn?_here hResolve with
            ⟨args', hArgs, hEq, hOccurrence'⟩
          subst expr'
          exact ⟨args', hArgs, hOccurrence'⟩
      | arg hMem hArg =>
          cases kind with
          | primitive =>
              rcases
                  resolveObjectBuiltinsIn?_nonObjectBuiltin_call
                    (by intro h; cases h) hResolve with
                ⟨callArgs', hArgsResolve, hExpr'⟩
              subst expr'
              rcases
                  resolveObjectBuiltinsIn?_list_mem_occurrence
                    hArgsResolve hMem hArg with
                ⟨arg', args', _hArgResolve, hArgMem, hGeneratedArgs,
                  hOccurrence'⟩
              exact
                ⟨args', hGeneratedArgs,
                  UserCall.arg hArgMem hOccurrence'⟩
          | user =>
              rcases
                  resolveObjectBuiltinsIn?_nonObjectBuiltin_call
                    (by intro h; cases h) hResolve with
                ⟨callArgs', hArgsResolve, hExpr'⟩
              subst expr'
              rcases
                  resolveObjectBuiltinsIn?_list_mem_occurrence
                    hArgsResolve hMem hArg with
                ⟨arg', args', _hArgResolve, hArgMem, hGeneratedArgs,
                  hOccurrence'⟩
              exact
                ⟨args', hGeneratedArgs,
                  UserCall.arg hArgMem hOccurrence'⟩
          | dialectBuiltin =>
              rcases
                  resolveObjectBuiltinsIn?_nonObjectBuiltin_call
                    (by intro h; cases h) hResolve with
                ⟨callArgs', hArgsResolve, hExpr'⟩
              subst expr'
              rcases
                  resolveObjectBuiltinsIn?_list_mem_occurrence
                    hArgsResolve hMem hArg with
                ⟨arg', args', _hArgResolve, hArgMem, hGeneratedArgs,
                  hOccurrence'⟩
              exact
                ⟨args', hGeneratedArgs,
                  UserCall.arg hArgMem hOccurrence'⟩
          | objectBuiltin =>
              cases callArgs with
              | nil =>
                  simp at hMem
              | cons first rest =>
                  cases rest with
                  | nil =>
                      simp at hMem
                      subst_vars
                      by_cases hDatasize : callee = "datasize"
                      · subst callee
                        unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
                        cases hName :
                            Frontend.Expr.objectBuiltinNameArg? first with
                        | none =>
                            simp [hName] at hResolve
                        | some name =>
                            have hNone := objectBuiltinNameArg?_none hArg
                            rw [hName] at hNone
                            simp at hNone
                      · by_cases hDataoffset : callee = "dataoffset"
                        · subst callee
                          unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
                          cases hName :
                              Frontend.Expr.objectBuiltinNameArg? first with
                          | none =>
                              simp [hName] at hResolve
                          | some name =>
                              have hNone := objectBuiltinNameArg?_none hArg
                              rw [hName] at hNone
                              simp at hNone
                        · by_cases hLinker : callee = "linkersymbol"
                          · subst callee
                            unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
                            cases hName :
                                Frontend.Expr.objectBuiltinNameArg? first with
                            | none =>
                                simp [hName] at hResolve
                            | some name =>
                                have hNone := objectBuiltinNameArg?_none hArg
                                rw [hName] at hNone
                                simp at hNone
                          · by_cases hLoad : callee = "loadimmutable"
                            · subst callee
                              unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
                              cases hName :
                                  Frontend.Expr.objectBuiltinNameArg? first with
                              | none =>
                                  simp [hName] at hResolve
                              | some name =>
                                  have hNone := objectBuiltinNameArg?_none hArg
                                  rw [hName] at hNone
                                  simp at hNone
                            · by_cases hMemoryguard : callee = "memoryguard"
                              · subst callee
                                unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
                                cases hValue :
                                    Frontend.Expr.resolveObjectBuiltinsIn?
                                      first context with
                                | none =>
                                    simp [hValue] at hResolve
                                | some value' =>
                                    cases value' with
                                    | lit size =>
                                        rcases
                                            resolveObjectBuiltinsIn?_occurrence
                                              hValue hArg with
                                          ⟨args', _hGeneratedArgs,
                                            hOccurrence'⟩
                                        exact False.elim
                                          (not_lit hOccurrence')
                                    | stringLit value =>
                                        simp [hValue] at hResolve
                                    | bytesLit bytes =>
                                        simp [hValue] at hResolve
                                    | var name =>
                                        simp [hValue] at hResolve
                                    | call kind callee callArgs =>
                                        simp [hValue] at hResolve
                              · unfold Frontend.Expr.resolveObjectBuiltinsIn?
                                  at hResolve
                                cases hArgsResolve :
                                    Frontend.Expr.List.resolveObjectBuiltinsIn?
                                      [first] context with
                                | none =>
                                    simp [hDatasize, hDataoffset, hLinker,
                                      hLoad, hMemoryguard, hArgsResolve]
                                      at hResolve
                                | some callArgs' =>
                                    simp [hDatasize, hDataoffset, hLinker,
                                      hLoad, hMemoryguard, hArgsResolve]
                                      at hResolve
                                    cases hResolve
                                    rcases
                                        resolveObjectBuiltinsIn?_list_mem_occurrence
                                          hArgsResolve (by simp) hArg with
                                      ⟨arg', args', _hArgResolve, hArgMem,
                                        hGeneratedArgs, hOccurrence'⟩
                                    exact
                                      ⟨args', hGeneratedArgs,
                                        UserCall.arg hArgMem hOccurrence'⟩
                  | cons second rest' =>
                      cases rest' with
                      | nil =>
                          unfold Frontend.Expr.resolveObjectBuiltinsIn?
                            at hResolve
                          cases hArgsResolve :
                              Frontend.Expr.List.resolveObjectBuiltinsIn?
                                [first, second] context with
                          | none =>
                              simp [hArgsResolve] at hResolve
                          | some callArgs' =>
                              simp [hArgsResolve] at hResolve
                              cases hResolve
                              rcases
                                  resolveObjectBuiltinsIn?_list_mem_occurrence
                                    hArgsResolve hMem hArg with
                                ⟨arg', args', _hArgResolve, hArgMem,
                                  hGeneratedArgs, hOccurrence'⟩
                              exact
                                ⟨args', hGeneratedArgs,
                                  UserCall.arg hArgMem hOccurrence'⟩
                      | cons third rest'' =>
                          cases rest'' with
                          | nil =>
                              by_cases hDatacopy : callee = "datacopy"
                              · subst callee
                                unfold Frontend.Expr.resolveObjectBuiltinsIn?
                                  at hResolve
                                cases hFirst :
                                    Frontend.Expr.resolveObjectBuiltinsIn?
                                      first context with
                                | none =>
                                    simp [hFirst] at hResolve
                                | some first' =>
                                    cases hSecond :
                                        Frontend.Expr.resolveObjectBuiltinsIn?
                                          second context with
                                    | none =>
                                        simp [hFirst, hSecond] at hResolve
                                    | some second' =>
                                        cases hThird :
                                            Frontend.Expr.resolveObjectBuiltinsIn?
                                              third context with
                                        | none =>
                                            simp [hFirst, hSecond, hThird]
                                              at hResolve
                                        | some third' =>
                                            simp [hFirst, hSecond, hThird]
                                              at hResolve
                                            cases hResolve
                                            simp at hMem
                                            rcases hMem with hHere |
                                              hSecondMem | hThirdMem
                                            · subst_vars
                                              rcases
                                                  resolveObjectBuiltinsIn?_occurrence
                                                    hFirst hArg with
                                                ⟨args', hGeneratedArgs,
                                                  hOccurrence'⟩
                                              exact
                                                ⟨args', hGeneratedArgs,
                                                  UserCall.arg (by simp)
                                                    hOccurrence'⟩
                                            · subst_vars
                                              rcases
                                                  resolveObjectBuiltinsIn?_occurrence
                                                    hSecond hArg with
                                                ⟨args', hGeneratedArgs,
                                                  hOccurrence'⟩
                                              exact
                                                ⟨args', hGeneratedArgs,
                                                  UserCall.arg (by simp)
                                                    hOccurrence'⟩
                                            · subst_vars
                                              rcases
                                                  resolveObjectBuiltinsIn?_occurrence
                                                    hThird hArg with
                                                ⟨args', hGeneratedArgs,
                                                  hOccurrence'⟩
                                              exact
                                                ⟨args', hGeneratedArgs,
                                                  UserCall.arg (by simp)
                                                    hOccurrence'⟩
                              · unfold Frontend.Expr.resolveObjectBuiltinsIn?
                                  at hResolve
                                cases hArgsResolve :
                                    Frontend.Expr.List.resolveObjectBuiltinsIn?
                                      [first, second, third] context with
                                | none =>
                                    simp [hDatacopy, hArgsResolve] at hResolve
                                | some callArgs' =>
                                    simp [hDatacopy, hArgsResolve] at hResolve
                                    cases hResolve
                                    rcases
                                        resolveObjectBuiltinsIn?_list_mem_occurrence
                                          hArgsResolve hMem hArg with
                                      ⟨arg', args', _hArgResolve, hArgMem,
                                        hGeneratedArgs, hOccurrence'⟩
                                    exact
                                      ⟨args', hGeneratedArgs,
                                        UserCall.arg hArgMem hOccurrence'⟩
                          | cons fourth rest''' =>
                              unfold Frontend.Expr.resolveObjectBuiltinsIn?
                                at hResolve
                              cases hArgsResolve :
                                  Frontend.Expr.List.resolveObjectBuiltinsIn?
                                    (first :: second :: third ::
                                      fourth :: rest''') context with
                              | none =>
                                  simp [hArgsResolve] at hResolve
                              | some callArgs' =>
                                  simp [hArgsResolve] at hResolve
                                  cases hResolve
                                  rcases
                                      resolveObjectBuiltinsIn?_list_mem_occurrence
                                        hArgsResolve hMem hArg with
                                    ⟨arg', args', _hArgResolve, hArgMem,
                                      hGeneratedArgs, hOccurrence'⟩
                                  exact
                                    ⟨args', hGeneratedArgs,
                                      UserCall.arg hArgMem hOccurrence'⟩
termination_by sizeOf expr

theorem resolveObjectBuiltinsIn?_list_mem_occurrence
    {exprs exprs' : List Frontend.Expr} {expr : Frontend.Expr}
    {generated : Name} {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext}
    (hResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? exprs context = some exprs')
    (hMem : expr ∈ exprs)
    (hOccurrence : UserCall expr generated args) :
    ∃ expr' args',
      Frontend.Expr.resolveObjectBuiltinsIn? expr context = some expr' ∧
        expr' ∈ exprs' ∧
          Frontend.Expr.List.resolveObjectBuiltinsIn? args context =
            some args' ∧
            UserCall expr' generated args' := by
  cases exprs with
  | nil =>
      simp at hMem
  | cons head tail =>
      unfold Frontend.Expr.List.resolveObjectBuiltinsIn? at hResolve
      cases hHead :
          Frontend.Expr.resolveObjectBuiltinsIn? head context with
      | none =>
          simp [hHead] at hResolve
      | some head' =>
          cases hTail :
              Frontend.Expr.List.resolveObjectBuiltinsIn? tail context with
          | none =>
              simp [hHead, hTail] at hResolve
          | some tail' =>
              simp [hHead, hTail] at hResolve
              cases hResolve
              simp at hMem
              rcases hMem with hHere | hTailMem
              · subst expr
                rcases
                    resolveObjectBuiltinsIn?_occurrence hHead
                      hOccurrence with
                  ⟨args', hGeneratedArgs, hOccurrence'⟩
                exact
                  ⟨head', args', hHead, by simp, hGeneratedArgs,
                    hOccurrence'⟩
              · rcases
                    resolveObjectBuiltinsIn?_list_mem_occurrence
                      hTail hTailMem hOccurrence with
                  ⟨expr', args', hExprResolve, hExprMem,
                    hGeneratedArgs, hOccurrence'⟩
                exact
                  ⟨expr', args', hExprResolve, by simp [hExprMem],
                    hGeneratedArgs, hOccurrence'⟩
termination_by sizeOf exprs

end

theorem resolveObjectBuiltinsIn?_not_lit
    {expr : Frontend.Expr} {value : Frontend.Word}
    {generated : Name} {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext}
    (hResolve :
      Frontend.Expr.resolveObjectBuiltinsIn? expr context =
        some (.lit value))
    (hOccurrence : UserCall expr generated args) :
    False := by
  rcases resolveObjectBuiltinsIn?_occurrence hResolve hOccurrence with
    ⟨args', _hArgs, hOccurrence'⟩
  exact not_lit hOccurrence'

end UserCall

/-- Generated frontend user-call occurrence in a statement expression field. -/
inductive StmtIncomingUserCall :
    Frontend.Stmt → Name → List Frontend.Expr → Prop where
  | letValue {names value generated args} :
      UserCall value generated args →
        StmtIncomingUserCall (.letDecl names (some value)) generated args
  | assignmentValue {names value generated args} :
      UserCall value generated args →
        StmtIncomingUserCall (.assign names value) generated args
  | expressionStatement {expr generated args} :
      UserCall expr generated args →
        StmtIncomingUserCall (.exprStmt expr) generated args
  | switchScrutinee {scrutinee cases default generated args} :
      UserCall scrutinee generated args →
        StmtIncomingUserCall (.switch scrutinee cases default) generated args
  | ifCondition {condition body generated args} :
      UserCall condition generated args →
        StmtIncomingUserCall (.ifThen condition body) generated args

mutual

/-- Recursive generated frontend user-call occurrence in a statement. -/
inductive StmtUserCall : Frontend.Stmt → Name → List Frontend.Expr → Prop where
  | incoming {stmt generated args} :
      StmtIncomingUserCall stmt generated args →
        StmtUserCall stmt generated args
  | block {stmts generated args} :
      StmtListUserCall stmts generated args →
        StmtUserCall (.block stmts) generated args
  | functionBody {name params returns body generated args} :
      StmtListUserCall body generated args →
        StmtUserCall (.functionDef name params returns body) generated args
  | switchCase {scrutinee cases default generated args} :
      CaseListUserCall cases generated args →
        StmtUserCall (.switch scrutinee cases default) generated args
  | switchDefault {scrutinee cases default generated args} :
      StmtListUserCall default generated args →
        StmtUserCall (.switch scrutinee cases default) generated args
  | forCondition {pre condition post body generated args} :
      UserCall condition generated args →
        StmtUserCall (.forLoop pre condition post body) generated args
  | forPre {pre condition post body generated args} :
      StmtListUserCall pre generated args →
        StmtUserCall (.forLoop pre condition post body) generated args
  | forPost {pre condition post body generated args} :
      StmtListUserCall post generated args →
        StmtUserCall (.forLoop pre condition post body) generated args
  | forBody {pre condition post body generated args} :
      StmtListUserCall body generated args →
        StmtUserCall (.forLoop pre condition post body) generated args
  | ifBody {condition body generated args} :
      StmtListUserCall body generated args →
        StmtUserCall (.ifThen condition body) generated args

/-- Recursive generated frontend user-call occurrence in a statement list. -/
inductive StmtListUserCall :
    List Frontend.Stmt → Name → List Frontend.Expr → Prop where
  | head {stmt rest generated args} :
      StmtUserCall stmt generated args →
        StmtListUserCall (stmt :: rest) generated args
  | tail {stmt rest generated args} :
      StmtListUserCall rest generated args →
        StmtListUserCall (stmt :: rest) generated args

/-- Recursive generated frontend user-call occurrence in switch case bodies. -/
inductive CaseListUserCall :
    List (Frontend.SwitchCaseValue × List Frontend.Stmt) →
      Name → List Frontend.Expr → Prop where
  | head {value body rest generated args} :
      StmtListUserCall body generated args →
        CaseListUserCall ((value, body) :: rest) generated args
  | tail {case rest generated args} :
      CaseListUserCall rest generated args →
        CaseListUserCall (case :: rest) generated args

end

namespace StmtUserCall

theorem ofIncoming
    {stmt : Frontend.Stmt} {generated : Name}
    {args : List Frontend.Expr}
    (hOccurrence :
      StmtIncomingUserCall stmt generated args) :
    StmtUserCall stmt generated args :=
  .incoming hOccurrence

end StmtUserCall

namespace StmtListUserCall

theorem of_mem_stmt
    {stmts : List Frontend.Stmt} {stmt : Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hMem : stmt ∈ stmts)
    (hOccurrence : StmtUserCall stmt generated args) :
    StmtListUserCall stmts generated args := by
  induction stmts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp at hMem
      rcases hMem with hHead | hTail
      · subst stmt
        exact .head hOccurrence
      · exact .tail (ih hTail)

theorem of_mem_incoming
    {stmts : List Frontend.Stmt} {stmt : Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hMem : stmt ∈ stmts)
    (hOccurrence :
      StmtIncomingUserCall stmt generated args) :
    StmtListUserCall stmts generated args :=
  of_mem_stmt hMem (StmtUserCall.ofIncoming hOccurrence)

end StmtListUserCall

namespace CaseListUserCall

theorem of_mem_body
    {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {value : Frontend.SwitchCaseValue} {body : List Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hMem : (value, body) ∈ cases)
    (hOccurrence : StmtListUserCall body generated args) :
    CaseListUserCall cases generated args := by
  induction cases with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp at hMem
      rcases hMem with hHead | hTail
      · cases hHead
        exact .head hOccurrence
      · exact .tail (ih hTail)

end CaseListUserCall

namespace ImmutablePatchOccurrence

theorem patchStmt?_base
    {reference : Frontend.ImmutableReference}
    {base value : Frontend.Expr} {stmt : Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hPatch :
      Frontend.ImmutableReference.patchStmt? reference base value =
        some stmt)
    (hOccurrence : UserCall base generated args) :
    StmtUserCall stmt generated args := by
  unfold Frontend.ImmutableReference.patchStmt? at hPatch
  by_cases hPatchable : reference.isPatchable
  · simp [hPatchable] at hPatch
    cases hPatch
    let offset :=
      Frontend.Expr.lit (EvmYul.UInt256.ofNat reference.start)
    let addExpr : Frontend.Expr :=
      .call .primitive "add" [base, offset]
    have hBaseMem : base ∈ [base, offset] := by
      simp [offset]
    have hAddOccurrence :
        UserCall addExpr generated args :=
      UserCall.arg hBaseMem hOccurrence
    have hAddMem : addExpr ∈ [addExpr, value] := by
      simp [addExpr]
    exact
      StmtUserCall.ofIncoming
        (StmtIncomingUserCall.expressionStatement
          (UserCall.arg hAddMem hAddOccurrence))
  · simp [hPatchable] at hPatch

theorem patchStmt?_value
    {reference : Frontend.ImmutableReference}
    {base value : Frontend.Expr} {stmt : Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hPatch :
      Frontend.ImmutableReference.patchStmt? reference base value =
        some stmt)
    (hOccurrence : UserCall value generated args) :
    StmtUserCall stmt generated args := by
  unfold Frontend.ImmutableReference.patchStmt? at hPatch
  by_cases hPatchable : reference.isPatchable
  · simp [hPatchable] at hPatch
    cases hPatch
    let offset :=
      Frontend.Expr.lit (EvmYul.UInt256.ofNat reference.start)
    let addExpr : Frontend.Expr :=
      .call .primitive "add" [base, offset]
    have hValueMem : value ∈ [addExpr, value] := by
      simp [addExpr]
    exact
      StmtUserCall.ofIncoming
        (StmtIncomingUserCall.expressionStatement
          (UserCall.arg hValueMem hOccurrence))
  · simp [hPatchable] at hPatch

theorem patchStmts?_base
    {references : List Frontend.ImmutableReference}
    {base value : Frontend.Expr} {stmts : List Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hPatch :
      Frontend.ImmutableReference.List.patchStmts?
        references base value = some stmts)
    (hNonempty : references ≠ [])
    (hOccurrence : UserCall base generated args) :
    StmtListUserCall stmts generated args := by
  cases references with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons reference rest =>
      unfold Frontend.ImmutableReference.List.patchStmts? at hPatch
      cases hHead :
          Frontend.ImmutableReference.patchStmt? reference base value with
      | none =>
          simp [hHead] at hPatch
      | some headStmt =>
          cases hTail :
              Frontend.ImmutableReference.List.patchStmts?
                rest base value with
          | none =>
              simp [hHead, hTail] at hPatch
          | some tailStmts =>
              simp [hHead, hTail] at hPatch
              cases hPatch
              exact
                StmtListUserCall.head
                  (patchStmt?_base hHead hOccurrence)

theorem patchStmts?_value
    {references : List Frontend.ImmutableReference}
    {base value : Frontend.Expr} {stmts : List Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hPatch :
      Frontend.ImmutableReference.List.patchStmts?
        references base value = some stmts)
    (hNonempty : references ≠ [])
    (hOccurrence : UserCall value generated args) :
    StmtListUserCall stmts generated args := by
  cases references with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons reference rest =>
      unfold Frontend.ImmutableReference.List.patchStmts? at hPatch
      cases hHead :
          Frontend.ImmutableReference.patchStmt? reference base value with
      | none =>
          simp [hHead] at hPatch
      | some headStmt =>
          cases hTail :
              Frontend.ImmutableReference.List.patchStmts?
                rest base value with
          | none =>
              simp [hHead, hTail] at hPatch
          | some tailStmts =>
              simp [hHead, hTail] at hPatch
              cases hPatch
              exact
                StmtListUserCall.head
                  (patchStmt?_value hHead hOccurrence)

end ImmutablePatchOccurrence

namespace StmtIncomingUserCall

private theorem findImmutableReferences?_some_nonempty
    {context : Frontend.ObjectBuiltinContext} {name : Name}
    {references : List Frontend.ImmutableReference}
    (hRefs :
      context.findImmutableReferences? name = some references) :
    references ≠ [] := by
  intro hNil
  subst references
  unfold Frontend.ObjectBuiltinContext.findImmutableReferences? at hRefs
  cases hCollect :
      Frontend.ObjectBuiltinContext.collectImmutableReferences
        context.immutableReferences name <;>
    simp [hCollect] at hRefs

theorem resolveObjectBuiltinsIn?_occurrence
    {stmt stmt' : Frontend.Stmt} {generated : Name}
    {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext}
    (hResolve :
      Frontend.Stmt.resolveObjectBuiltinsIn? stmt context = some stmt')
    (hOccurrence : StmtIncomingUserCall stmt generated args) :
    ∃ args',
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context = some args' ∧
        StmtUserCall stmt' generated args' := by
  cases hOccurrence with
  | letValue hValue =>
      rename_i names value
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hValueResolve :
          Frontend.Expr.resolveObjectBuiltinsIn? value context with
      | none =>
          simp [hValueResolve] at hResolve
      | some value' =>
          simp [hValueResolve] at hResolve
          cases hResolve
          rcases
              UserCall.resolveObjectBuiltinsIn?_occurrence
                hValueResolve hValue with
            ⟨args', hArgs, hValue'⟩
          exact
            ⟨args', hArgs,
              StmtUserCall.ofIncoming
                (StmtIncomingUserCall.letValue hValue')⟩
  | assignmentValue hValue =>
      rename_i names value
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hValueResolve :
          Frontend.Expr.resolveObjectBuiltinsIn? value context with
      | none =>
          simp [hValueResolve] at hResolve
      | some value' =>
          simp [hValueResolve] at hResolve
          cases hResolve
          rcases
              UserCall.resolveObjectBuiltinsIn?_occurrence
                hValueResolve hValue with
            ⟨args', hArgs, hValue'⟩
          exact
            ⟨args', hArgs,
              StmtUserCall.ofIncoming
                (StmtIncomingUserCall.assignmentValue hValue')⟩
  | expressionStatement hExpr =>
      rename_i expr
      cases expr with
      | lit value =>
          cases hExpr
      | stringLit value =>
          cases hExpr
      | bytesLit bytes =>
          cases hExpr
      | var name =>
          cases hExpr
      | call kind callee callArgs =>
          cases kind with
          | primitive =>
              unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
              cases hExprResolve :
                  Frontend.Expr.resolveObjectBuiltinsIn?
                    (.call .primitive callee callArgs) context with
              | none =>
                  simp [hExprResolve] at hResolve
              | some expr' =>
                  simp [hExprResolve] at hResolve
                  cases hResolve
                  rcases
                      UserCall.resolveObjectBuiltinsIn?_occurrence
                        hExprResolve hExpr with
                    ⟨args', hArgs, hExpr'⟩
                  exact
                    ⟨args', hArgs,
                      StmtUserCall.ofIncoming
                        (StmtIncomingUserCall.expressionStatement hExpr')⟩
          | user =>
              unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
              cases hExprResolve :
                  Frontend.Expr.resolveObjectBuiltinsIn?
                    (.call .user callee callArgs) context with
              | none =>
                  simp [hExprResolve] at hResolve
              | some expr' =>
                  simp [hExprResolve] at hResolve
                  cases hResolve
                  rcases
                      UserCall.resolveObjectBuiltinsIn?_occurrence
                        hExprResolve hExpr with
                    ⟨args', hArgs, hExpr'⟩
                  exact
                    ⟨args', hArgs,
                      StmtUserCall.ofIncoming
                        (StmtIncomingUserCall.expressionStatement hExpr')⟩
          | dialectBuiltin =>
              unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
              cases hExprResolve :
                  Frontend.Expr.resolveObjectBuiltinsIn?
                    (.call .dialectBuiltin callee callArgs) context with
              | none =>
                  simp [hExprResolve] at hResolve
              | some expr' =>
                  simp [hExprResolve] at hResolve
                  cases hResolve
                  rcases
                      UserCall.resolveObjectBuiltinsIn?_occurrence
                        hExprResolve hExpr with
                    ⟨args', hArgs, hExpr'⟩
                  exact
                    ⟨args', hArgs,
                      StmtUserCall.ofIncoming
                        (StmtIncomingUserCall.expressionStatement hExpr')⟩
          | objectBuiltin =>
              cases callArgs with
              | nil =>
                  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
                  cases hExprResolve :
                      Frontend.Expr.resolveObjectBuiltinsIn?
                        (.call .objectBuiltin callee []) context with
                  | none =>
                      simp [hExprResolve] at hResolve
                  | some expr' =>
                      simp [hExprResolve] at hResolve
                      cases hResolve
                      rcases
                          UserCall.resolveObjectBuiltinsIn?_occurrence
                            hExprResolve hExpr with
                        ⟨args', hArgs, hExpr'⟩
                      exact
                        ⟨args', hArgs,
                          StmtUserCall.ofIncoming
                            (StmtIncomingUserCall.expressionStatement hExpr')⟩
              | cons first rest =>
                  cases rest with
                  | nil =>
                      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
                      cases hExprResolve :
                          Frontend.Expr.resolveObjectBuiltinsIn?
                            (.call .objectBuiltin callee [first]) context with
                      | none =>
                          simp [hExprResolve] at hResolve
                      | some expr' =>
                          simp [hExprResolve] at hResolve
                          cases hResolve
                          rcases
                              UserCall.resolveObjectBuiltinsIn?_occurrence
                                hExprResolve hExpr with
                            ⟨args', hArgs, hExpr'⟩
                          exact
                            ⟨args', hArgs,
                              StmtUserCall.ofIncoming
                                (StmtIncomingUserCall.expressionStatement
                                  hExpr')⟩
                  | cons second rest' =>
                      cases rest' with
                      | nil =>
                          unfold Frontend.Stmt.resolveObjectBuiltinsIn?
                            at hResolve
                          cases hExprResolve :
                              Frontend.Expr.resolveObjectBuiltinsIn?
                                (.call .objectBuiltin callee [first, second])
                                context with
                          | none =>
                              simp [hExprResolve] at hResolve
                          | some expr' =>
                              simp [hExprResolve] at hResolve
                              cases hResolve
                              rcases
                                  UserCall.resolveObjectBuiltinsIn?_occurrence
                                    hExprResolve hExpr with
                                ⟨args', hArgs, hExpr'⟩
                              exact
                                ⟨args', hArgs,
                                  StmtUserCall.ofIncoming
                                    (StmtIncomingUserCall.expressionStatement
                                      hExpr')⟩
                      | cons third rest'' =>
                          cases rest'' with
                          | nil =>
                              by_cases hSet : callee = "setimmutable"
                              · subst callee
                                unfold Frontend.Stmt.resolveObjectBuiltinsIn?
                                  at hResolve
                                cases hName :
                                    Frontend.Expr.objectBuiltinNameArg?
                                      second with
                                | none =>
                                    simp [hName] at hResolve
                                | some immutableName =>
                                    cases hBase :
                                        Frontend.Expr.resolveObjectBuiltinsIn?
                                          first context with
                                    | none =>
                                        simp [hName, hBase] at hResolve
                                    | some base' =>
                                        cases hValue :
                                            Frontend.Expr.resolveObjectBuiltinsIn?
                                              third context with
                                        | none =>
                                            simp [hName, hBase, hValue]
                                              at hResolve
                                        | some value' =>
                                            cases hRefs :
                                                context.findImmutableReferences?
                                                  immutableName with
                                            | none =>
                                                simp [hName, hBase, hValue,
                                                  hRefs] at hResolve
                                            | some references =>
                                                cases hPatch :
                                                    Frontend.ImmutableReference.List.patchStmts?
                                                      references base' value' with
                                                | none =>
                                                    simp [hName, hBase,
                                                      hValue, hRefs, hPatch]
                                                      at hResolve
                                                | some stmts =>
                                                    simp [hName, hBase,
                                                      hValue, hRefs, hPatch]
                                                      at hResolve
                                                    cases hResolve
                                                    cases hExpr with
                                                    | arg hMem hArg =>
                                                        simp at hMem
                                                        rcases hMem with
                                                          hBaseMem |
                                                          hNameMem |
                                                          hValueMem
                                                        · subst_vars
                                                          rcases
                                                              UserCall.resolveObjectBuiltinsIn?_occurrence
                                                                hBase hArg with
                                                            ⟨args', hArgs,
                                                              hBase'⟩
                                                          exact
                                                            ⟨args', hArgs,
                                                              StmtUserCall.block
                                                                (ImmutablePatchOccurrence.patchStmts?_base
                                                                  hPatch
                                                                  (findImmutableReferences?_some_nonempty
                                                                    hRefs)
                                                                  hBase')⟩
                                                        · subst_vars
                                                          have hNone :=
                                                            UserCall.objectBuiltinNameArg?_none
                                                              hArg
                                                          rw [hName] at hNone
                                                          simp at hNone
                                                        · subst_vars
                                                          rcases
                                                              UserCall.resolveObjectBuiltinsIn?_occurrence
                                                                hValue hArg with
                                                            ⟨args', hArgs,
                                                              hValue'⟩
                                                          exact
                                                            ⟨args', hArgs,
                                                              StmtUserCall.block
                                                                (ImmutablePatchOccurrence.patchStmts?_value
                                                                  hPatch
                                                                  (findImmutableReferences?_some_nonempty
                                                                    hRefs)
                                                                  hValue')⟩
                              · unfold Frontend.Stmt.resolveObjectBuiltinsIn?
                                  at hResolve
                                cases hExprResolve :
                                    Frontend.Expr.resolveObjectBuiltinsIn?
                                      (.call .objectBuiltin callee
                                        [first, second, third]) context with
                                | none =>
                                    simp [hSet, hExprResolve] at hResolve
                                | some expr' =>
                                    simp [hSet, hExprResolve] at hResolve
                                    cases hResolve
                                    rcases
                                        UserCall.resolveObjectBuiltinsIn?_occurrence
                                          hExprResolve hExpr with
                                      ⟨args', hArgs, hExpr'⟩
                                    exact
                                      ⟨args', hArgs,
                                        StmtUserCall.ofIncoming
                                          (StmtIncomingUserCall.expressionStatement
                                            hExpr')⟩
                          | cons fourth rest''' =>
                              unfold Frontend.Stmt.resolveObjectBuiltinsIn?
                                at hResolve
                              cases hExprResolve :
                                  Frontend.Expr.resolveObjectBuiltinsIn?
                                    (.call .objectBuiltin callee
                                      (first :: second :: third ::
                                        fourth :: rest''')) context with
                              | none =>
                                  simp [hExprResolve] at hResolve
                              | some expr' =>
                                  simp [hExprResolve] at hResolve
                                  cases hResolve
                                  rcases
                                      UserCall.resolveObjectBuiltinsIn?_occurrence
                                        hExprResolve hExpr with
                                    ⟨args', hArgs, hExpr'⟩
                                  exact
                                    ⟨args', hArgs,
                                      StmtUserCall.ofIncoming
                                        (StmtIncomingUserCall.expressionStatement
                                          hExpr')⟩
  | switchScrutinee hScrutinee =>
      rename_i scrutinee cases default
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hScrutineeResolve :
          Frontend.Expr.resolveObjectBuiltinsIn? scrutinee context with
      | none =>
          simp [hScrutineeResolve] at hResolve
      | some scrutinee' =>
          cases hCases :
              Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? cases context with
          | none =>
              simp [hScrutineeResolve, hCases] at hResolve
          | some cases' =>
              cases hDefault :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? default context with
              | none =>
                  simp [hScrutineeResolve, hCases, hDefault] at hResolve
              | some default' =>
                  simp [hScrutineeResolve, hCases, hDefault] at hResolve
                  cases hResolve
                  rcases
                      UserCall.resolveObjectBuiltinsIn?_occurrence
                        hScrutineeResolve hScrutinee with
                    ⟨args', hArgs, hScrutinee'⟩
                  exact
                    ⟨args', hArgs,
                      StmtUserCall.ofIncoming
                        (StmtIncomingUserCall.switchScrutinee
                          hScrutinee')⟩
  | ifCondition hCondition =>
      rename_i condition body
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hConditionResolve :
          Frontend.Expr.resolveObjectBuiltinsIn? condition context with
      | none =>
          simp [hConditionResolve] at hResolve
      | some condition' =>
          cases hBody :
              Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
          | none =>
              simp [hConditionResolve, hBody] at hResolve
          | some body' =>
              simp [hConditionResolve, hBody] at hResolve
              cases hResolve
              rcases
                  UserCall.resolveObjectBuiltinsIn?_occurrence
                    hConditionResolve hCondition with
                ⟨args', hArgs, hCondition'⟩
              exact
                ⟨args', hArgs,
                  StmtUserCall.ofIncoming
                    (StmtIncomingUserCall.ifCondition hCondition')⟩

end StmtIncomingUserCall

mutual

theorem StmtUserCall.resolveObjectBuiltinsIn?_occurrence
    {stmt stmt' : Frontend.Stmt} {generated : Name}
    {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext}
    (hResolve :
      Frontend.Stmt.resolveObjectBuiltinsIn? stmt context = some stmt')
    (hOccurrence : StmtUserCall stmt generated args) :
    ∃ args',
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context = some args' ∧
        StmtUserCall stmt' generated args' := by
  cases hOccurrence with
  | incoming hIncoming =>
      exact StmtIncomingUserCall.resolveObjectBuiltinsIn?_occurrence
        hResolve hIncoming
  | block hBody =>
      rename_i stmts
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hBodyResolve :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? stmts context with
      | none =>
          simp [hBodyResolve] at hResolve
      | some stmts' =>
          simp [hBodyResolve] at hResolve
          cases hResolve
          rcases
              StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                hBodyResolve hBody with
            ⟨args', hArgs, hBody'⟩
          exact ⟨args', hArgs, StmtUserCall.block hBody'⟩
  | functionBody hBody =>
      rename_i name params returns body
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hBodyResolve :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
      | none =>
          simp [hBodyResolve] at hResolve
      | some body' =>
          simp [hBodyResolve] at hResolve
          cases hResolve
          rcases
              StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                hBodyResolve hBody with
            ⟨args', hArgs, hBody'⟩
          exact ⟨args', hArgs, StmtUserCall.functionBody hBody'⟩
  | switchCase hCases =>
      rename_i scrutinee cases default
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hScrutinee :
          Frontend.Expr.resolveObjectBuiltinsIn? scrutinee context with
      | none =>
          simp [hScrutinee] at hResolve
      | some scrutinee' =>
          cases hCasesResolve :
              Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? cases context with
          | none =>
              simp [hScrutinee, hCasesResolve] at hResolve
          | some cases' =>
              cases hDefault :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? default context with
              | none =>
                  simp [hScrutinee, hCasesResolve, hDefault] at hResolve
              | some default' =>
                  simp [hScrutinee, hCasesResolve, hDefault] at hResolve
                  cases hResolve
                  rcases
                      CaseListUserCall.resolveObjectBuiltinsIn?_occurrence
                        hCasesResolve hCases with
                    ⟨args', hArgs, hCases'⟩
                  exact ⟨args', hArgs, StmtUserCall.switchCase hCases'⟩
  | switchDefault hDefaultOccurrence =>
      rename_i scrutinee cases default
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hScrutinee :
          Frontend.Expr.resolveObjectBuiltinsIn? scrutinee context with
      | none =>
          simp [hScrutinee] at hResolve
      | some scrutinee' =>
          cases hCasesResolve :
              Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? cases context with
          | none =>
              simp [hScrutinee, hCasesResolve] at hResolve
          | some cases' =>
              cases hDefault :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? default context with
              | none =>
                  simp [hScrutinee, hCasesResolve, hDefault] at hResolve
              | some default' =>
                  simp [hScrutinee, hCasesResolve, hDefault] at hResolve
                  cases hResolve
                  rcases
                      StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                        hDefault hDefaultOccurrence with
                    ⟨args', hArgs, hDefault'⟩
                  exact ⟨args', hArgs, StmtUserCall.switchDefault hDefault'⟩
  | forCondition hCondition =>
      rename_i pre condition post body
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hPre :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? pre context with
      | none =>
          simp [hPre] at hResolve
      | some pre' =>
          cases hConditionResolve :
              Frontend.Expr.resolveObjectBuiltinsIn? condition context with
          | none =>
              simp [hPre, hConditionResolve] at hResolve
          | some condition' =>
              cases hPost :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? post context with
              | none =>
                  simp [hPre, hConditionResolve, hPost] at hResolve
              | some post' =>
                  cases hBody :
                      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
                  | none =>
                      simp [hPre, hConditionResolve, hPost, hBody] at hResolve
                  | some body' =>
                      simp [hPre, hConditionResolve, hPost, hBody] at hResolve
                      cases hResolve
                      rcases
                          UserCall.resolveObjectBuiltinsIn?_occurrence
                            hConditionResolve hCondition with
                        ⟨args', hArgs, hCondition'⟩
                      exact ⟨args', hArgs, StmtUserCall.forCondition hCondition'⟩
  | forPre hPreOccurrence =>
      rename_i pre condition post body
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hPre :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? pre context with
      | none =>
          simp [hPre] at hResolve
      | some pre' =>
          cases hCondition :
              Frontend.Expr.resolveObjectBuiltinsIn? condition context with
          | none =>
              simp [hPre, hCondition] at hResolve
          | some condition' =>
              cases hPost :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? post context with
              | none =>
                  simp [hPre, hCondition, hPost] at hResolve
              | some post' =>
                  cases hBody :
                      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
                  | none =>
                      simp [hPre, hCondition, hPost, hBody] at hResolve
                  | some body' =>
                      simp [hPre, hCondition, hPost, hBody] at hResolve
                      cases hResolve
                      rcases
                          StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                            hPre hPreOccurrence with
                        ⟨args', hArgs, hPre'⟩
                      exact ⟨args', hArgs, StmtUserCall.forPre hPre'⟩
  | forPost hPostOccurrence =>
      rename_i pre condition post body
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hPre :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? pre context with
      | none =>
          simp [hPre] at hResolve
      | some pre' =>
          cases hCondition :
              Frontend.Expr.resolveObjectBuiltinsIn? condition context with
          | none =>
              simp [hPre, hCondition] at hResolve
          | some condition' =>
              cases hPost :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? post context with
              | none =>
                  simp [hPre, hCondition, hPost] at hResolve
              | some post' =>
                  cases hBody :
                      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
                  | none =>
                      simp [hPre, hCondition, hPost, hBody] at hResolve
                  | some body' =>
                      simp [hPre, hCondition, hPost, hBody] at hResolve
                      cases hResolve
                      rcases
                          StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                            hPost hPostOccurrence with
                        ⟨args', hArgs, hPost'⟩
                      exact ⟨args', hArgs, StmtUserCall.forPost hPost'⟩
  | forBody hBodyOccurrence =>
      rename_i pre condition post body
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hPre :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? pre context with
      | none =>
          simp [hPre] at hResolve
      | some pre' =>
          cases hCondition :
              Frontend.Expr.resolveObjectBuiltinsIn? condition context with
          | none =>
              simp [hPre, hCondition] at hResolve
          | some condition' =>
              cases hPost :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? post context with
              | none =>
                  simp [hPre, hCondition, hPost] at hResolve
              | some post' =>
                  cases hBody :
                      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
                  | none =>
                      simp [hPre, hCondition, hPost, hBody] at hResolve
                  | some body' =>
                      simp [hPre, hCondition, hPost, hBody] at hResolve
                      cases hResolve
                      rcases
                          StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                            hBody hBodyOccurrence with
                        ⟨args', hArgs, hBody'⟩
                      exact ⟨args', hArgs, StmtUserCall.forBody hBody'⟩
  | ifBody hBodyOccurrence =>
      rename_i condition body
      unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
      cases hCondition :
          Frontend.Expr.resolveObjectBuiltinsIn? condition context with
      | none =>
          simp [hCondition] at hResolve
      | some condition' =>
          cases hBody :
              Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
          | none =>
              simp [hCondition, hBody] at hResolve
          | some body' =>
              simp [hCondition, hBody] at hResolve
              cases hResolve
              rcases
                  StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                    hBody hBodyOccurrence with
                ⟨args', hArgs, hBody'⟩
              exact ⟨args', hArgs, StmtUserCall.ifBody hBody'⟩

theorem StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
    {stmts stmts' : List Frontend.Stmt} {generated : Name}
    {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext}
    (hResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? stmts context = some stmts')
    (hOccurrence : StmtListUserCall stmts generated args) :
    ∃ args',
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context = some args' ∧
        StmtListUserCall stmts' generated args' := by
  cases hOccurrence with
  | head hHeadOccurrence =>
      rename_i stmt rest
      unfold Frontend.Stmt.List.resolveObjectBuiltinsIn? at hResolve
      cases hHead :
          Frontend.Stmt.resolveObjectBuiltinsIn? stmt context with
      | none =>
          simp [hHead] at hResolve
      | some stmt' =>
          cases hRest :
              Frontend.Stmt.List.resolveObjectBuiltinsIn? rest context with
          | none =>
              simp [hHead, hRest] at hResolve
          | some rest' =>
              simp [hHead, hRest] at hResolve
              cases hResolve
              rcases
                  StmtUserCall.resolveObjectBuiltinsIn?_occurrence
                    hHead hHeadOccurrence with
                ⟨args', hArgs, hHead'⟩
              exact ⟨args', hArgs, StmtListUserCall.head hHead'⟩
  | tail hTailOccurrence =>
      rename_i stmt rest
      unfold Frontend.Stmt.List.resolveObjectBuiltinsIn? at hResolve
      cases hHead :
          Frontend.Stmt.resolveObjectBuiltinsIn? stmt context with
      | none =>
          simp [hHead] at hResolve
      | some stmt' =>
          cases hRest :
              Frontend.Stmt.List.resolveObjectBuiltinsIn? rest context with
          | none =>
              simp [hHead, hRest] at hResolve
          | some rest' =>
              simp [hHead, hRest] at hResolve
              cases hResolve
              rcases
                  StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                    hRest hTailOccurrence with
                ⟨args', hArgs, hTail'⟩
              exact ⟨args', hArgs, StmtListUserCall.tail hTail'⟩

theorem CaseListUserCall.resolveObjectBuiltinsIn?_occurrence
    {cases cases' :
      List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {generated : Name} {args : List Frontend.Expr}
    {context : Frontend.ObjectBuiltinContext}
    (hResolve :
      Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? cases context =
        some cases')
    (hOccurrence : CaseListUserCall cases generated args) :
    ∃ args',
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context = some args' ∧
        CaseListUserCall cases' generated args' := by
  cases hOccurrence with
  | head hBodyOccurrence =>
      rename_i value body rest
      unfold Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? at hResolve
      cases hBody :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
      | none =>
          simp [hBody] at hResolve
      | some body' =>
          cases hRest :
              Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? rest context with
          | none =>
              simp [hBody, hRest] at hResolve
          | some rest' =>
              simp [hBody, hRest] at hResolve
              cases hResolve
              rcases
                  StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
                    hBody hBodyOccurrence with
                ⟨args', hArgs, hBody'⟩
              exact ⟨args', hArgs, CaseListUserCall.head hBody'⟩
  | tail hTailOccurrence =>
      rename_i case rest
      rcases case with ⟨value, body⟩
      unfold Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? at hResolve
      cases hBody :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
      | none =>
          simp [hBody] at hResolve
      | some body' =>
          cases hRest :
              Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? rest context with
          | none =>
              simp [hBody, hRest] at hResolve
          | some rest' =>
              simp [hBody, hRest] at hResolve
              cases hResolve
              rcases
                  CaseListUserCall.resolveObjectBuiltinsIn?_occurrence
                    hRest hTailOccurrence with
                ⟨args', hArgs, hTail'⟩
              exact ⟨args', hArgs, CaseListUserCall.tail hTail'⟩

end

end FrontendOccurrence

namespace YulOccurrence

/-- Occurrence of a generated Yul user call in a lowered Yul expression. -/
inductive UserCall : Frontend.AstExpr → Name → List Frontend.AstExpr → Prop where
  | here {generated args} :
      UserCall (.Call (.inr generated) args) generated args
  | arg {callee args arg generated generatedArgs} :
      arg ∈ args →
        UserCall arg generated generatedArgs →
          UserCall (.Call callee args) generated generatedArgs

namespace UserCall

theorem headArg
    {callee : Sum (EvmYul.Operation .Yul) Name}
    {arg : Frontend.AstExpr} {args : List Frontend.AstExpr}
    {generated : Name} {generatedArgs : List Frontend.AstExpr}
    (hArg : UserCall arg generated generatedArgs) :
    UserCall (.Call callee (arg :: args)) generated generatedArgs :=
  .arg (by simp) hArg

private theorem mem_split
    {args : List Frontend.AstExpr} {arg : Frontend.AstExpr}
    (hMem : arg ∈ args) :
    ∃ (left right : List Frontend.AstExpr),
      args = left ++ arg :: right := by
  induction args with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      simp at hMem
      rcases hMem with hHere | hTail
      · subst head
        exact ⟨[], tail, rfl⟩
      · rcases ih hTail with ⟨left, right, hEq⟩
        exact ⟨head :: left, right, by simp [hEq]⟩

theorem direct_or_arg_split
    {expr : Frontend.AstExpr} {generated : Name}
    {generatedArgs : List Frontend.AstExpr}
    (hOccurrence : UserCall expr generated generatedArgs) :
    expr = .Call (.inr generated) generatedArgs ∨
      ∃ (callee : Sum (EvmYul.Operation .Yul) Name)
          (left : List Frontend.AstExpr)
          (focus : Frontend.AstExpr)
          (right : List Frontend.AstExpr),
        expr = .Call callee (left ++ focus :: right) ∧
          UserCall focus generated generatedArgs := by
  cases hOccurrence with
  | here =>
      exact Or.inl rfl
  | arg hMem hArg =>
      rename_i callee _args arg
      rcases mem_split hMem with ⟨left, right, hEq⟩
      exact Or.inr ⟨callee, left, arg, right, by simp [hEq], hArg⟩

end UserCall

/-- Generated Yul user-call occurrence in a lowered statement expression field. -/
inductive StmtIncomingUserCall :
    Frontend.AstStmt → Name → List Frontend.AstExpr → Prop where
  | letValue {names value generated args} :
      UserCall value generated args →
        StmtIncomingUserCall (.Let names (some value)) generated args
  | assignmentValue {names value generated args} :
      UserCall value generated args →
        StmtIncomingUserCall (.Assign names value) generated args
  | expressionStatement {expr generated args} :
      UserCall expr generated args →
        StmtIncomingUserCall (.ExprStmtCall expr) generated args
  | switchScrutinee {scrutinee cases default generated args} :
      UserCall scrutinee generated args →
        StmtIncomingUserCall (.Switch scrutinee cases default) generated args
  | ifCondition {condition body generated args} :
      UserCall condition generated args →
        StmtIncomingUserCall (.If condition body) generated args

namespace StmtIncomingUserCall

/-- Incoming statement expression field whose occurrence is exactly the
generated call. -/
inductive Direct : Frontend.AstStmt → Name → List Frontend.AstExpr → Prop where
  | letValue {names generated args} :
      Direct (.Let names (some (.Call (.inr generated) args))) generated args
  | assignmentValue {names generated args} :
      Direct (.Assign names (.Call (.inr generated) args)) generated args
  | expressionStatement {generated args} :
      Direct (.ExprStmtCall (.Call (.inr generated) args)) generated args
  | switchScrutinee {cases default generated args} :
      Direct (.Switch (.Call (.inr generated) args) cases default) generated args
  | ifCondition {body generated args} :
      Direct (.If (.Call (.inr generated) args) body) generated args

/-- Incoming statement expression field whose occurrence is inside one
surrounding call argument. The focused argument still carries the recursive
occurrence, so deeper expression nesting remains explicit. -/
inductive OuterArg : Frontend.AstStmt → Name → List Frontend.AstExpr → Prop where
  | letValue {names callee left focus right generated args} :
      UserCall focus generated args →
        OuterArg
          (.Let names (some (.Call callee (left ++ focus :: right))))
          generated args
  | assignmentValue {names callee left focus right generated args} :
      UserCall focus generated args →
        OuterArg
          (.Assign names (.Call callee (left ++ focus :: right)))
          generated args
  | expressionStatement {callee left focus right generated args} :
      UserCall focus generated args →
        OuterArg
          (.ExprStmtCall (.Call callee (left ++ focus :: right)))
          generated args
  | switchScrutinee
      {callee left focus right cases default generated args} :
      UserCall focus generated args →
        OuterArg
          (.Switch (.Call callee (left ++ focus :: right)) cases default)
          generated args
  | ifCondition {callee left focus right body generated args} :
      UserCall focus generated args →
        OuterArg
          (.If (.Call callee (left ++ focus :: right)) body)
          generated args

namespace Direct

theorem toIncoming
    {stmt : Frontend.AstStmt} {generated : Name}
    {args : List Frontend.AstExpr}
    (hDirect : Direct stmt generated args) :
    StmtIncomingUserCall stmt generated args := by
  cases hDirect with
  | letValue =>
      exact .letValue .here
  | assignmentValue =>
      exact .assignmentValue .here
  | expressionStatement =>
      exact .expressionStatement .here
  | switchScrutinee =>
      exact .switchScrutinee .here
  | ifCondition =>
      exact .ifCondition .here

end Direct

namespace OuterArg

theorem toIncoming
    {stmt : Frontend.AstStmt} {generated : Name}
    {args : List Frontend.AstExpr}
    (hOuter : OuterArg stmt generated args) :
    StmtIncomingUserCall stmt generated args := by
  cases hOuter with
  | letValue hFocus =>
      exact .letValue (.arg (by simp) hFocus)
  | assignmentValue hFocus =>
      exact .assignmentValue (.arg (by simp) hFocus)
  | expressionStatement hFocus =>
      exact .expressionStatement (.arg (by simp) hFocus)
  | switchScrutinee hFocus =>
      exact .switchScrutinee (.arg (by simp) hFocus)
  | ifCondition hFocus =>
      exact .ifCondition (.arg (by simp) hFocus)

end OuterArg

theorem direct_or_outerArg
    {stmt : Frontend.AstStmt} {generated : Name}
    {args : List Frontend.AstExpr}
    (hOccurrence : StmtIncomingUserCall stmt generated args) :
    Direct stmt generated args ∨ OuterArg stmt generated args := by
  cases hOccurrence with
  | letValue hValue =>
      rcases UserCall.direct_or_arg_split hValue with hDirect | hOuter
      · cases hDirect
        exact Or.inl Direct.letValue
      · rcases hOuter with ⟨callee, left, focus, right, hEq, hFocus⟩
        cases hEq
        exact Or.inr (OuterArg.letValue hFocus)
  | assignmentValue hValue =>
      rcases UserCall.direct_or_arg_split hValue with hDirect | hOuter
      · cases hDirect
        exact Or.inl Direct.assignmentValue
      · rcases hOuter with ⟨callee, left, focus, right, hEq, hFocus⟩
        cases hEq
        exact Or.inr (OuterArg.assignmentValue hFocus)
  | expressionStatement hExpr =>
      rcases UserCall.direct_or_arg_split hExpr with hDirect | hOuter
      · cases hDirect
        exact Or.inl Direct.expressionStatement
      · rcases hOuter with ⟨callee, left, focus, right, hEq, hFocus⟩
        cases hEq
        exact Or.inr (OuterArg.expressionStatement hFocus)
  | switchScrutinee hScrutinee =>
      rcases UserCall.direct_or_arg_split hScrutinee with hDirect | hOuter
      · cases hDirect
        exact Or.inl Direct.switchScrutinee
      · rcases hOuter with ⟨callee, left, focus, right, hEq, hFocus⟩
        cases hEq
        exact Or.inr (OuterArg.switchScrutinee hFocus)
  | ifCondition hCondition =>
      rcases UserCall.direct_or_arg_split hCondition with hDirect | hOuter
      · cases hDirect
        exact Or.inl Direct.ifCondition
      · rcases hOuter with ⟨callee, left, focus, right, hEq, hFocus⟩
        cases hEq
        exact Or.inr (OuterArg.ifCondition hFocus)

end StmtIncomingUserCall

mutual

/-- Recursive generated Yul user-call occurrence in a lowered statement. -/
inductive StmtUserCall : Frontend.AstStmt → Name → List Frontend.AstExpr → Prop where
  | incoming {stmt generated args} :
      StmtIncomingUserCall stmt generated args →
        StmtUserCall stmt generated args
  | block {stmts generated args} :
      StmtListUserCall stmts generated args →
        StmtUserCall (.Block stmts) generated args
  | switchCase {scrutinee cases default generated args} :
      CaseListUserCall cases generated args →
        StmtUserCall (.Switch scrutinee cases default) generated args
  | switchDefault {scrutinee cases default generated args} :
      StmtListUserCall default generated args →
        StmtUserCall (.Switch scrutinee cases default) generated args
  | forCondition {condition post body generated args} :
      UserCall condition generated args →
        StmtUserCall (.For condition post body) generated args
  | forPost {condition post body generated args} :
      StmtListUserCall post generated args →
        StmtUserCall (.For condition post body) generated args
  | forBody {condition post body generated args} :
      StmtListUserCall body generated args →
        StmtUserCall (.For condition post body) generated args
  | ifBody {condition body generated args} :
      StmtListUserCall body generated args →
        StmtUserCall (.If condition body) generated args

/-- Recursive generated Yul user-call occurrence in a lowered statement list. -/
inductive StmtListUserCall :
    List Frontend.AstStmt → Name → List Frontend.AstExpr → Prop where
  | head {stmt rest generated args} :
      StmtUserCall stmt generated args →
        StmtListUserCall (stmt :: rest) generated args
  | tail {stmt rest generated args} :
      StmtListUserCall rest generated args →
        StmtListUserCall (stmt :: rest) generated args

/-- Recursive generated Yul user-call occurrence in lowered switch case bodies. -/
inductive CaseListUserCall :
    List (Word × List Frontend.AstStmt) →
      Name → List Frontend.AstExpr → Prop where
  | head {value body rest generated args} :
      StmtListUserCall body generated args →
        CaseListUserCall ((value, body) :: rest) generated args
  | tail {case rest generated args} :
      CaseListUserCall rest generated args →
        CaseListUserCall (case :: rest) generated args

end

namespace StmtUserCall

theorem ofIncoming
    {stmt : Frontend.AstStmt} {generated : Name}
    {args : List Frontend.AstExpr}
    (hOccurrence :
      StmtIncomingUserCall stmt generated args) :
    StmtUserCall stmt generated args :=
  .incoming hOccurrence

/-- Focused statement occurrences whose generated call remains in a nested
statement/control context rather than in the statement's incoming expression
field. -/
inductive Context : Frontend.AstStmt → Name → List Frontend.AstExpr → Prop where
  | block {stmts generated args} :
      StmtListUserCall stmts generated args →
        Context (.Block stmts) generated args
  | switchCase {scrutinee cases default generated args} :
      CaseListUserCall cases generated args →
        Context (.Switch scrutinee cases default) generated args
  | switchDefault {scrutinee cases default generated args} :
      StmtListUserCall default generated args →
        Context (.Switch scrutinee cases default) generated args
  | forCondition {condition post body generated args} :
      UserCall condition generated args →
        Context (.For condition post body) generated args
  | forPost {condition post body generated args} :
      StmtListUserCall post generated args →
        Context (.For condition post body) generated args
  | forBody {condition post body generated args} :
      StmtListUserCall body generated args →
        Context (.For condition post body) generated args
  | ifBody {condition body generated args} :
      StmtListUserCall body generated args →
        Context (.If condition body) generated args

namespace Context

theorem toStmtUserCall
    {stmt : Frontend.AstStmt} {generated : Name}
    {args : List Frontend.AstExpr}
    (hContext : Context stmt generated args) :
    StmtUserCall stmt generated args := by
  cases hContext with
  | block hBody =>
      exact .block hBody
  | switchCase hCases =>
      exact .switchCase hCases
  | switchDefault hDefault =>
      exact .switchDefault hDefault
  | forCondition hCondition =>
      exact .forCondition hCondition
  | forPost hPost =>
      exact .forPost hPost
  | forBody hBody =>
      exact .forBody hBody
  | ifBody hBody =>
      exact .ifBody hBody

end Context

theorem direct_or_outerArg_or_context
    {stmt : Frontend.AstStmt} {generated : Name}
    {args : List Frontend.AstExpr}
    (hOccurrence : StmtUserCall stmt generated args) :
    StmtIncomingUserCall.Direct stmt generated args ∨
      StmtIncomingUserCall.OuterArg stmt generated args ∨
        Context stmt generated args := by
  cases hOccurrence with
  | incoming hIncoming =>
      rcases StmtIncomingUserCall.direct_or_outerArg hIncoming with
        hDirect | hOuter
      · exact Or.inl hDirect
      · exact Or.inr (Or.inl hOuter)
  | block hBody =>
      exact Or.inr (Or.inr (Context.block hBody))
  | switchCase hCases =>
      exact Or.inr (Or.inr (Context.switchCase hCases))
  | switchDefault hDefault =>
      exact Or.inr (Or.inr (Context.switchDefault hDefault))
  | forCondition hCondition =>
      exact Or.inr (Or.inr (Context.forCondition hCondition))
  | forPost hPost =>
      exact Or.inr (Or.inr (Context.forPost hPost))
  | forBody hBody =>
      exact Or.inr (Or.inr (Context.forBody hBody))
  | ifBody hBody =>
      exact Or.inr (Or.inr (Context.ifBody hBody))

end StmtUserCall

namespace StmtListUserCall

theorem append_left
    {left right : List Frontend.AstStmt}
    {generated : Name} {args : List Frontend.AstExpr}
    (hOccurrence : StmtListUserCall left generated args) :
    StmtListUserCall (left ++ right) generated args := by
  induction left with
  | nil =>
      cases hOccurrence
  | cons stmt rest ih =>
      cases hOccurrence with
      | head hHead =>
          exact .head hHead
      | tail hTail =>
          exact .tail (ih hTail)

theorem append_right
    (pre : List Frontend.AstStmt)
    {suffix : List Frontend.AstStmt}
    {generated : Name} {args : List Frontend.AstExpr}
    (hOccurrence : StmtListUserCall suffix generated args) :
    StmtListUserCall (pre ++ suffix) generated args := by
  induction pre with
  | nil =>
      simpa using hOccurrence
  | cons head rest ih =>
      exact .tail ih

theorem of_last
    (pre : List Frontend.AstStmt)
    {stmt : Frontend.AstStmt}
    {generated : Name} {args : List Frontend.AstExpr}
    (hOccurrence : StmtUserCall stmt generated args) :
    StmtListUserCall (pre ++ [stmt]) generated args :=
  append_right pre (StmtListUserCall.head hOccurrence)

theorem exists_split_stmt
    {stmts : List Frontend.AstStmt}
    {generated : Name} {args : List Frontend.AstExpr}
    (hOccurrence : StmtListUserCall stmts generated args) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      stmts = pre ++ stmt :: rest ∧
        StmtUserCall stmt generated args := by
  induction stmts with
  | nil =>
      cases hOccurrence
  | cons head tail ih =>
      cases hOccurrence with
      | head hHead =>
          exact ⟨[], head, tail, rfl, hHead⟩
      | tail hTail =>
          rcases ih hTail with
            ⟨pre, focus, suffix, hEq, hFocus⟩
          exact ⟨head :: pre, focus, suffix, by simp [hEq], hFocus⟩

theorem exists_split_direct_or_outerArg_or_context
    {stmts : List Frontend.AstStmt}
    {generated : Name} {args : List Frontend.AstExpr}
    (hOccurrence : StmtListUserCall stmts generated args) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      stmts = pre ++ stmt :: rest ∧
        (StmtIncomingUserCall.Direct stmt generated args ∨
          StmtIncomingUserCall.OuterArg stmt generated args ∨
            StmtUserCall.Context stmt generated args) := by
  rcases exists_split_stmt hOccurrence with
    ⟨pre, stmt, rest, hEq, hStmt⟩
  exact
    ⟨pre, stmt, rest, hEq,
      StmtUserCall.direct_or_outerArg_or_context hStmt⟩

end StmtListUserCall

namespace CaseListUserCall

theorem exists_split_body
    {cases : List (Word × List Frontend.AstStmt)}
    {generated : Name} {args : List Frontend.AstExpr}
    (hOccurrence : CaseListUserCall cases generated args) :
    ∃ (pre : List (Word × List Frontend.AstStmt))
        (value : Word)
        (body : List Frontend.AstStmt)
        (rest : List (Word × List Frontend.AstStmt)),
      cases = pre ++ (value, body) :: rest ∧
        StmtListUserCall body generated args := by
  induction cases with
  | nil =>
      cases hOccurrence
  | cons headCase tail ih =>
      cases hOccurrence with
      | head hBody =>
          exact ⟨[], _, _, _, rfl, hBody⟩
      | tail hTail =>
          rcases ih hTail with
            ⟨pre, value, body, rest, hEq, hBody⟩
          exact ⟨headCase :: pre, value, body, rest, by simp [hEq], hBody⟩

end CaseListUserCall

end YulOccurrence

namespace FrontendOccurrence

mutual

/--
Generated frontend user-call occurrence that should lower into the current Yul
statement body.

Retained `functionDef` staging nodes are intentionally absent: their statement
itself lowers to `Block []`, while the function body is emitted through the
separate generated function entry.
-/
inductive LowerableStmtUserCall :
    Frontend.Stmt → Name → List Frontend.Expr → Prop where
  | incoming {stmt generated args} :
      StmtIncomingUserCall stmt generated args →
        LowerableStmtUserCall stmt generated args
  | block {stmts generated args} :
      LowerableStmtListUserCall stmts generated args →
        LowerableStmtUserCall (.block stmts) generated args
  | switchCase {scrutinee cases default generated args} :
      LowerableCaseListUserCall cases generated args →
        LowerableStmtUserCall (.switch scrutinee cases default) generated args
  | switchDefault {scrutinee cases default generated args} :
      LowerableStmtListUserCall default generated args →
        LowerableStmtUserCall (.switch scrutinee cases default) generated args
  | forCondition {pre condition post body generated args} :
      UserCall condition generated args →
        LowerableStmtUserCall (.forLoop pre condition post body) generated args
  | forPre {pre condition post body generated args} :
      LowerableStmtListUserCall pre generated args →
        LowerableStmtUserCall (.forLoop pre condition post body) generated args
  | forPost {pre condition post body generated args} :
      LowerableStmtListUserCall post generated args →
        LowerableStmtUserCall (.forLoop pre condition post body) generated args
  | forBody {pre condition post body generated args} :
      LowerableStmtListUserCall body generated args →
        LowerableStmtUserCall (.forLoop pre condition post body) generated args
  | ifBody {condition body generated args} :
      LowerableStmtListUserCall body generated args →
        LowerableStmtUserCall (.ifThen condition body) generated args

/-- Recursive lowerable frontend user-call occurrence in a statement list. -/
inductive LowerableStmtListUserCall :
    List Frontend.Stmt → Name → List Frontend.Expr → Prop where
  | head {stmt rest generated args} :
      LowerableStmtUserCall stmt generated args →
        LowerableStmtListUserCall (stmt :: rest) generated args
  | tail {stmt rest generated args} :
      LowerableStmtListUserCall rest generated args →
        LowerableStmtListUserCall (stmt :: rest) generated args

/-- Recursive lowerable frontend user-call occurrence in switch case bodies. -/
inductive LowerableCaseListUserCall :
    List (Frontend.SwitchCaseValue × List Frontend.Stmt) →
      Name → List Frontend.Expr → Prop where
  | head {value body rest generated args} :
      LowerableStmtListUserCall body generated args →
        LowerableCaseListUserCall ((value, body) :: rest) generated args
  | tail {case rest generated args} :
      LowerableCaseListUserCall rest generated args →
        LowerableCaseListUserCall (case :: rest) generated args

end

mutual

/--
Generated frontend user-call occurrence that is inside a retained
`functionDef` staging body.

Such occurrences are not lowerable in the current statement body: the staging
node lowers to `Block []`, and the body must be followed through the generated
function entry validated by `functionDefStubsLoweredToEntries?`.
-/
inductive StubBodyStmtUserCall :
    Frontend.Stmt → Name → List Frontend.Expr → Prop where
  | functionBody {name params returns body generated args} :
      StmtListUserCall body generated args →
        StubBodyStmtUserCall (.functionDef name params returns body)
          generated args
  | block {stmts generated args} :
      StubBodyStmtListUserCall stmts generated args →
        StubBodyStmtUserCall (.block stmts) generated args
  | switchCase {scrutinee cases default generated args} :
      StubBodyCaseListUserCall cases generated args →
        StubBodyStmtUserCall (.switch scrutinee cases default) generated args
  | switchDefault {scrutinee cases default generated args} :
      StubBodyStmtListUserCall default generated args →
        StubBodyStmtUserCall (.switch scrutinee cases default) generated args
  | forPre {pre condition post body generated args} :
      StubBodyStmtListUserCall pre generated args →
        StubBodyStmtUserCall (.forLoop pre condition post body) generated args
  | forPost {pre condition post body generated args} :
      StubBodyStmtListUserCall post generated args →
        StubBodyStmtUserCall (.forLoop pre condition post body) generated args
  | forBody {pre condition post body generated args} :
      StubBodyStmtListUserCall body generated args →
        StubBodyStmtUserCall (.forLoop pre condition post body) generated args
  | ifBody {condition body generated args} :
      StubBodyStmtListUserCall body generated args →
        StubBodyStmtUserCall (.ifThen condition body) generated args

/-- Recursive retained-stub-body occurrence in a frontend statement list. -/
inductive StubBodyStmtListUserCall :
    List Frontend.Stmt → Name → List Frontend.Expr → Prop where
  | head {stmt rest generated args} :
      StubBodyStmtUserCall stmt generated args →
        StubBodyStmtListUserCall (stmt :: rest) generated args
  | tail {stmt rest generated args} :
      StubBodyStmtListUserCall rest generated args →
        StubBodyStmtListUserCall (stmt :: rest) generated args

/-- Recursive retained-stub-body occurrence in frontend switch case bodies. -/
inductive StubBodyCaseListUserCall :
    List (Frontend.SwitchCaseValue × List Frontend.Stmt) →
      Name → List Frontend.Expr → Prop where
  | head {value body rest generated args} :
      StubBodyStmtListUserCall body generated args →
        StubBodyCaseListUserCall ((value, body) :: rest) generated args
  | tail {case rest generated args} :
      StubBodyCaseListUserCall rest generated args →
        StubBodyCaseListUserCall (case :: rest) generated args

end

namespace StmtListUserCall

theorem lowerable_or_stubBody
    {front : List Frontend.Stmt}
    {generated : Name} {args : List Frontend.Expr}
    (hOccurrence : StmtListUserCall front generated args) :
    LowerableStmtListUserCall front generated args ∨
      StubBodyStmtListUserCall front generated args :=
  StmtListUserCall.rec
    (motive_1 := fun stmt generated args _ =>
      LowerableStmtUserCall stmt generated args ∨
        StubBodyStmtUserCall stmt generated args)
    (motive_2 := fun stmts generated args _ =>
      LowerableStmtListUserCall stmts generated args ∨
        StubBodyStmtListUserCall stmts generated args)
    (motive_3 := fun cases generated args _ =>
      LowerableCaseListUserCall cases generated args ∨
        StubBodyCaseListUserCall cases generated args)
    (incoming := by
      intro stmt generated args hIncoming
      exact Or.inl (LowerableStmtUserCall.incoming hIncoming))
    (block := by
      intro stmts generated args hList ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtUserCall.block hLowerable)
      · exact Or.inr (StubBodyStmtUserCall.block hStub))
    (functionBody := by
      intro name params returns body generated args hBody _ih
      exact
        Or.inr (StubBodyStmtUserCall.functionBody hBody))
    (switchCase := by
      intro scrutinee cases default generated args hCases ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtUserCall.switchCase hLowerable)
      · exact Or.inr (StubBodyStmtUserCall.switchCase hStub))
    (switchDefault := by
      intro scrutinee cases default generated args hDefault ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtUserCall.switchDefault hLowerable)
      · exact Or.inr (StubBodyStmtUserCall.switchDefault hStub))
    (forCondition := by
      intro pre condition post body generated args hCondition
      exact Or.inl (LowerableStmtUserCall.forCondition hCondition))
    (forPre := by
      intro pre condition post body generated args hPre ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtUserCall.forPre hLowerable)
      · exact Or.inr (StubBodyStmtUserCall.forPre hStub))
    (forPost := by
      intro pre condition post body generated args hPost ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtUserCall.forPost hLowerable)
      · exact Or.inr (StubBodyStmtUserCall.forPost hStub))
    (forBody := by
      intro pre condition post body generated args hBody ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtUserCall.forBody hLowerable)
      · exact Or.inr (StubBodyStmtUserCall.forBody hStub))
    (ifBody := by
      intro condition body generated args hBody ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtUserCall.ifBody hLowerable)
      · exact Or.inr (StubBodyStmtUserCall.ifBody hStub))
    (head := by
      intro stmt rest generated args hHead ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtListUserCall.head hLowerable)
      · exact Or.inr (StubBodyStmtListUserCall.head hStub))
    (tail := by
      intro stmt rest generated args hTail ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableStmtListUserCall.tail hLowerable)
      · exact Or.inr (StubBodyStmtListUserCall.tail hStub))
    (by
      intro value body rest generated args hBody ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableCaseListUserCall.head hLowerable)
      · exact Or.inr (StubBodyCaseListUserCall.head hStub))
    (by
      intro caseEntry rest generated args hTail ih
      rcases ih with hLowerable | hStub
      · exact Or.inl (LowerableCaseListUserCall.tail hLowerable)
      · exact Or.inr (StubBodyCaseListUserCall.tail hStub))
    hOccurrence

end StmtListUserCall

namespace StubBodyStmtListUserCall

theorem lowered_function_entry
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    ∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt),
      StmtListUserCall body generated args ∧
        Frontend.Stmt.List.toYul? body = some yulBody ∧
          entries.contains
            (stubName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                params returns yulBody) = true :=
  StubBodyStmtListUserCall.rec
    (motive_1 := fun stmt generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.functionDefStubsLoweredToEntries?
          entries stmt = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true)
    (motive_2 := fun stmts generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.List.functionDefStubsLoweredToEntries?
          entries stmts = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true)
    (motive_3 := fun cases generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?
          entries cases = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true)
    (functionBody := by
      intro name params returns body generated args hBody entries hValid
      rcases Frontend.Stmt.functionDefStubsLoweredToEntries?_functionDef_entry
          hValid with
        ⟨⟨yulBody, hBodyYul, hContains⟩, _hBodyValid⟩
      exact
        ⟨name, params, returns, body, yulBody,
          hBody, hBodyYul, hContains⟩)
    (block := by
      intro stmts generated args hList ih entries hValid
      exact ih (by
        simpa [Frontend.Stmt.functionDefStubsLoweredToEntries?]
          using hValid))
    (switchCase := by
      intro scrutinee cases default generated args hCases ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1)
    (switchDefault := by
      intro scrutinee cases default generated args hDefault ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    (forPre := by
      intro pre condition post body generated args hPre ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1.1)
    (forPost := by
      intro pre condition post body generated args hPost ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1.2)
    (forBody := by
      intro pre condition post body generated args hBody ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    (ifBody := by
      intro condition body generated args hBody ih entries hValid
      exact ih (by
        simpa [Frontend.Stmt.functionDefStubsLoweredToEntries?]
          using hValid))
    (head := by
      intro stmt rest generated args hHead ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.List.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1)
    (tail := by
      intro stmt rest generated args hTail ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.List.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    (by
      intro value body rest generated args hBody ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1)
    (by
      intro caseEntry rest generated args hTail ih entries hValid
      rcases caseEntry with ⟨value, body⟩
      have hParts := hValid
      simp [Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    hStub hValid

theorem lowered_function_entry_with_body_valid
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    ∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt),
      StmtListUserCall body generated args ∧
        Frontend.Stmt.List.toYul? body = some yulBody ∧
          entries.contains
            (stubName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                params returns yulBody) = true ∧
            Frontend.Stmt.List.functionDefStubsLoweredToEntries?
              entries body = true :=
  StubBodyStmtListUserCall.rec
    (motive_1 := fun stmt generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.functionDefStubsLoweredToEntries?
          entries stmt = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true ∧
                  Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                    entries body = true)
    (motive_2 := fun stmts generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.List.functionDefStubsLoweredToEntries?
          entries stmts = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true ∧
                  Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                    entries body = true)
    (motive_3 := fun cases generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?
          entries cases = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true ∧
                  Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                    entries body = true)
    (functionBody := by
      intro name params returns body generated args hBody entries hValid
      rcases Frontend.Stmt.functionDefStubsLoweredToEntries?_functionDef_entry
          hValid with
        ⟨⟨yulBody, hBodyYul, hContains⟩, hBodyValid⟩
      exact
        ⟨name, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid⟩)
    (block := by
      intro stmts generated args hList ih entries hValid
      exact ih (by
        simpa [Frontend.Stmt.functionDefStubsLoweredToEntries?]
          using hValid))
    (switchCase := by
      intro scrutinee cases default generated args hCases ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1)
    (switchDefault := by
      intro scrutinee cases default generated args hDefault ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    (forPre := by
      intro pre condition post body generated args hPre ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1.1)
    (forPost := by
      intro pre condition post body generated args hPost ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1.2)
    (forBody := by
      intro pre condition post body generated args hBody ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    (ifBody := by
      intro condition body generated args hBody ih entries hValid
      exact ih (by
        simpa [Frontend.Stmt.functionDefStubsLoweredToEntries?]
          using hValid))
    (head := by
      intro stmt rest generated args hHead ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.List.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1)
    (tail := by
      intro stmt rest generated args hTail ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.List.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    (by
      intro value body rest generated args hBody ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.1)
    (by
      intro caseEntry rest generated args hTail ih entries hValid
      rcases caseEntry with ⟨value, body⟩
      have hParts := hValid
      simp [Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?] at hParts
      exact ih hParts.2)
    hStub hValid

theorem lowered_function_entry_with_body_valid_size_lt
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    ∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt),
      StmtListUserCall body generated args ∧
        Frontend.Stmt.List.toYul? body = some yulBody ∧
          entries.contains
            (stubName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                params returns yulBody) = true ∧
            Frontend.Stmt.List.functionDefStubsLoweredToEntries?
              entries body = true ∧
              sizeOf body < sizeOf front :=
  StubBodyStmtListUserCall.rec
    (motive_1 := fun stmt generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.functionDefStubsLoweredToEntries?
          entries stmt = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true ∧
                  Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                    entries body = true ∧
                    sizeOf body < sizeOf stmt)
    (motive_2 := fun stmts generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.List.functionDefStubsLoweredToEntries?
          entries stmts = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true ∧
                  Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                    entries body = true ∧
                    sizeOf body < sizeOf stmts)
    (motive_3 := fun cases generated args _ =>
      ∀ {entries : List (Name × Frontend.AstFunctionDefinition)},
        Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?
          entries cases = true →
          ∃ (stubName : Name)
              (params returns : List Name)
              (body : List Frontend.Stmt)
              (yulBody : List Frontend.AstStmt),
            StmtListUserCall body generated args ∧
              Frontend.Stmt.List.toYul? body = some yulBody ∧
                entries.contains
                  (stubName,
                    EvmYul.Yul.Ast.FunctionDefinition.Def
                      params returns yulBody) = true ∧
                  Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                    entries body = true ∧
                    sizeOf body < sizeOf cases)
    (functionBody := by
      intro name params returns body generated args hBody entries hValid
      rcases Frontend.Stmt.functionDefStubsLoweredToEntries?_functionDef_entry
          hValid with
        ⟨⟨yulBody, hBodyYul, hContains⟩, hBodyValid⟩
      exact
        ⟨name, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid, by simp⟩)
    (block := by
      intro stmts generated args hList ih entries hValid
      rcases ih (by
          simpa [Frontend.Stmt.functionDefStubsLoweredToEntries?]
            using hValid) with
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp)⟩)
    (switchCase := by
      intro scrutinee cases default generated args hCases ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.1 with
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp; omega)⟩)
    (switchDefault := by
      intro scrutinee cases default generated args hDefault ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.2 with
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp)⟩)
    (forPre := by
      intro pre condition post body generated args hPre ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.1.1 with
        ⟨stubName, params, returns, body', yulBody,
          hBody, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body', yulBody,
          hBody, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp; omega)⟩)
    (forPost := by
      intro pre condition post body generated args hPost ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.1.2 with
        ⟨stubName, params, returns, body', yulBody,
          hBody, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body', yulBody,
          hBody, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp; omega)⟩)
    (forBody := by
      intro pre condition post body generated args hBody ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.2 with
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp)⟩)
    (ifBody := by
      intro condition body generated args hBody ih entries hValid
      rcases ih (by
          simpa [Frontend.Stmt.functionDefStubsLoweredToEntries?]
            using hValid) with
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp)⟩)
    (head := by
      intro stmt rest generated args hHead ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.List.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.1 with
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp; omega)⟩)
    (tail := by
      intro stmt rest generated args hTail ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.List.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.2 with
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body, yulBody,
          hBody, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp)⟩)
    (by
      intro value body rest generated args hBody ih entries hValid
      have hParts := hValid
      simp [Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.1 with
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp; omega)⟩)
    (by
      intro caseEntry rest generated args hTail ih entries hValid
      rcases caseEntry with ⟨value, body⟩
      have hParts := hValid
      simp [Frontend.Stmt.CaseList.functionDefStubsLoweredToEntries?] at hParts
      rcases ih hParts.2 with
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid, hLt⟩
      exact
        ⟨stubName, params, returns, body', yulBody,
          hBodyOccurrence, hBodyYul, hContains, hBodyValid,
          Nat.lt_trans hLt (by simp)⟩)
    hStub hValid

end StubBodyStmtListUserCall

namespace ExprListToYul

theorem mem
    {exprs : List Frontend.Expr} {yulExprs : List Frontend.AstExpr}
    {expr : Frontend.Expr}
    (hYul : Frontend.Expr.List.toYul? exprs = some yulExprs)
    (hMem : expr ∈ exprs) :
    ∃ yulExpr,
      Frontend.Expr.toYul? expr = some yulExpr ∧
        yulExpr ∈ yulExprs := by
  induction exprs generalizing yulExprs with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Frontend.Expr.List.toYul? at hYul
      cases hHead : Frontend.Expr.toYul? head with
      | none =>
          simp [hHead] at hYul
      | some yulHead =>
          cases hRest : Frontend.Expr.List.toYul? rest with
          | none =>
              simp [hHead, hRest] at hYul
          | some yulRest =>
              simp [hHead, hRest] at hYul
              subst yulExprs
              simp at hMem
              rcases hMem with hHere | hTail
              · subst expr
                exact ⟨yulHead, hHead, by simp⟩
              · rcases ih hRest hTail with
                  ⟨yulExpr, hExprYul, hYulMem⟩
                exact ⟨yulExpr, hExprYul, by simp [hYulMem]⟩

end ExprListToYul

namespace UserCall

theorem toYul?_occurrence
    {front : Frontend.Expr} {yul : Frontend.AstExpr}
    {generated : Name} {args : List Frontend.Expr}
    (hOccurrence : UserCall front generated args)
    (hYul : Frontend.Expr.toYul? front = some yul) :
    ∃ yulArgs,
      Frontend.Expr.List.toYul? args = some yulArgs ∧
        YulOccurrence.UserCall yul generated yulArgs := by
  induction hOccurrence generalizing yul with
  | here =>
      rename_i _generated callArgs
      unfold Frontend.Expr.toYul? at hYul
      cases hArgs : Frontend.Expr.List.toYul? callArgs with
      | none =>
          simp [hArgs] at hYul
      | some yulArgs =>
          simp [hArgs] at hYul
          cases hYul
          exact
            ⟨yulArgs, by simpa [hArgs],
              YulOccurrence.UserCall.here⟩
  | arg hArgMem hArgOccurrence ih =>
      rename_i kind callee callArgs _arg _generated _generatedArgs
      unfold Frontend.Expr.toYul? at hYul
      cases kind with
      | primitive =>
        cases hArgsYul : Frontend.Expr.List.toYul? callArgs with
        | none =>
            simp [hArgsYul] at hYul
        | some yulArgs =>
            cases hPrim : Frontend.Primitive.ofName? callee with
            | none =>
                simp [hPrim, hArgsYul] at hYul
            | some prim =>
                simp [hPrim, hArgsYul] at hYul
                cases hYul
                rcases ExprListToYul.mem hArgsYul hArgMem with
                  ⟨yulArg, hArgYul, hArgYulMem⟩
                rcases ih hArgYul with
                  ⟨generatedYulArgs, hGeneratedArgsYul, hYulOccurrence⟩
                exact
                  ⟨generatedYulArgs, hGeneratedArgsYul,
                    YulOccurrence.UserCall.arg hArgYulMem
                      hYulOccurrence⟩
      | user =>
        cases hArgsYul : Frontend.Expr.List.toYul? callArgs with
        | none =>
            simp [hArgsYul] at hYul
        | some yulArgs =>
            simp [hArgsYul] at hYul
            cases hYul
            rcases ExprListToYul.mem hArgsYul hArgMem with
              ⟨yulArg, hArgYul, hArgYulMem⟩
            rcases ih hArgYul with
              ⟨generatedYulArgs, hGeneratedArgsYul, hYulOccurrence⟩
            exact
              ⟨generatedYulArgs, hGeneratedArgsYul,
                YulOccurrence.UserCall.arg hArgYulMem
                  hYulOccurrence⟩
      | objectBuiltin =>
          simp at hYul
      | dialectBuiltin =>
          simp at hYul

end UserCall

namespace StmtIncomingUserCall

theorem toYul?_occurrence
    {front : Frontend.Stmt} {yul : Frontend.AstStmt}
    {generated : Name} {args : List Frontend.Expr}
    (hOccurrence : StmtIncomingUserCall front generated args)
    (hYul : Frontend.Stmt.toYul? front = some yul) :
    ∃ yulArgs,
      Frontend.Expr.List.toYul? args = some yulArgs ∧
        YulOccurrence.StmtIncomingUserCall yul generated yulArgs := by
  cases hOccurrence with
  | letValue hExprOccurrence =>
      rename_i _names value
      unfold Frontend.Stmt.toYul? at hYul
      cases hValue : Frontend.Expr.toYul? value with
      | none =>
          simp [hValue] at hYul
      | some yulValue =>
          simp [hValue] at hYul
          cases hYul
          rcases UserCall.toYul?_occurrence hExprOccurrence hValue with
            ⟨yulArgs, hArgsYul, hYulOccurrence⟩
          exact
            ⟨yulArgs, hArgsYul,
              YulOccurrence.StmtIncomingUserCall.letValue
                hYulOccurrence⟩
  | assignmentValue hExprOccurrence =>
      rename_i _names value
      unfold Frontend.Stmt.toYul? at hYul
      cases hValue : Frontend.Expr.toYul? value with
      | none =>
          simp [hValue] at hYul
      | some yulValue =>
          simp [hValue] at hYul
          cases hYul
          rcases UserCall.toYul?_occurrence hExprOccurrence hValue with
            ⟨yulArgs, hArgsYul, hYulOccurrence⟩
          exact
            ⟨yulArgs, hArgsYul,
              YulOccurrence.StmtIncomingUserCall.assignmentValue
                hYulOccurrence⟩
  | expressionStatement hExprOccurrence =>
      rename_i expr
      unfold Frontend.Stmt.toYul? at hYul
      cases hExpr : Frontend.Expr.toYul? expr with
      | none =>
          simp [hExpr] at hYul
      | some yulExpr =>
          simp [hExpr] at hYul
          cases hYul
          rcases UserCall.toYul?_occurrence hExprOccurrence hExpr with
            ⟨yulArgs, hArgsYul, hYulOccurrence⟩
          exact
            ⟨yulArgs, hArgsYul,
              YulOccurrence.StmtIncomingUserCall.expressionStatement
                hYulOccurrence⟩
  | switchScrutinee hExprOccurrence =>
      rename_i scrutinee cases default
      unfold Frontend.Stmt.toYul? at hYul
      cases hScrutinee : Frontend.Expr.toYul? scrutinee with
      | none =>
          simp [hScrutinee] at hYul
      | some yulScrutinee =>
          cases hCases : Frontend.Stmt.CaseList.toYul? cases with
          | none =>
              simp [hScrutinee, hCases] at hYul
          | some yulCases =>
              cases hDefault : Frontend.Stmt.List.toYul? default with
              | none =>
                  simp [hScrutinee, hCases, hDefault] at hYul
              | some yulDefault =>
                  simp [hScrutinee, hCases, hDefault] at hYul
                  cases hYul
                  rcases UserCall.toYul?_occurrence hExprOccurrence
                      hScrutinee with
                    ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                  exact
                    ⟨yulArgs, hArgsYul,
                      YulOccurrence.StmtIncomingUserCall.switchScrutinee
                        hYulOccurrence⟩
  | ifCondition hExprOccurrence =>
      rename_i condition body
      unfold Frontend.Stmt.toYul? at hYul
      cases hCondition : Frontend.Expr.toYul? condition with
      | none =>
          simp [hCondition] at hYul
      | some yulCondition =>
          cases hBody : Frontend.Stmt.List.toYul? body with
          | none =>
              simp [hCondition, hBody] at hYul
          | some yulBody =>
              simp [hCondition, hBody] at hYul
              cases hYul
              rcases UserCall.toYul?_occurrence hExprOccurrence
                  hCondition with
                ⟨yulArgs, hArgsYul, hYulOccurrence⟩
              exact
                ⟨yulArgs, hArgsYul,
                  YulOccurrence.StmtIncomingUserCall.ifCondition
                    hYulOccurrence⟩

end StmtIncomingUserCall

namespace LowerableStmtListUserCall

theorem toYul?_occurrence
    {front : List Frontend.Stmt}
    {yul : List Frontend.AstStmt}
    {generated : Name} {args : List Frontend.Expr}
    (hOccurrence : LowerableStmtListUserCall front generated args)
    (hYul : Frontend.Stmt.List.toYul? front = some yul) :
    ∃ yulArgs,
      Frontend.Expr.List.toYul? args = some yulArgs ∧
        YulOccurrence.StmtListUserCall yul generated yulArgs :=
  LowerableStmtListUserCall.rec
    (motive_1 := fun stmt generated args _ =>
      ∀ {yul : Frontend.AstStmt},
        Frontend.Stmt.toYul? stmt = some yul →
          ∃ yulArgs,
            Frontend.Expr.List.toYul? args = some yulArgs ∧
              YulOccurrence.StmtUserCall yul generated yulArgs)
    (motive_2 := fun stmts generated args _ =>
      ∀ {yul : List Frontend.AstStmt},
        Frontend.Stmt.List.toYul? stmts = some yul →
          ∃ yulArgs,
            Frontend.Expr.List.toYul? args = some yulArgs ∧
              YulOccurrence.StmtListUserCall yul generated yulArgs)
    (motive_3 := fun cases generated args _ =>
      ∀ {yul : List (Word × List Frontend.AstStmt)},
        Frontend.Stmt.CaseList.toYul? cases = some yul →
          ∃ yulArgs,
            Frontend.Expr.List.toYul? args = some yulArgs ∧
              YulOccurrence.CaseListUserCall yul generated yulArgs)
    (incoming := by
      intro stmt generated args hIncoming yul hYul
      rcases StmtIncomingUserCall.toYul?_occurrence hIncoming hYul with
        ⟨yulArgs, hArgsYul, hYulOccurrence⟩
      exact
        ⟨yulArgs, hArgsYul,
          YulOccurrence.StmtUserCall.incoming hYulOccurrence⟩)
    (block := by
      intro stmts generated args hBlock ih yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hStmts : Frontend.Stmt.List.toYul? stmts with
      | none =>
          simp [hStmts] at hYul
      | some yulStmts =>
          simp [hStmts] at hYul
          cases hYul
          rcases ih hStmts with
            ⟨yulArgs, hArgsYul, hYulOccurrence⟩
          exact
            ⟨yulArgs, hArgsYul,
              YulOccurrence.StmtUserCall.block hYulOccurrence⟩)
    (switchCase := by
      intro scrutinee cases default generated args hCases ih yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hScrutinee : Frontend.Expr.toYul? scrutinee with
      | none =>
          simp [hScrutinee] at hYul
      | some yulScrutinee =>
          cases hCaseList : Frontend.Stmt.CaseList.toYul? cases with
          | none =>
              simp [hScrutinee, hCaseList] at hYul
          | some yulCases =>
              cases hDefault : Frontend.Stmt.List.toYul? default with
              | none =>
                  simp [hScrutinee, hCaseList, hDefault] at hYul
              | some yulDefault =>
                  simp [hScrutinee, hCaseList, hDefault] at hYul
                  cases hYul
                  rcases ih hCaseList with
                    ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                  exact
                    ⟨yulArgs, hArgsYul,
                      YulOccurrence.StmtUserCall.switchCase
                        hYulOccurrence⟩)
    (switchDefault := by
      intro scrutinee cases default generated args hDefaultOccurrence ih yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hScrutinee : Frontend.Expr.toYul? scrutinee with
      | none =>
          simp [hScrutinee] at hYul
      | some yulScrutinee =>
          cases hCaseList : Frontend.Stmt.CaseList.toYul? cases with
          | none =>
              simp [hScrutinee, hCaseList] at hYul
          | some yulCases =>
              cases hDefault : Frontend.Stmt.List.toYul? default with
              | none =>
                  simp [hScrutinee, hCaseList, hDefault] at hYul
              | some yulDefault =>
                  simp [hScrutinee, hCaseList, hDefault] at hYul
                  cases hYul
                  rcases ih hDefault with
                    ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                  exact
                    ⟨yulArgs, hArgsYul,
                      YulOccurrence.StmtUserCall.switchDefault
                        hYulOccurrence⟩)
    (forCondition := by
      intro pre condition post body generated args hCondition yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hPre : Frontend.Stmt.List.toYul? pre with
      | none =>
          simp [hPre] at hYul
      | some yulPre =>
          cases hConditionYul : Frontend.Expr.toYul? condition with
          | none =>
              simp [hPre, hConditionYul] at hYul
          | some yulCondition =>
              cases hPost : Frontend.Stmt.List.toYul? post with
              | none =>
                  simp [hPre, hConditionYul, hPost] at hYul
              | some yulPost =>
                  cases hBody : Frontend.Stmt.List.toYul? body with
                  | none =>
                      simp [hPre, hConditionYul, hPost, hBody] at hYul
                  | some yulBody =>
                      rcases UserCall.toYul?_occurrence hCondition
                          hConditionYul with
                        ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                      cases yulPre with
                      | nil =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          exact
                            ⟨yulArgs, hArgsYul,
                              YulOccurrence.StmtUserCall.forCondition
                                hYulOccurrence⟩
                      | cons head rest =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          exact
                            ⟨yulArgs, hArgsYul,
                              YulOccurrence.StmtUserCall.block
                                (YulOccurrence.StmtListUserCall.of_last
                                  (head :: rest)
                                  (YulOccurrence.StmtUserCall.forCondition
                                    hYulOccurrence))⟩)
    (forPre := by
      intro pre condition post body generated args hPreOccurrence ih yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hPre : Frontend.Stmt.List.toYul? pre with
      | none =>
          simp [hPre] at hYul
      | some yulPre =>
          cases hConditionYul : Frontend.Expr.toYul? condition with
          | none =>
              simp [hPre, hConditionYul] at hYul
          | some yulCondition =>
              cases hPost : Frontend.Stmt.List.toYul? post with
              | none =>
                  simp [hPre, hConditionYul, hPost] at hYul
              | some yulPost =>
                  cases hBody : Frontend.Stmt.List.toYul? body with
                  | none =>
                      simp [hPre, hConditionYul, hPost, hBody] at hYul
                  | some yulBody =>
                      rcases ih hPre with
                        ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                      cases yulPre with
                      | nil =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          cases hYulOccurrence
                      | cons head rest =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          exact
                            ⟨yulArgs, hArgsYul,
                              YulOccurrence.StmtUserCall.block
                                (YulOccurrence.StmtListUserCall.append_left
                                  hYulOccurrence)⟩)
    (forPost := by
      intro pre condition post body generated args hPostOccurrence ih yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hPre : Frontend.Stmt.List.toYul? pre with
      | none =>
          simp [hPre] at hYul
      | some yulPre =>
          cases hConditionYul : Frontend.Expr.toYul? condition with
          | none =>
              simp [hPre, hConditionYul] at hYul
          | some yulCondition =>
              cases hPost : Frontend.Stmt.List.toYul? post with
              | none =>
                  simp [hPre, hConditionYul, hPost] at hYul
              | some yulPost =>
                  cases hBody : Frontend.Stmt.List.toYul? body with
                  | none =>
                      simp [hPre, hConditionYul, hPost, hBody] at hYul
                  | some yulBody =>
                      rcases ih hPost with
                        ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                      cases yulPre with
                      | nil =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          exact
                            ⟨yulArgs, hArgsYul,
                              YulOccurrence.StmtUserCall.forPost
                                hYulOccurrence⟩
                      | cons head rest =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          exact
                            ⟨yulArgs, hArgsYul,
                              YulOccurrence.StmtUserCall.block
                                (YulOccurrence.StmtListUserCall.of_last
                                  (head :: rest)
                                  (YulOccurrence.StmtUserCall.forPost
                                    hYulOccurrence))⟩)
    (forBody := by
      intro pre condition post body generated args hBodyOccurrence ih yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hPre : Frontend.Stmt.List.toYul? pre with
      | none =>
          simp [hPre] at hYul
      | some yulPre =>
          cases hConditionYul : Frontend.Expr.toYul? condition with
          | none =>
              simp [hPre, hConditionYul] at hYul
          | some yulCondition =>
              cases hPost : Frontend.Stmt.List.toYul? post with
              | none =>
                  simp [hPre, hConditionYul, hPost] at hYul
              | some yulPost =>
                  cases hBody : Frontend.Stmt.List.toYul? body with
                  | none =>
                      simp [hPre, hConditionYul, hPost, hBody] at hYul
                  | some yulBody =>
                      rcases ih hBody with
                        ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                      cases yulPre with
                      | nil =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          exact
                            ⟨yulArgs, hArgsYul,
                              YulOccurrence.StmtUserCall.forBody
                                hYulOccurrence⟩
                      | cons head rest =>
                          simp [hPre, hConditionYul, hPost, hBody] at hYul
                          cases hYul
                          exact
                            ⟨yulArgs, hArgsYul,
                              YulOccurrence.StmtUserCall.block
                                (YulOccurrence.StmtListUserCall.of_last
                                  (head :: rest)
                                  (YulOccurrence.StmtUserCall.forBody
                                    hYulOccurrence))⟩)
    (ifBody := by
      intro condition body generated args hBodyOccurrence ih yul hYul
      unfold Frontend.Stmt.toYul? at hYul
      cases hConditionYul : Frontend.Expr.toYul? condition with
      | none =>
          simp [hConditionYul] at hYul
      | some yulCondition =>
          cases hBody : Frontend.Stmt.List.toYul? body with
          | none =>
              simp [hConditionYul, hBody] at hYul
          | some yulBody =>
              simp [hConditionYul, hBody] at hYul
              cases hYul
              rcases ih hBody with
                ⟨yulArgs, hArgsYul, hYulOccurrence⟩
              exact
                ⟨yulArgs, hArgsYul,
                  YulOccurrence.StmtUserCall.ifBody hYulOccurrence⟩)
    (head := by
      intro stmt rest generated args hHeadOccurrence ih yul hYul
      unfold Frontend.Stmt.List.toYul? at hYul
      cases hHead : Frontend.Stmt.toYul? stmt with
      | none =>
          simp [hHead] at hYul
      | some yulHead =>
          cases hRest : Frontend.Stmt.List.toYul? rest with
          | none =>
              simp [hHead, hRest] at hYul
          | some yulRest =>
              simp [hHead, hRest] at hYul
              cases hYul
              rcases ih hHead with
                ⟨yulArgs, hArgsYul, hYulOccurrence⟩
              exact
                ⟨yulArgs, hArgsYul,
                  YulOccurrence.StmtListUserCall.head
                    hYulOccurrence⟩)
    (tail := by
      intro stmt rest generated args hTailOccurrence ih yul hYul
      unfold Frontend.Stmt.List.toYul? at hYul
      cases hHead : Frontend.Stmt.toYul? stmt with
      | none =>
          simp [hHead] at hYul
      | some yulHead =>
          cases hRest : Frontend.Stmt.List.toYul? rest with
          | none =>
              simp [hHead, hRest] at hYul
          | some yulRest =>
              simp [hHead, hRest] at hYul
              cases hYul
              rcases ih hRest with
                ⟨yulArgs, hArgsYul, hYulOccurrence⟩
              exact
                ⟨yulArgs, hArgsYul,
                  YulOccurrence.StmtListUserCall.tail
                    hYulOccurrence⟩)
    (by
      intro value body rest generated args hBodyOccurrence ih yul hYul
      unfold Frontend.Stmt.CaseList.toYul? at hYul
      cases hValue : Frontend.SwitchCaseValue.toWord? value with
      | none =>
          simp [hValue] at hYul
      | some yulValue =>
          cases hBody : Frontend.Stmt.List.toYul? body with
          | none =>
              simp [hValue, hBody] at hYul
          | some yulBody =>
              cases hRest : Frontend.Stmt.CaseList.toYul? rest with
              | none =>
                  simp [hValue, hBody, hRest] at hYul
              | some yulRest =>
                  simp [hValue, hBody, hRest] at hYul
                  cases hYul
                  rcases ih hBody with
                    ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                  exact
                    ⟨yulArgs, hArgsYul,
                      YulOccurrence.CaseListUserCall.head
                        hYulOccurrence⟩)
    (by
      intro caseEntry rest generated args hTailOccurrence ih yul hYul
      unfold Frontend.Stmt.CaseList.toYul? at hYul
      rcases caseEntry with ⟨value, body⟩
      cases hValue : Frontend.SwitchCaseValue.toWord? value with
      | none =>
          simp [hValue] at hYul
      | some yulValue =>
          cases hBody : Frontend.Stmt.List.toYul? body with
          | none =>
              simp [hValue, hBody] at hYul
          | some yulBody =>
              cases hRest : Frontend.Stmt.CaseList.toYul? rest with
              | none =>
                  simp [hValue, hBody, hRest] at hYul
              | some yulRest =>
                  simp [hValue, hBody, hRest] at hYul
                  cases hYul
                  rcases ih hRest with
                    ⟨yulArgs, hArgsYul, hYulOccurrence⟩
                  exact
                    ⟨yulArgs, hArgsYul,
                      YulOccurrence.CaseListUserCall.tail
                        hYulOccurrence⟩)
    hOccurrence hYul

end LowerableStmtListUserCall

namespace StubBodyStmtListUserCall

theorem lowered_function_entry_step
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    ∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt),
      Frontend.Stmt.List.toYul? body = some yulBody ∧
        entries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true ∧
          ((∃ yulArgs,
              Frontend.Expr.List.toYul? args = some yulArgs ∧
                YulOccurrence.StmtListUserCall
                  yulBody generated yulArgs) ∨
            StubBodyStmtListUserCall body generated args) := by
  rcases lowered_function_entry hStub hValid with
    ⟨stubName, params, returns, body, yulBody,
      hBodyOccurrence, hBodyYul, hContains⟩
  rcases StmtListUserCall.lowerable_or_stubBody hBodyOccurrence with
    hLowerable | hNestedStub
  · rcases LowerableStmtListUserCall.toYul?_occurrence
      hLowerable hBodyYul with
      ⟨yulArgs, hArgsYul, hYulOccurrence⟩
    exact
      ⟨stubName, params, returns, body, yulBody,
        hBodyYul, hContains,
        Or.inl ⟨yulArgs, hArgsYul, hYulOccurrence⟩⟩
  · exact
      ⟨stubName, params, returns, body, yulBody,
        hBodyYul, hContains, Or.inr hNestedStub⟩

theorem lowered_function_entry_step_with_valid
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    (∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      Frontend.Stmt.List.toYul? body = some yulBody ∧
        entries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true ∧
          Frontend.Expr.List.toYul? args = some yulArgs ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∨
      ∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt),
        Frontend.Stmt.List.toYul? body = some yulBody ∧
          entries.contains
            (stubName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                params returns yulBody) = true ∧
            StubBodyStmtListUserCall body generated args ∧
              Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                entries body = true := by
  rcases lowered_function_entry_with_body_valid hStub hValid with
    ⟨stubName, params, returns, body, yulBody,
      hBodyOccurrence, hBodyYul, hContains, hBodyValid⟩
  rcases StmtListUserCall.lowerable_or_stubBody hBodyOccurrence with
    hLowerable | hNestedStub
  · rcases LowerableStmtListUserCall.toYul?_occurrence
      hLowerable hBodyYul with
      ⟨yulArgs, hArgsYul, hYulOccurrence⟩
    exact
      Or.inl
        ⟨stubName, params, returns, body, yulBody, yulArgs,
          hBodyYul, hContains, hArgsYul, hYulOccurrence⟩
  · exact
      Or.inr
        ⟨stubName, params, returns, body, yulBody,
          hBodyYul, hContains, hNestedStub, hBodyValid⟩

theorem lowered_function_entry_step_with_valid_decreasing
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    (∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      Frontend.Stmt.List.toYul? body = some yulBody ∧
        entries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true ∧
          Frontend.Expr.List.toYul? args = some yulArgs ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∨
      ∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt),
        Frontend.Stmt.List.toYul? body = some yulBody ∧
          entries.contains
            (stubName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                params returns yulBody) = true ∧
            StubBodyStmtListUserCall body generated args ∧
              Frontend.Stmt.List.functionDefStubsLoweredToEntries?
                entries body = true ∧
                sizeOf body < sizeOf front := by
  rcases lowered_function_entry_with_body_valid_size_lt hStub hValid with
    ⟨stubName, params, returns, body, yulBody,
      hBodyOccurrence, hBodyYul, hContains, hBodyValid, hLt⟩
  rcases StmtListUserCall.lowerable_or_stubBody hBodyOccurrence with
    hLowerable | hNestedStub
  · rcases LowerableStmtListUserCall.toYul?_occurrence
      hLowerable hBodyYul with
      ⟨yulArgs, hArgsYul, hYulOccurrence⟩
    exact
      Or.inl
        ⟨stubName, params, returns, body, yulBody, yulArgs,
          hBodyYul, hContains, hArgsYul, hYulOccurrence⟩
  · exact
      Or.inr
        ⟨stubName, params, returns, body, yulBody,
          hBodyYul, hContains, hNestedStub, hBodyValid, hLt⟩

theorem lowered_function_entry_chaseFuel
    (fuel : Nat)
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    (∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      Frontend.Stmt.List.toYul? body = some yulBody ∧
        entries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true ∧
          Frontend.Expr.List.toYul? args = some yulArgs ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∨
      ∃ body,
        StubBodyStmtListUserCall body generated args ∧
          Frontend.Stmt.List.functionDefStubsLoweredToEntries?
            entries body = true := by
  induction fuel generalizing front with
  | zero =>
      exact Or.inr ⟨front, hStub, hValid⟩
  | succ fuel ih =>
      rcases lowered_function_entry_step_with_valid hStub hValid with
        hFound | hNext
      · exact Or.inl hFound
      · rcases hNext with
          ⟨_stubName, _params, _returns, body, _yulBody,
            _hBodyYul, _hContains, hNestedStub, hBodyValid⟩
        exact ih hNestedStub hBodyValid

theorem lowered_function_entry_chase
    {front : List Frontend.Stmt}
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {generated : Name} {args : List Frontend.Expr}
    (hStub : StubBodyStmtListUserCall front generated args)
    (hValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        entries front = true) :
    ∃ (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      Frontend.Stmt.List.toYul? body = some yulBody ∧
        entries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true ∧
          Frontend.Expr.List.toYul? args = some yulArgs ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs := by
  rcases lowered_function_entry_step_with_valid_decreasing hStub hValid with
    hFound | hNext
  · exact hFound
  · rcases hNext with
      ⟨_stubName, _params, _returns, body, _yulBody,
        _hBodyYul, _hContains, hNestedStub, hBodyValid, hLt⟩
    exact lowered_function_entry_chase hNestedStub hBodyValid
termination_by sizeOf front
decreasing_by exact hLt

end StubBodyStmtListUserCall

/--
Generated frontend realization of a raw source-local call.

The relation deliberately hides the generated alpha-renamed callee from the
source-facing API while still requiring both sides of resolution: the caller
function contains the generated `.user` call and the generated callee is a
callable entry in the same frontend function table.
-/
def ResolvedLocalCall
    (functions : List (Name × Frontend.FunctionDef))
    (topName : Name) : Prop :=
  ∃ (generated : Name)
      (localFn : Frontend.FunctionDef)
      (args : List Frontend.Expr)
      (topFn : Frontend.FunctionDef),
    (topName, topFn) ∈ functions ∧
      StmtListUserCall topFn.body generated args ∧
        (generated, localFn) ∈ functions

/--
Resolved local call whose occurrence lowers into the current caller function
body. This is deliberately stricter than `ResolvedLocalCall`: retained
`functionDef` staging-node bodies are emitted as separate generated functions,
not as statements in the caller's lowered body.
-/
def LowerableResolvedLocalCall
    (functions : List (Name × Frontend.FunctionDef))
    (topName : Name) : Prop :=
  ∃ (generated : Name)
      (localFn : Frontend.FunctionDef)
      (args : List Frontend.Expr)
      (topFn : Frontend.FunctionDef),
    (topName, topFn) ∈ functions ∧
      LowerableStmtListUserCall topFn.body generated args ∧
        (generated, localFn) ∈ functions

/--
Resolved local call whose occurrence is inside a retained `functionDef` staging
body, and therefore must be followed through the generated function-entry route.
-/
def StubBodyResolvedLocalCall
    (functions : List (Name × Frontend.FunctionDef))
    (topName : Name) : Prop :=
  ∃ (generated : Name)
      (localFn : Frontend.FunctionDef)
      (args : List Frontend.Expr)
      (topFn : Frontend.FunctionDef),
    (topName, topFn) ∈ functions ∧
      StubBodyStmtListUserCall topFn.body generated args ∧
        (generated, localFn) ∈ functions

namespace ResolvedLocalCall

theorem lowerable_or_stubBody
    {functions : List (Name × Frontend.FunctionDef)}
    {topName : Name}
    (hResolved : ResolvedLocalCall functions topName) :
    LowerableResolvedLocalCall functions topName ∨
      StubBodyResolvedLocalCall functions topName := by
  rcases hResolved with
    ⟨generated, localFn, args, topFn,
      hTopMem, hOccurrence, hCalleeMem⟩
  rcases StmtListUserCall.lowerable_or_stubBody hOccurrence with
    hLowerable | hStub
  · exact
      Or.inl
        ⟨generated, localFn, args, topFn,
          hTopMem, hLowerable, hCalleeMem⟩
  · exact
      Or.inr
        ⟨generated, localFn, args, topFn,
          hTopMem, hStub, hCalleeMem⟩

end ResolvedLocalCall

private theorem functionDefList_functionDefStubsLoweredToEntries?_of_mem
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    {functions : List (Name × Frontend.FunctionDef)}
    {name : Name} {fn : Frontend.FunctionDef}
    (hValid :
      Frontend.FunctionDef.List.functionDefStubsLoweredToEntries?
        entries functions = true)
    (hMem : (name, fn) ∈ functions) :
    Frontend.Stmt.List.functionDefStubsLoweredToEntries?
      entries fn.body = true := by
  induction functions with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      rcases head with ⟨headName, headFn⟩
      have hParts := hValid
      simp [Frontend.FunctionDef.List.functionDefStubsLoweredToEntries?]
        at hParts
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl⟩
        exact hParts.1
      · exact ih hParts.2 hTail

namespace LowerableResolvedLocalCall

theorem toSolcYulOrderedProgram?_entries
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Name}
    (hResolved :
      LowerableResolvedLocalCall object.functions topName)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (topFn : Frontend.FunctionDef)
        (topYulBody localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (topName, topFn) ∈ object.functions ∧
        LowerableStmtListUserCall topFn.body generated frontArgs ∧
        (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        YulOccurrence.StmtListUserCall topYulBody generated yulArgs ∧
        (topName,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            topFn.params topFn.returns topYulBody) ∈
          ordered.functionEntries ∧
        (generated,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            localFn.params localFn.returns localYulBody) ∈
          ordered.functionEntries := by
  rcases hResolved with
    ⟨generated, localFn, frontArgs, topFn,
      hTopMem, hOccurrence, hCalleeMem⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_function_entry
      hConvert hTopMem with
    ⟨topYulBody, hTopYul, hTopEntry⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_function_entry
      hConvert hCalleeMem with
    ⟨localYulBody, hLocalYul, hLocalEntry⟩
  rcases LowerableStmtListUserCall.toYul?_occurrence
      hOccurrence hTopYul with
    ⟨yulArgs, hArgsYul, hYulOccurrence⟩
  exact
    ⟨generated, localFn, frontArgs, topFn, topYulBody, localYulBody,
      yulArgs, hTopMem, hOccurrence, hCalleeMem, hTopYul, hLocalYul,
      hArgsYul, hYulOccurrence, hTopEntry, hLocalEntry⟩

end LowerableResolvedLocalCall

namespace StubBodyResolvedLocalCall

theorem toSolcYulOrderedProgram?_chase
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Name}
    (hResolved :
      StubBodyResolvedLocalCall object.functions topName)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (topFn : Frontend.FunctionDef)
        (stubName : Name)
        (params returns : List Name)
        (body : List Frontend.Stmt)
        (yulBody localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (topName, topFn) ∈ object.functions ∧
        StubBodyStmtListUserCall topFn.body generated frontArgs ∧
        (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? body = some yulBody ∧
        ordered.functionEntries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        YulOccurrence.StmtListUserCall yulBody generated yulArgs ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        (generated,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            localFn.params localFn.returns localYulBody) ∈
          ordered.functionEntries := by
  rcases hResolved with
    ⟨generated, localFn, frontArgs, topFn,
      hTopMem, hOccurrence, hCalleeMem⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_function_entry
      hConvert hCalleeMem with
    ⟨localYulBody, hLocalYul, hLocalEntry⟩
  have hObjectValid :=
    Frontend.Object.toSolcYulOrderedProgram?_functionDefStubsLoweredToEntries
      hConvert
  have hObjectParts := hObjectValid
  simp [Frontend.Object.functionDefStubsLoweredToEntries?] at hObjectParts
  have hTopValid :
      Frontend.Stmt.List.functionDefStubsLoweredToEntries?
        ordered.functionEntries topFn.body = true :=
    functionDefList_functionDefStubsLoweredToEntries?_of_mem
      hObjectParts.2 hTopMem
  rcases StubBodyStmtListUserCall.lowered_function_entry_chase
      hOccurrence hTopValid with
    ⟨stubName, params, returns, body, yulBody, yulArgs,
      hBodyYul, hContains, hArgsYul, hYulOccurrence⟩
  exact
    ⟨generated, localFn, frontArgs, topFn, stubName, params, returns,
      body, yulBody, localYulBody, yulArgs, hTopMem, hOccurrence,
      hCalleeMem, hBodyYul, hContains, hArgsYul, hYulOccurrence,
      hLocalYul, hLocalEntry⟩

end StubBodyResolvedLocalCall

end FrontendOccurrence

namespace Raw
namespace Source

/--
Source-facing alpha-renaming preservation for a raw local function call.

This is the frontend theorem boundary for solc-emitted nested functions: a raw
block declares a local function under the source spelling `name`, a resolver-safe
source call to that spelling occurs in the same body, and checked elaboration
realizes that source fact as a generated frontend caller/callee resolution.
-/
structure AlphaRenamedLocalCallPreserved
    (topBody : List Stmt)
    (functions : List (Name × Frontend.FunctionDef))
    (topName name : Name)
    (localParams localReturns : List Name)
    (localBody : List Stmt)
    (args : List Expr) : Prop where
  source_local :
    LocalFunction topBody name localParams localReturns localBody
  source_call :
    NoShadowStmtListCall topBody name args
  resolved :
    FrontendOccurrence.ResolvedLocalCall functions topName

namespace AlphaRenamedLocalCallPreserved

private theorem lookup_foldl_insert_of_not_mem
    (entries : List (Name × Frontend.AstFunctionDefinition))
    (state :
      Finmap (fun (_ : Name) => Frontend.AstFunctionDefinition))
    (name : Name)
    (hNotMem : name ∉ entries.map Prod.fst) :
    (entries.foldl
        (fun acc entry => acc.insert entry.fst entry.snd) state).lookup name =
      state.lookup name := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨headName, headFn⟩
      simp only [List.map_cons, List.mem_cons, not_or] at hNotMem
      rw [List.foldl_cons, ih _ hNotMem.2]
      exact Finmap.lookup_insert_of_ne state hNotMem.1

private theorem lookup_foldl_insert_of_mem
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    (hNames : (entries.map Prod.fst).Nodup)
    {name : Name} {fn : Frontend.AstFunctionDefinition}
    (hMem : (name, fn) ∈ entries)
    (state :
      Finmap (fun (_ : Name) => Frontend.AstFunctionDefinition)) :
    (entries.foldl
        (fun acc entry => acc.insert entry.fst entry.snd) state).lookup name =
      some fn := by
  induction entries generalizing state with
  | nil =>
      simp at hMem
  | cons entry rest ih =>
      rcases entry with ⟨headName, headFn⟩
      simp only [List.map_cons, List.nodup_cons] at hNames
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl⟩
        rw [List.foldl_cons,
          lookup_foldl_insert_of_not_mem rest _ name hNames.1]
        exact Finmap.lookup_insert _
      · rw [List.foldl_cons]
        exact ih hNames.2 hTail _

private theorem lookup_functionMap_of_mem
    {entries : List (Name × Frontend.AstFunctionDefinition)}
    (hNames : (entries.map Prod.fst).Nodup)
    {name : Name} {fn : Frontend.AstFunctionDefinition}
    (hMem : (name, fn) ∈ entries) :
    (Yul.FunctionList.functionMap entries).lookup name = some fn := by
  exact lookup_foldl_insert_of_mem hNames hMem _

theorem of_entries
    {topBody : List Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {topName name : Name}
    {localParams localReturns : List Name}
    {localBody : List Stmt}
    {args : List Expr}
    {generated : Name}
    {localFn : Frontend.FunctionDef}
    {frontArgs : List Frontend.Expr}
    {topFn : Frontend.FunctionDef}
    (hLocal :
      LocalFunction topBody name localParams localReturns localBody)
    (hOccurs : NoShadowStmtListCall topBody name args)
    (hTop : (topName, topFn) ∈ functions)
    (hOccurrence :
      FrontendOccurrence.StmtListUserCall
        topFn.body generated frontArgs)
    (hCallee : (generated, localFn) ∈ functions) :
    AlphaRenamedLocalCallPreserved topBody functions topName name
      localParams localReturns localBody args :=
  { source_local := hLocal
    source_call := hOccurs
    resolved :=
      ⟨generated, localFn, frontArgs, topFn,
        hTop, hOccurrence, hCallee⟩ }

theorem resolveObjectBuiltinsPreserved
    {topBody : List Stmt}
    {object resolved : Frontend.Object}
    {context : Frontend.ObjectBuiltinContext}
    {topName name : Name}
    {localParams localReturns : List Name}
    {localBody : List Stmt}
    {args : List Expr}
    (hAlpha :
      AlphaRenamedLocalCallPreserved topBody object.functions topName name
        localParams localReturns localBody args)
    (hResolve :
      object.resolveObjectBuiltinsIn? context = some resolved) :
    AlphaRenamedLocalCallPreserved topBody resolved.functions topName name
      localParams localReturns localBody args := by
  rcases hAlpha.resolved with
    ⟨generated, localFn, frontArgs, topFn,
      hTopMem, hOccurrence, hCalleeMem⟩
  rcases Frontend.Object.resolveObjectBuiltinsIn?_function_entry
      hResolve hTopMem with
    ⟨_memoryContract, topResolvedFn, _hMemory, hTopResolve,
      hTopResolvedMem, _hTopParams, _hTopReturns⟩
  rcases Frontend.FunctionDef.resolveObjectBuiltinsIn?_body
      hTopResolve with
    ⟨topResolvedBody, hTopBodyResolve, hTopResolvedEq⟩
  rcases
      FrontendOccurrence.StmtListUserCall.resolveObjectBuiltinsIn?_occurrence
        hTopBodyResolve hOccurrence with
    ⟨resolvedArgs, _hResolvedArgs, hResolvedOccurrence⟩
  rcases Frontend.Object.resolveObjectBuiltinsIn?_function_entry
      hResolve hCalleeMem with
    ⟨_localMemoryContract, localResolvedFn, _hLocalMemory,
      _hLocalResolve, hLocalResolvedMem, _hLocalParams,
      _hLocalReturns⟩
  have hOccurrence' :
      FrontendOccurrence.StmtListUserCall
        topResolvedFn.body generated resolvedArgs := by
    rw [hTopResolvedEq]
    exact hResolvedOccurrence
  exact
    { source_local := hAlpha.source_local
      source_call := hAlpha.source_call
      resolved :=
        ⟨generated, localResolvedFn, resolvedArgs, topResolvedFn,
          hTopResolvedMem, hOccurrence', hLocalResolvedMem⟩ }

theorem toSolcYulOrderedProgram?_entries
    {topBody : List Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Name}
    {localParams localReturns : List Name}
    {localBody : List Stmt}
    {args : List Expr}
    (hAlpha :
      AlphaRenamedLocalCallPreserved topBody object.functions topName name
        localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (topFn : Frontend.FunctionDef)
        (topYulBody localYulBody : List Frontend.AstStmt),
      (topName, topFn) ∈ object.functions ∧
        FrontendOccurrence.StmtListUserCall
          topFn.body generated frontArgs ∧
        (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        (topName,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            topFn.params topFn.returns topYulBody) ∈
          ordered.functionEntries ∧
        (generated,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            localFn.params localFn.returns localYulBody) ∈
          ordered.functionEntries := by
  rcases hAlpha.resolved with
    ⟨generated, localFn, frontArgs, topFn,
      hTopMem, hOccurrence, hCalleeMem⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_function_entry
      hConvert hTopMem with
    ⟨topYulBody, hTopYul, hTopEntry⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_function_entry
      hConvert hCalleeMem with
    ⟨localYulBody, hLocalYul, hLocalEntry⟩
  exact
    ⟨generated, localFn, frontArgs, topFn, topYulBody, localYulBody,
      hTopMem, hOccurrence, hCalleeMem, hTopYul, hLocalYul,
      hTopEntry, hLocalEntry⟩

theorem toSolcYulOrderedProgram?_callable_entries
    {topBody : List Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Name}
    {localParams localReturns : List Name}
    {localBody : List Stmt}
    {args : List Expr}
    (hAlpha :
      AlphaRenamedLocalCallPreserved topBody object.functions topName name
        localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (topFn : Frontend.FunctionDef)
        (topYulBody localYulBody : List Frontend.AstStmt),
      (topName, topFn) ∈ object.functions ∧
        FrontendOccurrence.StmtListUserCall
          topFn.body generated frontArgs ∧
        (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        ordered.program.contract.functions.lookup topName =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              topFn.params topFn.returns topYulBody) ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) := by
  rcases toSolcYulOrderedProgram?_entries hAlpha hConvert with
    ⟨generated, localFn, frontArgs, topFn, topYulBody, localYulBody,
      hTopMem, hOccurrence, hCalleeMem, hTopYul, hLocalYul,
      hTopEntry, hLocalEntry⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_source hConvert with
    ⟨hRepresents, hNames, _hProgramOk, _hMemory⟩
  have hTopLookup :
      ordered.program.contract.functions.lookup topName =
        some
          (EvmYul.Yul.Ast.FunctionDefinition.Def
            topFn.params topFn.returns topYulBody) := by
    rw [hRepresents]
    exact lookup_functionMap_of_mem hNames hTopEntry
  have hCalleeLookup :
      ordered.program.contract.functions.lookup generated =
        some
          (EvmYul.Yul.Ast.FunctionDefinition.Def
            localFn.params localFn.returns localYulBody) := by
    rw [hRepresents]
    exact lookup_functionMap_of_mem hNames hLocalEntry
  exact
    ⟨generated, localFn, frontArgs, topFn, topYulBody, localYulBody,
      hTopMem, hOccurrence, hCalleeMem, hTopYul, hLocalYul,
      hTopLookup, hCalleeLookup⟩

theorem toSolcYulOrderedProgram?_call_occurrence_routes
    {topBody : List Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Name}
    {localParams localReturns : List Name}
    {localBody : List Stmt}
    {args : List Expr}
    (hAlpha :
      AlphaRenamedLocalCallPreserved topBody object.functions topName name
        localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        (generated,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            localFn.params localFn.returns localYulBody) ∈
          ordered.functionEntries ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Name)
            (params returns : List Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) := by
  rcases FrontendOccurrence.ResolvedLocalCall.lowerable_or_stubBody
      hAlpha.resolved with
    hLowerable | hStub
  · rcases
      FrontendOccurrence.LowerableResolvedLocalCall.toSolcYulOrderedProgram?_entries
        hLowerable hConvert with
      ⟨generated, localFn, frontArgs, topFn, topYulBody, localYulBody,
        yulArgs, hTopMem, hOccurrence, hCalleeMem, hTopYul,
        hLocalYul, hArgsYul, hYulOccurrence, hTopEntry, hLocalEntry⟩
    exact
      ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
        hCalleeMem, hLocalYul, hArgsYul, hLocalEntry,
        Or.inl
          ⟨topFn, topYulBody, hTopMem, hOccurrence, hTopYul,
            hYulOccurrence, hTopEntry⟩⟩
  · rcases
      FrontendOccurrence.StubBodyResolvedLocalCall.toSolcYulOrderedProgram?_chase
        hStub hConvert with
      ⟨generated, localFn, frontArgs, topFn, stubName, params, returns,
        body, yulBody, localYulBody, yulArgs, hTopMem, hOccurrence,
        hCalleeMem, hBodyYul, hContains, hArgsYul, hYulOccurrence,
        hLocalYul, hLocalEntry⟩
    exact
      ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
        hCalleeMem, hLocalYul, hArgsYul, hLocalEntry,
        Or.inr
          ⟨topFn, stubName, params, returns, body, yulBody,
            hTopMem, hOccurrence, hBodyYul, hContains,
            hYulOccurrence⟩⟩

theorem toSolcYulOrderedProgram?_call_occurrence_routes_lookup
    {topBody : List Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Name}
    {localParams localReturns : List Name}
    {localBody : List Stmt}
    {args : List Expr}
    (hAlpha :
      AlphaRenamedLocalCallPreserved topBody object.functions topName name
        localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Name)
            (params returns : List Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) := by
  rcases toSolcYulOrderedProgram?_call_occurrence_routes
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hLocalEntry, hRoutes⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_source hConvert with
    ⟨hRepresents, hNames, _hProgramOk, _hMemory⟩
  have hLookup :
      ordered.program.contract.functions.lookup generated =
        some
          (EvmYul.Yul.Ast.FunctionDefinition.Def
            localFn.params localFn.returns localYulBody) := by
    rw [hRepresents]
    exact lookup_functionMap_of_mem hNames hLocalEntry
  exact
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hLookup, hRoutes⟩

end AlphaRenamedLocalCallPreserved

end Source
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

theorem collectDeclaredIdentifiers_single_bindingNameOk
    {name : Name} {description : String} {scopes : List (List Name)}
    {seen : List Name}
    (hCollect :
      collectDeclaredIdentifiers [name] description scopes = .ok seen) :
    bindingNameOk? name = true := by
  cases hOk : bindingNameOk? name with
  | false =>
      simp [collectDeclaredIdentifiers, collectDeclaredIdentifiers.loop,
        hOk] at hCollect
  | true =>
      rfl

theorem declareIdentifiers_single_bindingNameOk
    {name : Name} {description : String} {state state' : State}
    (hDeclare :
      (declareIdentifiers [name] description).run state =
        .ok ((), state')) :
    bindingNameOk? name = true := by
  unfold declareIdentifiers at hDeclare
  simp [StateT.run_bind, StateT.run_get] at hDeclare
  cases hScopes : state.identifierScopes with
  | nil =>
      simp [hScopes] at hDeclare
      cases hCollect :
          collectDeclaredIdentifiers [name] description [[]] with
      | error err =>
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hDeclare
          simp [hCollect, StateT.run_map, Functor.map] at hDeclare
          change Except.map
              (fun a : List Name × State => (PUnit.unit,
                { state with identifierScopes := [a.1] }))
              (Except.error err) = Except.ok ((), state') at hDeclare
          cases hDeclare
      | ok seen =>
          exact collectDeclaredIdentifiers_single_bindingNameOk hCollect
  | cons scope rest =>
      simp [hScopes] at hDeclare
      cases hCollect :
          collectDeclaredIdentifiers [name] description (scope :: rest) with
      | error err =>
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hDeclare
          simp [hCollect, StateT.run_map, Functor.map] at hDeclare
          change Except.map
              (fun a : List Name × State => (PUnit.unit,
                { state with identifierScopes := (a.1 ++ scope) :: rest }))
              (Except.error err) = Except.ok ((), state') at hDeclare
          cases hDeclare
      | ok seen =>
          exact collectDeclaredIdentifiers_single_bindingNameOk hCollect

theorem bindingNameOk_ne_memoryguard
    {name : Name} (hOk : bindingNameOk? name = true) :
    name ≠ "memoryguard" := by
  intro hName
  subst name
  simp [bindingNameOk?, CallClass.reservedBindingName?,
    CallClass.objectBuiltins] at hOk

theorem bindingNameOk_ne_clz
    {name : Name} (hOk : bindingNameOk? name = true) :
    name ≠ "clz" := by
  intro hName
  subst name
  simp [bindingNameOk?, CallClass.reservedBindingName?] at hOk

theorem bindingNameOk_classifyCall_user
    {name : Name} (hOk : bindingNameOk? name = true) :
    CallClass.classifyCall name = .user := by
  have hReserved : CallClass.reservedBindingName? name = false := by
    cases hReserved : CallClass.reservedBindingName? name with
    | false => rfl
    | true =>
        simp [bindingNameOk?, hReserved] at hOk
  unfold CallClass.classifyCall
  cases hPrim : Frontend.Primitive.ofName? name with
  | some prim =>
      unfold CallClass.reservedBindingName? at hReserved
      simp [hPrim] at hReserved
  | none =>
      simp [hPrim]
      unfold CallClass.reservedBindingName? at hReserved
      simp [hPrim] at hReserved
      by_cases hObject : name ∈ CallClass.objectBuiltins
      · exact False.elim (hReserved.1.1 hObject)
      · simp [hObject]
        cases hDialect : CallClass.unsupportedDialectBuiltin? name with
        | true =>
            rw [hDialect] at hReserved
            cases hReserved.1.2
        | false =>
            simp [hObject, hDialect]

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

def PreservesFunctionScopes {α : Type} (action : ElabM α) : Prop :=
  ∀ {state state' : State} {value : α},
    action.run state = .ok (value, state') →
      state'.functionScopes = state.functionScopes

theorem PreservesFunctionScopes.bind {α β : Type}
    {action : ElabM α} {next : α → ElabM β}
    (hAction : PreservesFunctionScopes action)
    (hNext : ∀ value, PreservesFunctionScopes (next value)) :
    PreservesFunctionScopes (action >>= next) := by
  intro state state' value hRun
  simp [StateT.run_bind] at hRun
  cases hActionRun : action.run state with
  | error _ =>
      simp [hActionRun] at hRun
  | ok result =>
      rcases result with ⟨midValue, midState⟩
      have hMid := hAction hActionRun
      simp [hActionRun] at hRun
      have hFinal := hNext midValue hRun
      exact hFinal.trans hMid

theorem PreservesFunctionScopes.map {α β : Type} {action : ElabM α}
    (f : α → β) (hAction : PreservesFunctionScopes action) :
    PreservesFunctionScopes (f <$> action) := by
  intro state state' value hRun
  simp [StateT.run_map] at hRun
  cases hActionRun : action.run state with
  | error _ =>
      simp [hActionRun] at hRun
  | ok result =>
      rcases result with ⟨_midValue, midState⟩
      have hMid := hAction hActionRun
      simp [hActionRun] at hRun
      rcases hRun with ⟨_hValue, hState⟩
      subst state'
      exact hMid

theorem PreservesFunctionScopes.pure {α : Type} (value : α) :
    PreservesFunctionScopes (pure value : ElabM α) := by
  intro state state' result hRun
  simp [StateT.run_pure] at hRun
  cases hRun
  rfl

theorem PreservesFunctionScopes.throw {α : Type} (message : String) :
    PreservesFunctionScopes (throw message : ElabM α) := by
  intro state state' value hRun
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

theorem requireIdentifierVisible_preserves_functionScopes
    (name : Name) (what : String) :
    PreservesFunctionScopes (requireIdentifierVisible name what) := by
  intro state state' value hRun
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
      rfl

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

theorem requireIdentifiersVisible_preserves_functionScopes
    (names : List Name) (what : String) :
    PreservesFunctionScopes (requireIdentifiersVisible names what) := by
  induction names with
  | nil =>
      simp [requireIdentifiersVisible]
      exact PreservesFunctionScopes.pure ()
  | cons name rest ih =>
      change PreservesFunctionScopes
        (requireIdentifierVisible name what >>= fun _ =>
          requireIdentifiersVisible rest what)
      exact
        PreservesFunctionScopes.bind
          (requireIdentifierVisible_preserves_functionScopes name what)
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

theorem declareIdentifiers_preserves_functionScopes
    (names : List Name) (description : String) :
    PreservesFunctionScopes (declareIdentifiers names description) := by
  intro state state' value hRun
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
          rfl
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
          rfl

theorem hoistFunctionEntry_preserves_hoistedFunction_mem
    (generated : Name) (fn : Frontend.FunctionDef) :
    PreservesHoisted (modify fun state =>
      { state with hoistedFunctions := (generated, fn) ::
        state.hoistedFunctions }) := by
  intro state state' value entry hRun hEntry
  simp [StateT.run_modify] at hRun
  cases hRun
  exact List.mem_cons_of_mem (generated, fn) hEntry

theorem hoistFunctionEntry_preserves_functionScopes
    (generated : Name) (fn : Frontend.FunctionDef) :
    PreservesFunctionScopes (modify fun state =>
      { state with hoistedFunctions := (generated, fn) ::
        state.hoistedFunctions }) := by
  intro state state' value hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  rfl

theorem pushIdentifierScope_preserves_hoistedFunction_mem :
    PreservesHoisted pushIdentifierScope := by
  intro state state' value entry hRun hEntry
  unfold pushIdentifierScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  exact hEntry

theorem pushIdentifierScope_preserves_functionScopes :
    PreservesFunctionScopes pushIdentifierScope := by
  intro state state' value hRun
  unfold pushIdentifierScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  rfl

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

theorem popIdentifierScope_preserves_functionScopes :
    PreservesFunctionScopes popIdentifierScope := by
  intro state state' value hRun
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
      rfl

theorem pushFunctionScope_preserves_hoistedFunction_mem
    (scope : List (Name × Name)) :
    PreservesHoisted (pushFunctionScope scope) := by
  intro state state' value entry hRun hEntry
  unfold pushFunctionScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  exact hEntry

theorem pushFunctionScope_functionScopes
    {scope : List (Name × Name)} {state state' : State}
    (hRun : (pushFunctionScope scope).run state = .ok ((), state')) :
    state'.functionScopes = scope :: state.functionScopes := by
  unfold pushFunctionScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  rfl

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

theorem popFunctionScope_functionScopes
    {state state' : State} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    (hScopes : state.functionScopes = scope :: outer)
    (hRun : popFunctionScope.run state = .ok ((), state')) :
    state'.functionScopes = outer := by
  unfold popFunctionScope at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  rw [hScopes] at hRun
  simp [StateT.run_set] at hRun
  cases hRun
  rfl

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

theorem resolveFunction_preserves_functionScopes (name : Name) :
    PreservesFunctionScopes (resolveFunction name) := by
  intro state state' value hRun
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
      rfl

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

theorem freshGeneratedFunctionNameFrom_preserves_functionScopes
    (stem : Name) (fuel : Nat) :
    PreservesFunctionScopes (freshGeneratedFunctionNameFrom stem fuel) := by
  induction fuel with
  | zero =>
      intro state state' value hRun
      unfold freshGeneratedFunctionNameFrom at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "could not allocate fresh generated Yul function name" :
          DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | succ fuel ih =>
      intro state state' value hRun
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
        have hMid := ih hRun
        simpa [bumpedState] using hMid
      · simp [hContains, StateT.run_map, StateT.run_set] at hRun
        simp [pure, Except.pure] at hRun
        rcases hRun with ⟨_hValue, hState⟩
        subst state'
        rfl

theorem freshGeneratedFunctionName_preserves_functionScopes
    (base : Name) :
    PreservesFunctionScopes (freshGeneratedFunctionName base) := by
  unfold freshGeneratedFunctionName
  exact
    freshGeneratedFunctionNameFrom_preserves_functionScopes
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

theorem freshNonFunctionBindingNameFrom_preserves_functionScopes
    (stem : Name) (index fuel : Nat) :
    PreservesFunctionScopes
      (freshNonFunctionBindingNameFrom stem index fuel) := by
  induction fuel generalizing index with
  | zero =>
      intro state state' value hRun
      unfold freshNonFunctionBindingNameFrom at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "could not allocate fresh generated Yul binding name" :
          DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | succ fuel ih =>
      intro state state' value hRun
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
        exact ih (index + 1) hRun
      · simp [hContains, StateT.run_map, StateT.run_set] at hRun
        simp [pure, Except.pure] at hRun
        rcases hRun with ⟨_hValue, hState⟩
        subst state'
        rfl

theorem freshNonFunctionBindingName_preserves_functionScopes
    (base : Name) :
    PreservesFunctionScopes (freshNonFunctionBindingName base) := by
  unfold freshNonFunctionBindingName
  exact
    freshNonFunctionBindingNameFrom_preserves_functionScopes
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

theorem ensureClzHelper_preserves_functionScopes :
    PreservesFunctionScopes ensureClzHelper := by
  intro state state' value hRun
  unfold ensureClzHelper at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hHelper : state.clzHelperName? with
  | some _ =>
      simp [hHelper] at hRun
      cases hRun
      rfl
  | none =>
      simp [hHelper] at hRun
      cases hFreshHelper :
          (freshGeneratedFunctionName "clz").run state with
      | error _ =>
          simp [hFreshHelper] at hRun
      | ok helperResult =>
          rcases helperResult with ⟨helper, helperState⟩
          have hHelperScopes :
              helperState.functionScopes = state.functionScopes :=
            freshGeneratedFunctionName_preserves_functionScopes
              "clz" hFreshHelper
          simp [hFreshHelper] at hRun
          cases hFreshArg :
              (freshNonFunctionBindingName "clz_arg").run helperState with
          | error _ =>
              simp [hFreshArg] at hRun
          | ok argResult =>
              rcases argResult with ⟨arg, argState⟩
              have hArgScopes :
                  argState.functionScopes = helperState.functionScopes :=
                freshNonFunctionBindingName_preserves_functionScopes
                  "clz_arg" hFreshArg
              simp [hFreshArg] at hRun
              cases hFreshRet :
                  (freshNonFunctionBindingName "clz_ret").run argState with
              | error _ =>
                  simp [hFreshRet] at hRun
              | ok retResult =>
                  rcases retResult with ⟨ret, retState⟩
                  have hRetScopes :
                      retState.functionScopes = argState.functionScopes :=
                    freshNonFunctionBindingName_preserves_functionScopes
                      "clz_ret" hFreshRet
                  simp [hFreshRet, StateT.run_modify] at hRun
                  rcases hRun with ⟨_hValue, hState⟩
                  subst state'
                  exact hRetScopes.trans (hArgScopes.trans hHelperScopes)

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

mutual

theorem elaborate_preserves_functionScopes
    (expr : Raw.Expr) : PreservesFunctionScopes (Expr.elaborate expr) := by
  intro state state' value hRun
  cases expr with
  | literal literal =>
      cases literal <;>
        simp [Expr.elaborate, Literal.elaborate] at hRun <;>
        cases hRun <;>
        rfl
  | identifier name =>
      unfold Expr.elaborate at hRun
      exact
        PreservesFunctionScopes.map (fun _ => Frontend.Expr.var name)
          (requireIdentifierVisible_preserves_functionScopes
            name "expression") hRun
  | functionCall name args =>
      by_cases hMemoryguard : name = "memoryguard"
      · subst name
        cases args with
        | nil =>
            unfold Expr.elaborate at hRun
            exact PreservesFunctionScopes.throw
              "memoryguard expects one argument" hRun
        | cons arg rest =>
            cases rest with
            | nil =>
                unfold Expr.elaborate at hRun
                exact
                  PreservesFunctionScopes.map
                    (fun arg =>
                      Frontend.Expr.call .objectBuiltin "memoryguard" [arg])
                    (elaborate_preserves_functionScopes arg)
                    hRun
            | cons _ _ =>
                unfold Expr.elaborate at hRun
                exact PreservesFunctionScopes.throw
                  "memoryguard expects one argument" hRun
      · by_cases hClz : name = "clz"
        · subst name
          cases args with
          | nil =>
              unfold Expr.elaborate at hRun
              exact PreservesFunctionScopes.throw "clz expects one argument"
                hRun
          | cons arg rest =>
              cases rest with
              | nil =>
                  unfold Expr.elaborate at hRun
                  exact
                    PreservesFunctionScopes.bind
                      (elaborate_preserves_functionScopes arg)
                      (fun arg =>
                        PreservesFunctionScopes.bind
                          ensureClzHelper_preserves_functionScopes
                          (fun helper => PreservesFunctionScopes.pure
                            (Frontend.Expr.call .user helper [arg])))
                      hRun
              | cons _ _ =>
                  unfold Expr.elaborate at hRun
                  exact PreservesFunctionScopes.throw "clz expects one argument"
                    hRun
        · unfold Expr.elaborate at hRun
          simp [hMemoryguard, hClz, StateT.run_bind] at hRun
          cases hArgs : (Expr.List.elaborate args).run state with
          | error _ =>
              simp [hArgs] at hRun
          | ok result =>
              rcases result with ⟨args', argState⟩
              have hArgsScopes :
                  argState.functionScopes = state.functionScopes :=
                List.elaborate_preserves_functionScopes args hArgs
              simp [hArgs] at hRun
              cases hClass : CallClass.classifyCall name with
              | primitive =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hArgsScopes
              | user =>
                  simp [hClass] at hRun
                  have hResolveScopes :
                      state'.functionScopes = argState.functionScopes :=
                    PreservesFunctionScopes.map
                      (fun callee =>
                        Frontend.Expr.call .user callee args')
                      (resolveFunction_preserves_functionScopes name)
                      hRun
                  exact hResolveScopes.trans hArgsScopes
              | objectBuiltin =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hArgsScopes
              | dialectBuiltin =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hArgsScopes
  termination_by 2 * sizeOf expr
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem List.elaborate_preserves_functionScopes
    (exprs : List Raw.Expr) :
    PreservesFunctionScopes (Expr.List.elaborate exprs) := by
  cases exprs with
  | nil =>
      intro state state' value hRun
      unfold Expr.List.elaborate at hRun
      simp [StateT.run_pure] at hRun
      cases hRun
      rfl
  | cons expr rest =>
      intro state state' value hRun
      unfold Expr.List.elaborate at hRun
      exact
        PreservesFunctionScopes.bind
          (elaborate_preserves_functionScopes expr)
          (fun head =>
            PreservesFunctionScopes.bind
              (List.elaborate_preserves_functionScopes rest)
              (fun tail => PreservesFunctionScopes.pure (head :: tail)))
          hRun
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

theorem elaborate_direct_source_user_call_occurrence
    {expr : Raw.Expr} {state finalState : State}
    {front : Frontend.Expr} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    {name generated : Name} {args : List Raw.Expr}
    (hCall : Raw.Source.ExprCall.Direct expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Expr.elaborate expr).run state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.UserCall front generated args' := by
  cases hCall
  have hNotMemoryguard : name ≠ "memoryguard" :=
    bindingNameOk_ne_memoryguard hNameOk
  have hNotClz : name ≠ "clz" :=
    bindingNameOk_ne_clz hNameOk
  have hClass : CallClass.classifyCall name = .user :=
    bindingNameOk_classifyCall_user hNameOk
  unfold Expr.elaborate at hElab
  simp [hNotMemoryguard, hNotClz, StateT.run_bind] at hElab
  cases hArgs : (Expr.List.elaborate args).run state with
  | error err =>
      simp [hArgs] at hElab
  | ok argResult =>
      rcases argResult with ⟨args', argState⟩
      have hArgScopes :
          argState.functionScopes = scope :: outer := by
        rw [Expr.List.elaborate_preserves_functionScopes args hArgs,
          hScopes]
      have hResolve :
          resolveFunctionIn name argState.functionScopes = some generated := by
        rw [hArgScopes]
        simp [resolveFunctionIn, hLookup]
      simp [hArgs, hClass, resolveFunction, hResolve] at hElab
      cases hElab
      exact ⟨args', .here⟩

theorem List.elaborate_direct_source_user_call_occurrence
    {exprs : List Raw.Expr} {state finalState : State}
    {fronts : List Frontend.Expr} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    {expr : Raw.Expr} {name generated : Name} {args : List Raw.Expr}
    (hMem : expr ∈ exprs)
    (hCall : Raw.Source.ExprCall.Direct expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Expr.List.elaborate exprs).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.UserCall front generated args' := by
  induction exprs generalizing state finalState fronts outer with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      simp at hMem
      rcases hMem with hHeadMem | hTailMem
      · subst expr
        cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            rcases
              EvmCompiler.Solidity.RawAst.Elab.Expr.elaborate_direct_source_user_call_occurrence
                (expr := head) (state := state)
                (finalState := headState) (front := headFront)
                (scope := scope) (outer := outer)
                (name := name) (generated := generated)
                (args := args) hCall hNameOk hLookup hScopes hHead with
              ⟨args', hOccurrence⟩
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                have hMemFront : headFront ∈ fronts := by
                  rw [← hElab.1]
                  simp
                exact ⟨args', headFront, hMemFront, hOccurrence⟩
      · cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            have hHeadScopes :
                headState.functionScopes = scope :: outer := by
              rw [Expr.elaborate_preserves_functionScopes head hHead,
                hScopes]
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                rcases ih hTailMem hHeadScopes hTail with
                  ⟨args', front, hMemTail, hOccurrence⟩
                have hMemFront : front ∈ fronts := by
                  rw [← hElab.1]
                  exact List.mem_cons_of_mem _ hMemTail
                exact ⟨args', front, hMemFront, hOccurrence⟩

theorem elaborate_direct_argument_source_user_call_occurrence
    {callee : Name} {callArgs : List Raw.Expr}
    {state finalState : State} {front : Frontend.Expr}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {expr : Raw.Expr} {name generated : Name} {args : List Raw.Expr}
    (hOuterNotMemoryguard : callee ≠ "memoryguard")
    (hOuterNotClz : callee ≠ "clz")
    (hMem : expr ∈ callArgs)
    (hCall : Raw.Source.ExprCall.Direct expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Expr.elaborate (.functionCall callee callArgs)).run state =
      .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.UserCall front generated args' := by
  unfold Expr.elaborate at hElab
  simp [hOuterNotMemoryguard, hOuterNotClz, StateT.run_bind] at hElab
  cases hArgs : (Expr.List.elaborate callArgs).run state with
  | error err =>
      simp [hArgs] at hElab
  | ok argResult =>
      rcases argResult with ⟨frontArgs, argState⟩
      rcases
        List.elaborate_direct_source_user_call_occurrence
          (exprs := callArgs) (state := state)
          (finalState := argState) (fronts := frontArgs)
          (scope := scope) (outer := outer)
          (expr := expr) (name := name) (generated := generated)
          (args := args) hMem hCall hNameOk hLookup hScopes hArgs with
        ⟨generatedArgs, frontArg, hFrontArgMem, hOccurrence⟩
      simp [hArgs] at hElab
      cases hClass : CallClass.classifyCall callee with
      | primitive =>
          simp [hClass] at hElab
          cases hElab
          exact
            ⟨generatedArgs,
              FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩
      | user =>
          simp [hClass] at hElab
          cases hResolve : (resolveFunction callee).run argState with
          | error err =>
              simp [hResolve] at hElab
          | ok resolveResult =>
              rcases resolveResult with ⟨resolved, resolvedState⟩
              simp [hResolve] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨generatedArgs,
                  FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩
      | objectBuiltin =>
          simp [hClass] at hElab
          cases hElab
          exact
            ⟨generatedArgs,
              FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩
      | dialectBuiltin =>
          simp [hClass] at hElab
          cases hElab
          exact
            ⟨generatedArgs,
              FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩

theorem List.elaborate_member_source_user_call_occurrence
    {exprs : List Raw.Expr} {target : Raw.Expr}
    {state finalState : State} {fronts : List Frontend.Expr}
    {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    {generated : Name}
    (hMem : target ∈ exprs)
    (hTarget :
      ∀ {state finalState : State} {front : Frontend.Expr}
        {outer : List (List (Name × Name))},
        state.functionScopes = scope :: outer →
          (Expr.elaborate target).run state = .ok (front, finalState) →
            ∃ args',
              FrontendOccurrence.UserCall front generated args')
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Expr.List.elaborate exprs).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.UserCall front generated args' := by
  induction exprs generalizing state finalState fronts outer with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      simp at hMem
      rcases hMem with hHeadMem | hTailMem
      · subst target
        cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            rcases hTarget hScopes hHead with
              ⟨args', hOccurrence⟩
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                have hMemFront : headFront ∈ fronts := by
                  rw [← hElab.1]
                  simp
                exact ⟨args', headFront, hMemFront, hOccurrence⟩
      · cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            have hHeadScopes :
                headState.functionScopes = scope :: outer := by
              rw [Expr.elaborate_preserves_functionScopes head hHead,
                hScopes]
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                rcases ih hTailMem hHeadScopes hTail with
                  ⟨args', front, hMemTail, hOccurrence⟩
                have hMemFront : front ∈ fronts := by
                  rw [← hElab.1]
                  exact List.mem_cons_of_mem _ hMemTail
                exact ⟨args', front, hMemFront, hOccurrence⟩

theorem elaborate_source_user_call_occurrence
    {expr : Raw.Expr} {state finalState : State}
    {front : Frontend.Expr} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.ExprCall.Occurs expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Expr.elaborate expr).run state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.UserCall front generated args' := by
  induction hOccurs generalizing state finalState front outer with
  | direct hDirect =>
      exact
        elaborate_direct_source_user_call_occurrence
          hDirect hNameOk hLookup hScopes hElab
  | @arg callee callArgs arg name args hMem hArgOccurs ih =>
      by_cases hMemoryguard : callee = "memoryguard"
      · subst callee
        unfold Expr.elaborate at hElab
        cases callArgs with
        | nil =>
            simp at hMem
        | cons head rest =>
            cases rest with
            | nil =>
                simp at hMem
                subst arg
                simp [StateT.run_bind] at hElab
                cases hHead : (Expr.elaborate head).run state with
                | error err =>
                    simp [hHead] at hElab
                | ok headResult =>
                    rcases headResult with ⟨headFront, headState⟩
                    rcases ih hNameOk hLookup hScopes hHead with
                      ⟨args', hOccurrence⟩
                    simp [hHead] at hElab
                    rcases hElab with ⟨hFront, _hState⟩
                    rw [← hFront]
                    exact
                      ⟨args',
                        FrontendOccurrence.UserCall.arg (by simp)
                          hOccurrence⟩
            | cons second more =>
                unfold EvmCompiler.Solidity.RawAst.Elab.throw at hElab
                change (Except.error
                  "memoryguard expects one argument" :
                    DecodeM (Frontend.Expr × State)) =
                  .ok (front, finalState) at hElab
                cases hElab
      · by_cases hClz : callee = "clz"
        · subst callee
          unfold Expr.elaborate at hElab
          cases callArgs with
          | nil =>
              simp at hMem
          | cons head rest =>
              cases rest with
              | nil =>
                  simp at hMem
                  subst arg
                  simp [StateT.run_bind] at hElab
                  cases hHead : (Expr.elaborate head).run state with
                  | error err =>
                      simp [hHead] at hElab
                  | ok headResult =>
                      rcases headResult with ⟨headFront, headState⟩
                      rcases ih hNameOk hLookup hScopes hHead with
                        ⟨args', hOccurrence⟩
                      simp [hHead] at hElab
                      cases hHelper : ensureClzHelper.run headState with
                      | error err =>
                          simp [hHelper] at hElab
                      | ok helperResult =>
                          rcases helperResult with ⟨helper, helperState⟩
                          simp [hHelper] at hElab
                          rcases hElab with ⟨hFront, _hState⟩
                          rw [← hFront]
                          exact
                            ⟨args',
                              FrontendOccurrence.UserCall.arg (by simp)
                                hOccurrence⟩
              | cons second more =>
                  unfold EvmCompiler.Solidity.RawAst.Elab.throw at hElab
                  change (Except.error
                    "clz expects one argument" :
                      DecodeM (Frontend.Expr × State)) =
                    .ok (front, finalState) at hElab
                  cases hElab
        · unfold Expr.elaborate at hElab
          simp [hMemoryguard, hClz, StateT.run_bind] at hElab
          cases hArgs : (Expr.List.elaborate callArgs).run state with
          | error err =>
              simp [hArgs] at hElab
          | ok argResult =>
              rcases argResult with ⟨frontArgs, argState⟩
              rcases
                List.elaborate_member_source_user_call_occurrence
                  (exprs := callArgs) (target := arg)
                  (state := state) (finalState := argState)
                  (fronts := frontArgs) (scope := scope)
                  (outer := outer) (generated := generated)
                  hMem
                  (fun {state finalState front outer} hScopes hElab =>
                    ih hNameOk hLookup hScopes hElab)
                  hScopes hArgs with
                ⟨generatedArgs, frontArg, hFrontArgMem, hOccurrence⟩
              simp [hArgs] at hElab
              cases hClass : CallClass.classifyCall callee with
              | primitive =>
                  simp [hClass] at hElab
                  cases hElab
                  exact
                    ⟨generatedArgs,
                      FrontendOccurrence.UserCall.arg hFrontArgMem
                        hOccurrence⟩
              | user =>
                  simp [hClass] at hElab
                  cases hResolve : (resolveFunction callee).run argState with
                  | error err =>
                      simp [hResolve] at hElab
                  | ok resolveResult =>
                      rcases resolveResult with ⟨resolved, resolvedState⟩
                      simp [hResolve] at hElab
                      rcases hElab with ⟨hFront, _hState⟩
                      rw [← hFront]
                      exact
                        ⟨generatedArgs,
                          FrontendOccurrence.UserCall.arg hFrontArgMem
                            hOccurrence⟩
              | objectBuiltin =>
                  simp [hClass] at hElab
                  cases hElab
                  exact
                    ⟨generatedArgs,
                      FrontendOccurrence.UserCall.arg hFrontArgMem
                        hOccurrence⟩
              | dialectBuiltin =>
                  simp [hClass] at hElab
                  cases hElab
                  exact
                    ⟨generatedArgs,
                      FrontendOccurrence.UserCall.arg hFrontArgMem
                        hOccurrence⟩

theorem List.elaborate_source_user_call_occurrence
    {exprs : List Raw.Expr} {state finalState : State}
    {fronts : List Frontend.Expr} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.ExprCall.ListOccurs exprs name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Expr.List.elaborate exprs).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.UserCall front generated args' := by
  induction hOccurs generalizing state finalState fronts outer with
  | @head expr rest name args hExprOccurs =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Expr.elaborate expr).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headFront, headState⟩
          rcases
            EvmCompiler.Solidity.RawAst.Elab.Expr.elaborate_source_user_call_occurrence
              hExprOccurs hNameOk hLookup hScopes hHead with
            ⟨args', hOccurrence⟩
          simp [hHead] at hElab
          cases hTail : (Expr.List.elaborate rest).run headState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailFronts, tailState⟩
              simp [hTail] at hElab
              have hMemFront : headFront ∈ fronts := by
                rw [← hElab.1]
                simp
              exact ⟨args', headFront, hMemFront, hOccurrence⟩
  | @tail expr rest name args hTailOccurs ih =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Expr.elaborate expr).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headFront, headState⟩
          have hHeadScopes :
              headState.functionScopes = scope :: outer := by
            rw [Expr.elaborate_preserves_functionScopes expr hHead,
              hScopes]
          simp [hHead] at hElab
          cases hTail : (Expr.List.elaborate rest).run headState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailFronts, tailState⟩
              simp [hTail] at hElab
              rcases ih hNameOk hLookup hHeadScopes hTail with
                ⟨args', front, hMemTail, hOccurrence⟩
              have hMemFront : front ∈ fronts := by
                rw [← hElab.1]
                exact List.mem_cons_of_mem _ hMemTail
              exact ⟨args', front, hMemFront, hOccurrence⟩

theorem elaborate_direct_resolved_source_user_call_occurrence
    {expr : Raw.Expr} {state finalState : State}
    {front : Frontend.Expr}
    {name generated : Name} {args : List Raw.Expr}
    (hCall : Raw.Source.ExprCall.Direct expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Expr.elaborate expr).run state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.UserCall front generated args' := by
  cases hCall
  have hNotMemoryguard : name ≠ "memoryguard" :=
    bindingNameOk_ne_memoryguard hNameOk
  have hNotClz : name ≠ "clz" :=
    bindingNameOk_ne_clz hNameOk
  have hClass : CallClass.classifyCall name = .user :=
    bindingNameOk_classifyCall_user hNameOk
  unfold Expr.elaborate at hElab
  simp [hNotMemoryguard, hNotClz, StateT.run_bind] at hElab
  cases hArgs : (Expr.List.elaborate args).run state with
  | error err =>
      simp [hArgs] at hElab
  | ok argResult =>
      rcases argResult with ⟨args', argState⟩
      have hArgScopes :
          argState.functionScopes = state.functionScopes :=
        Expr.List.elaborate_preserves_functionScopes args hArgs
      have hArgResolve :
          resolveFunctionIn name argState.functionScopes = some generated := by
        rw [hArgScopes]
        exact hResolve
      simp [hArgs, hClass, resolveFunction, hArgResolve] at hElab
      cases hElab
      exact ⟨args', .here⟩

theorem List.elaborate_direct_resolved_source_user_call_occurrence
    {exprs : List Raw.Expr} {state finalState : State}
    {fronts : List Frontend.Expr}
    {expr : Raw.Expr} {name generated : Name} {args : List Raw.Expr}
    (hMem : expr ∈ exprs)
    (hCall : Raw.Source.ExprCall.Direct expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Expr.List.elaborate exprs).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.UserCall front generated args' := by
  induction exprs generalizing state finalState fronts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      simp at hMem
      rcases hMem with hHeadMem | hTailMem
      · subst expr
        cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            rcases
              EvmCompiler.Solidity.RawAst.Elab.Expr.elaborate_direct_resolved_source_user_call_occurrence
                (expr := head) (state := state)
                (finalState := headState) (front := headFront)
                (name := name) (generated := generated)
                (args := args) hCall hNameOk hResolve hHead with
              ⟨args', hOccurrence⟩
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                have hMemFront : headFront ∈ fronts := by
                  rw [← hElab.1]
                  simp
                exact ⟨args', headFront, hMemFront, hOccurrence⟩
      · cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            have hHeadScopes :
                headState.functionScopes = state.functionScopes :=
              Expr.elaborate_preserves_functionScopes head hHead
            have hHeadResolve :
                resolveFunctionIn name headState.functionScopes =
                  some generated := by
              rw [hHeadScopes]
              exact hResolve
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                rcases ih hTailMem hHeadResolve hTail with
                  ⟨args', front, hMemTail, hOccurrence⟩
                have hMemFront : front ∈ fronts := by
                  rw [← hElab.1]
                  exact List.mem_cons_of_mem _ hMemTail
                exact ⟨args', front, hMemFront, hOccurrence⟩

theorem elaborate_direct_argument_resolved_source_user_call_occurrence
    {callee : Name} {callArgs : List Raw.Expr}
    {state finalState : State} {front : Frontend.Expr}
    {expr : Raw.Expr} {name generated : Name} {args : List Raw.Expr}
    (hOuterNotMemoryguard : callee ≠ "memoryguard")
    (hOuterNotClz : callee ≠ "clz")
    (hMem : expr ∈ callArgs)
    (hCall : Raw.Source.ExprCall.Direct expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Expr.elaborate (.functionCall callee callArgs)).run state =
      .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.UserCall front generated args' := by
  unfold Expr.elaborate at hElab
  simp [hOuterNotMemoryguard, hOuterNotClz, StateT.run_bind] at hElab
  cases hArgs : (Expr.List.elaborate callArgs).run state with
  | error err =>
      simp [hArgs] at hElab
  | ok argResult =>
      rcases argResult with ⟨frontArgs, argState⟩
      rcases
        List.elaborate_direct_resolved_source_user_call_occurrence
          (exprs := callArgs) (state := state)
          (finalState := argState) (fronts := frontArgs)
          (expr := expr) (name := name) (generated := generated)
          (args := args) hMem hCall hNameOk hResolve hArgs with
        ⟨generatedArgs, frontArg, hFrontArgMem, hOccurrence⟩
      simp [hArgs] at hElab
      cases hClass : CallClass.classifyCall callee with
      | primitive =>
          simp [hClass] at hElab
          cases hElab
          exact
            ⟨generatedArgs,
              FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩
      | user =>
          simp [hClass] at hElab
          cases hResolveOuter : (resolveFunction callee).run argState with
          | error err =>
              simp [hResolveOuter] at hElab
          | ok resolveResult =>
              rcases resolveResult with ⟨resolved, resolvedState⟩
              simp [hResolveOuter] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨generatedArgs,
                  FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩
      | objectBuiltin =>
          simp [hClass] at hElab
          cases hElab
          exact
            ⟨generatedArgs,
              FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩
      | dialectBuiltin =>
          simp [hClass] at hElab
          cases hElab
          exact
            ⟨generatedArgs,
              FrontendOccurrence.UserCall.arg hFrontArgMem hOccurrence⟩

theorem List.elaborate_member_resolved_source_user_call_occurrence
    {exprs : List Raw.Expr} {target : Raw.Expr}
    {state finalState : State} {fronts : List Frontend.Expr}
    {name generated : Name}
    (hMem : target ∈ exprs)
    (hTarget :
      ∀ {state finalState : State} {front : Frontend.Expr},
        resolveFunctionIn name state.functionScopes = some generated →
        (Expr.elaborate target).run state = .ok (front, finalState) →
          ∃ args',
            FrontendOccurrence.UserCall front generated args')
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Expr.List.elaborate exprs).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.UserCall front generated args' := by
  induction exprs generalizing state finalState fronts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      simp at hMem
      rcases hMem with hHeadMem | hTailMem
      · subst target
        cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            rcases hTarget hResolve hHead with
              ⟨args', hOccurrence⟩
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                have hMemFront : headFront ∈ fronts := by
                  rw [← hElab.1]
                  simp
                exact ⟨args', headFront, hMemFront, hOccurrence⟩
      · cases hHead : (Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            have hHeadScopes :
                headState.functionScopes = state.functionScopes :=
              Expr.elaborate_preserves_functionScopes head hHead
            have hHeadResolve :
                resolveFunctionIn name headState.functionScopes =
                  some generated := by
              rw [hHeadScopes]
              exact hResolve
            simp [hHead] at hElab
            cases hTail : (Expr.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                rcases ih hTailMem hHeadResolve hTail with
                  ⟨args', front, hMemTail, hOccurrence⟩
                have hMemFront : front ∈ fronts := by
                  rw [← hElab.1]
                  exact List.mem_cons_of_mem _ hMemTail
                exact ⟨args', front, hMemFront, hOccurrence⟩

theorem elaborate_resolved_source_user_call_occurrence
    {expr : Raw.Expr} {state finalState : State}
    {front : Frontend.Expr}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.ExprCall.Occurs expr name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Expr.elaborate expr).run state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.UserCall front generated args' := by
  induction hOccurs generalizing state finalState front with
  | direct hDirect =>
      exact
        elaborate_direct_resolved_source_user_call_occurrence
          hDirect hNameOk hResolve hElab
  | @arg callee callArgs arg name args hMem hArgOccurs ih =>
      by_cases hMemoryguard : callee = "memoryguard"
      · subst callee
        unfold Expr.elaborate at hElab
        cases callArgs with
        | nil =>
            simp at hMem
        | cons head rest =>
            cases rest with
            | nil =>
                simp at hMem
                subst arg
                simp [StateT.run_bind] at hElab
                cases hHead : (Expr.elaborate head).run state with
                | error err =>
                    simp [hHead] at hElab
                | ok headResult =>
                    rcases headResult with ⟨headFront, headState⟩
                    rcases ih hNameOk hResolve hHead with
                      ⟨args', hOccurrence⟩
                    simp [hHead] at hElab
                    rcases hElab with ⟨hFront, _hState⟩
                    rw [← hFront]
                    exact
                      ⟨args',
                        FrontendOccurrence.UserCall.arg (by simp)
                          hOccurrence⟩
            | cons second more =>
                unfold EvmCompiler.Solidity.RawAst.Elab.throw at hElab
                change (Except.error
                  "memoryguard expects one argument" :
                    DecodeM (Frontend.Expr × State)) =
                  .ok (front, finalState) at hElab
                cases hElab
      · by_cases hClz : callee = "clz"
        · subst callee
          unfold Expr.elaborate at hElab
          cases callArgs with
          | nil =>
              simp at hMem
          | cons head rest =>
              cases rest with
              | nil =>
                  simp at hMem
                  subst arg
                  simp [StateT.run_bind] at hElab
                  cases hHead : (Expr.elaborate head).run state with
                  | error err =>
                      simp [hHead] at hElab
                  | ok headResult =>
                      rcases headResult with ⟨headFront, headState⟩
                      rcases ih hNameOk hResolve hHead with
                        ⟨args', hOccurrence⟩
                      simp [hHead] at hElab
                      cases hHelper : ensureClzHelper.run headState with
                      | error err =>
                          simp [hHelper] at hElab
                      | ok helperResult =>
                          rcases helperResult with ⟨helper, helperState⟩
                          simp [hHelper] at hElab
                          rcases hElab with ⟨hFront, _hState⟩
                          rw [← hFront]
                          exact
                            ⟨args',
                              FrontendOccurrence.UserCall.arg (by simp)
                                hOccurrence⟩
              | cons second more =>
                  unfold EvmCompiler.Solidity.RawAst.Elab.throw at hElab
                  change (Except.error
                    "clz expects one argument" :
                      DecodeM (Frontend.Expr × State)) =
                    .ok (front, finalState) at hElab
                  cases hElab
        · unfold Expr.elaborate at hElab
          simp [hMemoryguard, hClz, StateT.run_bind] at hElab
          cases hArgs : (Expr.List.elaborate callArgs).run state with
          | error err =>
              simp [hArgs] at hElab
          | ok argResult =>
              rcases argResult with ⟨frontArgs, argState⟩
              rcases
                List.elaborate_member_resolved_source_user_call_occurrence
                  (exprs := callArgs) (target := arg)
                  (state := state) (finalState := argState)
                  (fronts := frontArgs) (name := name)
                  (generated := generated)
                  hMem
                  (fun {state finalState front} hResolve hElab =>
                    ih hNameOk hResolve hElab)
                  hResolve
                  hArgs with
                ⟨generatedArgs, frontArg, hFrontArgMem, hOccurrence⟩
              simp [hArgs] at hElab
              cases hClass : CallClass.classifyCall callee with
              | primitive =>
                  simp [hClass] at hElab
                  cases hElab
                  exact
                    ⟨generatedArgs,
                      FrontendOccurrence.UserCall.arg hFrontArgMem
                        hOccurrence⟩
              | user =>
                  simp [hClass] at hElab
                  cases hResolveOuter : (resolveFunction callee).run argState with
                  | error err =>
                      simp [hResolveOuter] at hElab
                  | ok resolveResult =>
                      rcases resolveResult with ⟨resolved, resolvedState⟩
                      simp [hResolveOuter] at hElab
                      rcases hElab with ⟨hFront, _hState⟩
                      rw [← hFront]
                      exact
                        ⟨generatedArgs,
                          FrontendOccurrence.UserCall.arg hFrontArgMem
                            hOccurrence⟩
              | objectBuiltin =>
                  simp [hClass] at hElab
                  cases hElab
                  exact
                    ⟨generatedArgs,
                      FrontendOccurrence.UserCall.arg hFrontArgMem
                        hOccurrence⟩
              | dialectBuiltin =>
                  simp [hClass] at hElab
                  cases hElab
                  exact
                    ⟨generatedArgs,
                      FrontendOccurrence.UserCall.arg hFrontArgMem
                        hOccurrence⟩

theorem List.elaborate_resolved_source_user_call_occurrence
    {exprs : List Raw.Expr} {state finalState : State}
    {fronts : List Frontend.Expr}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.ExprCall.ListOccurs exprs name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Expr.List.elaborate exprs).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.UserCall front generated args' := by
  induction hOccurs generalizing state finalState fronts with
  | @head expr rest name args hExprOccurs =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Expr.elaborate expr).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headFront, headState⟩
          rcases
            EvmCompiler.Solidity.RawAst.Elab.Expr.elaborate_resolved_source_user_call_occurrence
              hExprOccurs hNameOk hResolve hHead with
            ⟨args', hOccurrence⟩
          simp [hHead] at hElab
          cases hTail : (Expr.List.elaborate rest).run headState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailFronts, tailState⟩
              simp [hTail] at hElab
              have hMemFront : headFront ∈ fronts := by
                rw [← hElab.1]
                simp
              exact ⟨args', headFront, hMemFront, hOccurrence⟩
  | @tail expr rest name args hTailOccurs ih =>
      unfold Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Expr.elaborate expr).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headFront, headState⟩
          have hHeadScopes :
              headState.functionScopes = state.functionScopes :=
            Expr.elaborate_preserves_functionScopes expr hHead
          have hHeadResolve :
              resolveFunctionIn name headState.functionScopes =
                some generated := by
            rw [hHeadScopes]
            exact hResolve
          simp [hHead] at hElab
          cases hTail : (Expr.List.elaborate rest).run headState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailFronts, tailState⟩
              simp [hTail] at hElab
              rcases ih hNameOk hHeadResolve hTail with
                ⟨args', front, hMemTail, hOccurrence⟩
              have hMemFront : front ∈ fronts := by
                rw [← hElab.1]
                exact List.mem_cons_of_mem _ hMemTail
              exact ⟨args', front, hMemFront, hOccurrence⟩

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

theorem elaborate_incoming_scope_source_user_call_occurrence
    {stmt : Raw.Stmt} {state finalState : State}
    {front : Frontend.Stmt} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Stmt.elaborate stmt).run state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtIncomingUserCall front generated args' := by
  cases hOccurs with
  | @variableValue names value name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind, StateT.run_map] at hElab
      cases hValue : (Expr.elaborate value).run state with
      | error err =>
          simp [hValue] at hElab
      | ok valueResult =>
          rcases valueResult with ⟨frontValue, valueState⟩
          rcases
            Expr.elaborate_source_user_call_occurrence
              hExprOccurs hNameOk hLookup hScopes hValue with
            ⟨args', hOccurrence⟩
          simp [hValue] at hElab
          cases hDeclare :
              (declareIdentifiers names "variable").run valueState with
          | error err =>
              simp [hDeclare] at hElab
          | ok declareResult =>
              rcases declareResult with ⟨_, declaredState⟩
              simp [hDeclare] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtIncomingUserCall.letValue
                    hOccurrence⟩
  | @assignmentValue names value name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hVisible :
          (requireIdentifiersVisible names "assignment").run state with
      | error err =>
          simp [hVisible] at hElab
      | ok visibleResult =>
          rcases visibleResult with ⟨_, visibleState⟩
          have hVisibleScopes :
              visibleState.functionScopes = scope :: outer := by
            rw [requireIdentifiersVisible_preserves_functionScopes
              names "assignment" hVisible, hScopes]
          simp [hVisible] at hElab
          cases hValue : (Expr.elaborate value).run visibleState with
          | error err =>
              simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              rcases
                Expr.elaborate_source_user_call_occurrence
                  hExprOccurs hNameOk hLookup hVisibleScopes hValue with
                ⟨args', hOccurrence⟩
              simp [hValue] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtIncomingUserCall.assignmentValue
                    hOccurrence⟩
  | @expressionStatement expr name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hExpr : (Expr.elaborate expr).run state with
      | error err =>
          simp [hExpr] at hElab
      | ok exprResult =>
          rcases exprResult with ⟨frontExpr, exprState⟩
          rcases
            Expr.elaborate_source_user_call_occurrence
              hExprOccurs hNameOk hLookup hScopes hExpr with
            ⟨args', hOccurrence⟩
          simp [hExpr] at hElab
          rcases hElab with ⟨hFront, _hState⟩
          rw [← hFront]
          exact
            ⟨args',
              FrontendOccurrence.StmtIncomingUserCall.expressionStatement
                hOccurrence⟩
  | @switchScrutinee scrutinee cases default name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hScrutinee : (Expr.elaborate scrutinee).run state with
      | error err =>
          simp [hScrutinee] at hElab
      | ok scrutineeResult =>
          rcases scrutineeResult with ⟨frontScrutinee, scrutineeState⟩
          rcases
            Expr.elaborate_source_user_call_occurrence
              hExprOccurs hNameOk hLookup hScopes hScrutinee with
            ⟨args', hOccurrence⟩
          simp [hScrutinee] at hElab
          cases hCases : (Stmt.CaseList.elaborate cases).run
              scrutineeState with
          | error err =>
              simp [hCases] at hElab
          | ok casesResult =>
              rcases casesResult with ⟨frontCases, casesState⟩
              simp [hCases] at hElab
              cases hDefault :
                  (Stmt.List.elaborateBlock default true).run casesState with
              | error err =>
                  simp [hDefault] at hElab
              | ok defaultResult =>
                  rcases defaultResult with ⟨frontDefault, defaultState⟩
                  simp [hDefault] at hElab
                  rcases hElab with ⟨hFront, _hState⟩
                  rw [← hFront]
                  exact
                    ⟨args',
                      FrontendOccurrence.StmtIncomingUserCall.switchScrutinee
                        hOccurrence⟩
  | @ifCondition condition body name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hCondition : (Expr.elaborate condition).run state with
      | error err =>
          simp [hCondition] at hElab
      | ok conditionResult =>
          rcases conditionResult with ⟨frontCondition, conditionState⟩
          rcases
            Expr.elaborate_source_user_call_occurrence
              hExprOccurs hNameOk hLookup hScopes hCondition with
            ⟨args', hOccurrence⟩
          simp [hCondition] at hElab
          cases hBody :
              (Stmt.List.elaborateBlock body true).run conditionState with
          | error err =>
              simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              simp [hBody] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtIncomingUserCall.ifCondition
                    hOccurrence⟩

theorem elaborate_resolved_incoming_scope_source_user_call_occurrence
    {stmt : Raw.Stmt} {state finalState : State}
    {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Stmt.elaborate stmt).run state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtIncomingUserCall front generated args' := by
  cases hOccurs with
  | @variableValue names value name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind, StateT.run_map] at hElab
      cases hValue : (Expr.elaborate value).run state with
      | error err =>
          simp [hValue] at hElab
      | ok valueResult =>
          rcases valueResult with ⟨frontValue, valueState⟩
          rcases
            Expr.elaborate_resolved_source_user_call_occurrence
              hExprOccurs hNameOk hResolve hValue with
            ⟨args', hOccurrence⟩
          simp [hValue] at hElab
          cases hDeclare :
              (declareIdentifiers names "variable").run valueState with
          | error err =>
              simp [hDeclare] at hElab
          | ok declareResult =>
              rcases declareResult with ⟨_, declaredState⟩
              simp [hDeclare] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtIncomingUserCall.letValue
                    hOccurrence⟩
  | @assignmentValue names value name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hVisible :
          (requireIdentifiersVisible names "assignment").run state with
      | error err =>
          simp [hVisible] at hElab
      | ok visibleResult =>
          rcases visibleResult with ⟨_, visibleState⟩
          have hVisibleScopes :
              visibleState.functionScopes = state.functionScopes :=
            requireIdentifiersVisible_preserves_functionScopes
              names "assignment" hVisible
          have hVisibleResolve :
              resolveFunctionIn name visibleState.functionScopes =
                some generated := by
            rw [hVisibleScopes]
            exact hResolve
          simp [hVisible] at hElab
          cases hValue : (Expr.elaborate value).run visibleState with
          | error err =>
              simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              rcases
                Expr.elaborate_resolved_source_user_call_occurrence
                  hExprOccurs hNameOk hVisibleResolve hValue with
                ⟨args', hOccurrence⟩
              simp [hValue] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtIncomingUserCall.assignmentValue
                    hOccurrence⟩
  | @expressionStatement expr name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hExpr : (Expr.elaborate expr).run state with
      | error err =>
          simp [hExpr] at hElab
      | ok exprResult =>
          rcases exprResult with ⟨frontExpr, exprState⟩
          rcases
            Expr.elaborate_resolved_source_user_call_occurrence
              hExprOccurs hNameOk hResolve hExpr with
            ⟨args', hOccurrence⟩
          simp [hExpr] at hElab
          rcases hElab with ⟨hFront, _hState⟩
          rw [← hFront]
          exact
            ⟨args',
              FrontendOccurrence.StmtIncomingUserCall.expressionStatement
                hOccurrence⟩
  | @switchScrutinee scrutinee cases default name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hScrutinee : (Expr.elaborate scrutinee).run state with
      | error err =>
          simp [hScrutinee] at hElab
      | ok scrutineeResult =>
          rcases scrutineeResult with ⟨frontScrutinee, scrutineeState⟩
          rcases
            Expr.elaborate_resolved_source_user_call_occurrence
              hExprOccurs hNameOk hResolve hScrutinee with
            ⟨args', hOccurrence⟩
          simp [hScrutinee] at hElab
          cases hCases : (Stmt.CaseList.elaborate cases).run
              scrutineeState with
          | error err =>
              simp [hCases] at hElab
          | ok casesResult =>
              rcases casesResult with ⟨frontCases, casesState⟩
              simp [hCases] at hElab
              cases hDefault :
                  (Stmt.List.elaborateBlock default true).run casesState with
              | error err =>
                  simp [hDefault] at hElab
              | ok defaultResult =>
                  rcases defaultResult with ⟨frontDefault, defaultState⟩
                  simp [hDefault] at hElab
                  rcases hElab with ⟨hFront, _hState⟩
                  rw [← hFront]
                  exact
                    ⟨args',
                      FrontendOccurrence.StmtIncomingUserCall.switchScrutinee
                        hOccurrence⟩
  | @ifCondition condition body name args hExprOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hCondition : (Expr.elaborate condition).run state with
      | error err =>
          simp [hCondition] at hElab
      | ok conditionResult =>
          rcases conditionResult with ⟨frontCondition, conditionState⟩
          rcases
            Expr.elaborate_resolved_source_user_call_occurrence
              hExprOccurs hNameOk hResolve hCondition with
            ⟨args', hOccurrence⟩
          simp [hCondition] at hElab
          cases hBody :
              (Stmt.List.elaborateBlock body true).run conditionState with
          | error err =>
              simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              simp [hBody] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtIncomingUserCall.ifCondition
                    hOccurrence⟩

theorem elaborate_resolved_source_stmt_call_incoming_occurrence
    {stmt : Raw.Stmt} {state finalState : State}
    {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Stmt.elaborate stmt).run state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  rcases
    elaborate_resolved_incoming_scope_source_user_call_occurrence
      hOccurs hNameOk hResolve hElab with
    ⟨args', hOccurrence⟩
  exact
    ⟨args',
      FrontendOccurrence.StmtUserCall.ofIncoming hOccurrence⟩

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

theorem localFunctionScope_preserves_functionScopes
    (stmts : List Raw.Stmt) :
    PreservesFunctionScopes (Stmt.List.localFunctionScope stmts) := by
  induction stmts with
  | nil =>
      simp [Stmt.List.localFunctionScope]
      exact PreservesFunctionScopes.pure []
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          change PreservesFunctionScopes
            (Stmt.List.localFunctionScope rest >>= fun tail =>
              if tail.any fun entry => entry.fst == name then
                throw s!"duplicate Yul function {name} in block"
              else
                declareIdentifiers [name] "function" >>= fun _ =>
                  freshGeneratedFunctionName name >>= fun generated =>
                    pure ((name, generated) :: tail))
          exact
            PreservesFunctionScopes.bind ih (fun tail => by
              cases hDuplicate :
                  (tail.any fun entry => entry.fst == name) with
              | false =>
                  simp [hDuplicate]
                  exact
                    PreservesFunctionScopes.bind
                      (declareIdentifiers_preserves_functionScopes
                        [name] "function")
                      (fun _ =>
                        PreservesFunctionScopes.bind
                          (freshGeneratedFunctionName_preserves_functionScopes
                            name)
                          (fun generated =>
                            PreservesFunctionScopes.pure
                              ((name, generated) :: tail)))
              | true =>
                  simp [hDuplicate]
                  exact PreservesFunctionScopes.throw
                    s!"duplicate Yul function {name} in block")
      | block stmts =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | variableDeclaration names value? =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | assignment names value =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | expressionStatement expr =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | switch scrutinee cases default =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | forLoop pre condition post body =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | ifThen condition body =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | «break» =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | «continue» =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
          exact ih
      | «leave» =>
          change PreservesFunctionScopes (Stmt.List.localFunctionScope rest)
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

mutual

theorem Stmt.elaborate_preserves_functionScopes
    (stmt : Raw.Stmt) : PreservesFunctionScopes (Stmt.elaborate stmt) := by
  cases stmt with
  | block stmts =>
      simp only [Stmt.elaborate]
      exact
        PreservesFunctionScopes.bind
          (Stmt.List.elaborateBlock_preserves_functionScopes stmts true)
          (fun stmts => PreservesFunctionScopes.pure
            (Frontend.Stmt.block stmts))
  | variableDeclaration names value? =>
      cases value? with
      | none =>
          simp only [Stmt.elaborate]
          exact
            PreservesFunctionScopes.bind
              (declareIdentifiers_preserves_functionScopes names "variable")
              (fun _ => PreservesFunctionScopes.pure
                (Frontend.Stmt.letDecl names none))
      | some value =>
          simp only [Stmt.elaborate]
          exact
            PreservesFunctionScopes.bind
              (PreservesFunctionScopes.map some
                (Expr.elaborate_preserves_functionScopes value))
              (fun value? =>
                PreservesFunctionScopes.bind
                  (declareIdentifiers_preserves_functionScopes
                    names "variable")
                  (fun _ => PreservesFunctionScopes.pure
                    (Frontend.Stmt.letDecl names value?)))
  | assignment names value =>
      simp only [Stmt.elaborate]
      exact
        PreservesFunctionScopes.bind
          (requireIdentifiersVisible_preserves_functionScopes
            names "assignment")
          (fun _ =>
            PreservesFunctionScopes.bind
              (Expr.elaborate_preserves_functionScopes value)
              (fun value => PreservesFunctionScopes.pure
                (Frontend.Stmt.assign names value)))
  | expressionStatement expr =>
      simp only [Stmt.elaborate]
      exact
        PreservesFunctionScopes.bind
          (Expr.elaborate_preserves_functionScopes expr)
          (fun expr => PreservesFunctionScopes.pure
            (Frontend.Stmt.exprStmt expr))
  | functionDefinition name params returns body =>
      simp only [Stmt.elaborate]
      exact
        PreservesFunctionScopes.bind
          (resolveFunction_preserves_functionScopes name)
          (fun generated =>
            PreservesFunctionScopes.bind
              (FunctionDef.elaborate_preserves_functionScopes
                params returns body)
              (fun fn => PreservesFunctionScopes.pure
                (Frontend.Stmt.functionDef generated params returns fn.body)))
  | switch scrutinee cases defaultBody =>
      simp only [Stmt.elaborate]
      exact
        PreservesFunctionScopes.bind
          (Expr.elaborate_preserves_functionScopes scrutinee)
          (fun scrutinee =>
            PreservesFunctionScopes.bind
              (Stmt.CaseList.elaborate_preserves_functionScopes cases)
              (fun cases =>
                PreservesFunctionScopes.bind
                  (Stmt.List.elaborateBlock_preserves_functionScopes
                    defaultBody true)
                  (fun defaultBody => PreservesFunctionScopes.pure
                    (Frontend.Stmt.switch scrutinee cases defaultBody))))
  | forLoop pre condition post body =>
      cases hPre : Stmt.List.hasImmediateFunctionDefinition pre with
      | false =>
          simp only [Stmt.elaborate, hPre, Bool.false_eq_true, ↓reduceIte]
          exact
            PreservesFunctionScopes.bind
              pushIdentifierScope_preserves_functionScopes
              (fun _ =>
                PreservesFunctionScopes.bind
                  (Stmt.List.elaborateBlock_preserves_functionScopes
                    pre false)
                  (fun pre =>
                    PreservesFunctionScopes.bind
                      (Expr.elaborate_preserves_functionScopes condition)
                      (fun condition =>
                        PreservesFunctionScopes.bind
                          (Stmt.List.elaborateBlock_preserves_functionScopes
                            post true)
                          (fun post =>
                            PreservesFunctionScopes.bind
                              (Stmt.List.elaborateBlock_preserves_functionScopes
                                body true)
                              (fun body =>
                                PreservesFunctionScopes.bind
                                  popIdentifierScope_preserves_functionScopes
                                  (fun _ => PreservesFunctionScopes.pure
                                    (Frontend.Stmt.forLoop
                                      pre condition post body)))))))
      | true =>
          intro state state' value hRun
          simp only [Stmt.elaborate, hPre, Bool.true_eq_false, ↓reduceIte]
            at hRun
          simp [StateT.run_bind] at hRun
          cases hPushIdentifier : pushIdentifierScope.run state with
          | error err =>
              simp [hPushIdentifier] at hRun
          | ok pushIdentifierResult =>
              rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
              have hPushIdentifierScopes :
                  identifierPushedState.functionScopes =
                    state.functionScopes :=
                pushIdentifierScope_preserves_functionScopes
                  hPushIdentifier
              simp [hPushIdentifier] at hRun
              cases hPreRun :
                  (Stmt.List.elaborateForInitBlockWithScope pre).run
                    identifierPushedState with
              | error err =>
                  simp [hPreRun] at hRun
              | ok preResult =>
                  rcases preResult with ⟨preFront, preState⟩
                  rcases
                      Stmt.List.elaborateForInitBlockWithScope_functionScopes
                        hPreRun with
                    ⟨scope, hPreScopes⟩
                  simp [hPreRun] at hRun
                  cases hCond :
                      (Expr.elaborate condition).run preState with
                  | error err =>
                      simp [hCond] at hRun
                  | ok condResult =>
                      rcases condResult with ⟨conditionFront, condState⟩
                      have hCondScopes :
                          condState.functionScopes =
                            preState.functionScopes :=
                        Expr.elaborate_preserves_functionScopes
                          condition hCond
                      simp [hCond] at hRun
                      cases hPost :
                          (Stmt.List.elaborateBlock post true).run
                            condState with
                      | error err =>
                          simp [hPost] at hRun
                      | ok postResult =>
                          rcases postResult with ⟨postFront, postState⟩
                          have hPostScopes :
                              postState.functionScopes =
                                condState.functionScopes :=
                            Stmt.List.elaborateBlock_preserves_functionScopes
                              post true hPost
                          simp [hPost] at hRun
                          cases hBody :
                              (Stmt.List.elaborateBlock body true).run
                                postState with
                          | error err =>
                              simp [hBody] at hRun
                          | ok bodyResult =>
                              rcases bodyResult with ⟨bodyFront, bodyState⟩
                              have hBodyScopes :
                                  bodyState.functionScopes =
                                    postState.functionScopes :=
                                Stmt.List.elaborateBlock_preserves_functionScopes
                                  body true hBody
                              simp [hBody] at hRun
                              have hBodyStack :
                                  bodyState.functionScopes =
                                    scope :: state.functionScopes := by
                                rw [hBodyScopes, hPostScopes, hCondScopes,
                                  hPreScopes, hPushIdentifierScopes]
                              cases hPopFunction :
                                  popFunctionScope.run bodyState with
                              | error err =>
                                  simp [hPopFunction] at hRun
                              | ok popFunctionResult =>
                                  rcases popFunctionResult with
                                    ⟨_, functionPoppedState⟩
                                  have hPopFunctionScopes :
                                      functionPoppedState.functionScopes =
                                        state.functionScopes :=
                                    popFunctionScope_functionScopes
                                      hBodyStack hPopFunction
                                  simp [hPopFunction] at hRun
                                  cases hPopIdentifier :
                                      popIdentifierScope.run
                                        functionPoppedState with
                                  | error err =>
                                      simp [hPopIdentifier] at hRun
                                  | ok popIdentifierResult =>
                                      rcases popIdentifierResult with
                                        ⟨_, identifierPoppedState⟩
                                      have hPopIdentifierScopes :
                                          identifierPoppedState.functionScopes =
                                            functionPoppedState.functionScopes :=
                                        popIdentifierScope_preserves_functionScopes
                                          hPopIdentifier
                                      simp [hPopIdentifier] at hRun
                                      rcases hRun with ⟨_hValue, hFinal⟩
                                      cases hFinal
                                      exact
                                        hPopIdentifierScopes.trans
                                          hPopFunctionScopes
  | ifThen condition body =>
      simp only [Stmt.elaborate]
      exact
        PreservesFunctionScopes.bind
          (Expr.elaborate_preserves_functionScopes condition)
          (fun condition =>
            PreservesFunctionScopes.bind
              (Stmt.List.elaborateBlock_preserves_functionScopes
                body true)
              (fun body => PreservesFunctionScopes.pure
                (Frontend.Stmt.ifThen condition body)))
  | «break» =>
      simp only [Stmt.elaborate]
      exact PreservesFunctionScopes.pure Frontend.Stmt.break
  | «continue» =>
      simp only [Stmt.elaborate]
      exact PreservesFunctionScopes.pure Frontend.Stmt.continue
  | «leave» =>
      simp only [Stmt.elaborate]
      exact PreservesFunctionScopes.pure Frontend.Stmt.leave
  termination_by 20 * sizeOf stmt + 18
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborate_preserves_functionScopes
    (stmts : List Raw.Stmt) :
    PreservesFunctionScopes (Stmt.List.elaborate stmts) := by
  cases stmts with
  | nil =>
      simp [Stmt.List.elaborate]
      exact PreservesFunctionScopes.pure []
  | cons stmt rest =>
      simp [Stmt.List.elaborate]
      exact
        PreservesFunctionScopes.bind
          (Stmt.elaborate_preserves_functionScopes stmt)
          (fun head =>
            PreservesFunctionScopes.bind
              (Stmt.List.elaborate_preserves_functionScopes rest)
              (fun tail => PreservesFunctionScopes.pure (head :: tail)))
  termination_by 20 * sizeOf stmts + 10
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.hoistLocalFunctions_preserves_functionScopes
    (stmts : List Raw.Stmt) (scope : List (Name × Name)) :
    PreservesFunctionScopes (Stmt.List.hoistLocalFunctions stmts scope) := by
  cases stmts with
  | nil =>
      simp [Stmt.List.hoistLocalFunctions]
      exact PreservesFunctionScopes.pure ()
  | cons stmt rest =>
      cases stmt with
      | functionDefinition name params returns body =>
          cases hLookup : lookupFunctionInScope name scope with
          | none =>
              simp [Stmt.List.hoistLocalFunctions, hLookup]
              exact PreservesFunctionScopes.throw
                s!"internal frontend error: missing generated name for {name}"
          | some generated =>
              simp [Stmt.List.hoistLocalFunctions, hLookup]
              exact
                PreservesFunctionScopes.bind
                  (FunctionDef.elaborate_preserves_functionScopes
                    params returns body)
                  (fun fn =>
                    PreservesFunctionScopes.bind
                      (hoistFunctionEntry_preserves_functionScopes
                        generated fn)
                      (fun _ =>
                        Stmt.List.hoistLocalFunctions_preserves_functionScopes
                          rest scope))
      | block stmts =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | variableDeclaration names value? =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | assignment names value =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | expressionStatement expr =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | switch scrutinee cases default =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | forLoop pre condition post body =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | ifThen condition body =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | «break» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | «continue» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
      | «leave» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_functionScopes
              rest scope
  termination_by 20 * sizeOf stmts + 12
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateBlock_preserves_functionScopes
    (stmts : List Raw.Stmt) (createsScope : Bool) :
    PreservesFunctionScopes (Stmt.List.elaborateBlock stmts createsScope) := by
  intro state state' value hRun
  cases createsScope with
  | false =>
      unfold Stmt.List.elaborateBlock at hRun
      simp [StateT.run_bind] at hRun
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run state with
      | error err =>
          simp [hScope] at hRun
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          have hScopeScopes :
              scopeState.functionScopes = state.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes stmts hScope
          simp [hScope] at hRun
          cases hPush : (pushFunctionScope scope).run scopeState with
          | error err =>
              simp [hPush] at hRun
          | ok pushResult =>
              rcases pushResult with ⟨_, pushedState⟩
              have hPushScopes :
                  pushedState.functionScopes =
                    scope :: scopeState.functionScopes :=
                pushFunctionScope_functionScopes hPush
              simp [hPush] at hRun
              cases hHoist :
                  (Stmt.List.hoistLocalFunctions stmts scope).run
                    pushedState with
              | error err =>
                  simp [hHoist] at hRun
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  have hHoistScopes :
                      hoistState.functionScopes =
                        pushedState.functionScopes :=
                    Stmt.List.hoistLocalFunctions_preserves_functionScopes
                      stmts scope hHoist
                  simp [hHoist] at hRun
                  cases hElab :
                      (Stmt.List.elaborate stmts).run hoistState with
                  | error err =>
                      simp [hElab] at hRun
                  | ok elabResult =>
                      rcases elabResult with ⟨front, elabState⟩
                      have hElabScopes :
                          elabState.functionScopes =
                            hoistState.functionScopes :=
                        Stmt.List.elaborate_preserves_functionScopes
                          stmts hElab
                      simp [hElab] at hRun
                      have hStack :
                          elabState.functionScopes =
                            scope :: state.functionScopes := by
                        rw [hElabScopes, hHoistScopes, hPushScopes,
                          hScopeScopes]
                      cases hPop : popFunctionScope.run elabState with
                      | error err =>
                          simp [hPop] at hRun
                      | ok popResult =>
                          rcases popResult with ⟨_, poppedState⟩
                          have hPopScopes :
                              poppedState.functionScopes =
                                state.functionScopes :=
                            popFunctionScope_functionScopes hStack hPop
                          simp [hPop] at hRun
                          rcases hRun with ⟨_hValue, hFinal⟩
                          cases hFinal
                          exact hPopScopes
  | true =>
      unfold Stmt.List.elaborateBlock at hRun
      simp [StateT.run_bind] at hRun
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hRun
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushIdentifierScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          simp [hPushIdentifier] at hRun
          cases hScope :
              (Stmt.List.localFunctionScope stmts).run
                identifierPushedState with
          | error err =>
              simp [hScope] at hRun
          | ok scopeResult =>
              rcases scopeResult with ⟨scope, scopeState⟩
              have hScopeScopes :
                  scopeState.functionScopes =
                    identifierPushedState.functionScopes :=
                Stmt.List.localFunctionScope_preserves_functionScopes
                  stmts hScope
              simp [hScope] at hRun
              cases hPushFunction :
                  (pushFunctionScope scope).run scopeState with
              | error err =>
                  simp [hPushFunction] at hRun
              | ok pushFunctionResult =>
                  rcases pushFunctionResult with ⟨_, functionPushedState⟩
                  have hPushFunctionScopes :
                      functionPushedState.functionScopes =
                        scope :: scopeState.functionScopes :=
                    pushFunctionScope_functionScopes hPushFunction
                  simp [hPushFunction] at hRun
                  cases hHoist :
                      (Stmt.List.hoistLocalFunctions stmts scope).run
                        functionPushedState with
                  | error err =>
                      simp [hHoist] at hRun
                  | ok hoistResult =>
                      rcases hoistResult with ⟨_, hoistState⟩
                      have hHoistScopes :
                          hoistState.functionScopes =
                            functionPushedState.functionScopes :=
                        Stmt.List.hoistLocalFunctions_preserves_functionScopes
                          stmts scope hHoist
                      simp [hHoist] at hRun
                      cases hElab :
                          (Stmt.List.elaborate stmts).run hoistState with
                      | error err =>
                          simp [hElab] at hRun
                      | ok elabResult =>
                          rcases elabResult with ⟨front, elabState⟩
                          have hElabScopes :
                              elabState.functionScopes =
                                hoistState.functionScopes :=
                            Stmt.List.elaborate_preserves_functionScopes
                              stmts hElab
                          simp [hElab] at hRun
                          have hStack :
                              elabState.functionScopes =
                                scope :: state.functionScopes := by
                            rw [hElabScopes, hHoistScopes,
                              hPushFunctionScopes, hScopeScopes,
                              hPushIdentifierScopes]
                          cases hPopFunction :
                              popFunctionScope.run elabState with
                          | error err =>
                              simp [hPopFunction] at hRun
                          | ok popFunctionResult =>
                              rcases popFunctionResult with
                                ⟨_, functionPoppedState⟩
                              have hPopFunctionScopes :
                                  functionPoppedState.functionScopes =
                                    state.functionScopes :=
                                popFunctionScope_functionScopes
                                  hStack hPopFunction
                              simp [hPopFunction] at hRun
                              cases hPopIdentifier :
                                  popIdentifierScope.run
                                    functionPoppedState with
                              | error err =>
                                  simp [hPopIdentifier] at hRun
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  have hPopIdentifierScopes :
                                      identifierPoppedState.functionScopes =
                                        functionPoppedState.functionScopes :=
                                    popIdentifierScope_preserves_functionScopes
                                      hPopIdentifier
                                  simp [hPopIdentifier] at hRun
                                  rcases hRun with ⟨_hValue, hFinal⟩
                                  cases hFinal
                                  exact hPopIdentifierScopes.trans
                                    hPopFunctionScopes
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateForInitBlockWithScope_functionScopes
    {stmts : List Raw.Stmt} {state state' : State}
    {front : List Frontend.Stmt}
    (hRun :
      (Stmt.List.elaborateForInitBlockWithScope stmts).run state =
        .ok (front, state')) :
    ∃ scope, state'.functionScopes = scope :: state.functionScopes := by
  unfold Stmt.List.elaborateForInitBlockWithScope at hRun
  simp [StateT.run_bind] at hRun
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hRun
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      have hScopeScopes :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes stmts hScope
      simp [hScope] at hRun
      cases hPush : (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPush] at hRun
      | ok pushResult =>
          rcases pushResult with ⟨_, pushedState⟩
          have hPushScopes :
              pushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPush
          simp [hPush] at hRun
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                pushedState with
          | error err =>
              simp [hHoist] at hRun
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    pushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              simp [hHoist] at hRun
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hRun
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  have hElabScopes :
                      elabState.functionScopes =
                        hoistState.functionScopes :=
                    Stmt.List.elaborate_preserves_functionScopes
                      stmts hElab
                  simp [hElab] at hRun
                  rcases hRun with ⟨_hFront, hFinal⟩
                  cases hFinal
                  refine ⟨scope, ?_⟩
                  rw [hElabScopes, hHoistScopes, hPushScopes, hScopeScopes]
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.CaseList.elaborate_preserves_functionScopes
    (cases : List (Raw.SwitchCaseValue × List Raw.Stmt)) :
    PreservesFunctionScopes (Stmt.CaseList.elaborate cases) := by
  cases cases with
  | nil =>
      simp [Stmt.CaseList.elaborate]
      exact PreservesFunctionScopes.pure []
  | cons head rest =>
      rcases head with ⟨value, body⟩
      cases value with
      | literal literal =>
          cases literal with
          | number value =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesFunctionScopes.bind
                  (Stmt.List.elaborateBlock_preserves_functionScopes
                    body true)
                  (fun body =>
                    PreservesFunctionScopes.bind
                      (Stmt.CaseList.elaborate_preserves_functionScopes
                        rest)
                      (fun rest => PreservesFunctionScopes.pure
                        ((Frontend.SwitchCaseValue.word value, body) ::
                          rest)))
          | bool value =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesFunctionScopes.bind
                  (Stmt.List.elaborateBlock_preserves_functionScopes
                    body true)
                  (fun body =>
                    PreservesFunctionScopes.bind
                      (Stmt.CaseList.elaborate_preserves_functionScopes
                        rest)
                      (fun rest => PreservesFunctionScopes.pure
                        ((Frontend.SwitchCaseValue.boolLit value, body) ::
                          rest)))
          | stringLit value =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesFunctionScopes.bind
                  (Stmt.List.elaborateBlock_preserves_functionScopes
                    body true)
                  (fun body =>
                    PreservesFunctionScopes.bind
                      (Stmt.CaseList.elaborate_preserves_functionScopes
                        rest)
                      (fun rest => PreservesFunctionScopes.pure
                        ((Frontend.SwitchCaseValue.stringLit value, body) ::
                          rest)))
          | bytesLit bytes =>
              simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate]
              exact
                PreservesFunctionScopes.bind
                  (Stmt.List.elaborateBlock_preserves_functionScopes
                    body true)
                  (fun body =>
                    PreservesFunctionScopes.bind
                      (Stmt.CaseList.elaborate_preserves_functionScopes
                        rest)
                      (fun rest => PreservesFunctionScopes.pure
                        ((Frontend.SwitchCaseValue.bytesLit bytes, body) ::
                          rest)))
  termination_by 20 * sizeOf cases + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem FunctionDef.elaborate_preserves_functionScopes
    (params returns : List Name) (body : List Raw.Stmt) :
    PreservesFunctionScopes (FunctionDef.elaborate params returns body) := by
  simp [FunctionDef.elaborate]
  exact
    PreservesFunctionScopes.bind
      pushIdentifierScope_preserves_functionScopes
      (fun _ =>
        PreservesFunctionScopes.bind
          (declareIdentifiers_preserves_functionScopes
            (params ++ returns) "function parameter/result")
          (fun _ =>
            PreservesFunctionScopes.bind
              (Stmt.List.elaborateBlock_preserves_functionScopes
                body true)
              (fun body =>
                PreservesFunctionScopes.bind
                  popIdentifierScope_preserves_functionScopes
                  (fun _ => PreservesFunctionScopes.pure
                    ({ params, returns, body } : Frontend.FunctionDef)))))
  termination_by 20 * sizeOf body + 16
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end

namespace Stmt.List

theorem elaborate_incoming_scope_source_user_call_occurrence
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {fronts : List Frontend.Stmt}
    {scope : List (Name × Name)}
    {outer : List (List (Name × Name))}
    {name generated : Name} {args : List Raw.Expr}
    (hMem : stmt ∈ stmts)
    (hOccurs : Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Stmt.List.elaborate stmts).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.StmtIncomingUserCall front generated args' := by
  induction stmts generalizing state finalState fronts outer with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      simp at hMem
      rcases hMem with hHeadMem | hTailMem
      · subst stmt
        cases hHead : (Stmt.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            rcases
              EvmCompiler.Solidity.RawAst.Elab.Stmt.elaborate_incoming_scope_source_user_call_occurrence
                hOccurs hNameOk hLookup hScopes hHead with
              ⟨args', hOccurrence⟩
            simp [hHead] at hElab
            cases hTail :
                (Stmt.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                have hMemFront : headFront ∈ fronts := by
                  rw [← hElab.1]
                  simp
                exact ⟨args', headFront, hMemFront, hOccurrence⟩
      · cases hHead : (Stmt.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            have hHeadScopes :
                headState.functionScopes = scope :: outer := by
              rw [Stmt.elaborate_preserves_functionScopes head hHead,
                hScopes]
            simp [hHead] at hElab
            cases hTail :
                (Stmt.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                rcases ih hTailMem hHeadScopes hTail with
                  ⟨args', front, hMemTail, hOccurrence⟩
                have hMemFront : front ∈ fronts := by
                  rw [← hElab.1]
                  exact List.mem_cons_of_mem _ hMemTail
                exact ⟨args', front, hMemFront, hOccurrence⟩

theorem elaborate_resolved_incoming_scope_source_user_call_occurrence
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {fronts : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hMem : stmt ∈ stmts)
    (hOccurs : Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Stmt.List.elaborate stmts).run state =
      .ok (fronts, finalState)) :
    ∃ args' front,
      front ∈ fronts ∧
        FrontendOccurrence.StmtIncomingUserCall front generated args' := by
  induction stmts generalizing state finalState fronts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      simp at hMem
      rcases hMem with hHeadMem | hTailMem
      · subst stmt
        cases hHead : (Stmt.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            rcases
              EvmCompiler.Solidity.RawAst.Elab.Stmt.elaborate_resolved_incoming_scope_source_user_call_occurrence
                hOccurs hNameOk hResolve hHead with
              ⟨args', hOccurrence⟩
            simp [hHead] at hElab
            cases hTail :
                (Stmt.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                have hMemFront : headFront ∈ fronts := by
                  rw [← hElab.1]
                  simp
                exact ⟨args', headFront, hMemFront, hOccurrence⟩
      · cases hHead : (Stmt.elaborate head).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨headFront, headState⟩
            have hHeadScopes :
                headState.functionScopes = state.functionScopes :=
              Stmt.elaborate_preserves_functionScopes head hHead
            have hHeadResolve :
                resolveFunctionIn name headState.functionScopes =
                  some generated := by
              rw [hHeadScopes]
              exact hResolve
            simp [hHead] at hElab
            cases hTail :
                (Stmt.List.elaborate rest).run headState with
            | error err =>
                simp [hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨tailFronts, tailState⟩
                simp [hTail] at hElab
                rcases ih hTailMem hHeadResolve hTail with
                  ⟨args', front, hMemTail, hOccurrence⟩
                have hMemFront : front ∈ fronts := by
                  rw [← hElab.1]
                  exact List.mem_cons_of_mem _ hMemTail
                exact ⟨args', front, hMemFront, hOccurrence⟩

theorem elaborate_resolved_source_stmt_list_call_incoming_mem
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {fronts : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hMem : stmt ∈ stmts)
    (hOccurs : Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Stmt.List.elaborate stmts).run state =
      .ok (fronts, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall fronts generated args' := by
  have _hSourceList :
      Raw.Source.StmtListCall stmts name args :=
    Raw.Source.StmtListCall.of_mem_incoming hMem hOccurs
  rcases
    elaborate_resolved_incoming_scope_source_user_call_occurrence
      hMem hOccurs hNameOk hResolve hElab with
    ⟨args', front, hMemFront, hOccurrence⟩
  exact
    ⟨args',
      FrontendOccurrence.StmtListUserCall.of_mem_incoming
        hMemFront hOccurrence⟩

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

theorem localFunctionScope_noLocalFunctionNamed_lookup_none
    {stmts : List Raw.Stmt} {state scopeState : State}
    {scope : List (Name × Name)} {name : Name}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name) :
    lookupFunctionInScope name scope = none := by
  cases hLookup : lookupFunctionInScope name scope with
  | none => rfl
  | some generated =>
      rcases localFunctionScope_lookup_functionDefinition hScope hLookup with
        ⟨params, returns, body, hMem⟩
      exact False.elim (hNoShadow hMem)

theorem lookupFunctionInScope_any_eq_true
    {scope : List (Name × Name)} {name generated : Name}
    (hLookup : lookupFunctionInScope name scope = some generated) :
    (scope.any fun entry => entry.fst == name) = true := by
  induction scope with
  | nil =>
      simp [lookupFunctionInScope] at hLookup
  | cons entry rest ih =>
      rcases entry with ⟨source, target⟩
      by_cases hName : source = name
      · subst name
        simp [lookupFunctionInScope]
      · simp [lookupFunctionInScope, hName] at hLookup
        have hTailAny := ih hLookup
        change (((source == name) ||
          (rest.any fun entry => entry.fst == name)) = true)
        simp [hName, hTailAny]

theorem localFunctionScope_lookup_bindingNameOk
    {stmts : List Raw.Stmt} {state scopeState : State}
    {scope : List (Name × Name)} {name generated : Name}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hLookup : lookupFunctionInScope name scope = some generated) :
    bindingNameOk? name = true := by
  induction stmts generalizing state scopeState scope with
  | nil =>
      simp [Stmt.List.localFunctionScope, lookupFunctionInScope] at hScope
      cases hScope
      simp [lookupFunctionInScope] at hLookup
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition head headParams headReturns headBody =>
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
                            exact
                              declareIdentifiers_single_bindingNameOk
                                hDeclare
                          · simp [lookupFunctionInScope, hName] at hLookup
                            exact ih hTail hLookup
      | block stmts =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | variableDeclaration names value? =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | assignment names value =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | expressionStatement expr =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | switch scrutinee cases default =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | forLoop pre condition post body =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | ifThen condition body =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | «break» =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | «continue» =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup
      | «leave» =>
          unfold Stmt.List.localFunctionScope at hScope
          exact ih hScope hLookup

theorem localFunctionScope_functionDefinition_lookup
    {stmts : List Raw.Stmt} {state scopeState : State}
    {scope : List (Name × Name)} {name : Name}
    {params returns : List Name} {body : List Raw.Stmt}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hMem :
      .functionDefinition name params returns body ∈ stmts) :
    ∃ generated, lookupFunctionInScope name scope = some generated := by
  induction stmts generalizing state scopeState scope with
  | nil =>
      simp at hMem
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition head headParams headReturns headBody =>
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
                          simp at hMem
                          rcases hMem with hHead | hTailMem
                          · rcases hHead with
                              ⟨hName, hParams, hReturns, hBody⟩
                            subst head
                            subst headParams
                            subst headReturns
                            subst headBody
                            exact
                              ⟨headGenerated,
                                by simp [lookupFunctionInScope]⟩
                          · rcases ih hTail hTailMem with
                              ⟨generated, hLookupTail⟩
                            by_cases hName : head = name
                            · subst name
                              have hAny :
                                  (tailScope.any fun entry =>
                                    entry.fst == head) = true :=
                                lookupFunctionInScope_any_eq_true hLookupTail
                              rw [hAny] at hDuplicate
                              cases hDuplicate
                            · exact
                                ⟨generated,
                                  by
                                    simp [lookupFunctionInScope, hName,
                                      hLookupTail]⟩
      | block stmts =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | variableDeclaration names value? =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | assignment names value =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | expressionStatement expr =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | switch scrutinee cases default =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | forLoop pre condition post body =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | ifThen condition body =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | «break» =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | «continue» =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem
      | «leave» =>
          unfold Stmt.List.localFunctionScope at hScope
          simp at hMem
          exact ih hScope hMem

theorem localFunctionScope_sourceLocalFunction_lookup
    {stmts : List Raw.Stmt} {state scopeState : State}
    {scope : List (Name × Name)} {name : Name}
    {params returns : List Name} {body : List Raw.Stmt}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body) :
    ∃ generated, lookupFunctionInScope name scope = some generated := by
  exact
    localFunctionScope_functionDefinition_lookup hScope
      (Raw.Source.LocalFunction.mem hLocal)

theorem localFunctionScope_sourceLocalFunction_bindingNameOk
    {stmts : List Raw.Stmt} {state scopeState : State}
    {scope : List (Name × Name)} {name : Name}
    {params returns : List Name} {body : List Raw.Stmt}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body) :
    bindingNameOk? name = true := by
  rcases localFunctionScope_sourceLocalFunction_lookup hScope hLocal with
    ⟨generated, hLookup⟩
  exact localFunctionScope_lookup_bindingNameOk hScope hLookup

theorem localFunctionScope_sourceLocalFunction_classifyCall_user
    {stmts : List Raw.Stmt} {state scopeState : State}
    {scope : List (Name × Name)} {name : Name}
    {params returns : List Name} {body : List Raw.Stmt}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body) :
    CallClass.classifyCall name = .user := by
  exact
    bindingNameOk_classifyCall_user
      (localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal)

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

theorem sourceLocalFunction_hoistLocalFunctions_elaborate_user_call_entry
    {stmts : List Raw.Stmt}
    {scopeInit scopeState hoistState callState argState : State}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hScope :
      (Stmt.List.localFunctionScope stmts).run scopeInit =
        .ok (scope, scopeState))
    (hHoist :
      (Stmt.List.hoistLocalFunctions stmts scope).run scopeState =
        .ok ((), hoistState))
    (hArgs :
      (Expr.List.elaborate args).run callState = .ok (args', argState))
    (hArgScopes : argState.functionScopes = scope :: outer)
    (hClass : CallClass.classifyCall name = .user) :
    ∃ generated fn,
      (Expr.elaborate (.functionCall name args)).run callState =
          .ok (.call .user generated args', argState) ∧
        (generated, fn) ∈ hoistState.hoistedFunctions := by
  rcases localFunctionScope_sourceLocalFunction_lookup hScope hLocal with
    ⟨generated, hLookup⟩
  rcases localFunctionScope_hoistLocalFunctions_elaborate_user_call_entry
      hNotMemoryguard hNotClz hScope hHoist hLookup hArgs hArgScopes
      hClass with
    ⟨hCall, _params, _returns, _body, fn, _hRawMem, hEntry⟩
  exact ⟨generated, fn, hCall, hEntry⟩

theorem sourceLocalFunction_hoistLocalFunctions_elaborate_user_call_entry_failClosed
    {stmts : List Raw.Stmt}
    {scopeInit scopeState hoistState callState argState : State}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hScope :
      (Stmt.List.localFunctionScope stmts).run scopeInit =
        .ok (scope, scopeState))
    (hHoist :
      (Stmt.List.hoistLocalFunctions stmts scope).run scopeState =
        .ok ((), hoistState))
    (hArgs :
      (Expr.List.elaborate args).run callState = .ok (args', argState))
    (hCallScopes : callState.functionScopes = scope :: outer) :
    ∃ generated fn,
      (Expr.elaborate (.functionCall name args)).run callState =
          .ok (.call .user generated args', argState) ∧
        (generated, fn) ∈ hoistState.hoistedFunctions := by
  have hNameOk :=
    localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
  have hClass :=
    bindingNameOk_classifyCall_user hNameOk
  have hArgScopes : argState.functionScopes = scope :: outer := by
    rw [Expr.List.elaborate_preserves_functionScopes args hArgs,
      hCallScopes]
  exact
    sourceLocalFunction_hoistLocalFunctions_elaborate_user_call_entry
      hLocal (bindingNameOk_ne_memoryguard hNameOk)
      (bindingNameOk_ne_clz hNameOk) hScope hHoist hArgs hArgScopes
      hClass

theorem hasImmediateFunctionDefinition_of_sourceLocalFunction
    {stmts : List Raw.Stmt} {name : Name}
    {params returns : List Name} {body : List Raw.Stmt}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body) :
    Stmt.List.hasImmediateFunctionDefinition stmts = true := by
  induction hLocal with
  | here =>
      simp [Stmt.List.hasImmediateFunctionDefinition]
  | @tail stmt rest name params returns body hLocal ih =>
      cases stmt <;> simp [Stmt.List.hasImmediateFunctionDefinition, ih]

theorem sourceLocalFunction_elaborateForInitBlockWithScope_entry
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hRun :
      (Stmt.List.elaborateForInitBlockWithScope stmts).run state =
        .ok (front, finalState)) :
    ∃ generated fn scope,
      lookupFunctionInScope name scope = some generated ∧
        bindingNameOk? name = true ∧
        finalState.functionScopes = scope :: state.functionScopes ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  unfold Stmt.List.elaborateForInitBlockWithScope at hRun
  simp [StateT.run_bind] at hRun
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hRun
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      rcases localFunctionScope_sourceLocalFunction_lookup hScope hLocal with
        ⟨generated, hLookup⟩
      have hNameOk :
          bindingNameOk? name = true :=
        localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
      have hScopeScopes :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes stmts hScope
      simp [hScope] at hRun
      cases hPush : (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPush] at hRun
      | ok pushResult =>
          rcases pushResult with ⟨_, pushedState⟩
          have hPushScopes :
              pushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPush
          simp [hPush] at hRun
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                pushedState with
          | error err =>
              simp [hHoist] at hRun
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              rcases hoistLocalFunctions_functionDefinition_entry
                  (Raw.Source.LocalFunction.mem hLocal) hLookup hHoist with
                ⟨fn, hEntryHoist⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    pushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              simp [hHoist] at hRun
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hRun
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  have hElabScopes :
                      elabState.functionScopes =
                        hoistState.functionScopes :=
                    Stmt.List.elaborate_preserves_functionScopes
                      stmts hElab
                  have hEntryFinal :
                      (generated, fn) ∈
                        elabState.hoistedFunctions :=
                    Stmt.List.elaborate_preserves_hoistedFunction_mem
                      stmts hElab hEntryHoist
                  simp [hElab] at hRun
                  rcases hRun with ⟨_hFront, hFinal⟩
                  cases hFinal
                  refine ⟨generated, fn, scope, hLookup, hNameOk, ?_, hEntryFinal⟩
                  rw [hElabScopes, hHoistScopes, hPushScopes, hScopeScopes]

theorem localFunctionScope_elaborateBlock_false_lookup_entry
    {stmts : List Raw.Stmt}
    {state scopeState finalState : State}
    {scope : List (Name × Name)} {name generated : Name}
    {front : List Frontend.Stmt}
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState))
    (hLookup : lookupFunctionInScope name scope = some generated) :
    ∃ params returns body fn,
      .functionDefinition name params returns body ∈ stmts ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases localFunctionScope_lookup_functionDefinition hScope hLookup with
    ⟨params, returns, body, hRawMem⟩
  unfold Stmt.List.elaborateBlock at hBlock
  simp [hScope, StateT.run_bind] at hBlock
  cases hPush : (pushFunctionScope scope).run scopeState with
  | error err =>
      simp [hPush] at hBlock
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      simp [hPush] at hBlock
      cases hHoist :
          (Stmt.List.hoistLocalFunctions stmts scope).run pushedState with
      | error err =>
          simp [hHoist] at hBlock
      | ok hoistResult =>
          rcases hoistResult with ⟨_, hoistState⟩
          simp [hHoist] at hBlock
          rcases hoistLocalFunctions_functionDefinition_entry
              hRawMem hLookup hHoist with ⟨fn, hEntryHoist⟩
          cases hElab : (Stmt.List.elaborate stmts).run hoistState with
          | error err =>
              simp [hElab] at hBlock
          | ok elabResult =>
              rcases elabResult with ⟨front', elabState⟩
              have hEntryElab :
                  (generated, fn) ∈ elabState.hoistedFunctions :=
                Stmt.List.elaborate_preserves_hoistedFunction_mem
                  stmts hElab hEntryHoist
              simp [hElab] at hBlock
              cases hPop : popFunctionScope.run elabState with
              | error err =>
                  simp [hPop] at hBlock
              | ok popResult =>
                  rcases popResult with ⟨_, poppedState⟩
                  have hEntryFinal :
                      (generated, fn) ∈ poppedState.hoistedFunctions :=
                    popFunctionScope_preserves_hoistedFunction_mem
                      hPop hEntryElab
                  simp [hPop] at hBlock
                  rcases hBlock with ⟨_hFront, hFinal⟩
                  cases hFinal
                  exact ⟨params, returns, body, fn, hRawMem, hEntryFinal⟩

theorem localFunctionScope_elaborateBlock_true_lookup_entry
    {stmts : List Raw.Stmt}
    {state pushedState scopeState finalState : State}
    {scope : List (Name × Name)} {name generated : Name}
    {front : List Frontend.Stmt}
    (hPushScope : pushIdentifierScope.run state = .ok ((), pushedState))
    (hScope :
      (Stmt.List.localFunctionScope stmts).run pushedState =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState))
    (hLookup : lookupFunctionInScope name scope = some generated) :
    ∃ params returns body fn,
      .functionDefinition name params returns body ∈ stmts ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases localFunctionScope_lookup_functionDefinition hScope hLookup with
    ⟨params, returns, body, hRawMem⟩
  unfold Stmt.List.elaborateBlock at hBlock
  simp [hPushScope, hScope, StateT.run_bind] at hBlock
  cases hPushFunction : (pushFunctionScope scope).run scopeState with
  | error err =>
      simp [hPushFunction] at hBlock
  | ok pushResult =>
      rcases pushResult with ⟨_, functionPushedState⟩
      simp [hPushFunction] at hBlock
      cases hHoist :
          (Stmt.List.hoistLocalFunctions stmts scope).run
            functionPushedState with
      | error err =>
          simp [hHoist] at hBlock
      | ok hoistResult =>
          rcases hoistResult with ⟨_, hoistState⟩
          simp [hHoist] at hBlock
          rcases hoistLocalFunctions_functionDefinition_entry
              hRawMem hLookup hHoist with ⟨fn, hEntryHoist⟩
          cases hElab : (Stmt.List.elaborate stmts).run hoistState with
          | error err =>
              simp [hElab] at hBlock
          | ok elabResult =>
              rcases elabResult with ⟨front', elabState⟩
              have hEntryElab :
                  (generated, fn) ∈ elabState.hoistedFunctions :=
                Stmt.List.elaborate_preserves_hoistedFunction_mem
                  stmts hElab hEntryHoist
              simp [hElab] at hBlock
              cases hPopFunction : popFunctionScope.run elabState with
              | error err =>
                  simp [hPopFunction] at hBlock
              | ok popFunctionResult =>
                  rcases popFunctionResult with ⟨_, functionPoppedState⟩
                  have hEntryFunctionPopped :
                      (generated, fn) ∈
                        functionPoppedState.hoistedFunctions :=
                    popFunctionScope_preserves_hoistedFunction_mem
                      hPopFunction hEntryElab
                  simp [hPopFunction] at hBlock
                  cases hPopIdentifier :
                      popIdentifierScope.run functionPoppedState with
                  | error err =>
                      simp [hPopIdentifier] at hBlock
                  | ok popIdentifierResult =>
                      rcases popIdentifierResult with
                        ⟨_, identifierPoppedState⟩
                      have hEntryFinalState :
                          (generated, fn) ∈
                            identifierPoppedState.hoistedFunctions :=
                        popIdentifierScope_preserves_hoistedFunction_mem
                          hPopIdentifier hEntryFunctionPopped
                      simp [hPopIdentifier] at hBlock
                      rcases hBlock with ⟨_hFront, hFinal⟩
                      cases hFinal
                      exact
                        ⟨params, returns, body, fn, hRawMem,
                          hEntryFinalState⟩

theorem sourceLocalFunction_elaborateBlock_false_entry
    {stmts : List Raw.Stmt}
    {state scopeState finalState : State}
    {scope : List (Name × Name)} {name : Name}
    {params returns : List Name} {body : List Raw.Stmt}
    {front : List Frontend.Stmt}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState)) :
    ∃ generated fn,
      lookupFunctionInScope name scope = some generated ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases localFunctionScope_sourceLocalFunction_lookup hScope hLocal with
    ⟨generated, hLookup⟩
  rcases localFunctionScope_elaborateBlock_false_lookup_entry
      hScope hBlock hLookup with
    ⟨_params, _returns, _body, fn, _hMem, hEntry⟩
  exact ⟨generated, fn, hLookup, hEntry⟩

theorem sourceLocalFunction_elaborateBlock_false_elaborate_user_call_entry
    {stmts : List Raw.Stmt}
    {state scopeState finalState callState argState : State}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {front : List Frontend.Stmt}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState))
    (hArgs :
      (Expr.List.elaborate args).run callState = .ok (args', argState))
    (hArgScopes : argState.functionScopes = scope :: outer)
    (hClass : CallClass.classifyCall name = .user) :
    ∃ generated fn,
      (Expr.elaborate (.functionCall name args)).run callState =
          .ok (.call .user generated args', argState) ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases sourceLocalFunction_elaborateBlock_false_entry
      hLocal hScope hBlock with
    ⟨generated, fn, hLookup, hEntry⟩
  have hResolve :
      resolveFunctionIn name argState.functionScopes = some generated := by
    rw [hArgScopes]
    exact resolveFunctionIn_of_scope_lookup hLookup
  exact
    ⟨generated, fn,
      Expr.elaborate_user_call_resolved
        hNotMemoryguard hNotClz hArgs hClass hResolve,
      hEntry⟩

theorem sourceLocalFunction_elaborateBlock_false_elaborate_user_call_entry_failClosed
    {stmts : List Raw.Stmt}
    {state scopeState finalState callState argState : State}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {front : List Frontend.Stmt}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hScope :
      (Stmt.List.localFunctionScope stmts).run state =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState))
    (hArgs :
      (Expr.List.elaborate args).run callState = .ok (args', argState))
    (hCallScopes : callState.functionScopes = scope :: outer) :
    ∃ generated fn,
      (Expr.elaborate (.functionCall name args)).run callState =
          .ok (.call .user generated args', argState) ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hNameOk :=
    localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
  have hClass :=
    bindingNameOk_classifyCall_user hNameOk
  have hArgScopes : argState.functionScopes = scope :: outer := by
    rw [Expr.List.elaborate_preserves_functionScopes args hArgs,
      hCallScopes]
  exact
    sourceLocalFunction_elaborateBlock_false_elaborate_user_call_entry
      hLocal (bindingNameOk_ne_memoryguard hNameOk)
      (bindingNameOk_ne_clz hNameOk) hScope hBlock hArgs hArgScopes
      hClass

theorem elaborate_source_local_call_mem
    {stmts : List Raw.Stmt} {state finalState : State}
    {front : List Frontend.Stmt} {scope : List (Name × Name)}
    {outer : List (List (Name × Name))} {name generated : Name}
    {args : List Raw.Expr}
    (hCall : Raw.Source.LocalCall stmts name args)
    (hNameOk : bindingNameOk? name = true)
    (hLookup : lookupFunctionInScope name scope = some generated)
    (hScopes : state.functionScopes = scope :: outer)
    (hElab : (Stmt.List.elaborate stmts).run state =
      .ok (front, finalState)) :
    ∃ args',
      .exprStmt (.call .user generated args') ∈ front := by
  induction hCall generalizing state finalState front outer with
  | here =>
      rename_i callName callArgs rest
      unfold Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      have hNotMemoryguard : callName ≠ "memoryguard" :=
        bindingNameOk_ne_memoryguard hNameOk
      have hNotClz : callName ≠ "clz" :=
        bindingNameOk_ne_clz hNameOk
      have hClass : CallClass.classifyCall callName = .user :=
        bindingNameOk_classifyCall_user hNameOk
      cases hArgs : (Expr.List.elaborate callArgs).run state with
      | error err =>
          simp [Stmt.elaborate, Expr.elaborate, hNotMemoryguard, hNotClz,
            hArgs, hClass] at hElab
      | ok argResult =>
          rcases argResult with ⟨args', argState⟩
          have hArgScopes :
              argState.functionScopes = scope :: outer := by
            rw [Expr.List.elaborate_preserves_functionScopes callArgs hArgs,
              hScopes]
          have hResolve :
              resolveFunctionIn callName argState.functionScopes =
                some generated := by
            rw [hArgScopes]
            exact resolveFunctionIn_of_scope_lookup hLookup
          have hCallElab :
              (Expr.elaborate (.functionCall callName callArgs)).run state =
                .ok (.call .user generated args', argState) :=
            Expr.elaborate_user_call_resolved
              hNotMemoryguard hNotClz hArgs hClass hResolve
          have hHead :
              (Stmt.elaborate
                (.expressionStatement
                  (.functionCall callName callArgs))).run state =
                .ok
                  (.exprStmt (.call .user generated args'), argState) := by
            simp [Stmt.elaborate, StateT.run_bind, hCallElab]
          simp [hHead] at hElab
          cases hTail :
              (Stmt.List.elaborate rest).run argState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailState⟩
              simp [hTail] at hElab
              have hMemFront :
                  .exprStmt (.call .user generated args') ∈ front := by
                rw [← hElab.1]
                simp
              exact ⟨args', hMemFront⟩
  | tail hCall ih =>
      rename_i stmt rest callName callArgs
      unfold Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Stmt.elaborate stmt).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨head, headState⟩
          have hHeadScopes :
              headState.functionScopes = scope :: outer := by
            rw [Stmt.elaborate_preserves_functionScopes stmt hHead,
              hScopes]
          simp [hHead] at hElab
          cases hTail :
              (Stmt.List.elaborate rest).run headState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailState⟩
              simp [hTail] at hElab
              rcases ih hNameOk hLookup hHeadScopes hTail with
                ⟨args', hMem⟩
              have hMemFront :
                  .exprStmt (.call .user generated args') ∈ front := by
                rw [← hElab.1]
                exact List.mem_cons_of_mem _ hMem
              exact ⟨args', hMemFront⟩

theorem sourceLocalFunction_elaborateBlock_false_head_user_call_entry
    {rest : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction
        (.expressionStatement (.functionCall name args) :: rest)
        name params returns body)
    (hBlock :
      (Stmt.List.elaborateBlock
          (.expressionStatement (.functionCall name args) :: rest)
          false).run state = .ok (front, finalState)) :
    ∃ generated fn args' frontTail,
      front = .exprStmt (.call .user generated args') :: frontTail ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  let stmts :=
    (.expressionStatement (.functionCall name args) :: rest)
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope : (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [stmts, hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      simp [stmts, hScope] at hBlock
      cases hPush : (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPush] at hBlock
      | ok pushResult =>
          rcases pushResult with ⟨_, pushedState⟩
          have hScopePres :
              scopeState.functionScopes = state.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          have hPushScopes :
              pushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPush
          simp [hPush] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run pushedState with
          | error err =>
              simp [stmts, hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    pushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hCallScopes :
                  hoistState.functionScopes = scope :: state.functionScopes := by
                rw [hHoistScopes, hPushScopes, hScopePres]
              simp [stmts, hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [stmts, hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  simp [stmts, hElab] at hBlock
                  cases hPop : popFunctionScope.run elabState with
                  | error err =>
                      simp [hPop] at hBlock
                  | ok popResult =>
                      rcases popResult with ⟨_, poppedState⟩
                      simp [hPop] at hBlock
                      unfold Stmt.List.elaborate at hElab
                      simp [stmts, StateT.run_bind] at hElab
                      have hNameOk :
                          bindingNameOk? name = true :=
                        localFunctionScope_sourceLocalFunction_bindingNameOk
                          hScope hLocal
                      have hNotMemoryguard : name ≠ "memoryguard" :=
                        bindingNameOk_ne_memoryguard hNameOk
                      have hNotClz : name ≠ "clz" :=
                        bindingNameOk_ne_clz hNameOk
                      have hClass : CallClass.classifyCall name = .user :=
                        bindingNameOk_classifyCall_user hNameOk
                      cases hArgs :
                          (Expr.List.elaborate args).run hoistState with
                      | error err =>
                          simp [Stmt.elaborate, Expr.elaborate,
                            hNotMemoryguard, hNotClz, hArgs, hClass] at hElab
                      | ok argResult =>
                          rcases argResult with ⟨args', argState⟩
                          rcases
                            sourceLocalFunction_elaborateBlock_false_elaborate_user_call_entry_failClosed
                              (stmts := stmts) (state := state)
                              (scopeState := scopeState)
                              (finalState := finalState)
                              (callState := hoistState)
                              (argState := argState)
                              (scope := scope)
                              (outer := state.functionScopes)
                              (name := name) (params := params)
                              (returns := returns) (body := body)
                              (front := front) (args := args)
                              (args' := args') hLocal hScope hBlockRun
                              hArgs hCallScopes with
                          ⟨generated, fn, hCall, hEntryFinal⟩
                          have hHead :
                              (Stmt.elaborate
                                (.expressionStatement
                                  (.functionCall name args))).run
                                  hoistState =
                                .ok
                                  (.exprStmt
                                    (.call .user generated args'),
                                    argState) := by
                            simp [Stmt.elaborate, StateT.run_bind, hCall]
                          simp [hHead] at hElab
                          cases hTail :
                              (Stmt.List.elaborate rest).run argState with
                          | error err =>
                              simp [hTail] at hElab
                          | ok tailResult =>
                              rcases tailResult with ⟨frontTail, tailState⟩
                              simp [hTail] at hElab
                              have hFrontShape :
                                  front' =
                                    .exprStmt
                                      (.call .user generated args') ::
                                        frontTail :=
                                hElab.1.symm
                              have hFront :
                                  front =
                                    .exprStmt
                                      (.call .user generated args') ::
                                        frontTail := by
                                exact hBlock.1.symm.trans hFrontShape
                              exact
                                ⟨generated, fn, args', frontTail, hFront,
                                  hEntryFinal⟩

theorem sourceLocalFunction_elaborateBlock_false_localCall_mem_entry
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hCall : Raw.Source.LocalCall stmts name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      .exprStmt (.call .user generated args') ∈ front ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope : (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      simp [hScope] at hBlock
      rcases sourceLocalFunction_elaborateBlock_false_entry
          hLocal hScope hBlockRun with
        ⟨generated, fn, hLookup, hEntryFinal⟩
      have hNameOk :
          bindingNameOk? name = true :=
        localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
      cases hPush : (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPush] at hBlock
      | ok pushResult =>
          rcases pushResult with ⟨_, pushedState⟩
          have hScopePres :
              scopeState.functionScopes = state.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          have hPushScopes :
              pushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPush
          simp [hPush] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run pushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    pushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hCallScopes :
                  hoistState.functionScopes =
                    scope :: state.functionScopes := by
                rw [hHoistScopes, hPushScopes, hScopePres]
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  rcases elaborate_source_local_call_mem
                      hCall hNameOk hLookup hCallScopes hElab with
                    ⟨args', hMemFront'⟩
                  simp [hElab] at hBlock
                  cases hPop : popFunctionScope.run elabState with
                  | error err =>
                      simp [hPop] at hBlock
                  | ok popResult =>
                      rcases popResult with ⟨_, poppedState⟩
                      simp [hPop] at hBlock
                      have hMemFront :
                          .exprStmt (.call .user generated args') ∈
                            front := by
                        rw [← hBlock.1]
                        exact hMemFront'
                      exact ⟨generated, fn, args', hMemFront, hEntryFinal⟩

theorem sourceLocalFunction_elaborateBlock_false_incoming_call_mem_entry
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState)) :
    ∃ generated fn args' frontStmt,
      frontStmt ∈ front ∧
        FrontendOccurrence.StmtIncomingUserCall
          frontStmt generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope : (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      simp [hScope] at hBlock
      rcases sourceLocalFunction_elaborateBlock_false_entry
          hLocal hScope hBlockRun with
        ⟨generated, fn, hLookup, hEntryFinal⟩
      have hNameOk :
          bindingNameOk? name = true :=
        localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
      cases hPush : (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPush] at hBlock
      | ok pushResult =>
          rcases pushResult with ⟨_, pushedState⟩
          have hScopePres :
              scopeState.functionScopes = state.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          have hPushScopes :
              pushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPush
          simp [hPush] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run pushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    pushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hCallScopes :
                  hoistState.functionScopes =
                    scope :: state.functionScopes := by
                rw [hHoistScopes, hPushScopes, hScopePres]
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  rcases
                    Stmt.List.elaborate_incoming_scope_source_user_call_occurrence
                      hMem hOccurs hNameOk hLookup hCallScopes hElab with
                    ⟨args', frontStmt, hMemFront', hOccurrence⟩
                  simp [hElab] at hBlock
                  cases hPop : popFunctionScope.run elabState with
                  | error err =>
                      simp [hPop] at hBlock
                  | ok popResult =>
                      rcases popResult with ⟨_, poppedState⟩
                      simp [hPop] at hBlock
                      have hMemFront :
                          frontStmt ∈ front := by
                        rw [← hBlock.1]
                        exact hMemFront'
                      exact
                        ⟨generated, fn, args', frontStmt, hMemFront,
                          hOccurrence, hEntryFinal⟩

theorem sourceLocalFunction_elaborateBlock_false_stmtUserCall_entry
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtListUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases sourceLocalFunction_elaborateBlock_false_incoming_call_mem_entry
      hLocal hMem hOccurs hBlock with
    ⟨generated, fn, args', frontStmt, hMemFront, hOccurrence, hEntry⟩
  exact
    ⟨generated, fn, args',
      FrontendOccurrence.StmtListUserCall.of_mem_incoming
        hMemFront hOccurrence,
      hEntry⟩

theorem sourceLocalFunction_elaborateBlock_true_entry
    {stmts : List Raw.Stmt}
    {state pushedState scopeState finalState : State}
    {scope : List (Name × Name)} {name : Name}
    {params returns : List Name} {body : List Raw.Stmt}
    {front : List Frontend.Stmt}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hPushScope : pushIdentifierScope.run state = .ok ((), pushedState))
    (hScope :
      (Stmt.List.localFunctionScope stmts).run pushedState =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ generated fn,
      lookupFunctionInScope name scope = some generated ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases localFunctionScope_sourceLocalFunction_lookup hScope hLocal with
    ⟨generated, hLookup⟩
  rcases localFunctionScope_elaborateBlock_true_lookup_entry
      hPushScope hScope hBlock hLookup with
    ⟨_params, _returns, _body, fn, _hMem, hEntry⟩
  exact ⟨generated, fn, hLookup, hEntry⟩

theorem sourceLocalFunction_elaborateBlock_true_elaborate_user_call_entry
    {stmts : List Raw.Stmt}
    {state pushedState scopeState finalState callState argState : State}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {front : List Frontend.Stmt}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hPushScope : pushIdentifierScope.run state = .ok ((), pushedState))
    (hScope :
      (Stmt.List.localFunctionScope stmts).run pushedState =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState))
    (hArgs :
      (Expr.List.elaborate args).run callState = .ok (args', argState))
    (hArgScopes : argState.functionScopes = scope :: outer)
    (hClass : CallClass.classifyCall name = .user) :
    ∃ generated fn,
      (Expr.elaborate (.functionCall name args)).run callState =
          .ok (.call .user generated args', argState) ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases sourceLocalFunction_elaborateBlock_true_entry
      hLocal hPushScope hScope hBlock with
    ⟨generated, fn, hLookup, hEntry⟩
  have hResolve :
      resolveFunctionIn name argState.functionScopes = some generated := by
    rw [hArgScopes]
    exact resolveFunctionIn_of_scope_lookup hLookup
  exact
    ⟨generated, fn,
      Expr.elaborate_user_call_resolved
        hNotMemoryguard hNotClz hArgs hClass hResolve,
      hEntry⟩

theorem sourceLocalFunction_elaborateBlock_true_elaborate_user_call_entry_failClosed
    {stmts : List Raw.Stmt}
    {state pushedState scopeState finalState callState argState : State}
    {scope : List (Name × Name)} {outer : List (List (Name × Name))}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {front : List Frontend.Stmt}
    {args : List Raw.Expr} {args' : List Frontend.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hPushScope : pushIdentifierScope.run state = .ok ((), pushedState))
    (hScope :
      (Stmt.List.localFunctionScope stmts).run pushedState =
        .ok (scope, scopeState))
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState))
    (hArgs :
      (Expr.List.elaborate args).run callState = .ok (args', argState))
    (hCallScopes : callState.functionScopes = scope :: outer) :
    ∃ generated fn,
      (Expr.elaborate (.functionCall name args)).run callState =
          .ok (.call .user generated args', argState) ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hNameOk :=
    localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
  have hClass :=
    bindingNameOk_classifyCall_user hNameOk
  have hArgScopes : argState.functionScopes = scope :: outer := by
    rw [Expr.List.elaborate_preserves_functionScopes args hArgs,
      hCallScopes]
  exact
    sourceLocalFunction_elaborateBlock_true_elaborate_user_call_entry
      hLocal (bindingNameOk_ne_memoryguard hNameOk)
      (bindingNameOk_ne_clz hNameOk) hPushScope hScope hBlock hArgs
      hArgScopes hClass

theorem sourceLocalFunction_elaborateBlock_true_head_user_call_entry
    {rest : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction
        (.expressionStatement (.functionCall name args) :: rest)
        name params returns body)
    (hBlock :
      (Stmt.List.elaborateBlock
          (.expressionStatement (.functionCall name args) :: rest)
          true).run state = .ok (front, finalState)) :
    ∃ generated fn args' frontTail,
      front = .exprStmt (.call .user generated args') :: frontTail ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  let stmts :=
    (.expressionStatement (.functionCall name args) :: rest)
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hBlock
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      have hIdentifierPushScopes :
          identifierPushedState.functionScopes = state.functionScopes :=
        pushIdentifierScope_preserves_functionScopes hPushIdentifier
      simp [hPushIdentifier] at hBlock
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run
            identifierPushedState with
      | error err =>
          simp [stmts, hScope] at hBlock
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          have hScopePres :
              scopeState.functionScopes =
                identifierPushedState.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          simp [stmts, hScope] at hBlock
          cases hPushFunction :
              (pushFunctionScope scope).run scopeState with
          | error err =>
              simp [hPushFunction] at hBlock
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              have hPushFunctionScopes :
                  functionPushedState.functionScopes =
                    scope :: scopeState.functionScopes :=
                pushFunctionScope_functionScopes hPushFunction
              simp [hPushFunction] at hBlock
              cases hHoist :
                  (Stmt.List.hoistLocalFunctions stmts scope).run
                    functionPushedState with
              | error err =>
                  simp [stmts, hHoist] at hBlock
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  have hHoistScopes :
                      hoistState.functionScopes =
                        functionPushedState.functionScopes :=
                    Stmt.List.hoistLocalFunctions_preserves_functionScopes
                      stmts scope hHoist
                  have hCallScopes :
                      hoistState.functionScopes =
                        scope :: state.functionScopes := by
                    rw [hHoistScopes, hPushFunctionScopes, hScopePres,
                      hIdentifierPushScopes]
                  simp [stmts, hHoist] at hBlock
                  cases hElab :
                      (Stmt.List.elaborate stmts).run hoistState with
                  | error err =>
                      simp [stmts, hElab] at hBlock
                  | ok elabResult =>
                      rcases elabResult with ⟨front', elabState⟩
                      simp [stmts, hElab] at hBlock
                      cases hPopFunction :
                          popFunctionScope.run elabState with
                      | error err =>
                          simp [hPopFunction] at hBlock
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hBlock
                          cases hPopIdentifier :
                              popIdentifierScope.run functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hBlock
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hBlock
                              unfold Stmt.List.elaborate at hElab
                              simp [stmts, StateT.run_bind] at hElab
                              have hNameOk :
                                  bindingNameOk? name = true :=
                                localFunctionScope_sourceLocalFunction_bindingNameOk
                                  hScope hLocal
                              have hNotMemoryguard : name ≠ "memoryguard" :=
                                bindingNameOk_ne_memoryguard hNameOk
                              have hNotClz : name ≠ "clz" :=
                                bindingNameOk_ne_clz hNameOk
                              have hClass :
                                  CallClass.classifyCall name = .user :=
                                bindingNameOk_classifyCall_user hNameOk
                              cases hArgs :
                                  (Expr.List.elaborate args).run
                                    hoistState with
                              | error err =>
                                  simp [Stmt.elaborate, Expr.elaborate,
                                    hNotMemoryguard, hNotClz, hArgs, hClass]
                                    at hElab
                              | ok argResult =>
                                  rcases argResult with ⟨args', argState⟩
                                  rcases
                                    sourceLocalFunction_elaborateBlock_true_elaborate_user_call_entry_failClosed
                                      (stmts := stmts) (state := state)
                                      (pushedState := identifierPushedState)
                                      (scopeState := scopeState)
                                      (finalState := finalState)
                                      (callState := hoistState)
                                      (argState := argState)
                                      (scope := scope)
                                      (outer := state.functionScopes)
                                      (name := name) (params := params)
                                      (returns := returns) (body := body)
                                      (front := front) (args := args)
                                      (args' := args') hLocal
                                      hPushIdentifier hScope hBlockRun
                                      hArgs hCallScopes with
                                  ⟨generated, fn, hCall, hEntryFinal⟩
                                  have hHead :
                                      (Stmt.elaborate
                                        (.expressionStatement
                                          (.functionCall name args))).run
                                          hoistState =
                                        .ok
                                          (.exprStmt
                                            (.call .user generated args'),
                                            argState) := by
                                    simp [Stmt.elaborate, StateT.run_bind,
                                      hCall]
                                  simp [hHead] at hElab
                                  cases hTail :
                                      (Stmt.List.elaborate rest).run
                                        argState with
                                  | error err =>
                                      simp [hTail] at hElab
                                  | ok tailResult =>
                                      rcases tailResult with
                                        ⟨frontTail, tailState⟩
                                      simp [hTail] at hElab
                                      have hFrontShape :
                                          front' =
                                            .exprStmt
                                              (.call .user generated args') ::
                                                frontTail :=
                                        hElab.1.symm
                                      have hFront :
                                          front =
                                            .exprStmt
                                              (.call .user generated args') ::
                                                frontTail := by
                                        exact hBlock.1.symm.trans hFrontShape
                                      exact
                                        ⟨generated, fn, args', frontTail,
                                          hFront, hEntryFinal⟩

theorem sourceLocalFunction_elaborateBlock_true_localCall_mem_entry
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hCall : Raw.Source.LocalCall stmts name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      .exprStmt (.call .user generated args') ∈ front ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hBlock
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      have hIdentifierPushScopes :
          identifierPushedState.functionScopes = state.functionScopes :=
        pushIdentifierScope_preserves_functionScopes hPushIdentifier
      simp [hPushIdentifier] at hBlock
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run
            identifierPushedState with
      | error err =>
          simp [hScope] at hBlock
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          simp [hScope] at hBlock
          rcases sourceLocalFunction_elaborateBlock_true_entry
              hLocal hPushIdentifier hScope hBlockRun with
            ⟨generated, fn, hLookup, hEntryFinal⟩
          have hNameOk :
              bindingNameOk? name = true :=
            localFunctionScope_sourceLocalFunction_bindingNameOk
              hScope hLocal
          have hScopePres :
              scopeState.functionScopes =
                identifierPushedState.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          cases hPushFunction :
              (pushFunctionScope scope).run scopeState with
          | error err =>
              simp [hPushFunction] at hBlock
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              have hPushFunctionScopes :
                  functionPushedState.functionScopes =
                    scope :: scopeState.functionScopes :=
                pushFunctionScope_functionScopes hPushFunction
              simp [hPushFunction] at hBlock
              cases hHoist :
                  (Stmt.List.hoistLocalFunctions stmts scope).run
                    functionPushedState with
              | error err =>
                  simp [hHoist] at hBlock
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  have hHoistScopes :
                      hoistState.functionScopes =
                        functionPushedState.functionScopes :=
                    Stmt.List.hoistLocalFunctions_preserves_functionScopes
                      stmts scope hHoist
                  have hCallScopes :
                      hoistState.functionScopes =
                        scope :: state.functionScopes := by
                    rw [hHoistScopes, hPushFunctionScopes, hScopePres,
                      hIdentifierPushScopes]
                  simp [hHoist] at hBlock
                  cases hElab :
                      (Stmt.List.elaborate stmts).run hoistState with
                  | error err =>
                      simp [hElab] at hBlock
                  | ok elabResult =>
                      rcases elabResult with ⟨front', elabState⟩
                      rcases elaborate_source_local_call_mem
                          hCall hNameOk hLookup hCallScopes hElab with
                        ⟨args', hMemFront'⟩
                      simp [hElab] at hBlock
                      cases hPopFunction :
                          popFunctionScope.run elabState with
                      | error err =>
                          simp [hPopFunction] at hBlock
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hBlock
                          cases hPopIdentifier :
                              popIdentifierScope.run
                                functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hBlock
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hBlock
                              have hMemFront :
                                  .exprStmt
                                      (.call .user generated args') ∈
                                    front := by
                                rw [← hBlock.1]
                                exact hMemFront'
                              exact
                                ⟨generated, fn, args', hMemFront,
                                  hEntryFinal⟩

theorem sourceLocalFunction_elaborateBlock_true_incoming_call_mem_entry
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ generated fn args' frontStmt,
      frontStmt ∈ front ∧
        FrontendOccurrence.StmtIncomingUserCall
          frontStmt generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hBlock
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      have hIdentifierPushScopes :
          identifierPushedState.functionScopes = state.functionScopes :=
        pushIdentifierScope_preserves_functionScopes hPushIdentifier
      simp [hPushIdentifier] at hBlock
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run
            identifierPushedState with
      | error err =>
          simp [hScope] at hBlock
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          simp [hScope] at hBlock
          rcases sourceLocalFunction_elaborateBlock_true_entry
              hLocal hPushIdentifier hScope hBlockRun with
            ⟨generated, fn, hLookup, hEntryFinal⟩
          have hNameOk :
              bindingNameOk? name = true :=
            localFunctionScope_sourceLocalFunction_bindingNameOk
              hScope hLocal
          have hScopePres :
              scopeState.functionScopes =
                identifierPushedState.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          cases hPushFunction :
              (pushFunctionScope scope).run scopeState with
          | error err =>
              simp [hPushFunction] at hBlock
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              have hPushFunctionScopes :
                  functionPushedState.functionScopes =
                    scope :: scopeState.functionScopes :=
                pushFunctionScope_functionScopes hPushFunction
              simp [hPushFunction] at hBlock
              cases hHoist :
                  (Stmt.List.hoistLocalFunctions stmts scope).run
                    functionPushedState with
              | error err =>
                  simp [hHoist] at hBlock
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  have hHoistScopes :
                      hoistState.functionScopes =
                        functionPushedState.functionScopes :=
                    Stmt.List.hoistLocalFunctions_preserves_functionScopes
                      stmts scope hHoist
                  have hCallScopes :
                      hoistState.functionScopes =
                        scope :: state.functionScopes := by
                    rw [hHoistScopes, hPushFunctionScopes, hScopePres,
                      hIdentifierPushScopes]
                  simp [hHoist] at hBlock
                  cases hElab :
                      (Stmt.List.elaborate stmts).run hoistState with
                  | error err =>
                      simp [hElab] at hBlock
                  | ok elabResult =>
                      rcases elabResult with ⟨front', elabState⟩
                      rcases
                        Stmt.List.elaborate_incoming_scope_source_user_call_occurrence
                          hMem hOccurs hNameOk hLookup hCallScopes hElab with
                        ⟨args', frontStmt, hMemFront', hOccurrence⟩
                      simp [hElab] at hBlock
                      cases hPopFunction :
                          popFunctionScope.run elabState with
                      | error err =>
                          simp [hPopFunction] at hBlock
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hBlock
                          cases hPopIdentifier :
                              popIdentifierScope.run
                                functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hBlock
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hBlock
                              have hMemFront :
                                  frontStmt ∈ front := by
                                rw [← hBlock.1]
                                exact hMemFront'
                              exact
                                ⟨generated, fn, args', frontStmt,
                                  hMemFront, hOccurrence, hEntryFinal⟩

theorem sourceLocalFunction_elaborateBlock_true_stmtUserCall_entry
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtListUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  rcases sourceLocalFunction_elaborateBlock_true_incoming_call_mem_entry
      hLocal hMem hOccurs hBlock with
    ⟨generated, fn, args', frontStmt, hMemFront, hOccurrence, hEntry⟩
  exact
    ⟨generated, fn, args',
      FrontendOccurrence.StmtListUserCall.of_mem_incoming
        hMemFront hOccurrence,
      hEntry⟩

theorem sourceLocalFunction_elaborateBlock_false_entry_of_run
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState)) :
    ∃ generated fn,
      (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      simp [hScope] at hBlock
      rcases sourceLocalFunction_elaborateBlock_false_entry
          hLocal hScope hBlockRun with
        ⟨generated, fn, hLookup, hEntry⟩
      exact ⟨generated, fn, hEntry⟩

theorem sourceLocalFunction_elaborateBlock_true_entry_of_run
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ generated fn,
      (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hPush : pushIdentifierScope.run state with
  | error err =>
      simp [hPush] at hBlock
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      simp [hPush] at hBlock
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run pushedState with
      | error err =>
          simp [hScope] at hBlock
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          simp [hScope] at hBlock
          rcases sourceLocalFunction_elaborateBlock_true_entry
              hLocal hPush hScope hBlockRun with
            ⟨generated, fn, hLookup, hEntry⟩
          exact ⟨generated, fn, hEntry⟩

theorem elaborateBlock_true_noShadow_resolved_incoming_call_mem
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolveOuter :
      resolveFunctionIn name state.functionScopes = some generated)
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall front generated args' := by
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hBlock
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      have hIdentifierPushScopes :
          identifierPushedState.functionScopes = state.functionScopes :=
        pushIdentifierScope_preserves_functionScopes hPushIdentifier
      simp [hPushIdentifier] at hBlock
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run
            identifierPushedState with
      | error err =>
          simp [hScope] at hBlock
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          have hLookupNone :
              lookupFunctionInScope name scope = none :=
            localFunctionScope_noLocalFunctionNamed_lookup_none
              hScope hNoShadow
          have hScopePres :
              scopeState.functionScopes =
                identifierPushedState.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          simp [hScope] at hBlock
          cases hPushFunction :
              (pushFunctionScope scope).run scopeState with
          | error err =>
              simp [hPushFunction] at hBlock
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              have hPushFunctionScopes :
                  functionPushedState.functionScopes =
                    scope :: scopeState.functionScopes :=
                pushFunctionScope_functionScopes hPushFunction
              simp [hPushFunction] at hBlock
              cases hHoist :
                  (Stmt.List.hoistLocalFunctions stmts scope).run
                    functionPushedState with
              | error err =>
                  simp [hHoist] at hBlock
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  have hHoistScopes :
                      hoistState.functionScopes =
                        functionPushedState.functionScopes :=
                    Stmt.List.hoistLocalFunctions_preserves_functionScopes
                      stmts scope hHoist
                  have hResolveHoist :
                      resolveFunctionIn name hoistState.functionScopes =
                        some generated := by
                    rw [hHoistScopes, hPushFunctionScopes, hScopePres,
                      hIdentifierPushScopes]
                    simp [resolveFunctionIn, hLookupNone, hResolveOuter]
                  simp [hHoist] at hBlock
                  cases hElab :
                      (Stmt.List.elaborate stmts).run hoistState with
                  | error err =>
                      simp [hElab] at hBlock
                  | ok elabResult =>
                      rcases elabResult with ⟨front', elabState⟩
                      rcases
                        Stmt.List.elaborate_resolved_incoming_scope_source_user_call_occurrence
                          hMem hOccurs hNameOk hResolveHoist hElab with
                        ⟨args', frontStmt, hMemFront', hOccurrence⟩
                      simp [hElab] at hBlock
                      cases hPopFunction :
                          popFunctionScope.run elabState with
                      | error err =>
                          simp [hPopFunction] at hBlock
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hBlock
                          cases hPopIdentifier :
                              popIdentifierScope.run
                                functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hBlock
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hBlock
                              have hMemFront :
                                  frontStmt ∈ front := by
                                rw [← hBlock.1]
                                exact hMemFront'
                              exact
                                ⟨args',
                                  FrontendOccurrence.StmtListUserCall.of_mem_incoming
                                    hMemFront hOccurrence⟩

theorem elaborateBlock_true_noShadow_resolved_source_stmt_list_call_incoming_mem
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolveOuter :
      resolveFunctionIn name state.functionScopes = some generated)
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall front generated args' := by
  have _hSourceList :
      Raw.Source.StmtListCall stmts name args :=
    Raw.Source.StmtListCall.of_mem_incoming hMem hOccurs
  exact
    elaborateBlock_true_noShadow_resolved_incoming_call_mem
      hNoShadow hMem hOccurs hNameOk hResolveOuter hBlock

theorem elaborateBlock_false_noShadow_resolved_incoming_call_mem
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolveOuter :
      resolveFunctionIn name state.functionScopes = some generated)
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall front generated args' := by
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      have hLookupNone :
          lookupFunctionInScope name scope = none :=
        localFunctionScope_noLocalFunctionNamed_lookup_none
          hScope hNoShadow
      have hScopePres :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes
          stmts hScope
      simp [hScope] at hBlock
      cases hPushFunction :
          (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPushFunction] at hBlock
      | ok pushFunctionResult =>
          rcases pushFunctionResult with ⟨_, functionPushedState⟩
          have hPushFunctionScopes :
              functionPushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPushFunction
          simp [hPushFunction] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                functionPushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    functionPushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hResolveHoist :
                  resolveFunctionIn name hoistState.functionScopes =
                    some generated := by
                rw [hHoistScopes, hPushFunctionScopes, hScopePres]
                simp [resolveFunctionIn, hLookupNone, hResolveOuter]
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  rcases
                    Stmt.List.elaborate_resolved_incoming_scope_source_user_call_occurrence
                      hMem hOccurs hNameOk hResolveHoist hElab with
                    ⟨args', frontStmt, hMemFront', hOccurrence⟩
                  simp [hElab] at hBlock
                  cases hPopFunction :
                      popFunctionScope.run elabState with
                  | error err =>
                      simp [hPopFunction] at hBlock
                  | ok popFunctionResult =>
                      rcases popFunctionResult with
                        ⟨_, functionPoppedState⟩
                      simp [hPopFunction] at hBlock
                      have hMemFront :
                          frontStmt ∈ front := by
                        rw [← hBlock.1]
                        exact hMemFront'
                      exact
                        ⟨args',
                          FrontendOccurrence.StmtListUserCall.of_mem_incoming
                            hMemFront hOccurrence⟩

theorem elaborateForInitBlockWithScope_noShadow_resolved_incoming_call_mem
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolveOuter :
      resolveFunctionIn name state.functionScopes = some generated)
    (hBlock :
      (Stmt.List.elaborateForInitBlockWithScope stmts).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall front generated args' := by
  unfold Stmt.List.elaborateForInitBlockWithScope at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      have hLookupNone :
          lookupFunctionInScope name scope = none :=
        localFunctionScope_noLocalFunctionNamed_lookup_none
          hScope hNoShadow
      have hScopePres :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes
          stmts hScope
      simp [hScope] at hBlock
      cases hPushFunction :
          (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPushFunction] at hBlock
      | ok pushFunctionResult =>
          rcases pushFunctionResult with ⟨_, functionPushedState⟩
          have hPushFunctionScopes :
              functionPushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPushFunction
          simp [hPushFunction] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                functionPushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    functionPushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hResolveHoist :
                  resolveFunctionIn name hoistState.functionScopes =
                    some generated := by
                rw [hHoistScopes, hPushFunctionScopes, hScopePres]
                simp [resolveFunctionIn, hLookupNone, hResolveOuter]
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  rcases
                    Stmt.List.elaborate_resolved_incoming_scope_source_user_call_occurrence
                      hMem hOccurs hNameOk hResolveHoist hElab with
                    ⟨args', frontStmt, hMemFront', hOccurrence⟩
                  simp [hElab] at hBlock
                  have hMemFront :
                      frontStmt ∈ front := by
                    rw [← hBlock.1]
                    exact hMemFront'
                  exact
                    ⟨args',
                      FrontendOccurrence.StmtListUserCall.of_mem_incoming
                        hMemFront hOccurrence⟩

theorem elaborateForInitBlockWithScope_noShadow_resolves_outer
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name generated : Name}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hResolveOuter :
      resolveFunctionIn name state.functionScopes = some generated)
    (hBlock :
      (Stmt.List.elaborateForInitBlockWithScope stmts).run state =
        .ok (front, finalState)) :
    resolveFunctionIn name finalState.functionScopes = some generated := by
  unfold Stmt.List.elaborateForInitBlockWithScope at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      have hLookupNone :
          lookupFunctionInScope name scope = none :=
        localFunctionScope_noLocalFunctionNamed_lookup_none
          hScope hNoShadow
      have hScopePres :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes
          stmts hScope
      simp [hScope] at hBlock
      cases hPushFunction :
          (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPushFunction] at hBlock
      | ok pushFunctionResult =>
          rcases pushFunctionResult with ⟨_, functionPushedState⟩
          have hPushFunctionScopes :
              functionPushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPushFunction
          simp [hPushFunction] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                functionPushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    functionPushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hResolveHoist :
                  resolveFunctionIn name hoistState.functionScopes =
                    some generated := by
                rw [hHoistScopes, hPushFunctionScopes, hScopePres]
                simp [resolveFunctionIn, hLookupNone, hResolveOuter]
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  have hElabScopes :
                      elabState.functionScopes =
                        hoistState.functionScopes :=
                    Stmt.List.elaborate_preserves_functionScopes
                      stmts hElab
                  simp [hElab] at hBlock
                  rcases hBlock with ⟨_hFront, hFinal⟩
                  cases hFinal
                  rw [hElabScopes]
                  exact hResolveHoist

end Stmt.List

theorem FunctionDef.elaborate_noShadow_resolved_source_stmt_list_call_incoming_mem
    {params returns : List Name} {body : List Raw.Stmt}
    {bodyStmt : Raw.Stmt}
    {state finalState : State} {fn : Frontend.FunctionDef}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hMem : bodyStmt ∈ body)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope bodyStmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (FunctionDef.elaborate params returns body).run state =
        .ok (fn, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall fn.body generated args' := by
  unfold FunctionDef.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      have hPushScopes :
          identifierPushedState.functionScopes =
            state.functionScopes :=
        pushIdentifierScope_preserves_functionScopes hPushIdentifier
      simp [hPushIdentifier] at hElab
      cases hDeclare :
          (declareIdentifiers (params ++ returns)
            "function parameter/result").run identifierPushedState with
      | error err =>
          simp [hDeclare] at hElab
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          have hDeclareScopes :
              declaredState.functionScopes =
                identifierPushedState.functionScopes :=
            declareIdentifiers_preserves_functionScopes
              (params ++ returns) "function parameter/result" hDeclare
          have hResolveBody :
              resolveFunctionIn name declaredState.functionScopes =
                some generated := by
            rw [hDeclareScopes, hPushScopes]
            exact hResolve
          simp [hDeclare] at hElab
          cases hBody :
              (Stmt.List.elaborateBlock body true).run declaredState with
          | error err =>
              simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              rcases
                Stmt.List.elaborateBlock_true_noShadow_resolved_source_stmt_list_call_incoming_mem
                  hNoShadow hMem hOccurs hNameOk hResolveBody hBody with
                ⟨args', hOccurrence⟩
              simp [hBody] at hElab
              cases hPopIdentifier : popIdentifierScope.run bodyState with
              | error err =>
                  simp [hPopIdentifier] at hElab
              | ok popIdentifierResult =>
                  rcases popIdentifierResult with
                    ⟨_, identifierPoppedState⟩
                  simp [hPopIdentifier] at hElab
                  rcases hElab with ⟨hFn, _hFinal⟩
                  rw [← hFn]
                  exact ⟨args', hOccurrence⟩

theorem Stmt.elaborate_functionDefinition_noShadow_resolved_source_stmt_list_call_incoming_mem
    {fnName : Name} {params returns : List Name}
    {body : List Raw.Stmt} {bodyStmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hMem : bodyStmt ∈ body)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope bodyStmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.functionDefinition fnName params returns body)).run
        state = .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hResolveFn : (resolveFunction fnName).run state with
  | error err =>
      simp [hResolveFn] at hElab
  | ok resolveResult =>
      rcases resolveResult with ⟨frontFnName, resolvedState⟩
      have hResolveFnScopes :
          resolvedState.functionScopes = state.functionScopes :=
        resolveFunction_preserves_functionScopes fnName hResolveFn
      have hResolveBody :
          resolveFunctionIn name resolvedState.functionScopes =
            some generated := by
        rw [hResolveFnScopes]
        exact hResolve
      simp [hResolveFn] at hElab
      cases hFn :
          (FunctionDef.elaborate params returns body).run resolvedState with
      | error err =>
          simp [hFn] at hElab
      | ok fnResult =>
          rcases fnResult with ⟨frontFn, fnState⟩
          rcases
            FunctionDef.elaborate_noShadow_resolved_source_stmt_list_call_incoming_mem
              hNoShadow hMem hOccurs hNameOk hResolveBody hFn with
            ⟨args', hOccurrence⟩
          simp [hFn] at hElab
          rcases hElab with ⟨hFront, _hFinal⟩
          rw [← hFront]
          exact
            ⟨args',
              FrontendOccurrence.StmtUserCall.functionBody hOccurrence⟩

theorem Stmt.elaborate_block_noShadow_resolved_source_stmt_list_call_incoming_mem
    {stmts : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hMem : stmt ∈ stmts)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.block stmts)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hBlock :
      (Stmt.List.elaborateBlock stmts true).run state with
  | error err =>
      simp [hBlock] at hElab
  | ok blockResult =>
      rcases blockResult with ⟨frontStmts, blockState⟩
      rcases
        Stmt.List.elaborateBlock_true_noShadow_resolved_source_stmt_list_call_incoming_mem
          hNoShadow hMem hOccurs hNameOk hResolve hBlock with
        ⟨args', hOccurrence⟩
      simp [hBlock] at hElab
      rcases hElab with ⟨hFront, _hState⟩
      rw [← hFront]
      exact ⟨args', FrontendOccurrence.StmtUserCall.block hOccurrence⟩

theorem Stmt.elaborate_ifBody_noShadow_resolved_source_stmt_list_call_incoming_mem
    {condition : Raw.Expr} {body : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hMem : stmt ∈ body)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.ifThen condition body)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hCondition :
      (Expr.elaborate condition).run state with
  | error err =>
      simp [hCondition] at hElab
  | ok conditionResult =>
      rcases conditionResult with ⟨frontCondition, conditionState⟩
      have hConditionScopes :
          conditionState.functionScopes = state.functionScopes :=
        Expr.elaborate_preserves_functionScopes condition hCondition
      have hResolveBody :
          resolveFunctionIn name conditionState.functionScopes =
            some generated := by
        rw [hConditionScopes]
        exact hResolve
      simp [hCondition] at hElab
      cases hBody :
          (Stmt.List.elaborateBlock body true).run conditionState with
      | error err =>
          simp [hBody] at hElab
      | ok bodyResult =>
          rcases bodyResult with ⟨frontBody, bodyState⟩
          rcases
            Stmt.List.elaborateBlock_true_noShadow_resolved_source_stmt_list_call_incoming_mem
              hNoShadow hMem hOccurs hNameOk hResolveBody hBody with
            ⟨args', hOccurrence⟩
          simp [hBody] at hElab
          rcases hElab with ⟨hFront, _hState⟩
          rw [← hFront]
          exact ⟨args', FrontendOccurrence.StmtUserCall.ifBody hOccurrence⟩

theorem Stmt.elaborate_switchDefault_noShadow_resolved_source_stmt_list_call_incoming_mem
    {scrutinee : Raw.Expr}
    {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {defaultBody : List Raw.Stmt} {stmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed defaultBody name)
    (hMem : stmt ∈ defaultBody)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.switch scrutinee cases defaultBody)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hScrutinee :
      (Expr.elaborate scrutinee).run state with
  | error err =>
      simp [hScrutinee] at hElab
  | ok scrutineeResult =>
      rcases scrutineeResult with ⟨frontScrutinee, scrutineeState⟩
      have hScrutineeScopes :
          scrutineeState.functionScopes = state.functionScopes :=
        Expr.elaborate_preserves_functionScopes scrutinee hScrutinee
      have hResolveCases :
          resolveFunctionIn name scrutineeState.functionScopes =
            some generated := by
        rw [hScrutineeScopes]
        exact hResolve
      simp [hScrutinee] at hElab
      cases hCases :
          (Stmt.CaseList.elaborate cases).run scrutineeState with
      | error err =>
          simp [hCases] at hElab
      | ok casesResult =>
          rcases casesResult with ⟨frontCases, casesState⟩
          have hCasesScopes :
              casesState.functionScopes =
                scrutineeState.functionScopes :=
            Stmt.CaseList.elaborate_preserves_functionScopes cases hCases
          have hResolveDefault :
              resolveFunctionIn name casesState.functionScopes =
                some generated := by
            rw [hCasesScopes]
            exact hResolveCases
          simp [hCases] at hElab
          cases hDefault :
              (Stmt.List.elaborateBlock defaultBody true).run
                casesState with
          | error err =>
              simp [hDefault] at hElab
          | ok defaultResult =>
              rcases defaultResult with ⟨frontDefault, defaultState⟩
              rcases
                Stmt.List.elaborateBlock_true_noShadow_resolved_source_stmt_list_call_incoming_mem
                  hNoShadow hMem hOccurs hNameOk hResolveDefault hDefault with
                ⟨args', hOccurrence⟩
              simp [hDefault] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtUserCall.switchDefault
                    hOccurrence⟩

theorem Stmt.CaseList.elaborate_noShadow_resolved_source_case_body_incoming_mem
    {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {caseValue : Raw.SwitchCaseValue} {body : List Raw.Stmt}
    {stmt : Raw.Stmt}
    {state finalState : State}
    {frontCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {name generated : Name} {args : List Raw.Expr}
    (hCaseMem : (caseValue, body) ∈ cases)
    (hNoShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hStmtMem : stmt ∈ body)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.CaseList.elaborate cases).run state =
        .ok (frontCases, finalState)) :
    ∃ args',
      FrontendOccurrence.CaseListUserCall frontCases generated args' := by
  induction cases generalizing state finalState frontCases with
  | nil =>
      simp at hCaseMem
  | cons head rest ih =>
      rcases head with ⟨headValue, headBody⟩
      simp at hCaseMem
      unfold Stmt.CaseList.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hValue : SwitchCaseValue.elaborate headValue with
      | error err =>
          simp [hValue] at hElab
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hElab
          cases hElab
      | ok frontValue =>
          simp [hValue] at hElab
          cases hHeadBody :
              (Stmt.List.elaborateBlock headBody true).run state with
          | error err =>
              simp [hHeadBody] at hElab
          | ok headBodyResult =>
              rcases headBodyResult with ⟨frontHeadBody, headBodyState⟩
              have hHeadBodyScopes :
                  headBodyState.functionScopes = state.functionScopes :=
                Stmt.List.elaborateBlock_preserves_functionScopes
                  headBody true hHeadBody
              have hResolveRest :
                  resolveFunctionIn name headBodyState.functionScopes =
                    some generated := by
                rw [hHeadBodyScopes]
                exact hResolve
              simp [hHeadBody] at hElab
              cases hRest :
                  (Stmt.CaseList.elaborate rest).run headBodyState with
              | error err =>
                  simp [hRest] at hElab
              | ok restResult =>
                  rcases restResult with ⟨frontRest, restState⟩
                  simp [hRest] at hElab
                  rcases hCaseMem with hHeadCase | hTailCase
                  · rcases hHeadCase with ⟨hCaseValue, hBodyEq⟩
                    subst caseValue
                    subst body
                    rcases
                      Stmt.List.elaborateBlock_true_noShadow_resolved_source_stmt_list_call_incoming_mem
                        hNoShadow hStmtMem hOccurs hNameOk
                        hResolve hHeadBody with
                      ⟨args', hOccurrence⟩
                    rcases hElab with ⟨hFront, _hState⟩
                    rw [← hFront]
                    exact
                      ⟨args',
                        FrontendOccurrence.CaseListUserCall.head
                          hOccurrence⟩
                  · rcases
                      ih hTailCase hResolveRest hRest with
                    ⟨args', hOccurrence⟩
                    rcases hElab with ⟨hFront, _hState⟩
                    rw [← hFront]
                    exact
                      ⟨args',
                        FrontendOccurrence.CaseListUserCall.tail
                          hOccurrence⟩

theorem Stmt.elaborate_switchCase_noShadow_resolved_source_case_body_incoming_mem
    {scrutinee : Raw.Expr}
    {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {defaultBody : List Raw.Stmt}
    {caseValue : Raw.SwitchCaseValue} {body : List Raw.Stmt}
    {stmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hCaseMem : (caseValue, body) ∈ cases)
    (hNoShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hStmtMem : stmt ∈ body)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.switch scrutinee cases defaultBody)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hScrutinee :
      (Expr.elaborate scrutinee).run state with
  | error err =>
      simp [hScrutinee] at hElab
  | ok scrutineeResult =>
      rcases scrutineeResult with ⟨frontScrutinee, scrutineeState⟩
      have hScrutineeScopes :
          scrutineeState.functionScopes = state.functionScopes :=
        Expr.elaborate_preserves_functionScopes scrutinee hScrutinee
      have hResolveCases :
          resolveFunctionIn name scrutineeState.functionScopes =
            some generated := by
        rw [hScrutineeScopes]
        exact hResolve
      simp [hScrutinee] at hElab
      cases hCases :
          (Stmt.CaseList.elaborate cases).run scrutineeState with
      | error err =>
          simp [hCases] at hElab
      | ok casesResult =>
          rcases casesResult with ⟨frontCases, casesState⟩
          rcases
            Stmt.CaseList.elaborate_noShadow_resolved_source_case_body_incoming_mem
              hCaseMem hNoShadow hStmtMem hOccurs hNameOk hResolveCases
              hCases with
            ⟨args', hCaseOccurrence⟩
          simp [hCases] at hElab
          cases hDefault :
              (Stmt.List.elaborateBlock defaultBody true).run casesState with
          | error err =>
              simp [hDefault] at hElab
          | ok defaultResult =>
              rcases defaultResult with ⟨frontDefault, defaultState⟩
              simp [hDefault] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtUserCall.switchCase
                    hCaseOccurrence⟩

theorem Stmt.elaborate_forLoop_condition_noShadow_resolved_source_expr_call
    {pre : List Raw.Stmt} {condition : Raw.Expr}
    {post body : List Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed pre name)
    (hOccurs : Raw.Source.ExprCall.Occurs condition name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  cases hPreHas : Stmt.List.hasImmediateFunctionDefinition pre with
  | false =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateBlock pre false).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              have hPreScopes :
                  preState.functionScopes =
                    identifierPushedState.functionScopes :=
                Stmt.List.elaborateBlock_preserves_functionScopes
                  pre false hPre
              have hResolveCondition :
                  resolveFunctionIn name preState.functionScopes =
                    some generated := by
                rw [hPreScopes, hPushScopes]
                exact hResolve
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  rcases
                    Expr.elaborate_resolved_source_user_call_occurrence
                      hOccurs hNameOk hResolveCondition hCondition with
                    ⟨args', hOccurrence⟩
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          simp [hBody] at hElab
                          cases hPopIdentifier :
                              popIdentifierScope.run bodyState with
                          | error err =>
                              simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨hFront, _hFinal⟩
                              rw [← hFront]
                              exact
                                ⟨args',
                                  FrontendOccurrence.StmtUserCall.forCondition
                                    hOccurrence⟩
  | true =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          have hResolvePre :
              resolveFunctionIn name identifierPushedState.functionScopes =
                some generated := by
            rw [hPushScopes]
            exact hResolve
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateForInitBlockWithScope pre).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              have hResolveCondition :
                  resolveFunctionIn name preState.functionScopes =
                    some generated :=
                Stmt.List.elaborateForInitBlockWithScope_noShadow_resolves_outer
                  hNoShadow hResolvePre hPre
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  rcases
                    Expr.elaborate_resolved_source_user_call_occurrence
                      hOccurs hNameOk hResolveCondition hCondition with
                    ⟨args', hOccurrence⟩
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          simp [hBody] at hElab
                          cases hPopFunction :
                              popFunctionScope.run bodyState with
                          | error err =>
                              simp [hPopFunction] at hElab
                          | ok popFunctionResult =>
                              rcases popFunctionResult with
                                ⟨_, functionPoppedState⟩
                              simp [hPopFunction] at hElab
                              cases hPopIdentifier :
                                  popIdentifierScope.run
                                    functionPoppedState with
                              | error err =>
                                  simp [hPopIdentifier] at hElab
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hElab
                                  rcases hElab with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact
                                    ⟨args',
                                      FrontendOccurrence.StmtUserCall.forCondition
                                        hOccurrence⟩

theorem Stmt.elaborate_forLoop_pre_noShadow_resolved_incoming_call_mem
    {pre : List Raw.Stmt} {condition : Raw.Expr}
    {post body : List Raw.Stmt} {preStmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed pre name)
    (hMem : preStmt ∈ pre)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope preStmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  cases hPreHas : Stmt.List.hasImmediateFunctionDefinition pre with
  | false =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          have hResolvePre :
              resolveFunctionIn name identifierPushedState.functionScopes =
                some generated := by
            rw [hPushScopes]
            exact hResolve
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateBlock pre false).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              rcases
                Stmt.List.elaborateBlock_false_noShadow_resolved_incoming_call_mem
                  hNoShadow hMem hOccurs hNameOk hResolvePre hPre with
                ⟨args', hPreOccurrence⟩
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          simp [hBody] at hElab
                          cases hPopIdentifier :
                              popIdentifierScope.run bodyState with
                          | error err =>
                              simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨hFront, _hFinal⟩
                              rw [← hFront]
                              exact
                                ⟨args',
                                  FrontendOccurrence.StmtUserCall.forPre
                                    hPreOccurrence⟩
  | true =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          have hResolvePre :
              resolveFunctionIn name identifierPushedState.functionScopes =
                some generated := by
            rw [hPushScopes]
            exact hResolve
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateForInitBlockWithScope pre).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              rcases
                Stmt.List.elaborateForInitBlockWithScope_noShadow_resolved_incoming_call_mem
                  hNoShadow hMem hOccurs hNameOk hResolvePre hPre with
                ⟨args', hPreOccurrence⟩
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          simp [hBody] at hElab
                          cases hPopFunction :
                              popFunctionScope.run bodyState with
                          | error err =>
                              simp [hPopFunction] at hElab
                          | ok popFunctionResult =>
                              rcases popFunctionResult with
                                ⟨_, functionPoppedState⟩
                              simp [hPopFunction] at hElab
                              cases hPopIdentifier :
                                  popIdentifierScope.run
                                    functionPoppedState with
                              | error err =>
                                  simp [hPopIdentifier] at hElab
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hElab
                                  rcases hElab with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact
                                    ⟨args',
                                      FrontendOccurrence.StmtUserCall.forPre
                                        hPreOccurrence⟩

theorem Stmt.elaborate_forLoop_post_noShadow_resolved_incoming_call_mem
    {pre : List Raw.Stmt} {condition : Raw.Expr}
    {post body : List Raw.Stmt} {postStmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoPreShadow : Raw.Source.NoLocalFunctionNamed pre name)
    (hNoPostShadow : Raw.Source.NoLocalFunctionNamed post name)
    (hMem : postStmt ∈ post)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope postStmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  cases hPreHas : Stmt.List.hasImmediateFunctionDefinition pre with
  | false =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateBlock pre false).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              have hPreScopes :
                  preState.functionScopes =
                    identifierPushedState.functionScopes :=
                Stmt.List.elaborateBlock_preserves_functionScopes
                  pre false hPre
              have hResolveCondition :
                  resolveFunctionIn name preState.functionScopes =
                    some generated := by
                rw [hPreScopes, hPushScopes]
                exact hResolve
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  have hConditionScopes :
                      conditionState.functionScopes =
                        preState.functionScopes :=
                    Expr.elaborate_preserves_functionScopes
                      condition hCondition
                  have hResolvePost :
                      resolveFunctionIn name conditionState.functionScopes =
                        some generated := by
                    rw [hConditionScopes]
                    exact hResolveCondition
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      rcases
                        Stmt.List.elaborateBlock_true_noShadow_resolved_incoming_call_mem
                          hNoPostShadow hMem hOccurs hNameOk
                          hResolvePost hPost with
                        ⟨args', hPostOccurrence⟩
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          simp [hBody] at hElab
                          cases hPopIdentifier :
                              popIdentifierScope.run bodyState with
                          | error err =>
                              simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨hFront, _hFinal⟩
                              rw [← hFront]
                              exact
                                ⟨args',
                                  FrontendOccurrence.StmtUserCall.forPost
                                    hPostOccurrence⟩
  | true =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          have hResolvePre :
              resolveFunctionIn name identifierPushedState.functionScopes =
                some generated := by
            rw [hPushScopes]
            exact hResolve
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateForInitBlockWithScope pre).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              have hResolveCondition :
                  resolveFunctionIn name preState.functionScopes =
                    some generated :=
                Stmt.List.elaborateForInitBlockWithScope_noShadow_resolves_outer
                  hNoPreShadow hResolvePre hPre
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  have hConditionScopes :
                      conditionState.functionScopes =
                        preState.functionScopes :=
                    Expr.elaborate_preserves_functionScopes
                      condition hCondition
                  have hResolvePost :
                      resolveFunctionIn name conditionState.functionScopes =
                        some generated := by
                    rw [hConditionScopes]
                    exact hResolveCondition
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      rcases
                        Stmt.List.elaborateBlock_true_noShadow_resolved_incoming_call_mem
                          hNoPostShadow hMem hOccurs hNameOk
                          hResolvePost hPost with
                        ⟨args', hPostOccurrence⟩
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          simp [hBody] at hElab
                          cases hPopFunction :
                              popFunctionScope.run bodyState with
                          | error err =>
                              simp [hPopFunction] at hElab
                          | ok popFunctionResult =>
                              rcases popFunctionResult with
                                ⟨_, functionPoppedState⟩
                              simp [hPopFunction] at hElab
                              cases hPopIdentifier :
                                  popIdentifierScope.run
                                    functionPoppedState with
                              | error err =>
                                  simp [hPopIdentifier] at hElab
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hElab
                                  rcases hElab with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact
                                    ⟨args',
                                      FrontendOccurrence.StmtUserCall.forPost
                                        hPostOccurrence⟩

theorem Stmt.elaborate_forLoop_body_noShadow_resolved_incoming_call_mem
    {pre : List Raw.Stmt} {condition : Raw.Expr}
    {post body : List Raw.Stmt} {bodyStmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoPreShadow : Raw.Source.NoLocalFunctionNamed pre name)
    (hNoBodyShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hMem : bodyStmt ∈ body)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope bodyStmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  unfold Stmt.elaborate at hElab
  cases hPreHas : Stmt.List.hasImmediateFunctionDefinition pre with
  | false =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateBlock pre false).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              have hPreScopes :
                  preState.functionScopes =
                    identifierPushedState.functionScopes :=
                Stmt.List.elaborateBlock_preserves_functionScopes
                  pre false hPre
              have hResolveCondition :
                  resolveFunctionIn name preState.functionScopes =
                    some generated := by
                rw [hPreScopes, hPushScopes]
                exact hResolve
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  have hConditionScopes :
                      conditionState.functionScopes =
                        preState.functionScopes :=
                    Expr.elaborate_preserves_functionScopes
                      condition hCondition
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      have hPostScopes :
                          postState.functionScopes =
                            conditionState.functionScopes :=
                        Stmt.List.elaborateBlock_preserves_functionScopes
                          post true hPost
                      have hResolveBody :
                          resolveFunctionIn name postState.functionScopes =
                            some generated := by
                        rw [hPostScopes, hConditionScopes]
                        exact hResolveCondition
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          rcases
                            Stmt.List.elaborateBlock_true_noShadow_resolved_incoming_call_mem
                              hNoBodyShadow hMem hOccurs hNameOk
                              hResolveBody hBody with
                            ⟨args', hBodyOccurrence⟩
                          simp [hBody] at hElab
                          cases hPopIdentifier :
                              popIdentifierScope.run bodyState with
                          | error err =>
                              simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨hFront, _hFinal⟩
                              rw [← hFront]
                              exact
                                ⟨args',
                                  FrontendOccurrence.StmtUserCall.forBody
                                    hBodyOccurrence⟩
  | true =>
      simp [hPreHas, StateT.run_bind] at hElab
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hElab
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hPushScopes :
              identifierPushedState.functionScopes =
                state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          have hResolvePre :
              resolveFunctionIn name identifierPushedState.functionScopes =
                some generated := by
            rw [hPushScopes]
            exact hResolve
          simp [hPushIdentifier] at hElab
          cases hPre :
              (Stmt.List.elaborateForInitBlockWithScope pre).run
                identifierPushedState with
          | error err =>
              simp [hPre] at hElab
          | ok preResult =>
              rcases preResult with ⟨frontPre, preState⟩
              have hResolveCondition :
                  resolveFunctionIn name preState.functionScopes =
                    some generated :=
                Stmt.List.elaborateForInitBlockWithScope_noShadow_resolves_outer
                  hNoPreShadow hResolvePre hPre
              simp [hPre] at hElab
              cases hCondition :
                  (Expr.elaborate condition).run preState with
              | error err =>
                  simp [hCondition] at hElab
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨frontCondition, conditionState⟩
                  have hConditionScopes :
                      conditionState.functionScopes =
                        preState.functionScopes :=
                    Expr.elaborate_preserves_functionScopes
                      condition hCondition
                  simp [hCondition] at hElab
                  cases hPost :
                      (Stmt.List.elaborateBlock post true).run
                        conditionState with
                  | error err =>
                      simp [hPost] at hElab
                  | ok postResult =>
                      rcases postResult with ⟨frontPost, postState⟩
                      have hPostScopes :
                          postState.functionScopes =
                            conditionState.functionScopes :=
                        Stmt.List.elaborateBlock_preserves_functionScopes
                          post true hPost
                      have hResolveBody :
                          resolveFunctionIn name postState.functionScopes =
                            some generated := by
                        rw [hPostScopes, hConditionScopes]
                        exact hResolveCondition
                      simp [hPost] at hElab
                      cases hBody :
                          (Stmt.List.elaborateBlock body true).run
                            postState with
                      | error err =>
                          simp [hBody] at hElab
                      | ok bodyResult =>
                          rcases bodyResult with ⟨frontBody, bodyState⟩
                          rcases
                            Stmt.List.elaborateBlock_true_noShadow_resolved_incoming_call_mem
                              hNoBodyShadow hMem hOccurs hNameOk
                              hResolveBody hBody with
                            ⟨args', hBodyOccurrence⟩
                          simp [hBody] at hElab
                          cases hPopFunction :
                              popFunctionScope.run bodyState with
                          | error err =>
                              simp [hPopFunction] at hElab
                          | ok popFunctionResult =>
                              rcases popFunctionResult with
                                ⟨_, functionPoppedState⟩
                              simp [hPopFunction] at hElab
                              cases hPopIdentifier :
                                  popIdentifierScope.run
                                    functionPoppedState with
                              | error err =>
                                  simp [hPopIdentifier] at hElab
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hElab
                                  rcases hElab with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact
                                    ⟨args',
                                      FrontendOccurrence.StmtUserCall.forBody
                                        hBodyOccurrence⟩

mutual

theorem Stmt.elaborate_noShadow_resolved_source_stmt_call
    {stmt : Raw.Stmt} {state finalState : State}
    {front : Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.NoShadowStmtCall stmt name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Stmt.elaborate stmt).run state =
      .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtUserCall front generated args' := by
  cases hOccurs with
  | @incoming stmt _ _ hIncoming =>
      exact
        Stmt.elaborate_resolved_source_stmt_call_incoming_occurrence
          hIncoming hNameOk hResolve hElab
  | @block stmts _ _ hNoShadow hList =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hBlock :
          (Stmt.List.elaborateBlock stmts true).run state with
      | error err =>
          simp [hBlock] at hElab
      | ok blockResult =>
          rcases blockResult with ⟨frontStmts, blockState⟩
          rcases
            Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
              true hNoShadow hList hNameOk hResolve hBlock with
            ⟨args', hOccurrence⟩
          simp [hBlock] at hElab
          rcases hElab with ⟨hFront, _hState⟩
          rw [← hFront]
          exact
            ⟨args', FrontendOccurrence.StmtUserCall.block hOccurrence⟩
  | @functionBody fn params returns body _ _ hNoShadow hBody =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hResolveFn : (resolveFunction fn).run state with
      | error err =>
          simp [hResolveFn] at hElab
      | ok resolveResult =>
          rcases resolveResult with ⟨frontFnName, resolvedState⟩
          have hResolveFnScopes :
              resolvedState.functionScopes = state.functionScopes :=
            resolveFunction_preserves_functionScopes fn hResolveFn
          have hResolveBody :
              resolveFunctionIn name resolvedState.functionScopes =
                some generated := by
            rw [hResolveFnScopes]
            exact hResolve
          simp [hResolveFn] at hElab
          cases hFn :
              (FunctionDef.elaborate params returns body).run
                resolvedState with
          | error err =>
              simp [hFn] at hElab
          | ok fnResult =>
              rcases fnResult with ⟨frontFn, fnState⟩
              rcases
                FunctionDef.elaborate_noShadow_resolved_source_stmt_list_call
                  hNoShadow hBody hNameOk hResolveBody hFn with
                ⟨args', hOccurrence⟩
              simp [hFn] at hElab
              rcases hElab with ⟨hFront, _hFinal⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtUserCall.functionBody hOccurrence⟩
  | @switchCase scrutinee cases defaultBody _ _ hCases =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hScrutinee :
          (Expr.elaborate scrutinee).run state with
      | error err =>
          simp [hScrutinee] at hElab
      | ok scrutineeResult =>
          rcases scrutineeResult with ⟨frontScrutinee, scrutineeState⟩
          have hScrutineeScopes :
              scrutineeState.functionScopes = state.functionScopes :=
            Expr.elaborate_preserves_functionScopes scrutinee hScrutinee
          have hResolveCases :
              resolveFunctionIn name scrutineeState.functionScopes =
                some generated := by
            rw [hScrutineeScopes]
            exact hResolve
          simp [hScrutinee] at hElab
          cases hCasesElab :
              (Stmt.CaseList.elaborate cases).run scrutineeState with
          | error err =>
              simp [hCasesElab] at hElab
          | ok casesResult =>
              rcases casesResult with ⟨frontCases, casesState⟩
              rcases
                Stmt.CaseList.elaborate_noShadow_resolved_source_case_list_call
                  hCases hNameOk hResolveCases hCasesElab with
                ⟨args', hCaseOccurrence⟩
              simp [hCasesElab] at hElab
              cases hDefault :
                  (Stmt.List.elaborateBlock defaultBody true).run
                    casesState with
              | error err =>
                  simp [hDefault] at hElab
              | ok defaultResult =>
                  rcases defaultResult with ⟨frontDefault, defaultState⟩
                  simp [hDefault] at hElab
                  rcases hElab with ⟨hFront, _hState⟩
                  rw [← hFront]
                  exact
                    ⟨args',
                      FrontendOccurrence.StmtUserCall.switchCase
                        hCaseOccurrence⟩
  | @switchDefault scrutinee cases defaultBody _ _ hNoShadow
      hDefaultOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hScrutinee :
          (Expr.elaborate scrutinee).run state with
      | error err =>
          simp [hScrutinee] at hElab
      | ok scrutineeResult =>
          rcases scrutineeResult with ⟨frontScrutinee, scrutineeState⟩
          have hScrutineeScopes :
              scrutineeState.functionScopes = state.functionScopes :=
            Expr.elaborate_preserves_functionScopes scrutinee hScrutinee
          have hResolveCases :
              resolveFunctionIn name scrutineeState.functionScopes =
                some generated := by
            rw [hScrutineeScopes]
            exact hResolve
          simp [hScrutinee] at hElab
          cases hCases :
              (Stmt.CaseList.elaborate cases).run scrutineeState with
          | error err =>
              simp [hCases] at hElab
          | ok casesResult =>
              rcases casesResult with ⟨frontCases, casesState⟩
              have hCasesScopes :
                  casesState.functionScopes =
                    scrutineeState.functionScopes :=
                Stmt.CaseList.elaborate_preserves_functionScopes cases hCases
              have hResolveDefault :
                  resolveFunctionIn name casesState.functionScopes =
                    some generated := by
                rw [hCasesScopes]
                exact hResolveCases
              simp [hCases] at hElab
              cases hDefault :
                  (Stmt.List.elaborateBlock defaultBody true).run
                    casesState with
              | error err =>
                  simp [hDefault] at hElab
              | ok defaultResult =>
                  rcases defaultResult with ⟨frontDefault, defaultState⟩
                  rcases
                    Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                      true hNoShadow hDefaultOccurs hNameOk hResolveDefault
                      hDefault with
                    ⟨args', hOccurrence⟩
                  simp [hDefault] at hElab
                  rcases hElab with ⟨hFront, _hState⟩
                  rw [← hFront]
                  exact
                    ⟨args',
                      FrontendOccurrence.StmtUserCall.switchDefault
                        hOccurrence⟩
  | @forCondition pre condition post body _ _ hNoPreShadow
      hConditionOccurs =>
      exact
        Stmt.elaborate_forLoop_condition_noShadow_resolved_source_expr_call
          hNoPreShadow hConditionOccurs hNameOk hResolve hElab
  | @forPre pre condition post body _ _ hNoPreShadow hPreOccurs =>
      unfold Stmt.elaborate at hElab
      cases hPreHas : Stmt.List.hasImmediateFunctionDefinition pre with
      | false =>
          simp [hPreHas, StateT.run_bind] at hElab
          cases hPushIdentifier : pushIdentifierScope.run state with
          | error err =>
              simp [hPushIdentifier] at hElab
          | ok pushIdentifierResult =>
              rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
              have hPushScopes :
                  identifierPushedState.functionScopes =
                    state.functionScopes :=
                pushIdentifierScope_preserves_functionScopes hPushIdentifier
              have hResolvePre :
                  resolveFunctionIn name identifierPushedState.functionScopes =
                    some generated := by
                rw [hPushScopes]
                exact hResolve
              simp [hPushIdentifier] at hElab
              cases hPre :
                  (Stmt.List.elaborateBlock pre false).run
                    identifierPushedState with
              | error err =>
                  simp [hPre] at hElab
              | ok preResult =>
                  rcases preResult with ⟨frontPre, preState⟩
                  rcases
                    Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                      false hNoPreShadow hPreOccurs hNameOk hResolvePre
                      hPre with
                    ⟨args', hPreOccurrence⟩
                  simp [hPre] at hElab
                  cases hCondition :
                      (Expr.elaborate condition).run preState with
                  | error err =>
                      simp [hCondition] at hElab
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontCondition, conditionState⟩
                      simp [hCondition] at hElab
                      cases hPost :
                          (Stmt.List.elaborateBlock post true).run
                            conditionState with
                      | error err =>
                          simp [hPost] at hElab
                      | ok postResult =>
                          rcases postResult with ⟨frontPost, postState⟩
                          simp [hPost] at hElab
                          cases hBody :
                              (Stmt.List.elaborateBlock body true).run
                                postState with
                          | error err =>
                              simp [hBody] at hElab
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontBody, bodyState⟩
                              simp [hBody] at hElab
                              cases hPopIdentifier :
                                  popIdentifierScope.run bodyState with
                              | error err =>
                                  simp [hPopIdentifier] at hElab
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hElab
                                  rcases hElab with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact
                                    ⟨args',
                                      FrontendOccurrence.StmtUserCall.forPre
                                        hPreOccurrence⟩
      | true =>
          simp [hPreHas, StateT.run_bind] at hElab
          cases hPushIdentifier : pushIdentifierScope.run state with
          | error err =>
              simp [hPushIdentifier] at hElab
          | ok pushIdentifierResult =>
              rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
              have hPushScopes :
                  identifierPushedState.functionScopes =
                    state.functionScopes :=
                pushIdentifierScope_preserves_functionScopes hPushIdentifier
              have hResolvePre :
                  resolveFunctionIn name identifierPushedState.functionScopes =
                    some generated := by
                rw [hPushScopes]
                exact hResolve
              simp [hPushIdentifier] at hElab
              cases hPre :
                  (Stmt.List.elaborateForInitBlockWithScope pre).run
                    identifierPushedState with
              | error err =>
                  simp [hPre] at hElab
              | ok preResult =>
                  rcases preResult with ⟨frontPre, preState⟩
                  rcases
                    Stmt.List.elaborateForInitBlockWithScope_noShadow_resolved_source_stmt_list_call
                      hNoPreShadow hPreOccurs hNameOk hResolvePre hPre with
                    ⟨args', hPreOccurrence⟩
                  simp [hPre] at hElab
                  cases hCondition :
                      (Expr.elaborate condition).run preState with
                  | error err =>
                      simp [hCondition] at hElab
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontCondition, conditionState⟩
                      simp [hCondition] at hElab
                      cases hPost :
                          (Stmt.List.elaborateBlock post true).run
                            conditionState with
                      | error err =>
                          simp [hPost] at hElab
                      | ok postResult =>
                          rcases postResult with ⟨frontPost, postState⟩
                          simp [hPost] at hElab
                          cases hBody :
                              (Stmt.List.elaborateBlock body true).run
                                postState with
                          | error err =>
                              simp [hBody] at hElab
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontBody, bodyState⟩
                              simp [hBody] at hElab
                              cases hPopFunction :
                                  popFunctionScope.run bodyState with
                              | error err =>
                                  simp [hPopFunction] at hElab
                              | ok popFunctionResult =>
                                  rcases popFunctionResult with
                                    ⟨_, functionPoppedState⟩
                                  simp [hPopFunction] at hElab
                                  cases hPopIdentifier :
                                      popIdentifierScope.run
                                        functionPoppedState with
                                  | error err =>
                                      simp [hPopIdentifier] at hElab
                                  | ok popIdentifierResult =>
                                      rcases popIdentifierResult with
                                        ⟨_, identifierPoppedState⟩
                                      simp [hPopIdentifier] at hElab
                                      rcases hElab with ⟨hFront, _hFinal⟩
                                      rw [← hFront]
                                      exact
                                        ⟨args',
                                          FrontendOccurrence.StmtUserCall.forPre
                                            hPreOccurrence⟩
  | @forPost pre condition post body _ _ hNoPreShadow hNoPostShadow
      hPostOccurs =>
      unfold Stmt.elaborate at hElab
      cases hPreHas : Stmt.List.hasImmediateFunctionDefinition pre with
      | false =>
          simp [hPreHas, StateT.run_bind] at hElab
          cases hPushIdentifier : pushIdentifierScope.run state with
          | error err =>
              simp [hPushIdentifier] at hElab
          | ok pushIdentifierResult =>
              rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
              have hPushScopes :
                  identifierPushedState.functionScopes =
                    state.functionScopes :=
                pushIdentifierScope_preserves_functionScopes hPushIdentifier
              simp [hPushIdentifier] at hElab
              cases hPre :
                  (Stmt.List.elaborateBlock pre false).run
                    identifierPushedState with
              | error err =>
                  simp [hPre] at hElab
              | ok preResult =>
                  rcases preResult with ⟨frontPre, preState⟩
                  have hPreScopes :
                      preState.functionScopes =
                        identifierPushedState.functionScopes :=
                    Stmt.List.elaborateBlock_preserves_functionScopes
                      pre false hPre
                  have hResolveCondition :
                      resolveFunctionIn name preState.functionScopes =
                        some generated := by
                    rw [hPreScopes, hPushScopes]
                    exact hResolve
                  simp [hPre] at hElab
                  cases hCondition :
                      (Expr.elaborate condition).run preState with
                  | error err =>
                      simp [hCondition] at hElab
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontCondition, conditionState⟩
                      have hConditionScopes :
                          conditionState.functionScopes =
                            preState.functionScopes :=
                        Expr.elaborate_preserves_functionScopes
                          condition hCondition
                      have hResolvePost :
                          resolveFunctionIn name conditionState.functionScopes =
                            some generated := by
                        rw [hConditionScopes]
                        exact hResolveCondition
                      simp [hCondition] at hElab
                      cases hPost :
                          (Stmt.List.elaborateBlock post true).run
                            conditionState with
                      | error err =>
                          simp [hPost] at hElab
                      | ok postResult =>
                          rcases postResult with ⟨frontPost, postState⟩
                          rcases
                            Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                              true hNoPostShadow hPostOccurs hNameOk
                              hResolvePost hPost with
                            ⟨args', hPostOccurrence⟩
                          simp [hPost] at hElab
                          cases hBody :
                              (Stmt.List.elaborateBlock body true).run
                                postState with
                          | error err =>
                              simp [hBody] at hElab
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontBody, bodyState⟩
                              simp [hBody] at hElab
                              cases hPopIdentifier :
                                  popIdentifierScope.run bodyState with
                              | error err =>
                                  simp [hPopIdentifier] at hElab
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hElab
                                  rcases hElab with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact
                                    ⟨args',
                                      FrontendOccurrence.StmtUserCall.forPost
                                        hPostOccurrence⟩
      | true =>
          simp [hPreHas, StateT.run_bind] at hElab
          cases hPushIdentifier : pushIdentifierScope.run state with
          | error err =>
              simp [hPushIdentifier] at hElab
          | ok pushIdentifierResult =>
              rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
              have hPushScopes :
                  identifierPushedState.functionScopes =
                    state.functionScopes :=
                pushIdentifierScope_preserves_functionScopes hPushIdentifier
              have hResolvePre :
                  resolveFunctionIn name identifierPushedState.functionScopes =
                    some generated := by
                rw [hPushScopes]
                exact hResolve
              simp [hPushIdentifier] at hElab
              cases hPre :
                  (Stmt.List.elaborateForInitBlockWithScope pre).run
                    identifierPushedState with
              | error err =>
                  simp [hPre] at hElab
              | ok preResult =>
                  rcases preResult with ⟨frontPre, preState⟩
                  have hResolveCondition :
                      resolveFunctionIn name preState.functionScopes =
                        some generated :=
                    Stmt.List.elaborateForInitBlockWithScope_noShadow_resolves_outer
                      hNoPreShadow hResolvePre hPre
                  simp [hPre] at hElab
                  cases hCondition :
                      (Expr.elaborate condition).run preState with
                  | error err =>
                      simp [hCondition] at hElab
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontCondition, conditionState⟩
                      have hConditionScopes :
                          conditionState.functionScopes =
                            preState.functionScopes :=
                        Expr.elaborate_preserves_functionScopes
                          condition hCondition
                      have hResolvePost :
                          resolveFunctionIn name conditionState.functionScopes =
                            some generated := by
                        rw [hConditionScopes]
                        exact hResolveCondition
                      simp [hCondition] at hElab
                      cases hPost :
                          (Stmt.List.elaborateBlock post true).run
                            conditionState with
                      | error err =>
                          simp [hPost] at hElab
                      | ok postResult =>
                          rcases postResult with ⟨frontPost, postState⟩
                          rcases
                            Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                              true hNoPostShadow hPostOccurs hNameOk
                              hResolvePost hPost with
                            ⟨args', hPostOccurrence⟩
                          simp [hPost] at hElab
                          cases hBody :
                              (Stmt.List.elaborateBlock body true).run
                                postState with
                          | error err =>
                              simp [hBody] at hElab
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontBody, bodyState⟩
                              simp [hBody] at hElab
                              cases hPopFunction :
                                  popFunctionScope.run bodyState with
                              | error err =>
                                  simp [hPopFunction] at hElab
                              | ok popFunctionResult =>
                                  rcases popFunctionResult with
                                    ⟨_, functionPoppedState⟩
                                  simp [hPopFunction] at hElab
                                  cases hPopIdentifier :
                                      popIdentifierScope.run
                                        functionPoppedState with
                                  | error err =>
                                      simp [hPopIdentifier] at hElab
                                  | ok popIdentifierResult =>
                                      rcases popIdentifierResult with
                                        ⟨_, identifierPoppedState⟩
                                      simp [hPopIdentifier] at hElab
                                      rcases hElab with ⟨hFront, _hFinal⟩
                                      rw [← hFront]
                                      exact
                                        ⟨args',
                                          FrontendOccurrence.StmtUserCall.forPost
                                            hPostOccurrence⟩
  | @forBody pre condition post body _ _ hNoPreShadow hNoBodyShadow
      hBodyOccurs =>
      unfold Stmt.elaborate at hElab
      cases hPreHas : Stmt.List.hasImmediateFunctionDefinition pre with
      | false =>
          simp [hPreHas, StateT.run_bind] at hElab
          cases hPushIdentifier : pushIdentifierScope.run state with
          | error err =>
              simp [hPushIdentifier] at hElab
          | ok pushIdentifierResult =>
              rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
              have hPushScopes :
                  identifierPushedState.functionScopes =
                    state.functionScopes :=
                pushIdentifierScope_preserves_functionScopes hPushIdentifier
              simp [hPushIdentifier] at hElab
              cases hPre :
                  (Stmt.List.elaborateBlock pre false).run
                    identifierPushedState with
              | error err =>
                  simp [hPre] at hElab
              | ok preResult =>
                  rcases preResult with ⟨frontPre, preState⟩
                  have hPreScopes :
                      preState.functionScopes =
                        identifierPushedState.functionScopes :=
                    Stmt.List.elaborateBlock_preserves_functionScopes
                      pre false hPre
                  have hResolveCondition :
                      resolveFunctionIn name preState.functionScopes =
                        some generated := by
                    rw [hPreScopes, hPushScopes]
                    exact hResolve
                  simp [hPre] at hElab
                  cases hCondition :
                      (Expr.elaborate condition).run preState with
                  | error err =>
                      simp [hCondition] at hElab
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontCondition, conditionState⟩
                      have hConditionScopes :
                          conditionState.functionScopes =
                            preState.functionScopes :=
                        Expr.elaborate_preserves_functionScopes
                          condition hCondition
                      simp [hCondition] at hElab
                      cases hPost :
                          (Stmt.List.elaborateBlock post true).run
                            conditionState with
                      | error err =>
                          simp [hPost] at hElab
                      | ok postResult =>
                          rcases postResult with ⟨frontPost, postState⟩
                          have hPostScopes :
                              postState.functionScopes =
                                conditionState.functionScopes :=
                            Stmt.List.elaborateBlock_preserves_functionScopes
                              post true hPost
                          have hResolveBody :
                              resolveFunctionIn name postState.functionScopes =
                                some generated := by
                            rw [hPostScopes, hConditionScopes]
                            exact hResolveCondition
                          simp [hPost] at hElab
                          cases hBody :
                              (Stmt.List.elaborateBlock body true).run
                                postState with
                          | error err =>
                              simp [hBody] at hElab
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontBody, bodyState⟩
                              rcases
                                Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                                  true hNoBodyShadow hBodyOccurs hNameOk
                                  hResolveBody hBody with
                                ⟨args', hBodyOccurrence⟩
                              simp [hBody] at hElab
                              cases hPopIdentifier :
                                  popIdentifierScope.run bodyState with
                              | error err =>
                                  simp [hPopIdentifier] at hElab
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hElab
                                  rcases hElab with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact
                                    ⟨args',
                                      FrontendOccurrence.StmtUserCall.forBody
                                        hBodyOccurrence⟩
      | true =>
          simp [hPreHas, StateT.run_bind] at hElab
          cases hPushIdentifier : pushIdentifierScope.run state with
          | error err =>
              simp [hPushIdentifier] at hElab
          | ok pushIdentifierResult =>
              rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
              have hPushScopes :
                  identifierPushedState.functionScopes =
                    state.functionScopes :=
                pushIdentifierScope_preserves_functionScopes hPushIdentifier
              have hResolvePre :
                  resolveFunctionIn name identifierPushedState.functionScopes =
                    some generated := by
                rw [hPushScopes]
                exact hResolve
              simp [hPushIdentifier] at hElab
              cases hPre :
                  (Stmt.List.elaborateForInitBlockWithScope pre).run
                    identifierPushedState with
              | error err =>
                  simp [hPre] at hElab
              | ok preResult =>
                  rcases preResult with ⟨frontPre, preState⟩
                  have hResolveCondition :
                      resolveFunctionIn name preState.functionScopes =
                        some generated :=
                    Stmt.List.elaborateForInitBlockWithScope_noShadow_resolves_outer
                      hNoPreShadow hResolvePre hPre
                  simp [hPre] at hElab
                  cases hCondition :
                      (Expr.elaborate condition).run preState with
                  | error err =>
                      simp [hCondition] at hElab
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontCondition, conditionState⟩
                      have hConditionScopes :
                          conditionState.functionScopes =
                            preState.functionScopes :=
                        Expr.elaborate_preserves_functionScopes
                          condition hCondition
                      simp [hCondition] at hElab
                      cases hPost :
                          (Stmt.List.elaborateBlock post true).run
                            conditionState with
                      | error err =>
                          simp [hPost] at hElab
                      | ok postResult =>
                          rcases postResult with ⟨frontPost, postState⟩
                          have hPostScopes :
                              postState.functionScopes =
                                conditionState.functionScopes :=
                            Stmt.List.elaborateBlock_preserves_functionScopes
                              post true hPost
                          have hResolveBody :
                              resolveFunctionIn name postState.functionScopes =
                                some generated := by
                            rw [hPostScopes, hConditionScopes]
                            exact hResolveCondition
                          simp [hPost] at hElab
                          cases hBody :
                              (Stmt.List.elaborateBlock body true).run
                                postState with
                          | error err =>
                              simp [hBody] at hElab
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontBody, bodyState⟩
                              rcases
                                Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                                  true hNoBodyShadow hBodyOccurs hNameOk
                                  hResolveBody hBody with
                                ⟨args', hBodyOccurrence⟩
                              simp [hBody] at hElab
                              cases hPopFunction :
                                  popFunctionScope.run bodyState with
                              | error err =>
                                  simp [hPopFunction] at hElab
                              | ok popFunctionResult =>
                                  rcases popFunctionResult with
                                    ⟨_, functionPoppedState⟩
                                  simp [hPopFunction] at hElab
                                  cases hPopIdentifier :
                                      popIdentifierScope.run
                                        functionPoppedState with
                                  | error err =>
                                      simp [hPopIdentifier] at hElab
                                  | ok popIdentifierResult =>
                                      rcases popIdentifierResult with
                                        ⟨_, identifierPoppedState⟩
                                      simp [hPopIdentifier] at hElab
                                      rcases hElab with ⟨hFront, _hFinal⟩
                                      rw [← hFront]
                                      exact
                                        ⟨args',
                                          FrontendOccurrence.StmtUserCall.forBody
                                            hBodyOccurrence⟩
  | @ifBody condition body _ _ hNoShadow hBodyOccurs =>
      unfold Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hCondition :
          (Expr.elaborate condition).run state with
      | error err =>
          simp [hCondition] at hElab
      | ok conditionResult =>
          rcases conditionResult with ⟨frontCondition, conditionState⟩
          have hConditionScopes :
              conditionState.functionScopes = state.functionScopes :=
            Expr.elaborate_preserves_functionScopes condition hCondition
          have hResolveBody :
              resolveFunctionIn name conditionState.functionScopes =
                some generated := by
            rw [hConditionScopes]
            exact hResolve
          simp [hCondition] at hElab
          cases hBody :
              (Stmt.List.elaborateBlock body true).run conditionState with
          | error err =>
              simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              rcases
                Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                  true hNoShadow hBodyOccurs hNameOk hResolveBody hBody with
                ⟨args', hOccurrence⟩
              simp [hBody] at hElab
              rcases hElab with ⟨hFront, _hState⟩
              rw [← hFront]
              exact
                ⟨args',
                  FrontendOccurrence.StmtUserCall.ifBody hOccurrence⟩
  termination_by 20 * sizeOf stmt + 18
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
    {stmts : List Raw.Stmt} {state finalState : State}
    {fronts : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.NoShadowStmtListCall stmts name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab : (Stmt.List.elaborate stmts).run state =
      .ok (fronts, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall fronts generated args' := by
  cases hOccurs with
  | @head stmt rest _ _ hHeadOccurs =>
      unfold Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Stmt.elaborate stmt).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headFront, headState⟩
          rcases
            Stmt.elaborate_noShadow_resolved_source_stmt_call
              hHeadOccurs hNameOk hResolve hHead with
            ⟨args', hHeadOccurrence⟩
          simp [hHead] at hElab
          cases hTail :
              (Stmt.List.elaborate rest).run headState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailFronts, tailState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨hFronts, _hFinal⟩
              rw [← hFronts]
              exact
                ⟨args',
                  FrontendOccurrence.StmtListUserCall.head
                    hHeadOccurrence⟩
  | @tail stmt rest _ _ hTailOccurs =>
      unfold Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Stmt.elaborate stmt).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headFront, headState⟩
          have hHeadScopes :
              headState.functionScopes = state.functionScopes :=
            Stmt.elaborate_preserves_functionScopes _ hHead
          have hHeadResolve :
              resolveFunctionIn name headState.functionScopes =
                some generated := by
            rw [hHeadScopes]
            exact hResolve
          simp [hHead] at hElab
          cases hTail :
              (Stmt.List.elaborate rest).run headState with
          | error err =>
              simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailFronts, tailState⟩
              rcases
                Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
                  hTailOccurs hNameOk hHeadResolve hTail with
                ⟨args', hTailOccurrence⟩
              simp [hTail] at hElab
              rcases hElab with ⟨hFronts, _hFinal⟩
              rw [← hFronts]
              exact
                ⟨args',
                  FrontendOccurrence.StmtListUserCall.tail
                    hTailOccurrence⟩
  termination_by 20 * sizeOf stmts + 10
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
    (createsScope : Bool)
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hOccurs : Raw.Source.NoShadowStmtListCall stmts name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolveOuter :
      resolveFunctionIn name state.functionScopes = some generated)
    (hBlock :
      (Stmt.List.elaborateBlock stmts createsScope).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall front generated args' := by
  cases createsScope with
  | false =>
      unfold Stmt.List.elaborateBlock at hBlock
      simp [StateT.run_bind] at hBlock
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run state with
      | error err =>
          simp [hScope] at hBlock
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          have hLookupNone :
              lookupFunctionInScope name scope = none :=
            Stmt.List.localFunctionScope_noLocalFunctionNamed_lookup_none
              hScope hNoShadow
          have hScopePres :
              scopeState.functionScopes = state.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          simp [hScope] at hBlock
          cases hPushFunction :
              (pushFunctionScope scope).run scopeState with
          | error err =>
              simp [hPushFunction] at hBlock
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              have hPushFunctionScopes :
                  functionPushedState.functionScopes =
                    scope :: scopeState.functionScopes :=
                pushFunctionScope_functionScopes hPushFunction
              simp [hPushFunction] at hBlock
              cases hHoist :
                  (Stmt.List.hoistLocalFunctions stmts scope).run
                    functionPushedState with
              | error err =>
                  simp [hHoist] at hBlock
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  have hHoistScopes :
                      hoistState.functionScopes =
                        functionPushedState.functionScopes :=
                    Stmt.List.hoistLocalFunctions_preserves_functionScopes
                      stmts scope hHoist
                  have hResolveHoist :
                      resolveFunctionIn name hoistState.functionScopes =
                        some generated := by
                    rw [hHoistScopes, hPushFunctionScopes, hScopePres]
                    simp [resolveFunctionIn, hLookupNone, hResolveOuter]
                  simp [hHoist] at hBlock
                  cases hElab :
                      (Stmt.List.elaborate stmts).run hoistState with
                  | error err =>
                      simp [hElab] at hBlock
                  | ok elabResult =>
                      rcases elabResult with ⟨front', elabState⟩
                      rcases
                        Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
                          hOccurs hNameOk hResolveHoist hElab with
                        ⟨args', hOccurrence⟩
                      simp [hElab] at hBlock
                      cases hPopFunction :
                          popFunctionScope.run elabState with
                      | error err =>
                          simp [hPopFunction] at hBlock
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hBlock
                          rcases hBlock with ⟨hFront, _hFinal⟩
                          rw [← hFront]
                          exact ⟨args', hOccurrence⟩
  | true =>
      unfold Stmt.List.elaborateBlock at hBlock
      simp [StateT.run_bind] at hBlock
      cases hPushIdentifier : pushIdentifierScope.run state with
      | error err =>
          simp [hPushIdentifier] at hBlock
      | ok pushIdentifierResult =>
          rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
          have hIdentifierPushScopes :
              identifierPushedState.functionScopes = state.functionScopes :=
            pushIdentifierScope_preserves_functionScopes hPushIdentifier
          simp [hPushIdentifier] at hBlock
          cases hScope :
              (Stmt.List.localFunctionScope stmts).run
                identifierPushedState with
          | error err =>
              simp [hScope] at hBlock
          | ok scopeResult =>
              rcases scopeResult with ⟨scope, scopeState⟩
              have hLookupNone :
                  lookupFunctionInScope name scope = none :=
                Stmt.List.localFunctionScope_noLocalFunctionNamed_lookup_none
                  hScope hNoShadow
              have hScopePres :
                  scopeState.functionScopes =
                    identifierPushedState.functionScopes :=
                Stmt.List.localFunctionScope_preserves_functionScopes
                  stmts hScope
              simp [hScope] at hBlock
              cases hPushFunction :
                  (pushFunctionScope scope).run scopeState with
              | error err =>
                  simp [hPushFunction] at hBlock
              | ok pushFunctionResult =>
                  rcases pushFunctionResult with ⟨_, functionPushedState⟩
                  have hPushFunctionScopes :
                      functionPushedState.functionScopes =
                        scope :: scopeState.functionScopes :=
                    pushFunctionScope_functionScopes hPushFunction
                  simp [hPushFunction] at hBlock
                  cases hHoist :
                      (Stmt.List.hoistLocalFunctions stmts scope).run
                        functionPushedState with
                  | error err =>
                      simp [hHoist] at hBlock
                  | ok hoistResult =>
                      rcases hoistResult with ⟨_, hoistState⟩
                      have hHoistScopes :
                          hoistState.functionScopes =
                            functionPushedState.functionScopes :=
                        Stmt.List.hoistLocalFunctions_preserves_functionScopes
                          stmts scope hHoist
                      have hResolveHoist :
                          resolveFunctionIn name hoistState.functionScopes =
                            some generated := by
                        rw [hHoistScopes, hPushFunctionScopes, hScopePres,
                          hIdentifierPushScopes]
                        simp [resolveFunctionIn, hLookupNone, hResolveOuter]
                      simp [hHoist] at hBlock
                      cases hElab :
                          (Stmt.List.elaborate stmts).run hoistState with
                      | error err =>
                          simp [hElab] at hBlock
                      | ok elabResult =>
                          rcases elabResult with ⟨front', elabState⟩
                          rcases
                            Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
                              hOccurs hNameOk hResolveHoist hElab with
                            ⟨args', hOccurrence⟩
                          simp [hElab] at hBlock
                          cases hPopFunction :
                              popFunctionScope.run elabState with
                          | error err =>
                              simp [hPopFunction] at hBlock
                          | ok popFunctionResult =>
                              rcases popFunctionResult with
                                ⟨_, functionPoppedState⟩
                              simp [hPopFunction] at hBlock
                              cases hPopIdentifier :
                                  popIdentifierScope.run
                                    functionPoppedState with
                              | error err =>
                                  simp [hPopIdentifier] at hBlock
                              | ok popIdentifierResult =>
                                  rcases popIdentifierResult with
                                    ⟨_, identifierPoppedState⟩
                                  simp [hPopIdentifier] at hBlock
                                  rcases hBlock with ⟨hFront, _hFinal⟩
                                  rw [← hFront]
                                  exact ⟨args', hOccurrence⟩
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateForInitBlockWithScope_noShadow_resolved_source_stmt_list_call
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed stmts name)
    (hOccurs : Raw.Source.NoShadowStmtListCall stmts name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolveOuter :
      resolveFunctionIn name state.functionScopes = some generated)
    (hBlock :
      (Stmt.List.elaborateForInitBlockWithScope stmts).run state =
        .ok (front, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall front generated args' := by
  unfold Stmt.List.elaborateForInitBlockWithScope at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      have hLookupNone :
          lookupFunctionInScope name scope = none :=
        Stmt.List.localFunctionScope_noLocalFunctionNamed_lookup_none
          hScope hNoShadow
      have hScopePres :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes
          stmts hScope
      simp [hScope] at hBlock
      cases hPushFunction :
          (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPushFunction] at hBlock
      | ok pushFunctionResult =>
          rcases pushFunctionResult with ⟨_, functionPushedState⟩
          have hPushFunctionScopes :
              functionPushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPushFunction
          simp [hPushFunction] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                functionPushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    functionPushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hResolveHoist :
                  resolveFunctionIn name hoistState.functionScopes =
                    some generated := by
                rw [hHoistScopes, hPushFunctionScopes, hScopePres]
                simp [resolveFunctionIn, hLookupNone, hResolveOuter]
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  rcases
                    Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
                      hOccurs hNameOk hResolveHoist hElab with
                    ⟨args', hOccurrence⟩
                  simp [hElab] at hBlock
                  rcases hBlock with ⟨hFront, _hFinal⟩
                  rw [← hFront]
                  exact ⟨args', hOccurrence⟩
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.CaseList.elaborate_noShadow_resolved_source_case_list_call
    {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {state finalState : State}
    {frontCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {name generated : Name} {args : List Raw.Expr}
    (hOccurs : Raw.Source.NoShadowCaseListCall cases name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (Stmt.CaseList.elaborate cases).run state =
        .ok (frontCases, finalState)) :
    ∃ args',
      FrontendOccurrence.CaseListUserCall frontCases generated args' := by
  cases hOccurs with
  | @head value body rest _ _ hNoShadow hBodyOccurs =>
      unfold Stmt.CaseList.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hValue : SwitchCaseValue.elaborate value with
      | error err =>
          simp [hValue] at hElab
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hElab
          cases hElab
      | ok frontValue =>
          simp [hValue] at hElab
          cases hHeadBody :
              (Stmt.List.elaborateBlock body true).run state with
          | error err =>
              simp [hHeadBody] at hElab
          | ok headBodyResult =>
              rcases headBodyResult with ⟨frontHeadBody, headBodyState⟩
              rcases
                Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                  true hNoShadow hBodyOccurs hNameOk hResolve hHeadBody with
                ⟨args', hOccurrence⟩
              simp [hHeadBody] at hElab
              cases hRest :
                  (Stmt.CaseList.elaborate rest).run headBodyState with
              | error err =>
                  simp [hRest] at hElab
              | ok restResult =>
                  rcases restResult with ⟨frontRest, restState⟩
                  simp [hRest] at hElab
                  rcases hElab with ⟨hFront, _hState⟩
                  rw [← hFront]
                  exact
                    ⟨args',
                      FrontendOccurrence.CaseListUserCall.head
                        hOccurrence⟩
  | @tail case rest _ _ hTailOccurs =>
      rcases case with ⟨value, body⟩
      unfold Stmt.CaseList.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hValue : SwitchCaseValue.elaborate value with
      | error err =>
          simp [hValue] at hElab
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hElab
          cases hElab
      | ok frontValue =>
          simp [hValue] at hElab
          cases hHeadBody :
              (Stmt.List.elaborateBlock body true).run state with
          | error err =>
              simp [hHeadBody] at hElab
          | ok headBodyResult =>
              rcases headBodyResult with ⟨frontHeadBody, headBodyState⟩
              have hHeadBodyScopes :
                  headBodyState.functionScopes = state.functionScopes :=
                Stmt.List.elaborateBlock_preserves_functionScopes
                  body true hHeadBody
              have hResolveRest :
                  resolveFunctionIn name headBodyState.functionScopes =
                    some generated := by
                rw [hHeadBodyScopes]
                exact hResolve
              simp [hHeadBody] at hElab
              cases hRest :
                  (Stmt.CaseList.elaborate rest).run headBodyState with
              | error err =>
                  simp [hRest] at hElab
              | ok restResult =>
                  rcases restResult with ⟨frontRest, restState⟩
                  rcases
                    Stmt.CaseList.elaborate_noShadow_resolved_source_case_list_call
                      hTailOccurs hNameOk hResolveRest hRest with
                    ⟨args', hOccurrence⟩
                  simp [hRest] at hElab
                  rcases hElab with ⟨hFront, _hState⟩
                  rw [← hFront]
                  exact
                    ⟨args',
                      FrontendOccurrence.CaseListUserCall.tail
                        hOccurrence⟩
  termination_by 20 * sizeOf cases + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem FunctionDef.elaborate_noShadow_resolved_source_stmt_list_call
    {params returns : List Name} {body : List Raw.Stmt}
    {state finalState : State} {fn : Frontend.FunctionDef}
    {name generated : Name} {args : List Raw.Expr}
    (hNoShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hOccurs : Raw.Source.NoShadowStmtListCall body name args)
    (hNameOk : bindingNameOk? name = true)
    (hResolve :
      resolveFunctionIn name state.functionScopes = some generated)
    (hElab :
      (FunctionDef.elaborate params returns body).run state =
        .ok (fn, finalState)) :
    ∃ args',
      FrontendOccurrence.StmtListUserCall fn.body generated args' := by
  unfold FunctionDef.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      have hPushScopes :
          identifierPushedState.functionScopes =
            state.functionScopes :=
        pushIdentifierScope_preserves_functionScopes hPushIdentifier
      simp [hPushIdentifier] at hElab
      cases hDeclare :
          (declareIdentifiers (params ++ returns)
            "function parameter/result").run identifierPushedState with
      | error err =>
          simp [hDeclare] at hElab
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          have hDeclareScopes :
              declaredState.functionScopes =
                identifierPushedState.functionScopes :=
            declareIdentifiers_preserves_functionScopes
              (params ++ returns) "function parameter/result" hDeclare
          have hResolveBody :
              resolveFunctionIn name declaredState.functionScopes =
                some generated := by
            rw [hDeclareScopes, hPushScopes]
            exact hResolve
          simp [hDeclare] at hElab
          cases hBody :
              (Stmt.List.elaborateBlock body true).run declaredState with
          | error err =>
              simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              rcases
                Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call
                  true hNoShadow hOccurs hNameOk hResolveBody hBody with
                ⟨args', hOccurrence⟩
              simp [hBody] at hElab
              cases hPopIdentifier : popIdentifierScope.run bodyState with
              | error err =>
                  simp [hPopIdentifier] at hElab
              | ok popIdentifierResult =>
                  rcases popIdentifierResult with
                    ⟨_, identifierPoppedState⟩
                  simp [hPopIdentifier] at hElab
                  rcases hElab with ⟨hFn, _hFinal⟩
                  rw [← hFn]
                  exact ⟨args', hOccurrence⟩
  termination_by 20 * sizeOf body + 16
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end

theorem Stmt.List.sourceLocalFunction_elaborateBlock_false_noShadow_stmtUserCall_entry
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hOccurs : Raw.Source.NoShadowStmtListCall stmts name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts false).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtListUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      simp [hScope] at hBlock
      rcases sourceLocalFunction_elaborateBlock_false_entry
          hLocal hScope hBlockRun with
        ⟨generated, fn, hLookup, hEntryFinal⟩
      have hNameOk :
          bindingNameOk? name = true :=
        localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
      have hScopePres :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes
          stmts hScope
      cases hPushFunction :
          (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPushFunction] at hBlock
      | ok pushFunctionResult =>
          rcases pushFunctionResult with ⟨_, functionPushedState⟩
          have hPushFunctionScopes :
              functionPushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPushFunction
          simp [hPushFunction] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                functionPushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    functionPushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hResolveHoist :
                  resolveFunctionIn name hoistState.functionScopes =
                    some generated := by
                rw [hHoistScopes, hPushFunctionScopes, hScopePres]
                exact resolveFunctionIn_of_scope_lookup hLookup
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  rcases
                    Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
                      hOccurs hNameOk hResolveHoist hElab with
                    ⟨args', hOccurrence⟩
                  simp [hElab] at hBlock
                  cases hPopFunction :
                      popFunctionScope.run elabState with
                  | error err =>
                      simp [hPopFunction] at hBlock
                  | ok popFunctionResult =>
                      rcases popFunctionResult with
                        ⟨_, functionPoppedState⟩
                      simp [hPopFunction] at hBlock
                      rcases hBlock with ⟨hFront, _hFinal⟩
                      rw [← hFront]
                      exact
                        ⟨generated, fn, args', hOccurrence, hEntryFinal⟩

theorem Stmt.List.sourceLocalFunction_elaborateBlock_true_noShadow_stmtUserCall_entry
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hOccurs : Raw.Source.NoShadowStmtListCall stmts name args)
    (hBlock :
      (Stmt.List.elaborateBlock stmts true).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtListUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hBlockRun := hBlock
  unfold Stmt.List.elaborateBlock at hBlock
  simp [StateT.run_bind] at hBlock
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hBlock
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      have hIdentifierPushScopes :
          identifierPushedState.functionScopes = state.functionScopes :=
        pushIdentifierScope_preserves_functionScopes hPushIdentifier
      simp [hPushIdentifier] at hBlock
      cases hScope :
          (Stmt.List.localFunctionScope stmts).run
            identifierPushedState with
      | error err =>
          simp [hScope] at hBlock
      | ok scopeResult =>
          rcases scopeResult with ⟨scope, scopeState⟩
          simp [hScope] at hBlock
          rcases sourceLocalFunction_elaborateBlock_true_entry
              hLocal hPushIdentifier hScope hBlockRun with
            ⟨generated, fn, hLookup, hEntryFinal⟩
          have hNameOk :
              bindingNameOk? name = true :=
            localFunctionScope_sourceLocalFunction_bindingNameOk
              hScope hLocal
          have hScopePres :
              scopeState.functionScopes =
                identifierPushedState.functionScopes :=
            Stmt.List.localFunctionScope_preserves_functionScopes
              stmts hScope
          cases hPushFunction :
              (pushFunctionScope scope).run scopeState with
          | error err =>
              simp [hPushFunction] at hBlock
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              have hPushFunctionScopes :
                  functionPushedState.functionScopes =
                    scope :: scopeState.functionScopes :=
                pushFunctionScope_functionScopes hPushFunction
              simp [hPushFunction] at hBlock
              cases hHoist :
                  (Stmt.List.hoistLocalFunctions stmts scope).run
                    functionPushedState with
              | error err =>
                  simp [hHoist] at hBlock
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  have hHoistScopes :
                      hoistState.functionScopes =
                        functionPushedState.functionScopes :=
                    Stmt.List.hoistLocalFunctions_preserves_functionScopes
                      stmts scope hHoist
                  have hResolveHoist :
                      resolveFunctionIn name hoistState.functionScopes =
                        some generated := by
                    rw [hHoistScopes, hPushFunctionScopes, hScopePres,
                      hIdentifierPushScopes]
                    exact resolveFunctionIn_of_scope_lookup hLookup
                  simp [hHoist] at hBlock
                  cases hElab :
                      (Stmt.List.elaborate stmts).run hoistState with
                  | error err =>
                      simp [hElab] at hBlock
                  | ok elabResult =>
                      rcases elabResult with ⟨front', elabState⟩
                      rcases
                        Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
                          hOccurs hNameOk hResolveHoist hElab with
                        ⟨args', hOccurrence⟩
                      simp [hElab] at hBlock
                      cases hPopFunction :
                          popFunctionScope.run elabState with
                      | error err =>
                          simp [hPopFunction] at hBlock
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hBlock
                          cases hPopIdentifier :
                              popIdentifierScope.run
                                functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hBlock
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hBlock
                              rcases hBlock with ⟨hFront, _hFinal⟩
                              rw [← hFront]
                              exact
                                ⟨generated, fn, args', hOccurrence,
                                  hEntryFinal⟩

theorem Stmt.List.sourceLocalFunction_elaborateForInitBlockWithScope_noShadow_stmtUserCall_entry
    {stmts : List Raw.Stmt}
    {state finalState : State} {front : List Frontend.Stmt}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction stmts name params returns body)
    (hOccurs : Raw.Source.NoShadowStmtListCall stmts name args)
    (hBlock :
      (Stmt.List.elaborateForInitBlockWithScope stmts).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtListUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  unfold Stmt.List.elaborateForInitBlockWithScope at hBlock
  simp [StateT.run_bind] at hBlock
  cases hScope :
      (Stmt.List.localFunctionScope stmts).run state with
  | error err =>
      simp [hScope] at hBlock
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      rcases localFunctionScope_sourceLocalFunction_lookup hScope hLocal with
        ⟨generated, hLookup⟩
      have hNameOk :
          bindingNameOk? name = true :=
        localFunctionScope_sourceLocalFunction_bindingNameOk hScope hLocal
      have hScopePres :
          scopeState.functionScopes = state.functionScopes :=
        Stmt.List.localFunctionScope_preserves_functionScopes
          stmts hScope
      simp [hScope] at hBlock
      cases hPushFunction :
          (pushFunctionScope scope).run scopeState with
      | error err =>
          simp [hPushFunction] at hBlock
      | ok pushFunctionResult =>
          rcases pushFunctionResult with ⟨_, functionPushedState⟩
          have hPushFunctionScopes :
              functionPushedState.functionScopes =
                scope :: scopeState.functionScopes :=
            pushFunctionScope_functionScopes hPushFunction
          simp [hPushFunction] at hBlock
          cases hHoist :
              (Stmt.List.hoistLocalFunctions stmts scope).run
                functionPushedState with
          | error err =>
              simp [hHoist] at hBlock
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              rcases hoistLocalFunctions_functionDefinition_entry
                  (Raw.Source.LocalFunction.mem hLocal) hLookup hHoist with
                ⟨fn, hEntryHoist⟩
              have hHoistScopes :
                  hoistState.functionScopes =
                    functionPushedState.functionScopes :=
                Stmt.List.hoistLocalFunctions_preserves_functionScopes
                  stmts scope hHoist
              have hResolveHoist :
                  resolveFunctionIn name hoistState.functionScopes =
                    some generated := by
                rw [hHoistScopes, hPushFunctionScopes, hScopePres]
                exact resolveFunctionIn_of_scope_lookup hLookup
              simp [hHoist] at hBlock
              cases hElab :
                  (Stmt.List.elaborate stmts).run hoistState with
              | error err =>
                  simp [hElab] at hBlock
              | ok elabResult =>
                  rcases elabResult with ⟨front', elabState⟩
                  rcases
                    Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call
                      hOccurs hNameOk hResolveHoist hElab with
                    ⟨args', hOccurrence⟩
                  have hEntryFinal :
                      (generated, fn) ∈ elabState.hoistedFunctions :=
                    Stmt.List.elaborate_preserves_hoistedFunction_mem
                      stmts hElab hEntryHoist
                  simp [hElab] at hBlock
                  rcases hBlock with ⟨hFront, hFinal⟩
                  cases hFront
                  cases hFinal
                  exact
                    ⟨generated, fn, args', hOccurrence, hEntryFinal⟩

theorem Stmt.sourceLocalFunction_forLoop_condition_stmtUserCall_entry
    {pre : List Raw.Stmt} {condition : Raw.Expr}
    {post body : List Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name : Name} {params returns : List Name} {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction pre name params returns localBody)
    (hOccurs : Raw.Source.ExprCall.Occurs condition name args)
    (hElab :
      (Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hPreHas :
      Stmt.List.hasImmediateFunctionDefinition pre = true :=
    Stmt.List.hasImmediateFunctionDefinition_of_sourceLocalFunction hLocal
  unfold Stmt.elaborate at hElab
  simp [hPreHas, StateT.run_bind] at hElab
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hElab
      cases hPre :
          (Stmt.List.elaborateForInitBlockWithScope pre).run
            identifierPushedState with
      | error err =>
          simp [hPre] at hElab
      | ok preResult =>
          rcases preResult with ⟨frontPre, preState⟩
          rcases
            Stmt.List.sourceLocalFunction_elaborateForInitBlockWithScope_entry
              hLocal hPre with
            ⟨generated, fn, scope, hLookup, hNameOk, hPreScopes, hEntryPre⟩
          have hResolvePre :
              resolveFunctionIn name preState.functionScopes =
                some generated := by
            rw [hPreScopes]
            simp [resolveFunctionIn, hLookup]
          simp [hPre] at hElab
          cases hCondition :
              (Expr.elaborate condition).run preState with
          | error err =>
              simp [hCondition] at hElab
          | ok conditionResult =>
              rcases conditionResult with ⟨frontCondition, conditionState⟩
              rcases
                Expr.elaborate_resolved_source_user_call_occurrence
                  hOccurs hNameOk hResolvePre hCondition with
                ⟨args', hOccurrence⟩
              have hEntryCondition :
                  (generated, fn) ∈ conditionState.hoistedFunctions :=
                Expr.elaborate_preserves_hoistedFunction_mem
                  condition hCondition hEntryPre
              simp [hCondition] at hElab
              cases hPost :
                  (Stmt.List.elaborateBlock post true).run
                    conditionState with
              | error err =>
                  simp [hPost] at hElab
              | ok postResult =>
                  rcases postResult with ⟨frontPost, postState⟩
                  have hEntryPost :
                      (generated, fn) ∈ postState.hoistedFunctions :=
                    Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                      post true hPost hEntryCondition
                  simp [hPost] at hElab
                  cases hBody :
                      (Stmt.List.elaborateBlock body true).run
                        postState with
                  | error err =>
                      simp [hBody] at hElab
                  | ok bodyResult =>
                      rcases bodyResult with ⟨frontBody, bodyState⟩
                      have hEntryBody :
                          (generated, fn) ∈ bodyState.hoistedFunctions :=
                        Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                          body true hBody hEntryPost
                      simp [hBody] at hElab
                      cases hPopFunction : popFunctionScope.run bodyState with
                      | error err =>
                          simp [hPopFunction] at hElab
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          have hEntryPopFunction :
                              (generated, fn) ∈
                                functionPoppedState.hoistedFunctions :=
                            popFunctionScope_preserves_hoistedFunction_mem
                              hPopFunction hEntryBody
                          simp [hPopFunction] at hElab
                          cases hPopIdentifier :
                              popIdentifierScope.run functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              have hEntryFinal :
                                  (generated, fn) ∈
                                    identifierPoppedState.hoistedFunctions :=
                                popIdentifierScope_preserves_hoistedFunction_mem
                                  hPopIdentifier hEntryPopFunction
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨hFront, hFinal⟩
                              cases hFinal
                              rw [← hFront]
                              exact
                                ⟨generated, fn, args',
                                  FrontendOccurrence.StmtUserCall.forCondition
                                    hOccurrence,
                                  hEntryFinal⟩

theorem Stmt.sourceLocalFunction_forLoop_post_stmtUserCall_entry
    {pre : List Raw.Stmt} {condition : Raw.Expr}
    {post body : List Raw.Stmt} {postStmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name : Name} {params returns : List Name} {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction pre name params returns localBody)
    (hNoPostShadow : Raw.Source.NoLocalFunctionNamed post name)
    (hMem : postStmt ∈ post)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope postStmt name args)
    (hElab :
      (Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hPreHas :
      Stmt.List.hasImmediateFunctionDefinition pre = true :=
    Stmt.List.hasImmediateFunctionDefinition_of_sourceLocalFunction hLocal
  unfold Stmt.elaborate at hElab
  simp [hPreHas, StateT.run_bind] at hElab
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hElab
      cases hPre :
          (Stmt.List.elaborateForInitBlockWithScope pre).run
            identifierPushedState with
      | error err =>
          simp [hPre] at hElab
      | ok preResult =>
          rcases preResult with ⟨frontPre, preState⟩
          rcases
            Stmt.List.sourceLocalFunction_elaborateForInitBlockWithScope_entry
              hLocal hPre with
            ⟨generated, fn, scope, hLookup, hNameOk, hPreScopes, hEntryPre⟩
          have hResolvePre :
              resolveFunctionIn name preState.functionScopes =
                some generated := by
            rw [hPreScopes]
            simp [resolveFunctionIn, hLookup]
          simp [hPre] at hElab
          cases hCondition :
              (Expr.elaborate condition).run preState with
          | error err =>
              simp [hCondition] at hElab
          | ok conditionResult =>
              rcases conditionResult with ⟨frontCondition, conditionState⟩
              have hConditionScopes :
                  conditionState.functionScopes =
                    preState.functionScopes :=
                Expr.elaborate_preserves_functionScopes
                  condition hCondition
              have hResolveCondition :
                  resolveFunctionIn name conditionState.functionScopes =
                    some generated := by
                rw [hConditionScopes]
                exact hResolvePre
              have hEntryCondition :
                  (generated, fn) ∈ conditionState.hoistedFunctions :=
                Expr.elaborate_preserves_hoistedFunction_mem
                  condition hCondition hEntryPre
              simp [hCondition] at hElab
              cases hPost :
                  (Stmt.List.elaborateBlock post true).run
                    conditionState with
              | error err =>
                  simp [hPost] at hElab
              | ok postResult =>
                  rcases postResult with ⟨frontPost, postState⟩
                  rcases
                    Stmt.List.elaborateBlock_true_noShadow_resolved_incoming_call_mem
                      hNoPostShadow hMem hOccurs hNameOk
                      hResolveCondition hPost with
                    ⟨args', hPostOccurrence⟩
                  have hEntryPost :
                      (generated, fn) ∈ postState.hoistedFunctions :=
                    Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                      post true hPost hEntryCondition
                  simp [hPost] at hElab
                  cases hBody :
                      (Stmt.List.elaborateBlock body true).run
                        postState with
                  | error err =>
                      simp [hBody] at hElab
                  | ok bodyResult =>
                      rcases bodyResult with ⟨frontBody, bodyState⟩
                      have hEntryBody :
                          (generated, fn) ∈ bodyState.hoistedFunctions :=
                        Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                          body true hBody hEntryPost
                      simp [hBody] at hElab
                      cases hPopFunction : popFunctionScope.run bodyState with
                      | error err =>
                          simp [hPopFunction] at hElab
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          have hEntryPopFunction :
                              (generated, fn) ∈
                                functionPoppedState.hoistedFunctions :=
                            popFunctionScope_preserves_hoistedFunction_mem
                              hPopFunction hEntryBody
                          simp [hPopFunction] at hElab
                          cases hPopIdentifier :
                              popIdentifierScope.run functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              have hEntryFinal :
                                  (generated, fn) ∈
                                    identifierPoppedState.hoistedFunctions :=
                                popIdentifierScope_preserves_hoistedFunction_mem
                                  hPopIdentifier hEntryPopFunction
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨hFront, hFinal⟩
                              cases hFinal
                              rw [← hFront]
                              exact
                                ⟨generated, fn, args',
                                  FrontendOccurrence.StmtUserCall.forPost
                                    hPostOccurrence,
                                  hEntryFinal⟩

theorem Stmt.sourceLocalFunction_forLoop_body_stmtUserCall_entry
    {pre : List Raw.Stmt} {condition : Raw.Expr}
    {post body : List Raw.Stmt} {bodyStmt : Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name : Name} {params returns : List Name} {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction pre name params returns localBody)
    (hNoBodyShadow : Raw.Source.NoLocalFunctionNamed body name)
    (hMem : bodyStmt ∈ body)
    (hOccurs :
      Raw.Source.StmtExprCall.IncomingScope bodyStmt name args)
    (hElab :
      (Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (front, finalState)) :
    ∃ generated fn args',
      FrontendOccurrence.StmtUserCall front generated args' ∧
        (generated, fn) ∈ finalState.hoistedFunctions := by
  have hPreHas :
      Stmt.List.hasImmediateFunctionDefinition pre = true :=
    Stmt.List.hasImmediateFunctionDefinition_of_sourceLocalFunction hLocal
  unfold Stmt.elaborate at hElab
  simp [hPreHas, StateT.run_bind] at hElab
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hElab
      cases hPre :
          (Stmt.List.elaborateForInitBlockWithScope pre).run
            identifierPushedState with
      | error err =>
          simp [hPre] at hElab
      | ok preResult =>
          rcases preResult with ⟨frontPre, preState⟩
          rcases
            Stmt.List.sourceLocalFunction_elaborateForInitBlockWithScope_entry
              hLocal hPre with
            ⟨generated, fn, scope, hLookup, hNameOk, hPreScopes, hEntryPre⟩
          have hResolvePre :
              resolveFunctionIn name preState.functionScopes =
                some generated := by
            rw [hPreScopes]
            simp [resolveFunctionIn, hLookup]
          simp [hPre] at hElab
          cases hCondition :
              (Expr.elaborate condition).run preState with
          | error err =>
              simp [hCondition] at hElab
          | ok conditionResult =>
              rcases conditionResult with ⟨frontCondition, conditionState⟩
              have hConditionScopes :
                  conditionState.functionScopes =
                    preState.functionScopes :=
                Expr.elaborate_preserves_functionScopes
                  condition hCondition
              have hEntryCondition :
                  (generated, fn) ∈ conditionState.hoistedFunctions :=
                Expr.elaborate_preserves_hoistedFunction_mem
                  condition hCondition hEntryPre
              simp [hCondition] at hElab
              cases hPost :
                  (Stmt.List.elaborateBlock post true).run
                    conditionState with
              | error err =>
                  simp [hPost] at hElab
              | ok postResult =>
                  rcases postResult with ⟨frontPost, postState⟩
                  have hPostScopes :
                      postState.functionScopes =
                        conditionState.functionScopes :=
                    Stmt.List.elaborateBlock_preserves_functionScopes
                      post true hPost
                  have hResolveBody :
                      resolveFunctionIn name postState.functionScopes =
                        some generated := by
                    rw [hPostScopes, hConditionScopes]
                    exact hResolvePre
                  have hEntryPost :
                      (generated, fn) ∈ postState.hoistedFunctions :=
                    Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                      post true hPost hEntryCondition
                  simp [hPost] at hElab
                  cases hBody :
                      (Stmt.List.elaborateBlock body true).run
                        postState with
                  | error err =>
                      simp [hBody] at hElab
                  | ok bodyResult =>
                      rcases bodyResult with ⟨frontBody, bodyState⟩
                      rcases
                        Stmt.List.elaborateBlock_true_noShadow_resolved_incoming_call_mem
                          hNoBodyShadow hMem hOccurs hNameOk
                          hResolveBody hBody with
                        ⟨args', hBodyOccurrence⟩
                      have hEntryBody :
                          (generated, fn) ∈ bodyState.hoistedFunctions :=
                        Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                          body true hBody hEntryPost
                      simp [hBody] at hElab
                      cases hPopFunction : popFunctionScope.run bodyState with
                      | error err =>
                          simp [hPopFunction] at hElab
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          have hEntryPopFunction :
                              (generated, fn) ∈
                                functionPoppedState.hoistedFunctions :=
                            popFunctionScope_preserves_hoistedFunction_mem
                              hPopFunction hEntryBody
                          simp [hPopFunction] at hElab
                          cases hPopIdentifier :
                              popIdentifierScope.run functionPoppedState with
                          | error err =>
                              simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              have hEntryFinal :
                                  (generated, fn) ∈
                                    identifierPoppedState.hoistedFunctions :=
                                popIdentifierScope_preserves_hoistedFunction_mem
                                  hPopIdentifier hEntryPopFunction
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨hFront, hFinal⟩
                              cases hFinal
                              rw [← hFront]
                              exact
                                ⟨generated, fn, args',
                                  FrontendOccurrence.StmtUserCall.forBody
                                    hBodyOccurrence,
                                  hEntryFinal⟩

theorem FunctionDef.elaborate_sourceLocalFunction_entry
    {params returns : List Name} {body : List Raw.Stmt}
    {state finalState : State} {fn : Frontend.FunctionDef}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt}
    (hLocal :
      Raw.Source.LocalFunction body name localParams localReturns localBody)
    (hElab :
      (FunctionDef.elaborate params returns body).run state =
        .ok (fn, finalState)) :
    ∃ generated localFn,
      (generated, localFn) ∈ finalState.hoistedFunctions := by
  unfold FunctionDef.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hPush : pushIdentifierScope.run state with
  | error err =>
      simp [hPush] at hElab
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      simp [hPush] at hElab
      cases hDeclare :
          (declareIdentifiers (params ++ returns)
            "function parameter/result").run pushedState with
      | error err =>
          simp [hDeclare] at hElab
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          simp [hDeclare] at hElab
          cases hBlock :
              (Stmt.List.elaborateBlock body true).run declaredState with
          | error err =>
              simp [hBlock] at hElab
          | ok blockResult =>
              rcases blockResult with ⟨front, blockState⟩
              rcases Stmt.List.sourceLocalFunction_elaborateBlock_true_entry_of_run
                  hLocal hBlock with
                ⟨generated, localFn, hEntryBlock⟩
              simp [hBlock] at hElab
              cases hPop : popIdentifierScope.run blockState with
              | error err =>
                  simp [hPop] at hElab
              | ok popResult =>
                  rcases popResult with ⟨_, poppedState⟩
                  have hEntryFinal :
                      (generated, localFn) ∈
                        poppedState.hoistedFunctions :=
                    popIdentifierScope_preserves_hoistedFunction_mem
                      hPop hEntryBlock
                  simp [hPop] at hElab
                  rcases hElab with ⟨_hFn, hFinal⟩
                  cases hFinal
                  exact ⟨generated, localFn, hEntryFinal⟩

theorem FunctionDef.elaborate_sourceLocalFunction_noShadow_stmtUserCall_entry
    {params returns : List Name} {body : List Raw.Stmt}
    {state finalState : State} {fn : Frontend.FunctionDef}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction body name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall body name args)
    (hElab :
      (FunctionDef.elaborate params returns body).run state =
        .ok (fn, finalState)) :
    ∃ generated localFn args',
      FrontendOccurrence.StmtListUserCall fn.body generated args' ∧
        (generated, localFn) ∈ finalState.hoistedFunctions := by
  unfold FunctionDef.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hPush : pushIdentifierScope.run state with
  | error err =>
      simp [hPush] at hElab
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      simp [hPush] at hElab
      cases hDeclare :
          (declareIdentifiers (params ++ returns)
            "function parameter/result").run pushedState with
      | error err =>
          simp [hDeclare] at hElab
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          simp [hDeclare] at hElab
          cases hBlock :
              (Stmt.List.elaborateBlock body true).run declaredState with
          | error err =>
              simp [hBlock] at hElab
          | ok blockResult =>
              rcases blockResult with ⟨frontBody, blockState⟩
              rcases
                Stmt.List.sourceLocalFunction_elaborateBlock_true_noShadow_stmtUserCall_entry
                  hLocal hOccurs hBlock with
                ⟨generated, localFn, args', hOccurrence, hEntryBlock⟩
              simp [hBlock] at hElab
              cases hPop : popIdentifierScope.run blockState with
              | error err =>
                  simp [hPop] at hElab
              | ok popResult =>
                  rcases popResult with ⟨_, poppedState⟩
                  have hEntryFinal :
                      (generated, localFn) ∈
                        poppedState.hoistedFunctions :=
                    popIdentifierScope_preserves_hoistedFunction_mem
                      hPop hEntryBlock
                  simp [hPop] at hElab
                  rcases hElab with ⟨hFn, hFinal⟩
                  cases hFinal
                  rw [← hFn]
                  exact
                    ⟨generated, localFn, args', hOccurrence, hEntryFinal⟩

theorem Stmt.elaborate_functionDefinition_sourceLocalFunction_noShadow_stmtUserCall_entry
    {fnName : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    {state finalState : State} {front : Frontend.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hLocal :
      Raw.Source.LocalFunction body name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall body name args)
    (hElab :
      (Stmt.elaborate (.functionDefinition fnName params returns body)).run
        state = .ok (front, finalState)) :
    ∃ generated localFn args',
      FrontendOccurrence.StmtUserCall front generated args' ∧
        (generated, localFn) ∈ finalState.hoistedFunctions := by
  unfold Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hResolveFn : (resolveFunction fnName).run state with
  | error err =>
      simp [hResolveFn] at hElab
  | ok resolveResult =>
      rcases resolveResult with ⟨frontFnName, resolvedState⟩
      simp [hResolveFn] at hElab
      cases hFn :
          (FunctionDef.elaborate params returns body).run
            resolvedState with
      | error err =>
          simp [hFn] at hElab
      | ok fnResult =>
          rcases fnResult with ⟨frontFn, fnState⟩
          rcases
            FunctionDef.elaborate_sourceLocalFunction_noShadow_stmtUserCall_entry
              hLocal hOccurs hFn with
            ⟨generated, localFn, args', hOccurrence, hEntry⟩
          simp [hFn] at hElab
          rcases hElab with ⟨hFront, hFinal⟩
          cases hFinal
          rw [← hFront]
          exact
            ⟨generated, localFn, args',
              FrontendOccurrence.StmtUserCall.functionBody hOccurrence,
              hEntry⟩

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

def elaborateTopLevel :
    List Raw.Stmt → List Frontend.Stmt →
      List (Name × Frontend.FunctionDef) →
        ElabM (List Frontend.Stmt × List (Name × Frontend.FunctionDef))
  | [], dispatcher, topFunctions => pure (dispatcher.reverse, topFunctions)
  | stmt :: rest, dispatcher, topFunctions => do
      match stmt with
      | .functionDefinition name params returns body =>
          let fn ← FunctionDef.elaborate params returns body
          elaborateTopLevel rest dispatcher ((name, fn) :: topFunctions)
      | _ =>
          let stmt ← Stmt.elaborate stmt
          elaborateTopLevel rest (stmt :: dispatcher) topFunctions

theorem elaborateTopLevel_preserves_hoistedFunction_mem
    (stmts : List Raw.Stmt) (dispatcher : List Frontend.Stmt)
    (topFunctions : List (Name × Frontend.FunctionDef)) :
    PreservesHoisted (elaborateTopLevel stmts dispatcher topFunctions) := by
  induction stmts generalizing dispatcher topFunctions with
  | nil =>
      intro state state' value entry hRun hEntry
      unfold elaborateTopLevel at hRun
      simp [StateT.run_pure] at hRun
      cases hRun
      exact hEntry
  | cons stmt rest ih =>
      cases stmt with
      | block stmts =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem
                (.block stmts))
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | variableDeclaration names value? =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem
                (.variableDeclaration names value?))
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | assignment names value =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem
                (.assignment names value))
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | expressionStatement expr =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem
                (.expressionStatement expr))
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | functionDefinition name params returns body =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (FunctionDef.elaborate_preserves_hoistedFunction_mem
                params returns body)
              (fun fn =>
                ih dispatcher ((name, fn) :: topFunctions))
      | switch scrutinee cases default =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem
                (.switch scrutinee cases default))
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | forLoop pre condition post body =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem
                (.forLoop pre condition post body))
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | ifThen condition body =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem
                (.ifThen condition body))
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | «break» =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem .break)
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | «continue» =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem .continue)
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)
      | «leave» =>
          unfold elaborateTopLevel
          exact
            PreservesHoisted.bind
              (Stmt.elaborate_preserves_hoistedFunction_mem .leave)
              (fun stmt =>
                ih (stmt :: dispatcher) topFunctions)

theorem elaborateTopLevel_preserves_topFunction_mem
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {topFunctions : List (Name × Frontend.FunctionDef)}
    {state finalState : State}
    {result : List Frontend.Stmt × List (Name × Frontend.FunctionDef)}
    {entry : Name × Frontend.FunctionDef}
    (hRun :
      (elaborateTopLevel stmts dispatcher topFunctions).run state =
        .ok (result, finalState))
    (hEntry : entry ∈ topFunctions) :
    entry ∈ result.2 := by
  induction stmts generalizing dispatcher topFunctions state finalState result with
  | nil =>
      unfold elaborateTopLevel at hRun
      simp [StateT.run_pure] at hRun
      cases hRun
      exact hEntry
  | cons stmt rest ih =>
      cases stmt with
      | block stmts =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate (.block stmts)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | variableDeclaration names value? =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.variableDeclaration names value?)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | assignment names value =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.assignment names value)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | expressionStatement expr =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.expressionStatement expr)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | functionDefinition name params returns body =>
          unfold elaborateTopLevel at hRun
          cases hFn :
              (FunctionDef.elaborate params returns body).run state with
          | error err =>
              simp [hFn] at hRun
          | ok fnResult =>
              rcases fnResult with ⟨fn, fnState⟩
              simp [hFn] at hRun
              exact ih hRun (by simp [hEntry])
      | switch scrutinee cases default =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.switch scrutinee cases default)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | forLoop pre condition post body =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.forLoop pre condition post body)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | ifThen condition body =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.ifThen condition body)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | «break» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .break).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | «continue» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .continue).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry
      | «leave» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .leave).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              exact ih hRun hEntry

theorem elaborateTopLevel_sourceLocalFunction_entry
    {stmts : List Raw.Stmt}
    {dispatcher : List Frontend.Stmt}
    {topFunctions : List (Name × Frontend.FunctionDef)}
    {state finalState : State}
    {result : List Frontend.Stmt × List (Name × Frontend.FunctionDef)}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hRun :
      (elaborateTopLevel stmts dispatcher topFunctions).run state =
        .ok (result, finalState)) :
    ∃ generated localFn,
      (generated, localFn) ∈ finalState.hoistedFunctions := by
  induction stmts generalizing dispatcher topFunctions state finalState result with
  | nil =>
      simp at hTop
  | cons stmt rest ih =>
      cases stmt with
      | block stmts =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate (.block stmts)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | variableDeclaration names value? =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.variableDeclaration names value?)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | assignment names value =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.assignment names value)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | expressionStatement expr =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.expressionStatement expr)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | functionDefinition headName headParams headReturns headBody =>
          unfold elaborateTopLevel at hRun
          cases hFn :
              (FunctionDef.elaborate headParams headReturns headBody).run
                state with
          | error err =>
              simp [hFn] at hRun
          | ok fnResult =>
              rcases fnResult with ⟨headFn, headState⟩
              simp [hFn] at hRun
              rcases List.mem_cons.mp hTop with hHead | hTail
              · cases hHead
                rcases FunctionDef.elaborate_sourceLocalFunction_entry
                    hLocal hFn with
                  ⟨generated, localFn, hEntryHead⟩
                have hEntryFinal :
                    (generated, localFn) ∈
                      finalState.hoistedFunctions :=
                  elaborateTopLevel_preserves_hoistedFunction_mem
                    rest dispatcher ((topName, headFn) :: topFunctions)
                    hRun hEntryHead
                exact ⟨generated, localFn, hEntryFinal⟩
              · exact ih hTail hRun
      | switch scrutinee cases default =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.switch scrutinee cases default)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | forLoop pre condition post body =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.forLoop pre condition post body)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | ifThen condition body =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.ifThen condition body)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | «break» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .break).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | «continue» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .continue).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | «leave» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .leave).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun

theorem elaborateTopLevel_sourceLocalFunction_noShadow_function_entries
    {stmts : List Raw.Stmt}
    {dispatcher : List Frontend.Stmt}
    {topFunctions : List (Name × Frontend.FunctionDef)}
    {state finalState : State}
    {result : List Frontend.Stmt × List (Name × Frontend.FunctionDef)}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hRun :
      (elaborateTopLevel stmts dispatcher topFunctions).run state =
        .ok (result, finalState)) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ result.2 ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ finalState.hoistedFunctions := by
  induction stmts generalizing dispatcher topFunctions state finalState result with
  | nil =>
      simp at hTop
  | cons stmt rest ih =>
      cases stmt with
      | block stmts =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate (.block stmts)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | variableDeclaration names value? =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.variableDeclaration names value?)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | assignment names value =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.assignment names value)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | expressionStatement expr =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.expressionStatement expr)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | functionDefinition headName headParams headReturns headBody =>
          unfold elaborateTopLevel at hRun
          cases hFn :
              (FunctionDef.elaborate headParams headReturns headBody).run
                state with
          | error err =>
              simp [hFn] at hRun
          | ok fnResult =>
              rcases fnResult with ⟨headFn, headState⟩
              simp [hFn] at hRun
              rcases List.mem_cons.mp hTop with hHead | hTail
              · cases hHead
                rcases
                  FunctionDef.elaborate_sourceLocalFunction_noShadow_stmtUserCall_entry
                    hLocal hOccurs hFn with
                  ⟨generated, localFn, args', hOccurrence, hEntryHead⟩
                have hEntryFinal :
                    (generated, localFn) ∈
                      finalState.hoistedFunctions :=
                  elaborateTopLevel_preserves_hoistedFunction_mem
                    rest dispatcher ((topName, headFn) :: topFunctions)
                    hRun hEntryHead
                have hTopFunction :
                    (topName, headFn) ∈ result.2 :=
                  elaborateTopLevel_preserves_topFunction_mem
                    hRun (by simp)
                exact
                  ⟨generated, localFn, args', headFn, hTopFunction,
                    hOccurrence, hEntryFinal⟩
              · exact ih hTail hRun
      | switch scrutinee cases default =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.switch scrutinee cases default)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | forLoop pre condition post body =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.forLoop pre condition post body)).run
                state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | ifThen condition body =>
          unfold elaborateTopLevel at hRun
          cases hStmt :
              (Stmt.elaborate (.ifThen condition body)).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | «break» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .break).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | «continue» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .continue).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun
      | «leave» =>
          unfold elaborateTopLevel at hRun
          cases hStmt : (Stmt.elaborate .leave).run state with
          | error err =>
              simp [hStmt] at hRun
          | ok stmtResult =>
              rcases stmtResult with ⟨stmt, stmtState⟩
              simp [hStmt] at hRun
              have hTail :
                  .functionDefinition topName topParams topReturns
                    topBody ∈ rest := by
                simpa using hTop
              exact ih hTail hRun

def elaborateCodeAction (stmts : List Raw.Stmt) :
    ElabM (List Frontend.Stmt) := do
  pushIdentifierScope
  let topScope ← collectTopFunctions stmts
  pushFunctionScope topScope
  let (dispatcher, topFunctions) ← elaborateTopLevel stmts [] []
  popFunctionScope
  popIdentifierScope
  modify fun state =>
    { state with hoistedFunctions := state.hoistedFunctions ++ topFunctions }
  pure dispatcher

theorem elaborateCodeAction_sourceLocalFunction_entry
    {stmts : List Raw.Stmt}
    {state finalState : State} {dispatcher : List Frontend.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hRun :
      (elaborateCodeAction stmts).run state =
        .ok (dispatcher, finalState)) :
    ∃ generated localFn,
      (generated, localFn) ∈ finalState.hoistedFunctions := by
  unfold elaborateCodeAction at hRun
  simp [StateT.run_bind] at hRun
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hRun
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hRun
      cases hCollect :
          (collectTopFunctions stmts).run identifierPushedState with
      | error err =>
          simp [hCollect] at hRun
      | ok collectResult =>
          rcases collectResult with ⟨topScope, collectState⟩
          simp [hCollect] at hRun
          cases hPushFunction :
              (pushFunctionScope topScope).run collectState with
          | error err =>
              simp [hPushFunction] at hRun
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              simp [hPushFunction] at hRun
              cases hTopLevel :
                  (elaborateTopLevel stmts [] []).run
                    functionPushedState with
              | error err =>
                  simp [hTopLevel] at hRun
              | ok topLevelResult =>
                  rcases topLevelResult with
                    ⟨topLevelValue, topLevelState⟩
                  rcases topLevelValue with
                    ⟨topDispatcher, topFunctions⟩
                  rcases elaborateTopLevel_sourceLocalFunction_entry
                      hTop hLocal hTopLevel with
                    ⟨generated, localFn, hEntryTop⟩
                  simp [hTopLevel] at hRun
                  cases hPopFunction :
                      popFunctionScope.run topLevelState with
                  | error err =>
                      simp [hPopFunction] at hRun
                  | ok popFunctionResult =>
                      rcases popFunctionResult with
                        ⟨_, functionPoppedState⟩
                      have hEntryFunctionPopped :
                          (generated, localFn) ∈
                            functionPoppedState.hoistedFunctions :=
                        popFunctionScope_preserves_hoistedFunction_mem
                          hPopFunction hEntryTop
                      simp [hPopFunction] at hRun
                      cases hPopIdentifier :
                          popIdentifierScope.run functionPoppedState with
                      | error err =>
                          simp [hPopIdentifier] at hRun
                      | ok popIdentifierResult =>
                          rcases popIdentifierResult with
                            ⟨_, identifierPoppedState⟩
                          have hEntryIdentifierPopped :
                              (generated, localFn) ∈
                                identifierPoppedState.hoistedFunctions :=
                            popIdentifierScope_preserves_hoistedFunction_mem
                              hPopIdentifier hEntryFunctionPopped
                          simp [hPopIdentifier, StateT.run_bind,
                            StateT.run_get, StateT.run_set] at hRun
                          rcases hRun with ⟨_hDispatcher, hFinal⟩
                          cases hFinal
                          exact
                            ⟨generated, localFn,
                              by simp [hEntryIdentifierPopped]⟩

theorem elaborateCodeAction_sourceLocalFunction_noShadow_function_entries
    {stmts : List Raw.Stmt}
    {state finalState : State} {dispatcher : List Frontend.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hRun :
      (elaborateCodeAction stmts).run state =
        .ok (dispatcher, finalState)) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ finalState.hoistedFunctions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ finalState.hoistedFunctions := by
  unfold elaborateCodeAction at hRun
  simp [StateT.run_bind] at hRun
  cases hPushIdentifier : pushIdentifierScope.run state with
  | error err =>
      simp [hPushIdentifier] at hRun
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hRun
      cases hCollect :
          (collectTopFunctions stmts).run identifierPushedState with
      | error err =>
          simp [hCollect] at hRun
      | ok collectResult =>
          rcases collectResult with ⟨topScope, collectState⟩
          simp [hCollect] at hRun
          cases hPushFunction :
              (pushFunctionScope topScope).run collectState with
          | error err =>
              simp [hPushFunction] at hRun
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              simp [hPushFunction] at hRun
              cases hTopLevel :
                  (elaborateTopLevel stmts [] []).run
                    functionPushedState with
              | error err =>
                  simp [hTopLevel] at hRun
              | ok topLevelResult =>
                  rcases topLevelResult with
                    ⟨topLevelValue, topLevelState⟩
                  rcases topLevelValue with
                    ⟨topDispatcher, topFunctions⟩
                  rcases
                    elaborateTopLevel_sourceLocalFunction_noShadow_function_entries
                      hTop hLocal hOccurs hTopLevel with
                    ⟨generated, localFn, args', topFn,
                      hTopFunction, hOccurrence, hEntryTop⟩
                  simp [hTopLevel] at hRun
                  cases hPopFunction :
                      popFunctionScope.run topLevelState with
                  | error err =>
                      simp [hPopFunction] at hRun
                  | ok popFunctionResult =>
                      rcases popFunctionResult with
                        ⟨_, functionPoppedState⟩
                      have hEntryFunctionPopped :
                          (generated, localFn) ∈
                            functionPoppedState.hoistedFunctions :=
                        popFunctionScope_preserves_hoistedFunction_mem
                          hPopFunction hEntryTop
                      simp [hPopFunction] at hRun
                      cases hPopIdentifier :
                          popIdentifierScope.run functionPoppedState with
                      | error err =>
                          simp [hPopIdentifier] at hRun
                      | ok popIdentifierResult =>
                          rcases popIdentifierResult with
                            ⟨_, identifierPoppedState⟩
                          have hEntryIdentifierPopped :
                              (generated, localFn) ∈
                                identifierPoppedState.hoistedFunctions :=
                            popIdentifierScope_preserves_hoistedFunction_mem
                              hPopIdentifier hEntryFunctionPopped
                          simp [hPopIdentifier, StateT.run_bind,
                            StateT.run_get, StateT.run_set] at hRun
                          rcases hRun with ⟨_hDispatcher, hFinal⟩
                          cases hFinal
                          exact
                            ⟨generated, localFn, args', topFn,
                              by simp [hTopFunction],
                              hOccurrence,
                              by simp [hEntryIdentifierPopped]⟩

def elaborateCodeCore (stmts : List Raw.Stmt) :
    DecodeM (List Frontend.Stmt × State) :=
  (elaborateCodeAction stmts).run {}

theorem elaborateCodeCore_sourceLocalFunction_entry
    {stmts : List Raw.Stmt}
    {state : State} {dispatcher : List Frontend.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hCore :
      elaborateCodeCore stmts = .ok (dispatcher, state)) :
    ∃ generated localFn,
      (generated, localFn) ∈ state.hoistedFunctions := by
  unfold elaborateCodeCore at hCore
  exact elaborateCodeAction_sourceLocalFunction_entry hTop hLocal hCore

theorem elaborateCodeCore_sourceLocalFunction_noShadow_function_entries
    {stmts : List Raw.Stmt}
    {state : State} {dispatcher : List Frontend.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hCore :
      elaborateCodeCore stmts = .ok (dispatcher, state)) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ state.hoistedFunctions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ state.hoistedFunctions := by
  unfold elaborateCodeCore at hCore
  exact
    elaborateCodeAction_sourceLocalFunction_noShadow_function_entries
      hTop hLocal hOccurs hCore

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

theorem elaborateCode_sourceLocalFunction_entry
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper? arg? ret? : Option Name}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hElab :
      elaborateCode stmts =
        .ok (dispatcher, functions, helper?, arg?, ret?)) :
    ∃ generated localFn,
      (generated, localFn) ∈ functions := by
  rcases elaborateCode_parts hElab with
    ⟨state, hCore, hFunctions, _hHelper, _hArg, _hRet⟩
  rcases elaborateCodeCore_sourceLocalFunction_entry
      hTop hLocal hCore with
    ⟨generated, localFn, hEntry⟩
  rw [hFunctions]
  exact ⟨generated, localFn, finalFunctions_hoistedFunction_mem state hEntry⟩

theorem elaborateCode_sourceLocalFunction_noShadow_function_entries
    {stmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper? arg? ret? : Option Name}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ stmts)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hElab :
      elaborateCode stmts =
        .ok (dispatcher, functions, helper?, arg?, ret?)) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ functions := by
  rcases elaborateCode_parts hElab with
    ⟨state, hCore, hFunctions, _hHelper, _hArg, _hRet⟩
  rcases
    elaborateCodeCore_sourceLocalFunction_noShadow_function_entries
      hTop hLocal hOccurs hCore with
    ⟨generated, localFn, args', topFn,
      hTopEntry, hOccurrence, hLocalEntry⟩
  rw [hFunctions]
  exact
    ⟨generated, localFn, args', topFn,
      finalFunctions_hoistedFunction_mem state hTopEntry,
      hOccurrence,
      finalFunctions_hoistedFunction_mem state hLocalEntry⟩

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

theorem Object.elaborate?_sourceLocalFunction_entry
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {code : List Raw.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt}
    (hCode : obj.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hElab : Object.elaborate? obj evmVersion = .ok frontend) :
    ∃ generated localFn,
      (generated, localFn) ∈ frontend.functions := by
  rcases Object.elaborate?_parts hElab with
    ⟨_itemFuel, dispatcher, functions, helper?, arg?, ret?,
      data, objects, items, _hFuel, hCodeElab, _hItems, hFrontend⟩
  rw [hCode] at hCodeElab
  rcases Elab.elaborateCode_sourceLocalFunction_entry
      hTop hLocal hCodeElab with
    ⟨generated, localFn, hEntry⟩
  subst frontend
  exact ⟨generated, localFn, hEntry⟩

theorem Object.elaborate?_sourceLocalFunction_noShadow_function_entries
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {code : List Raw.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hCode : obj.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hElab : Object.elaborate? obj evmVersion = .ok frontend) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ frontend.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ frontend.functions := by
  rcases Object.elaborate?_parts hElab with
    ⟨_itemFuel, dispatcher, functions, helper?, arg?, ret?,
      data, objects, items, _hFuel, hCodeElab, _hItems, hFrontend⟩
  rw [hCode] at hCodeElab
  rcases
    Elab.elaborateCode_sourceLocalFunction_noShadow_function_entries
      hTop hLocal hOccurs hCodeElab with
    ⟨generated, localFn, args', topFn,
      hTopEntry, hOccurrence, hLocalEntry⟩
  subst frontend
  exact
    ⟨generated, localFn, args', topFn,
      hTopEntry, hOccurrence, hLocalEntry⟩

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

theorem Object.elaboratePreservingOrder?_hoistedFunction_ordered_entry
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {ordered : Yul.OrderedProgram}
    {code : List Raw.Stmt} {coreDispatcher : List Frontend.Stmt}
    {state : Elab.State} {name : Name} {fn : Frontend.FunctionDef}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend)
    (hCode : obj.code? = some code)
    (hCore :
      Elab.elaborateCodeCore code = .ok (coreDispatcher, state))
    (hHoisted : (name, fn) ∈ state.hoistedFunctions)
    (hConvert : frontend.toSolcYulOrderedProgram? = some ordered) :
    ∃ yulBody,
      Frontend.Stmt.List.toYul? fn.body = some yulBody ∧
        (name,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            fn.params fn.returns yulBody) ∈ ordered.functionEntries := by
  have hObject := (Object.elaboratePreservingOrder?_parts hElab).1
  have hRetained := Object.elaborate?_hoistedFunctionsRetained hObject
  unfold Object.HoistedFunctionsRetained at hRetained
  rw [hCode] at hRetained
  rcases hRetained with
    ⟨coreDispatcher', state', helper?, arg?, ret?,
      hCore', _hCodeElab, hKeep⟩
  rw [hCore] at hCore'
  cases hCore'
  have hFrontendMem : (name, fn) ∈ frontend.functions :=
    hKeep (name, fn) hHoisted
  exact
    Frontend.Object.toSolcYulOrderedProgram?_function_entry
      hConvert hFrontendMem

theorem Object.elaboratePreservingOrder?_sourceLocalFunction_ordered_entry
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {ordered : Yul.OrderedProgram}
    {code : List Raw.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend)
    (hCode : obj.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hConvert : frontend.toSolcYulOrderedProgram? = some ordered) :
    ∃ generated localFn yulBody,
      (generated, localFn) ∈ frontend.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some yulBody ∧
          (generated,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns yulBody) ∈
            ordered.functionEntries := by
  have hObject := (Object.elaboratePreservingOrder?_parts hElab).1
  rcases Object.elaborate?_sourceLocalFunction_entry
      hCode hTop hLocal hObject with
    ⟨generated, localFn, hFrontendMem⟩
  rcases Frontend.Object.toSolcYulOrderedProgram?_function_entry
      hConvert hFrontendMem with
    ⟨yulBody, hBody, hEntry⟩
  exact
    ⟨generated, localFn, yulBody, hFrontendMem, hBody, hEntry⟩

theorem Object.elaboratePreservingOrder?_sourceLocalFunction_noShadow_function_entries
    {obj : Object} {evmVersion : Yul.SolcValidation.EvmVersion}
    {frontend : Frontend.Object} {code : List Raw.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hElab :
      Object.elaboratePreservingOrder? obj evmVersion = .ok frontend)
    (hCode : obj.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ frontend.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ frontend.functions := by
  have hObject := (Object.elaboratePreservingOrder?_parts hElab).1
  exact
    Object.elaborate?_sourceLocalFunction_noShadow_function_entries
      hCode hTop hLocal hOccurs hObject

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

theorem decodeAndElaborateSolcIrJson_sourceLocalFunction_noShadow_function_entries
    {json : Lean.Json} {selection : Selection}
    {program : Frontend.Program} {selected : SelectedIr}
    {code : List Raw.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hDecode :
      decodeAndElaborateSolcIrJson json selection = .ok program) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ program.object.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ program.object.functions := by
  rcases decodeAndElaborateSolcIrJson_parts hDecode with
    ⟨selected', object, hSelected', hObject, hProgram⟩
  have hSelectedEq : selected' = selected := by
    cases hSelected.symm.trans hSelected'
    rfl
  subst selected'
  subst program
  exact
    Raw.Object.elaborate?_sourceLocalFunction_noShadow_function_entries
      hCode hTop hLocal hOccurs hObject

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

theorem decodeAndElaborateSolcIr?_sourceLocalFunction_noShadow_function_entries
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {json : Lean.Json}
    {selected : SelectedIr} {code : List Raw.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hParse : Lean.Json.parse rawJson = .ok json)
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ generated localFn args' topFn,
      (topName, topFn) ∈ program.object.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
          (generated, localFn) ∈ program.object.functions := by
  rcases decodeAndElaborateSolcIr?_some hDecode with
    ⟨json', hParse', hJsonDecode⟩
  have hJsonEq : json' = json := by
    cases hParse.symm.trans hParse'
    rfl
  subst json'
  exact
    decodeAndElaborateSolcIrJson_sourceLocalFunction_noShadow_function_entries
      hSelected hCode hTop hLocal hOccurs hJsonDecode

theorem decodeAndElaborateSolcIr?_sourceLocalFunction_noShadow_alphaPreserved
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {json : Lean.Json}
    {selected : SelectedIr} {code : List Raw.Stmt}
    {topName : Name} {topParams topReturns : List Name}
    {topBody : List Raw.Stmt}
    {name : Name} {localParams localReturns : List Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hParse : Lean.Json.parse rawJson = .ok json)
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    Raw.Source.AlphaRenamedLocalCallPreserved
      topBody program.object.functions topName name
        localParams localReturns localBody args := by
  rcases
      decodeAndElaborateSolcIr?_sourceLocalFunction_noShadow_function_entries
        hParse hSelected hCode hTop hLocal hOccurs hDecode with
    ⟨generated, localFn, frontArgs, topFn,
      hTopEntry, hOccurrence, hCalleeEntry⟩
  exact
    Raw.Source.AlphaRenamedLocalCallPreserved.of_entries
      hLocal hOccurs hTopEntry hOccurrence hCalleeEntry

end RawAst
end Solidity
end EvmCompiler
