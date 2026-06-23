import EvmCompiler.Solidity.Frontend
import Lean.Data.Json

/-
Decoder for normalized `evm-compiler.solc-yul-bridge.v3` files.

The bridge file carries a full selected Yul object tree: dispatcher code,
function declarations, typed data sections, child objects, and the mixed
object/data item order emitted by solc.  It also preserves primitive calls over
the current verified external surface: CALL-family and CREATE-family boundaries,
BALANCE account-state queries, and EXT* account-code queries. Yul object
builtins stay separate until the computed object-image frontend resolves them.
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend
namespace BridgeJson

abbrev DecodeM := Except String

def maxDecodeFuel : Nat :=
  1000000

def field (json : Lean.Json) (name : String) : DecodeM Lean.Json :=
  match json.getObjVal? name with
  | .ok value => .ok value
  | .error err => .error s!"{name}: {err}"

def optionalField (json : Lean.Json) (name : String) : DecodeM (Option Lean.Json) :=
  match json.getObjVal? name with
  | .ok .null => .ok none
  | .ok value => .ok (some value)
  | .error err => .error s!"{name}: {err}"

def stringField (json : Lean.Json) (name : String) : DecodeM String := do
  (← field json name).getStr?

def natField (json : Lean.Json) (name : String) : DecodeM Nat := do
  (← field json name).getNat?

def arrayField (json : Lean.Json) (name : String) : DecodeM (Array Lean.Json) := do
  (← field json name).getArr?

def decodeArray {α : Type} (decode : Lean.Json → DecodeM α) (json : Lean.Json) :
    DecodeM (List α) := do
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

def decodeStringArrayField (json : Lean.Json) (name : String) :
    DecodeM (List String) :=
  decodeArrayField (fun value => value.getStr?) json name

def decodeWordNat (value : Nat) : DecodeM Word :=
  if value < 2 ^ (256 : Nat) then
    .ok (EvmYul.UInt256.ofNat value)
  else
    .error s!"UInt256 literal out of range: {value}"

def decodeWordField (json : Lean.Json) (name : String) : DecodeM Word := do
  decodeWordNat (← natField json name)

def decodeByte (value : Nat) : DecodeM UInt8 :=
  if value < 256 then
    .ok (UInt8.ofNat value)
  else
    .error s!"byte out of range: {value}"

def decodeByteArrayField (json : Lean.Json) (name : String) :
    DecodeM (List UInt8) :=
  decodeArrayField
    (fun value => do decodeByte (← value.getNat?))
    json name

def expectNode (json : Lean.Json) (expected : String) : DecodeM Unit := do
  let actual ← stringField json "node"
  if actual == expected then
    pure ()
  else
    .error s!"expected node {expected}, got {actual}"

def decodeCallKind : String → DecodeM CallKind
  | "primitive" => .ok .primitive
  | "user" => .ok .user
  | "objectBuiltin" => .ok .objectBuiltin
  | "dialectBuiltin" => .ok .dialectBuiltin
  | other => .error s!"unknown call kind: {other}"

def decodeEvmVersion : String → DecodeM Yul.SolcValidation.EvmVersion
  | "london" => .ok .london
  | "paris" => .ok .paris
  | "shanghai" => .ok .shanghai
  | "cancun" => .ok .cancun
  | other => .error s!"unsupported frontend evmVersion: {other}"

def decodeOptionalName (json : Lean.Json) (name : String) :
    DecodeM (Option Name) := do
  match ← optionalField json name with
  | none => pure none
  | some value => some <$> value.getStr?

mutual
  def decodeExpr : Nat → Lean.Json → DecodeM Expr
    | 0, _ => .error "expression JSON decoder ran out of fuel"
    | fuel + 1, json => do
        let node ← stringField json "node"
        match node with
        | "literal" =>
            .ok (.lit (← decodeWordField json "value"))
        | "stringLiteral" =>
            .ok (.stringLit (← stringField json "value"))
        | "bytesLiteral" =>
            .ok (.bytesLit (← decodeByteArrayField json "bytes"))
        | "var" =>
            .ok (.var (← stringField json "name"))
        | "call" =>
            let kind ← decodeCallKind (← stringField json "calleeKind")
            let callee ← stringField json "callee"
            let args ← decodeArrayField (decodeExpr fuel) json "args"
            .ok (.call kind callee args)
        | other =>
            .error s!"unknown expression node: {other}"

  def decodeSwitchCaseValue : Lean.Json → DecodeM SwitchCaseValue
    | json =>
        match json.getNat? with
        | .ok value => .word <$> decodeWordNat value
        | .error _ => do
            let node ← stringField json "node"
            match node with
            | "literal" =>
                .word <$> decodeWordField json "value"
            | "stringLiteral" =>
                .ok (.stringLit (← stringField json "value"))
            | "bytesLiteral" =>
                .ok (.bytesLit (← decodeByteArrayField json "bytes"))
            | "boolLiteral" =>
                .ok (.boolLit (← (← field json "value").getBool?))
            | other =>
                .error s!"unknown switch case value node: {other}"

  def decodeStmt : Nat → Lean.Json → DecodeM Stmt
    | 0, _ => .error "statement JSON decoder ran out of fuel"
    | fuel + 1, json => do
        let node ← stringField json "node"
        match node with
        | "block" =>
            .ok (.block (← decodeArrayField (decodeStmt fuel) json "stmts"))
        | "let" =>
            let names ← decodeStringArrayField json "names"
            let value? ← optionalField json "value"
            let value? ←
              match value? with
              | none => pure none
              | some value => some <$> decodeExpr fuel value
            .ok (.letDecl names value?)
        | "assign" =>
            let names ← decodeStringArrayField json "names"
            let value ← decodeExpr fuel (← field json "value")
            .ok (.assign names value)
        | "exprStmt" =>
            .ok (.exprStmt (← decodeExpr fuel (← field json "expr")))
        | "function" =>
            let name ← stringField json "name"
            let params ← decodeStringArrayField json "params"
            let returns ← decodeStringArrayField json "returns"
            let body ← decodeArrayField (decodeStmt fuel) json "body"
            .ok (.functionDef name params returns body)
        | "switch" =>
            let scrutinee ← decodeExpr fuel (← field json "scrutinee")
            let cases ← decodeArrayField (decodeSwitchCase fuel) json "cases"
            let default ← decodeArrayField (decodeStmt fuel) json "default"
            .ok (.switch scrutinee cases default)
        | "for" =>
            let pre ← decodeOptionalArrayField (decodeStmt fuel) json "pre"
            let condition ← decodeExpr fuel (← field json "condition")
            let post ← decodeArrayField (decodeStmt fuel) json "post"
            let body ← decodeArrayField (decodeStmt fuel) json "body"
            .ok (.forLoop pre condition post body)
        | "if" =>
            let condition ← decodeExpr fuel (← field json "condition")
            let body ← decodeArrayField (decodeStmt fuel) json "body"
            .ok (.ifThen condition body)
        | "break" => .ok .break
        | "continue" => .ok .continue
        | "leave" => .ok .leave
        | other =>
            .error s!"unknown statement node: {other}"

  def decodeSwitchCase : Nat → Lean.Json →
      DecodeM (SwitchCaseValue × List Stmt)
    | 0, _ => .error "switch-case JSON decoder ran out of fuel"
    | fuel + 1, json => do
        let value ← decodeSwitchCaseValue (← field json "value")
        let body ← decodeArrayField (decodeStmt fuel) json "body"
        .ok (value, body)

  def decodeFunctionDef : Nat → Lean.Json → DecodeM FunctionDef
    | 0, _ => .error "function JSON decoder ran out of fuel"
    | fuel + 1, json => do
        let params ← decodeStringArrayField json "params"
        let returns ← decodeStringArrayField json "returns"
        let body ← decodeArrayField (decodeStmt fuel) json "body"
        .ok { params := params, returns := returns, body := body }

  def decodeNamedFunction : Nat → Lean.Json → DecodeM (Name × FunctionDef)
    | 0, _ => .error "named-function JSON decoder ran out of fuel"
    | fuel + 1, json => do
        let name ← stringField json "name"
        let fn ← decodeFunctionDef fuel json
        .ok (name, fn)

  def decodeDataSection : Nat → Lean.Json → DecodeM DataSection
    | 0, _ => .error "data-section JSON decoder ran out of fuel"
    | _fuel + 1, json => do
        let name? ← decodeOptionalName json "name"
        let bytes ← decodeByteArrayField json "bytes"
        .ok { name? := name?, bytes := bytes }

  def decodeObjectItemRef : Nat → Lean.Json → DecodeM ObjectItemRef
    | 0, _ => .error "object-item JSON decoder ran out of fuel"
    | _fuel + 1, json => do
        let kind ← stringField json "kind"
        let index ← natField json "index"
        match kind with
        | "data" => .ok (.data index)
        | "object" => .ok (.object index)
        | other => .error s!"unknown object item kind: {other}"

  def decodeObject : Nat → Yul.SolcValidation.EvmVersion →
      Lean.Json → DecodeM Object
    | 0, _, _ => .error "object JSON decoder ran out of fuel"
    | fuel + 1, evmVersion, json => do
        expectNode json "object"
        let name ← stringField json "name"
        let dispatcher ← decodeArrayField (decodeStmt fuel) json "dispatcher"
        let functions ← decodeArrayField (decodeNamedFunction fuel) json "functions"
        let data ← decodeArrayField (decodeDataSection fuel) json "data"
        let objects ←
          decodeArrayField (decodeObject fuel evmVersion) json "subobjects"
        let items ← decodeArrayField (decodeObjectItemRef fuel) json "items"
        match json.getObjVal? "memoryContract" with
        | .ok _ =>
            .error "compiler scratch memory contracts are not supported"
        | .error _ =>
            .ok
              { name := name
                dispatcher := dispatcher
                functions := functions
                data := data
                objects := objects
                items := items
                memoryContract := MemoryContract.unrestricted
                evmVersion := evmVersion }
end

def decodeProgram (json : Lean.Json) : DecodeM Program := do
  let schema ← stringField json "schema"
  if schema != "evm-compiler.solc-yul-bridge.v3" then
    .error s!"unsupported bridge JSON schema: {schema}"
  else
    let source ← stringField json "source"
    let contract ← stringField json "contract"
    let frontend ← field json "frontend"
    let producer ← stringField frontend "producer"
    if producer != "solc" then
      .error s!"unsupported frontend producer: {producer}"
    else
      let ast ← stringField frontend "ast"
      if ast != "irOptimizedAst" && ast != "irAst" && ast != "yulAst" then
        .error s!"unsupported frontend AST: {ast}"
      else
        let evmVersion ← decodeEvmVersion (← stringField frontend "evmVersion")
        let objectJson ← field json "selectedObject"
        let object ← decodeObject maxDecodeFuel evmVersion objectJson
        .ok { source := source, contract := contract, object := object }

def parseProgram? (input : String) : DecodeM Program := do
  let json ← Lean.Json.parse input
  decodeProgram json

end BridgeJson
end Frontend
end Solidity
end EvmCompiler
