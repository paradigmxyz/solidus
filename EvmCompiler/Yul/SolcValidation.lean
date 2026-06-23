import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul

/-
Solc-facing validation for the normalized core Yul representation.

This layer is intentionally source-facing: it checks whether a direct
`Yul.Program` construction satisfies the static language conditions that solc's
Yul parser/analyzer would normally enforce before either source execution or
compiler lowering is trusted.

The current core AST has already erased raw Yul object syntax, for-loop init
blocks, literal kinds, and the distinction between an absent switch default and
`default {}`.  This checker therefore validates the normalized `YulContract`
shape used by the backend, while keeping those representation limits explicit.
-/
namespace SolcValidation

structure Signature where
  inputs : Nat
  outputs : Nat
  deriving Inhabited, Repr

def sig (inputs outputs : Nat) : Signature :=
  { inputs := inputs, outputs := outputs }

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
  | osaka
  deriving DecidableEq, Inhabited, Repr

namespace EvmVersion

def rank : EvmVersion → Nat
  | .frontier => 0
  | .homestead => 1
  | .byzantium => 2
  | .constantinople => 3
  | .istanbul => 4
  | .london => 5
  | .paris => 6
  | .shanghai => 7
  | .cancun => 8
  | .osaka => 9

def atLeast? (version minimum : EvmVersion) : Bool :=
  decide (minimum.rank ≤ version.rank)

end EvmVersion

structure DialectProfile where
  evmVersion : EvmVersion
  eof : Bool
  deriving Repr

def defaultDialectProfile : DialectProfile :=
  { evmVersion := .cancun, eof := false }

def EvmVersion.dialectProfile (version : EvmVersion) : DialectProfile :=
  { evmVersion := version, eof := false }

def primitiveSignature : EvmYul.Operation .Yul → Signature
  | .StopArith .STOP => sig 0 0
  | .StopArith .ADD => sig 2 1
  | .StopArith .MUL => sig 2 1
  | .StopArith .SUB => sig 2 1
  | .StopArith .DIV => sig 2 1
  | .StopArith .SDIV => sig 2 1
  | .StopArith .MOD => sig 2 1
  | .StopArith .SMOD => sig 2 1
  | .StopArith .ADDMOD => sig 3 1
  | .StopArith .MULMOD => sig 3 1
  | .StopArith .EXP => sig 2 1
  | .StopArith .SIGNEXTEND => sig 2 1
  | .CompBit .LT => sig 2 1
  | .CompBit .GT => sig 2 1
  | .CompBit .SLT => sig 2 1
  | .CompBit .SGT => sig 2 1
  | .CompBit .EQ => sig 2 1
  | .CompBit .ISZERO => sig 1 1
  | .CompBit .AND => sig 2 1
  | .CompBit .OR => sig 2 1
  | .CompBit .XOR => sig 2 1
  | .CompBit .NOT => sig 1 1
  | .CompBit .BYTE => sig 2 1
  | .CompBit .SHL => sig 2 1
  | .CompBit .SHR => sig 2 1
  | .CompBit .SAR => sig 2 1
  | .Keccak .KECCAK256 => sig 2 1
  | .Env .ADDRESS => sig 0 1
  | .Env .BALANCE => sig 1 1
  | .Env .ORIGIN => sig 0 1
  | .Env .CALLER => sig 0 1
  | .Env .CALLVALUE => sig 0 1
  | .Env .CALLDATALOAD => sig 1 1
  | .Env .CALLDATASIZE => sig 0 1
  | .Env .CALLDATACOPY => sig 3 0
  | .Env .CODESIZE => sig 0 1
  | .Env .GASPRICE => sig 0 1
  | .Env .CODECOPY => sig 3 0
  | .Env .EXTCODESIZE => sig 1 1
  | .Env .EXTCODECOPY => sig 4 0
  | .Env .RETURNDATASIZE => sig 0 1
  | .Env .RETURNDATACOPY => sig 3 0
  | .Env .EXTCODEHASH => sig 1 1
  | .Block .BLOCKHASH => sig 1 1
  | .Block .COINBASE => sig 0 1
  | .Block .TIMESTAMP => sig 0 1
  | .Block .NUMBER => sig 0 1
  | .Block .PREVRANDAO => sig 0 1
  | .Block .GASLIMIT => sig 0 1
  | .Block .CHAINID => sig 0 1
  | .Block .SELFBALANCE => sig 0 1
  | .Block .BASEFEE => sig 0 1
  | .Block .BLOBHASH => sig 1 1
  | .Block .BLOBBASEFEE => sig 0 1
  | .StackMemFlow .POP => sig 1 0
  | .StackMemFlow .MLOAD => sig 1 1
  | .StackMemFlow .MSTORE => sig 2 0
  | .StackMemFlow .SLOAD => sig 1 1
  | .StackMemFlow .SSTORE => sig 2 0
  | .StackMemFlow .MSTORE8 => sig 2 0
  | .StackMemFlow .MSIZE => sig 0 1
  | .StackMemFlow .GAS => sig 0 1
  | .StackMemFlow .TLOAD => sig 1 1
  | .StackMemFlow .TSTORE => sig 2 0
  | .StackMemFlow .MCOPY => sig 3 0
  | .Log .LOG0 => sig 2 0
  | .Log .LOG1 => sig 3 0
  | .Log .LOG2 => sig 4 0
  | .Log .LOG3 => sig 5 0
  | .Log .LOG4 => sig 6 0
  | .System .CREATE => sig 3 1
  | .System .CALL => sig 7 1
  | .System .CALLCODE => sig 7 1
  | .System .RETURN => sig 2 0
  | .System .DELEGATECALL => sig 6 1
  | .System .CREATE2 => sig 4 1
  | .System .STATICCALL => sig 6 1
  | .System .REVERT => sig 2 0
  | .System .INVALID => sig 0 0
  | .System .SELFDESTRUCT => sig 1 0

def primitiveAvailable? (profile : DialectProfile)
    (op : EvmYul.Operation .Yul) : Bool :=
  match op with
  | .System .DELEGATECALL =>
      profile.evmVersion.atLeast? .homestead
  | .Env .RETURNDATASIZE
  | .Env .RETURNDATACOPY
  | .System .STATICCALL
  | .System .REVERT =>
      profile.evmVersion.atLeast? .byzantium
  | .CompBit .SHL
  | .CompBit .SHR
  | .CompBit .SAR
  | .Env .EXTCODEHASH
  | .System .CREATE2 =>
      profile.evmVersion.atLeast? .constantinople
  | .Block .CHAINID
  | .Block .SELFBALANCE =>
      profile.evmVersion.atLeast? .istanbul
  | .Block .BASEFEE =>
      profile.evmVersion.atLeast? .london
  -- The core AST erases solc's `difficulty()`/`prevrandao()` spelling split
  -- into the same operation.  Solidity.Frontend checks the spelling before
  -- lowering; direct core validation accepts the shared operation so it does
  -- not reject valid pre-Paris `difficulty()` programs.
  | .Block .PREVRANDAO =>
      true
  | .Block .BLOBHASH
  | .Block .BLOBBASEFEE
  | .StackMemFlow .TLOAD
  | .StackMemFlow .TSTORE
  | .StackMemFlow .MCOPY =>
      profile.evmVersion.atLeast? .cancun
  | _ => true

theorem primitiveAvailable_msize (profile : DialectProfile) :
    primitiveAvailable? profile (.StackMemFlow .MSIZE) = true := by
  rfl

theorem primitiveAvailable_gas (profile : DialectProfile) :
    primitiveAvailable? profile (.StackMemFlow .GAS) = true := by
  rfl

def hasDoubleDot? : List Char → Bool
  | [] => false
  | [_] => false
  | first :: second :: rest =>
      (first == '.' && second == '.') || hasDoubleDot? (second :: rest)

def identifierStart? (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$'

def identifierContinue? (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$' || c == '.'

def numberedNames (pref : String) (start count : Nat) : List Name :=
  (List.range count).map fun i => pref ++ toString (start + i)

def primitiveReservedNames : List Name :=
  [ "stop", "add", "mul", "sub", "div", "sdiv", "mod", "smod"
  , "addmod", "mulmod", "exp", "signextend", "lt", "gt", "slt", "sgt"
  , "eq", "iszero", "and", "or", "xor", "not", "byte", "shl", "shr"
  , "sar", "keccak256", "sha3", "address", "balance", "origin", "caller"
  , "callvalue", "calldataload", "calldatasize", "calldatacopy", "codesize"
  , "gasprice", "codecopy", "extcodesize", "extcodecopy", "returndatasize"
  , "returndatacopy", "extcodehash", "blockhash", "coinbase", "timestamp"
  , "number", "difficulty", "prevrandao", "gaslimit", "chainid"
  , "selfbalance", "basefee", "blobhash", "blobbasefee", "pop", "mload"
  , "mstore", "sload", "sstore", "mstore8", "msize", "gas", "tload"
  , "tstore", "mcopy", "log0", "log1", "log2", "log3", "log4", "create"
  , "call", "callcode", "return", "delegatecall", "create2", "staticcall"
  , "revert", "invalid", "selfdestruct", "jump", "jumpi", "jumpdest", "pc"
  , "clz", "dataloadn", "auxdataloadn", "eofcreate", "returncontract"
  , "rjump", "rjumpi", "callf", "retf", "jumpf" ] ++
    numberedNames "push" 0 33 ++ numberedNames "dup" 1 16 ++
    numberedNames "swap" 1 16

def objectReservedNames : List Name :=
  [ "linkersymbol", "datasize", "dataoffset", "datacopy", "setimmutable"
  , "loadimmutable", "memoryguard" ]

def reservedIdentifier? (name : Name) : Bool :=
  primitiveReservedNames.contains name ||
    objectReservedNames.contains name ||
      name.startsWith "verbatim"

def identifierSyntax? (name : Name) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      identifierStart? first &&
        (rest.all identifierContinue? &&
          (!name.endsWith "." && !hasDoubleDot? rest))

def bindingName? (name : Name) : Bool :=
  identifierSyntax? name && !reservedIdentifier? name

def bindingNames? (names : List Name) : Bool :=
  names.all bindingName?

def namesNodup? (names : List Name) : Bool :=
  decide names.Nodup

def namesFresh? (env names : List Name) : Bool :=
  names.all fun name => decide (name ∉ env)

def namesIn? (env names : List Name) : Bool :=
  names.all fun name => decide (name ∈ env)

def nonemptyNames? (names : List Name) : Bool :=
  match names with
  | [] => false
  | _ :: _ => true

def bindableList? (env names : List Name) : Bool :=
  nonemptyNames? names &&
    (bindingNames? names && (namesNodup? names && namesFresh? env names))

def assignableList? (vars names : List Name) : Bool :=
  nonemptyNames? names && (namesNodup? names && namesIn? vars names)

def caseValuesNodup? (cases : List (Word × List AstStmt)) : Bool :=
  decide ((cases.map Prod.fst).Nodup)

def lookupFunction? (contract : AstContract) (functionName : Name) :
    Option AstFunctionDefinition :=
  contract.functions.lookup functionName

def StmtOutVars (vars : List Name) : AstStmt → List Name
  | .Let names _value? => identNames names ++ vars
  | _ => vars

def StmtsOutVars : List Name → List AstStmt → List Name
  | vars, [] => vars
  | vars, head :: tail =>
      StmtsOutVars (StmtOutVars vars head) tail

mutual
  def ExprOk? (profile : DialectProfile) (contract : AstContract)
      (vars : List Name) :
      Nat → AstExpr → Bool
    | expected, .Lit _value => decide (expected = 1)
    | expected, .Var name =>
        decide (expected = 1) && decide (identName name ∈ vars)
    | expected, .Call (.inl prim) args =>
        let signature := primitiveSignature prim
        primitiveAvailable? profile prim &&
          (decide (expected = signature.outputs) &&
            (decide (args.length = signature.inputs) &&
              ExprsOk? profile contract vars args))
    | expected, .Call (.inr functionName) args =>
        match lookupFunction? contract functionName with
        | none => false
        | some (.Def params returns _body) =>
            decide (expected = returns.length) &&
              (decide (args.length = params.length) &&
                ExprsOk? profile contract vars args)

  def ExprsOk? (profile : DialectProfile) (contract : AstContract)
      (vars : List Name) :
      List AstExpr → Bool
    | [] => true
    | head :: tail =>
        ExprOk? profile contract vars 1 head &&
          ExprsOk? profile contract vars tail

  def StmtOk? (profile : DialectProfile) (contract : AstContract)
      (functionNames vars : List Name) (canBreak canContinue canLeave : Bool) :
      AstStmt → Bool
    | .Block body =>
        StmtsOk? profile contract functionNames vars canBreak canContinue
          canLeave body
    | .Let names none =>
        bindableList? (functionNames ++ vars) (identNames names)
    | .Let names (some value) =>
        bindableList? (functionNames ++ vars) (identNames names) &&
          ExprOk? profile contract vars (names.length) value
    | .Assign names value =>
        assignableList? vars (identNames names) &&
          ExprOk? profile contract vars (names.length) value
    | .ExprStmtCall value =>
        ExprOk? profile contract vars 0 value
    | .Switch scrutinee cases defaultBody =>
        ExprOk? profile contract vars 1 scrutinee &&
          (caseValuesNodup? cases &&
            (CasesOk? profile contract functionNames vars canBreak canContinue
              canLeave cases &&
              StmtsOk? profile contract functionNames vars canBreak canContinue
                canLeave defaultBody))
    | .For cond post body =>
        ExprOk? profile contract vars 1 cond &&
          (StmtsOk? profile contract functionNames vars false false canLeave
            post &&
            StmtsOk? profile contract functionNames vars true true canLeave
              body)
    | .If cond body =>
        ExprOk? profile contract vars 1 cond &&
          StmtsOk? profile contract functionNames vars canBreak canContinue
            canLeave body
    | .Break => canBreak
    | .Continue => canContinue
    | .Leave => canLeave

  def StmtsOk? (profile : DialectProfile) (contract : AstContract)
      (functionNames vars : List Name) (canBreak canContinue canLeave : Bool) :
      List AstStmt → Bool
    | [] => true
    | head :: tail =>
        StmtOk? profile contract functionNames vars canBreak canContinue
          canLeave head &&
          StmtsOk? profile contract functionNames (StmtOutVars vars head)
            canBreak canContinue canLeave tail

  def CasesOk? (profile : DialectProfile) (contract : AstContract)
      (functionNames vars : List Name) (canBreak canContinue canLeave : Bool) :
      List (Word × List AstStmt) → Bool
    | [] => true
    | (_value, body) :: rest =>
        StmtsOk? profile contract functionNames vars canBreak canContinue
          canLeave body &&
          CasesOk? profile contract functionNames vars canBreak canContinue
            canLeave rest
end

theorem stmtsOk_cons_parts
    {profile : DialectProfile} {contract : AstContract}
    {functionNames vars : List Name}
    {canBreak canContinue canLeave : Bool}
    {head : AstStmt} {tail : List AstStmt}
    (hOk :
      StmtsOk? profile contract functionNames vars
          canBreak canContinue canLeave (head :: tail) =
        true) :
    StmtOk? profile contract functionNames vars
          canBreak canContinue canLeave head =
        true ∧
      StmtsOk? profile contract functionNames
          (StmtOutVars vars head)
          canBreak canContinue canLeave tail =
        true := by
  simpa [StmtsOk?] using hOk

def FunctionOk? (profile : DialectProfile) (contract : AstContract)
    (functionNames : List Name) : AstFunctionDefinition → Bool
  | .Def params returns body =>
      let locals := identNames returns ++ identNames params
      bindingNames? locals &&
        (namesNodup? locals &&
          (namesFresh? functionNames locals &&
            StmtsOk? profile contract functionNames locals false false true
              body))

def FunctionEntriesOk? (profile : DialectProfile) (contract : AstContract)
    (functionNames : List Name) : List (Name × AstFunctionDefinition) → Bool
  | [] => true
  | (_name, fn) :: rest =>
      FunctionOk? profile contract functionNames fn &&
        FunctionEntriesOk? profile contract functionNames rest

def FunctionNamesOk? (functionNames : List Name) : Bool :=
  bindingNames? functionNames && namesNodup? functionNames

def ContractOkWithEntries? (profile : DialectProfile)
    (contract : AstContract)
    (entries : List (Name × AstFunctionDefinition)) : Bool :=
  let functionNames := entries.map Prod.fst
  FunctionNamesOk? functionNames &&
    (StmtOk? profile contract functionNames [] false false false
      contract.dispatcher &&
      FunctionEntriesOk? profile contract functionNames entries)

noncomputable def ContractOkWith? (profile : DialectProfile)
    (contract : AstContract) : Bool :=
  let entries := Contract.functionEntries contract
  ContractOkWithEntries? profile contract entries

noncomputable def ProgramOkWith? (profile : DialectProfile)
    (program : Program) : Bool :=
  ContractOkWith? profile program.contract

def ProgramOkWithEntries? (profile : DialectProfile)
    (program : Program)
    (entries : List (Name × AstFunctionDefinition)) : Bool :=
  ContractOkWithEntries? profile program.contract entries

noncomputable def ContractOk? (contract : AstContract) : Bool :=
  ContractOkWith? defaultDialectProfile contract

noncomputable def ProgramOk? (program : Program) : Bool :=
  ProgramOkWith? defaultDialectProfile program

noncomputable def ProgramOk (program : Program) : Prop :=
  ProgramOk? program = true

theorem exprOk_functionCall_lookup_exists
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} {expected : Nat}
    {functionName : Name} {args : List AstExpr}
    (hOk :
      ExprOk? profile contract vars expected
          (.Call (.inr functionName) args) =
        true) :
    ∃ params returns body,
      contract.functions.lookup functionName =
        some (.Def params returns body) := by
  unfold ExprOk? lookupFunction? at hOk
  cases hLookup : contract.functions.lookup functionName with
  | none =>
      simp [hLookup] at hOk
  | some fn =>
      cases fn with
      | Def params returns body =>
          exact ⟨params, returns, body, rfl⟩

theorem exprOk_var_mem
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} {expected : Nat}
    {name : EvmYul.Identifier}
    (hOk : ExprOk? profile contract vars expected (.Var name) = true) :
    identName name ∈ vars := by
  simp [ExprOk?] at hOk
  exact hOk.2

theorem exprOk_functionCall_parts
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} {expected : Nat}
    {functionName : Name} {args : List AstExpr}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hOk :
      ExprOk? profile contract vars expected
          (.Call (.inr functionName) args) =
        true)
    (hLookup :
      contract.functions.lookup functionName =
        some (.Def params returns body)) :
    expected = returns.length ∧ args.length = params.length := by
  simp [ExprOk?, lookupFunction?, hLookup] at hOk
  exact ⟨hOk.1, hOk.2.1⟩

theorem exprsOk_of_exprOk_primitive
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} {expected : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    (hOk :
      ExprOk? profile contract vars expected
          (.Call (.inl prim) args) =
        true) :
    ExprsOk? profile contract vars args = true := by
  simp [ExprOk?] at hOk
  exact hOk.2.2.2

theorem exprsOk_of_exprOk_functionCall
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} {expected : Nat}
    {functionName : Name} {args : List AstExpr}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hOk :
      ExprOk? profile contract vars expected
          (.Call (.inr functionName) args) =
        true)
    (hLookup :
      contract.functions.lookup functionName =
        some (.Def params returns body)) :
    ExprsOk? profile contract vars args = true := by
  simp [ExprOk?, lookupFunction?, hLookup] at hOk
  exact hOk.2.2

theorem exprOk_of_exprsOk_of_mem
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} :
    ∀ {args : List AstExpr} {expr : AstExpr},
      ExprsOk? profile contract vars args = true →
      expr ∈ args →
      ExprOk? profile contract vars 1 expr = true
  | [], expr, hOk, hMem => by
      simp at hMem
  | head :: tail, expr, hOk, hMem => by
      simp [ExprsOk?] at hOk
      simp at hMem
      rcases hMem with rfl | hTail
      · exact hOk.1
      · exact exprOk_of_exprsOk_of_mem hOk.2 hTail

theorem exprsOk_append
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} :
    ∀ (left right : List AstExpr),
      ExprsOk? profile contract vars (left ++ right) = true ↔
        ExprsOk? profile contract vars left = true ∧
          ExprsOk? profile contract vars right = true
  | [], right => by simp [ExprsOk?]
  | head :: tail, right => by
      simp [ExprsOk?, exprsOk_append tail right, and_assoc]

theorem exprsOk_reverse
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} :
    ∀ {args : List AstExpr},
      ExprsOk? profile contract vars args = true →
        ExprsOk? profile contract vars args.reverse = true
  | [], _ => by simp [ExprsOk?]
  | head :: tail, hOk => by
      have hParts :
          ExprOk? profile contract vars 1 head = true ∧
            ExprsOk? profile contract vars tail = true := by
        simpa [ExprsOk?] using hOk
      rw [List.reverse_cons, (exprsOk_append tail.reverse [head])]
      refine ⟨exprsOk_reverse hParts.2, ?_⟩
      simpa [ExprsOk?] using hParts.1

theorem returns_singleton_of_exprOk_functionCall
    {profile : DialectProfile} {contract : AstContract}
    {vars : List Name} {functionName : Name} {args : List AstExpr}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hOk :
      ExprOk? profile contract vars 1
          (.Call (.inr functionName) args) =
        true)
    (hLookup :
      contract.functions.lookup functionName =
        some (.Def params returns body)) :
    ∃ returnName, returns = [returnName] := by
  have hLength :=
    (exprOk_functionCall_parts hOk hLookup).1
  cases returns with
  | nil =>
      simp at hLength
  | cons returnName tail =>
      cases tail with
      | nil =>
          exact ⟨returnName, rfl⟩
      | cons next rest =>
          simp at hLength

theorem functionOk_signature_nodup
    {profile : DialectProfile} {contract : AstContract}
    {functionNames : List Name}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hOk :
      FunctionOk? profile contract functionNames
          (.Def params returns body) =
        true) :
    (identNames returns ++ identNames params).Nodup := by
  simp [FunctionOk?, namesNodup?] at hOk
  exact hOk.2.1

theorem functionEntriesOk_functionOk_of_mem
    {profile : DialectProfile} {contract : AstContract}
    {functionNames : List Name} :
    ∀ {entries : List (Name × AstFunctionDefinition)}
      {name : Name} {fn : AstFunctionDefinition},
      FunctionEntriesOk? profile contract functionNames entries = true →
      (name, fn) ∈ entries →
      FunctionOk? profile contract functionNames fn = true
  | [], name, fn, hOk, hMem => by
      simp at hMem
  | (entryName, entryFn) :: rest, name, fn, hOk, hMem => by
      simp [FunctionEntriesOk?] at hOk
      simp at hMem
      rcases hMem with hHead | hTail
      · rcases hHead with ⟨rfl, rfl⟩
        exact hOk.1
      · exact
          functionEntriesOk_functionOk_of_mem hOk.2 hTail

theorem contractOkWithEntries_dispatcherOk
    {profile : DialectProfile} {contract : AstContract}
    {entries : List (Name × AstFunctionDefinition)}
    (hContract : ContractOkWithEntries? profile contract entries = true) :
    StmtOk? profile contract (entries.map Prod.fst) [] false false false
      contract.dispatcher = true := by
  simp [ContractOkWithEntries?] at hContract
  exact hContract.2.1

theorem contractOkWithEntries_functionOk_of_mem
    {profile : DialectProfile} {contract : AstContract}
    {entries : List (Name × AstFunctionDefinition)}
    {name : Name} {fn : AstFunctionDefinition}
    (hContract : ContractOkWithEntries? profile contract entries = true)
    (hMem : (name, fn) ∈ entries) :
    FunctionOk? profile contract (entries.map Prod.fst) fn = true := by
  have hEntries :
      FunctionEntriesOk? profile contract (entries.map Prod.fst) entries =
        true := by
    simp [ContractOkWithEntries?] at hContract
    exact hContract.2.2
  exact functionEntriesOk_functionOk_of_mem hEntries hMem

theorem contractOkWithEntries_function_signature_nodup_of_mem
    {profile : DialectProfile} {contract : AstContract}
    {entries : List (Name × AstFunctionDefinition)}
    {name : Name} {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hContract : ContractOkWithEntries? profile contract entries = true)
    (hMem : (name, .Def params returns body) ∈ entries) :
    (identNames returns ++ identNames params).Nodup := by
  exact functionOk_signature_nodup
    (contractOkWithEntries_functionOk_of_mem hContract hMem)

theorem contractOkWithEntries_function_bodyOk_of_mem
    {profile : DialectProfile} {contract : AstContract}
    {entries : List (Name × AstFunctionDefinition)}
    {name : Name} {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hContract : ContractOkWithEntries? profile contract entries = true)
    (hMem : (name, .Def params returns body) ∈ entries) :
    StmtsOk? profile contract (entries.map Prod.fst)
        (identNames returns ++ identNames params) false false true body =
      true := by
  have hOk := contractOkWithEntries_functionOk_of_mem hContract hMem
  simp [FunctionOk?] at hOk
  exact hOk.2.2.2

theorem contractOkWithEntries_functionCall_partsN
    {profile : DialectProfile} {contract : AstContract}
    {entries : List (Name × AstFunctionDefinition)}
    {vars : List Name} {expected : Nat}
    {functionName : Name} {args : List AstExpr}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hContract : ContractOkWithEntries? profile contract entries = true)
    (hExpr : ExprOk? profile contract vars expected
      (.Call (.inr functionName) args) = true)
    (hLookup : contract.functions.lookup functionName =
      some (.Def params returns body))
    (hMem : (functionName, .Def params returns body) ∈ entries) :
    expected = returns.length ∧
      args.length = params.length ∧
      (identNames returns ++ identNames params).Nodup := by
  exact
    ⟨(exprOk_functionCall_parts hExpr hLookup).1,
      (exprOk_functionCall_parts hExpr hLookup).2,
      contractOkWithEntries_function_signature_nodup_of_mem hContract hMem⟩

theorem contractOkWithEntries_functionCall_parts
    {profile : DialectProfile} {contract : AstContract}
    {entries : List (Name × AstFunctionDefinition)}
    {vars : List Name} {functionName : Name} {args : List AstExpr}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hContract : ContractOkWithEntries? profile contract entries = true)
    (hExpr : ExprOk? profile contract vars 1
      (.Call (.inr functionName) args) = true)
    (hLookup : contract.functions.lookup functionName =
      some (.Def params returns body))
    (hMem : (functionName, .Def params returns body) ∈ entries) :
    args.length = params.length ∧
      (identNames returns ++ identNames params).Nodup ∧
      ∃ returnName, returns = [returnName] := by
  exact
    ⟨(contractOkWithEntries_functionCall_partsN
        hContract hExpr hLookup hMem).2.1,
      (contractOkWithEntries_functionCall_partsN
        hContract hExpr hLookup hMem).2.2,
      returns_singleton_of_exprOk_functionCall hExpr hLookup⟩

theorem programOkWith_function_signature_nodup
    {profile : DialectProfile} {program : Program}
    {functionName : Name}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hProgram : ProgramOkWith? profile program = true)
    (hLookup :
      program.contract.functions.lookup functionName =
        some (.Def params returns body)) :
    (identNames returns ++ identNames params).Nodup := by
  let entries := Contract.functionEntries program.contract
  let functionNames := entries.map Prod.fst
  have hContract :
      ContractOkWithEntries? profile program.contract entries = true := by
    simpa [ProgramOkWith?, ContractOkWith?, entries]
      using hProgram
  have hEntries :
      FunctionEntriesOk? profile program.contract functionNames entries =
        true := by
    simp [ContractOkWithEntries?, functionNames] at hContract
    exact hContract.2.2
  have hMem :
      (functionName, .Def params returns body) ∈ entries := by
    exact Contract.functionEntries_mem_of_lookup hLookup
  exact
    functionOk_signature_nodup
      (functionEntriesOk_functionOk_of_mem hEntries hMem)

theorem programOkWith_functionOk
    {profile : DialectProfile} {program : Program}
    {functionName : Name}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hProgram : ProgramOkWith? profile program = true)
    (hLookup :
      program.contract.functions.lookup functionName =
        some (.Def params returns body)) :
    FunctionOk? profile program.contract
        ((Contract.functionEntries program.contract).map Prod.fst)
        (.Def params returns body) =
      true := by
  let entries := Contract.functionEntries program.contract
  let functionNames := entries.map Prod.fst
  have hContract :
      ContractOkWithEntries? profile program.contract entries = true := by
    simpa [ProgramOkWith?, ContractOkWith?, entries]
      using hProgram
  have hEntries :
      FunctionEntriesOk? profile program.contract functionNames entries =
        true := by
    simp [ContractOkWithEntries?, functionNames] at hContract
    exact hContract.2.2
  have hMem :
      (functionName, .Def params returns body) ∈ entries :=
    Contract.functionEntries_mem_of_lookup hLookup
  simpa [entries, functionNames] using
    functionEntriesOk_functionOk_of_mem hEntries hMem

theorem programOkWith_function_bodyOk
    {profile : DialectProfile} {program : Program}
    {functionName : Name}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hProgram : ProgramOkWith? profile program = true)
    (hLookup :
      program.contract.functions.lookup functionName =
        some (.Def params returns body)) :
    StmtsOk? profile program.contract
        ((Contract.functionEntries program.contract).map Prod.fst)
        (identNames returns ++ identNames params) false false true body =
      true := by
  have hOk := programOkWith_functionOk hProgram hLookup
  simp [FunctionOk?] at hOk
  exact hOk.2.2.2

theorem programOkWith_functionCall_partsN
    {profile : DialectProfile} {program : Program}
    {vars : List Name} {expected : Nat}
    {functionName : Name} {args : List AstExpr}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hProgram : ProgramOkWith? profile program = true)
    (hExpr :
      ExprOk? profile program.contract vars expected
          (.Call (.inr functionName) args) =
        true)
    (hLookup :
      program.contract.functions.lookup functionName =
        some (.Def params returns body)) :
    expected = returns.length ∧
      args.length = params.length ∧
      (identNames returns ++ identNames params).Nodup := by
  exact
    ⟨(exprOk_functionCall_parts hExpr hLookup).1,
      (exprOk_functionCall_parts hExpr hLookup).2,
      programOkWith_function_signature_nodup hProgram hLookup⟩

theorem programOkWith_functionCall_parts
    {profile : DialectProfile} {program : Program}
    {vars : List Name} {functionName : Name} {args : List AstExpr}
    {params returns : List EvmYul.Identifier} {body : List AstStmt}
    (hProgram : ProgramOkWith? profile program = true)
    (hExpr :
      ExprOk? profile program.contract vars 1
          (.Call (.inr functionName) args) =
        true)
    (hLookup :
      program.contract.functions.lookup functionName =
        some (.Def params returns body)) :
    args.length = params.length ∧
      (identNames returns ++ identNames params).Nodup ∧
      ∃ returnName, returns = [returnName] := by
  exact
    ⟨(programOkWith_functionCall_partsN hProgram hExpr hLookup).2.1,
      (programOkWith_functionCall_partsN hProgram hExpr hLookup).2.2,
      returns_singleton_of_exprOk_functionCall hExpr hLookup⟩

end SolcValidation
end Yul
end EvmCompiler
