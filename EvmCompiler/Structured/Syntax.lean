import EvmCompiler.Assembly.Syntax
import EvmYul.Semantics
import EvmYul.EVM.State

namespace EvmCompiler
namespace Structured

abbrev Word := Assembly.Word
abbrev EVMState := EvmYul.EVM.State
abbrev EVMException := EvmYul.EVM.ExecutionException
abbrev Name := String

structure ReturnDest where
  callerStack : EvmYul.Stack Word
  retc : Nat
  deriving DecidableEq, Repr

structure RunState where
  evm : EVMState
  returns : List ReturnDest

namespace RunState

def initial (state : EVMState) : RunState where
  evm := state
  returns := []

def withEVM (state : RunState) (evm : EVMState) : RunState :=
  { state with evm := evm }

def pushReturn (state : RunState) (callerStack : EvmYul.Stack Word)
    (retc : Nat) : RunState :=
  { state with
    returns :=
      { callerStack := callerStack, retc := retc } :: state.returns }

def popReturn? (state : RunState) : Option (ReturnDest × RunState) :=
  match state.returns with
  | [] => none
  | frame :: rest => some (frame, { state with returns := rest })

def inProcedure (state : RunState) : Prop :=
  state.returns ≠ []

@[simp] theorem initial_evm (state : EVMState) :
    (initial state).evm = state := rfl

@[simp] theorem initial_returns (state : EVMState) :
    (initial state).returns = [] := rfl

@[simp] theorem withEVM_evm (state : RunState) (evm : EVMState) :
    (withEVM state evm).evm = evm := rfl

@[simp] theorem withEVM_returns (state : RunState) (evm : EVMState) :
    (withEVM state evm).returns = state.returns := rfl

@[simp] theorem pushReturn_returns (state : RunState)
    (callerStack : EvmYul.Stack Word) (retc : Nat) :
    (pushReturn state callerStack retc).returns =
      { callerStack := callerStack, retc := retc } :: state.returns := rfl

end RunState

inductive Mode where
  | regular
  | brk
  | cont
  | leave
  | halt (kind : Assembly.HaltKind)
  deriving DecidableEq

structure Outcome where
  state : RunState
  mode : Mode

namespace Outcome

def regular (state : RunState) : Outcome where
  state := state
  mode := .regular

def brk (state : RunState) : Outcome where
  state := state
  mode := .brk

def cont (state : RunState) : Outcome where
  state := state
  mode := .cont

def leave (state : RunState) : Outcome where
  state := state
  mode := .leave

def halt (kind : Assembly.HaltKind) (state : RunState) : Outcome where
  state := state
  mode := .halt kind

@[simp] theorem regular_state (state : RunState) :
    (regular state).state = state := rfl

@[simp] theorem regular_mode (state : RunState) :
    (regular state).mode = .regular := rfl

@[simp] theorem brk_state (state : RunState) :
    (brk state).state = state := rfl

@[simp] theorem brk_mode (state : RunState) :
    (brk state).mode = .brk := rfl

@[simp] theorem cont_state (state : RunState) :
    (cont state).state = state := rfl

@[simp] theorem cont_mode (state : RunState) :
    (cont state).mode = .cont := rfl

@[simp] theorem leave_state (state : RunState) :
    (leave state).state = state := rfl

@[simp] theorem leave_mode (state : RunState) :
    (leave state).mode = .leave := rfl

@[simp] theorem halt_state (kind : Assembly.HaltKind) (state : RunState) :
    (halt kind state).state = state := rfl

@[simp] theorem halt_mode (kind : Assembly.HaltKind) (state : RunState) :
    (halt kind state).mode = .halt kind := rfl

end Outcome

/--
Primitive operations admitted as ordinary structured-control statements.

This layer is still EVM-state-shaped. Primitive operations reuse the same
shared EVM semantics as labeled assembly; the only control abstraction added by
this module is structured/procedure control over those primitive effects.
-/
inductive BasicOp where
  | add | mul | sub | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar
  | address | balance | origin | caller | callvalue | calldataload | calldatasize
  | calldatacopy | codesize | codecopy | gasprice | extcodesize | extcodecopy
  | returndatasize | returndatacopy | extcodehash
  | blockhash | coinbase | timestamp | number | prevrandao | gaslimit | chainid
  | selfbalance | basefee | blobhash | blobbasefee
  | pop | mload | mstore | sload | sstore | mstore8 | msize
  | tload | tstore
  | mcopy
  | keccak256
  | dup1 | dup2 | dup3 | dup4 | dup5 | dup6 | dup7 | dup8
  | dup9 | dup10 | dup11 | dup12 | dup13 | dup14 | dup15 | dup16
  | swap1 | swap2 | swap3 | swap4 | swap5 | swap6 | swap7 | swap8
  | swap9 | swap10 | swap11 | swap12 | swap13 | swap14 | swap15 | swap16
  | log0 | log1 | log2 | log3 | log4
  | create | call | callcode | delegatecall | create2 | staticcall
  | invalid
  | gas
  deriving DecidableEq, Repr

namespace BasicOp

def toPrimOp : BasicOp → Assembly.PrimOp
  | .add => .add
  | .mul => .mul
  | .sub => .sub
  | .div => .div
  | .sdiv => .sdiv
  | .mod => .mod
  | .smod => .smod
  | .addmod => .addmod
  | .mulmod => .mulmod
  | .exp => .exp
  | .signextend => .signextend
  | .lt => .lt
  | .gt => .gt
  | .slt => .slt
  | .sgt => .sgt
  | .eq => .eq
  | .iszero => .iszero
  | .and => .and
  | .or => .or
  | .xor => .xor
  | .not => .not
  | .byte => .byte
  | .shl => .shl
  | .shr => .shr
  | .sar => .sar
  | .address => .address
  | .balance => .balance
  | .origin => .origin
  | .caller => .caller
  | .callvalue => .callvalue
  | .calldataload => .calldataload
  | .calldatasize => .calldatasize
  | .calldatacopy => .calldatacopy
  | .codesize => .codesize
  | .codecopy => .codecopy
  | .gasprice => .gasprice
  | .extcodesize => .extcodesize
  | .extcodecopy => .extcodecopy
  | .returndatasize => .returndatasize
  | .returndatacopy => .returndatacopy
  | .extcodehash => .extcodehash
  | .blockhash => .blockhash
  | .coinbase => .coinbase
  | .timestamp => .timestamp
  | .number => .number
  | .prevrandao => .prevrandao
  | .gaslimit => .gaslimit
  | .chainid => .chainid
  | .selfbalance => .selfbalance
  | .basefee => .basefee
  | .blobhash => .blobhash
  | .blobbasefee => .blobbasefee
  | .pop => .pop
  | .mload => .mload
  | .mstore => .mstore
  | .sload => .sload
  | .sstore => .sstore
  | .mstore8 => .mstore8
  | .msize => .msize
  | .gas => .gas
  | .tload => .tload
  | .tstore => .tstore
  | .mcopy => .mcopy
  | .keccak256 => .keccak256
  | .dup1 => .dup1
  | .dup2 => .dup2
  | .dup3 => .dup3
  | .dup4 => .dup4
  | .dup5 => .dup5
  | .dup6 => .dup6
  | .dup7 => .dup7
  | .dup8 => .dup8
  | .dup9 => .dup9
  | .dup10 => .dup10
  | .dup11 => .dup11
  | .dup12 => .dup12
  | .dup13 => .dup13
  | .dup14 => .dup14
  | .dup15 => .dup15
  | .dup16 => .dup16
  | .swap1 => .swap1
  | .swap2 => .swap2
  | .swap3 => .swap3
  | .swap4 => .swap4
  | .swap5 => .swap5
  | .swap6 => .swap6
  | .swap7 => .swap7
  | .swap8 => .swap8
  | .swap9 => .swap9
  | .swap10 => .swap10
  | .swap11 => .swap11
  | .swap12 => .swap12
  | .swap13 => .swap13
  | .swap14 => .swap14
  | .swap15 => .swap15
  | .swap16 => .swap16
  | .log0 => .log0
  | .log1 => .log1
  | .log2 => .log2
  | .log3 => .log3
  | .log4 => .log4
  | .create => .create
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .create2 => .create2
  | .staticcall => .staticcall
  | .invalid => .invalid

end BasicOp

inductive BasicInstr where
  | push (value : Word)
  | op (op : BasicOp)
  deriving DecidableEq, Repr

abbrev Code := List BasicInstr

namespace BasicInstr

def usesCallCreate : BasicInstr → Bool
  | .push _ => false
  | BasicInstr.op basicOp => basicOp.toPrimOp.isCallCreate

end BasicInstr

namespace Code

def usesCallCreate (code : Code) : Bool :=
  code.any BasicInstr.usesCallCreate

end Code

mutual
  structure Block where
    stmts : List Stmt

  inductive Stmt where
    | code (code : Code)
    | if_ (cond : Code) (body : Block)
    | switch (scrutinee : Code) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Code) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | call (name : Name)
    | terminal (kind : Assembly.HaltKind)
end

mutual
  def Block.usesCallCreate : Block → Bool
    | ⟨stmts⟩ => StmtList.usesCallCreate stmts

  def Stmt.usesCallCreate : Stmt → Bool
    | .code code => code.usesCallCreate
    | .if_ cond body => cond.usesCallCreate || body.usesCallCreate
    | .switch scrutinee cases defaultBody =>
        scrutinee.usesCallCreate || CaseList.usesCallCreate cases ||
          Default.usesCallCreate defaultBody
    | .for_ init cond post body =>
        init.usesCallCreate || cond.usesCallCreate || post.usesCallCreate ||
          body.usesCallCreate
    | .brk | .cont | .leave | .call _ | .terminal _ => false

  def StmtList.usesCallCreate : List Stmt → Bool
    | [] => false
    | stmt :: rest => stmt.usesCallCreate || StmtList.usesCallCreate rest

  def CaseList.usesCallCreate : List (Word × Block) → Bool
    | [] => false
    | (_value, body) :: rest =>
        body.usesCallCreate || CaseList.usesCallCreate rest

  def Default.usesCallCreate : Option Block → Bool
    | none => false
    | some body => body.usesCallCreate
end

structure Proc where
  name : Name
  argc : Nat
  retc : Nat
  body : Block

namespace Proc

def usesCallCreate (proc : Proc) : Bool :=
  proc.body.usesCallCreate

end Proc

structure Program where
  procs : List Proc
  body : Block

namespace ProcList

def usesCallCreate : List Proc → Bool
  | [] => false
  | proc :: rest => proc.usesCallCreate || usesCallCreate rest

end ProcList

namespace ProcList

def lookup? (name : Name) : List Proc → Option Proc
  | [] => none
  | proc :: rest =>
      if proc.name = name then
        some proc
      else
        lookup? name rest

def contains (procs : List Proc) (name : Name) : Prop :=
  ∃ proc, proc ∈ procs ∧ proc.name = name

def NamesUnique (procs : List Proc) : Prop :=
  (procs.map Proc.name).Nodup

theorem lookup?_isSome_of_contains {procs : List Proc} {name : Name}
    (hContains : contains procs name) :
    (lookup? name procs).isSome = true := by
  rcases hContains with ⟨found, hMem, hName⟩
  induction procs with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp at hMem
      unfold lookup?
      by_cases hEq : head.name = name
      · simp [hEq]
      · simp [hEq]
        cases hMem with
        | inl hHead =>
            cases hHead
            exact (hEq hName).elim
        | inr hRest =>
            exact ih hRest

theorem exists_lookup?_of_contains {procs : List Proc} {name : Name}
    (hContains : contains procs name) :
    ∃ proc, lookup? name procs = some proc := by
  have hSome := lookup?_isSome_of_contains hContains
  cases hLookup : lookup? name procs with
  | none =>
      simp [hLookup] at hSome
  | some proc =>
      exact ⟨proc, rfl⟩

theorem name_of_lookup? {procs : List Proc} {name : Name} {proc : Proc}
    (hLookup : lookup? name procs = some proc) :
    proc.name = name := by
  induction procs with
  | nil =>
      simp [lookup?] at hLookup
  | cons head rest ih =>
      unfold lookup? at hLookup
      by_cases hEq : head.name = name
      · simp [hEq] at hLookup
        cases hLookup
        exact hEq
      · simp [hEq] at hLookup
        exact ih hLookup

theorem mem_of_lookup? {procs : List Proc} {name : Name} {proc : Proc}
    (hLookup : lookup? name procs = some proc) :
    proc ∈ procs := by
  induction procs with
  | nil =>
      simp [lookup?] at hLookup
  | cons head rest ih =>
      unfold lookup? at hLookup
      by_cases hEq : head.name = name
      · simp [hEq] at hLookup
        cases hLookup
        simp
      · simp [hEq] at hLookup
        exact List.mem_cons_of_mem head (ih hLookup)

end ProcList

mutual
  inductive Block.WF : Bool → Bool → Bool → Block → Prop where
    | nil {canBreak canContinue canLeave : Bool} :
        Block.WF canBreak canContinue canLeave { stmts := [] }
    | cons {canBreak canContinue canLeave : Bool} {stmt : Stmt} {rest : List Stmt}
        (hStmt : Stmt.WF canBreak canContinue canLeave stmt)
        (hRest : Block.WF canBreak canContinue canLeave { stmts := rest }) :
        Block.WF canBreak canContinue canLeave { stmts := stmt :: rest }

  inductive Stmt.WF : Bool → Bool → Bool → Stmt → Prop where
    | code {canBreak canContinue canLeave : Bool} {code : Code} :
        Stmt.WF canBreak canContinue canLeave (.code code)
    | if_ {canBreak canContinue canLeave : Bool} {cond : Code} {body : Block}
        (hBody : Block.WF canBreak canContinue canLeave body) :
        Stmt.WF canBreak canContinue canLeave (.if_ cond body)
    | switch {canBreak canContinue canLeave : Bool} {scrutinee : Code}
        {cases : List (Word × Block)}
        {defaultBody : Option Block}
        (hCases :
          ∀ value body, (value, body) ∈ cases →
            Block.WF canBreak canContinue canLeave body)
        (hDefault :
          ∀ body, defaultBody = some body →
            Block.WF canBreak canContinue canLeave body) :
        Stmt.WF canBreak canContinue canLeave (.switch scrutinee cases defaultBody)
    | for_ {canBreak canContinue canLeave : Bool} {init post body : Block}
        {cond : Code}
        (hInit : Block.WF false false canLeave init)
        (hPost : Block.WF false false canLeave post)
        (hBody : Block.WF true true canLeave body) :
        Stmt.WF canBreak canContinue canLeave (.for_ init cond post body)
    | brk {canBreak canContinue canLeave : Bool} (hAllowed : canBreak = true) :
        Stmt.WF canBreak canContinue canLeave .brk
    | cont {canBreak canContinue canLeave : Bool}
        (hAllowed : canContinue = true) :
        Stmt.WF canBreak canContinue canLeave .cont
    | leave {canBreak canContinue canLeave : Bool}
        (hAllowed : canLeave = true) :
        Stmt.WF canBreak canContinue canLeave .leave
    | call {canBreak canContinue canLeave : Bool} {name : Name} :
        Stmt.WF canBreak canContinue canLeave (.call name)
    | terminal {canBreak canContinue canLeave : Bool}
        {kind : Assembly.HaltKind} :
        Stmt.WF canBreak canContinue canLeave (.terminal kind)
end

namespace Proc

def WF (proc : Proc) : Prop :=
  proc.argc ≤ 16 ∧ proc.retc < 16 ∧
    Block.WF false false true proc.body

end Proc

namespace ProcList

def WF : List Proc → Prop
  | [] => True
  | proc :: rest => proc.WF ∧ WF rest

theorem WF_of_lookup? {procs : List Proc} {name : Name} {proc : Proc}
    (hWF : WF procs) (hLookup : lookup? name procs = some proc) :
    proc.WF := by
  induction procs with
  | nil =>
      simp [lookup?] at hLookup
  | cons head rest ih =>
      simp [lookup?] at hLookup
      by_cases hName : head.name = name
      · simp [hName] at hLookup
        cases hLookup
        exact hWF.1
      · simp [hName] at hLookup
        exact ih hWF.2 hLookup

mutual
  inductive BlockCallsResolved (procs : List Proc) : Block → Prop where
    | mk {stmts : List Stmt}
        (hStmts : StmtListCallsResolved procs stmts) :
        BlockCallsResolved procs { stmts := stmts }

  inductive StmtCallsResolved (procs : List Proc) : Stmt → Prop where
    | code {code : Code} :
        StmtCallsResolved procs (.code code)
    | if_ {cond : Code} {body : Block}
        (hBody : BlockCallsResolved procs body) :
        StmtCallsResolved procs (.if_ cond body)
    | switch {scrutinee : Code} {cases : List (Word × Block)}
        {defaultBody : Option Block}
        (hCases :
          ∀ value body, (value, body) ∈ cases →
            BlockCallsResolved procs body)
        (hDefault :
          ∀ body, defaultBody = some body →
            BlockCallsResolved procs body) :
        StmtCallsResolved procs (.switch scrutinee cases defaultBody)
    | for_ {init post body : Block} {cond : Code}
        (hInit : BlockCallsResolved procs init)
        (hPost : BlockCallsResolved procs post)
        (hBody : BlockCallsResolved procs body) :
        StmtCallsResolved procs (.for_ init cond post body)
    | brk : StmtCallsResolved procs .brk
    | cont : StmtCallsResolved procs .cont
    | leave : StmtCallsResolved procs .leave
    | call {name : Name} (hContains : contains procs name) :
        StmtCallsResolved procs (.call name)
    | terminal {kind : Assembly.HaltKind} :
        StmtCallsResolved procs (.terminal kind)

  inductive StmtListCallsResolved (procs : List Proc) :
      List Stmt → Prop where
    | nil : StmtListCallsResolved procs []
    | cons {stmt : Stmt} {rest : List Stmt}
        (hStmt : StmtCallsResolved procs stmt)
        (hRest : StmtListCallsResolved procs rest) :
        StmtListCallsResolved procs (stmt :: rest)
end

def CallsResolved (procs : List Proc) : Prop :=
  (∀ proc, proc ∈ procs → BlockCallsResolved procs proc.body)

end ProcList

namespace Program

def usesCallCreate (program : Program) : Bool :=
  ProcList.usesCallCreate program.procs || program.body.usesCallCreate

def WF (program : Program) : Prop :=
  ProcList.NamesUnique program.procs ∧
    ProcList.WF program.procs ∧
    ProcList.CallsResolved program.procs ∧
    ProcList.BlockCallsResolved program.procs program.body ∧
    Block.WF false false false program.body

theorem procWF_of_lookup? {program : Program} {name : Name} {proc : Proc}
    (hWF : program.WF)
    (hLookup : ProcList.lookup? name program.procs = some proc) :
    proc.WF :=
  ProcList.WF_of_lookup? hWF.2.1 hLookup

theorem procCallsResolved_of_lookup?
    {program : Program} {name : Name} {proc : Proc}
    (hWF : program.WF)
    (hLookup : ProcList.lookup? name program.procs = some proc) :
    ProcList.BlockCallsResolved program.procs proc.body :=
  hWF.2.2.1 proc (ProcList.mem_of_lookup? hLookup)

end Program

namespace BasicInstr

def toAssembly : BasicInstr → Assembly.Instr
  | .push value => .push value
  | .op basicOp => .prim basicOp.toPrimOp

theorem toAssembly_usesCallCreate (instr : BasicInstr) :
    instr.toAssembly.usesCallCreate = instr.usesCallCreate := by
  cases instr <;> simp [toAssembly, usesCallCreate,
    Assembly.Instr.usesCallCreate]

end BasicInstr

namespace Code

def toAssembly (code : Code) : Assembly.Program :=
  code.map BasicInstr.toAssembly

theorem toAssembly_usesCallCreate (code : Code) :
    Assembly.Program.usesCallCreate code.toAssembly = usesCallCreate code := by
  induction code with
  | nil =>
      rfl
  | cons instr rest ih =>
      simpa [toAssembly, usesCallCreate, Assembly.Program.usesCallCreate,
        BasicInstr.toAssembly_usesCallCreate, Function.comp] using
        congrArg (fun value => instr.usesCallCreate || value) ih

end Code

end Structured
end EvmCompiler
