import EvmCompiler.Structured.Syntax

namespace EvmCompiler
namespace Expressions

abbrev Word := Structured.Word
abbrev EVMState := Structured.EVMState
abbrev EVMException := Structured.EVMException
abbrev Name := Structured.Name

namespace Structured.BasicOp

def inputs : Structured.BasicOp → Nat
  | .add | .mul | .sub | .div | .sdiv | .mod | .smod | .exp | .signextend => 2
  | .lt | .gt | .slt | .sgt | .eq => 2
  | .and | .or | .xor | .byte | .shl | .shr | .sar => 2
  | .addmod | .mulmod => 3
  | .iszero | .not | .clz => 1
  | .address | .origin | .caller | .callvalue | .calldatasize | .codesize => 0
  | .gasprice | .returndatasize => 0
  | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid => 0
  | .selfbalance | .basefee | .blobbasefee => 0
  | .balance | .calldataload | .extcodesize | .extcodehash | .blockhash => 1
  | .blobhash => 1
  | .calldatacopy | .codecopy | .returndatacopy | .mcopy => 3
  | .extcodecopy => 4
  | .pop | .mload | .sload | .tload => 1
  | .mstore | .sstore | .mstore8 | .tstore | .keccak256 => 2
  | .msize | .gas => 0
  | .dup1 => 1
  | .dup2 => 2
  | .dup3 => 3
  | .dup4 => 4
  | .dup5 => 5
  | .dup6 => 6
  | .dup7 => 7
  | .dup8 => 8
  | .dup9 => 9
  | .dup10 => 10
  | .dup11 => 11
  | .dup12 => 12
  | .dup13 => 13
  | .dup14 => 14
  | .dup15 => 15
  | .dup16 => 16
  | .swap1 => 2
  | .swap2 => 3
  | .swap3 => 4
  | .swap4 => 5
  | .swap5 => 6
  | .swap6 => 7
  | .swap7 => 8
  | .swap8 => 9
  | .swap9 => 10
  | .swap10 => 11
  | .swap11 => 12
  | .swap12 => 13
  | .swap13 => 14
  | .swap14 => 15
  | .swap15 => 16
  | .swap16 => 17
  | .log0 => 2
  | .log1 => 3
  | .log2 => 4
  | .log3 => 5
  | .log4 => 6
  | .create => 3
  | .call | .callcode => 7
  | .delegatecall | .staticcall => 6
  | .create2 => 4
  | .invalid => 0

def outputs : Structured.BasicOp → Nat
  | .add | .mul | .sub | .div | .sdiv | .mod | .smod | .exp | .signextend => 1
  | .lt | .gt | .slt | .sgt | .eq => 1
  | .and | .or | .xor | .not | .byte | .shl | .shr | .sar => 1
  | .addmod | .mulmod => 1
  | .iszero | .clz => 1
  | .address | .origin | .caller | .callvalue | .calldatasize | .codesize => 1
  | .gasprice | .returndatasize => 1
  | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid => 1
  | .selfbalance | .basefee | .blobbasefee => 1
  | .balance | .calldataload | .extcodesize | .extcodehash | .blockhash => 1
  | .blobhash => 1
  | .calldatacopy | .codecopy | .returndatacopy | .extcodecopy | .mcopy => 0
  | .pop => 0
  | .mload | .sload | .tload => 1
  | .mstore | .sstore | .mstore8 | .tstore => 0
  | .keccak256 => 1
  | .msize | .gas => 1
  | .dup1 => 2
  | .dup2 => 3
  | .dup3 => 4
  | .dup4 => 5
  | .dup5 => 6
  | .dup6 => 7
  | .dup7 => 8
  | .dup8 => 9
  | .dup9 => 10
  | .dup10 => 11
  | .dup11 => 12
  | .dup12 => 13
  | .dup13 => 14
  | .dup14 => 15
  | .dup15 => 16
  | .dup16 => 17
  | .swap1 => 2
  | .swap2 => 3
  | .swap3 => 4
  | .swap4 => 5
  | .swap5 => 6
  | .swap6 => 7
  | .swap7 => 8
  | .swap8 => 9
  | .swap9 => 10
  | .swap10 => 11
  | .swap11 => 12
  | .swap12 => 13
  | .swap13 => 14
  | .swap14 => 15
  | .swap15 => 16
  | .swap16 => 17
  | .log0 | .log1 | .log2 | .log3 | .log4 => 0
  | .create | .call | .callcode | .delegatecall | .create2 | .staticcall => 1
  | .invalid => 0

end Structured.BasicOp

mutual
  inductive Expr : Nat → Type where
    | lit (value : Word) : Expr 1
    | code {results : Nat} (code : Structured.Code) : Expr results
    | prim (op : Structured.BasicOp)
        (args : ExprSeq (Structured.BasicOp.inputs op)) :
        Expr (Structured.BasicOp.outputs op)

  inductive ExprSeq : Nat → Type where
    | nil : ExprSeq 0
    | cons {left right : Nat} (head : Expr left)
        (tail : ExprSeq right) : ExprSeq (left + right)
end

mutual
  structure Block where
    stmts : List Stmt

  inductive Stmt where
    | code (code : Structured.Code)
    | expr {results : Nat} (expr : Expr results)
    | if_ (cond : Expr 1) (body : Block)
    | switch (scrutinee : Expr 1) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Expr 1) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | call (name : Name)
    | terminal (kind : Assembly.HaltKind)
end

structure Proc where
  name : Name
  argc : Nat
  retc : Nat
  body : Block

structure Program where
  procs : List Proc := []
  body : Block

mutual
  inductive Block.WF : Bool → Bool → Bool → Block → Prop where
    | nil {canBreak canContinue canLeave : Bool} :
        Block.WF canBreak canContinue canLeave { stmts := [] }
    | cons {canBreak canContinue canLeave : Bool} {stmt : Stmt}
        {rest : List Stmt}
        (hStmt : Stmt.WF canBreak canContinue canLeave stmt)
        (hRest : Block.WF canBreak canContinue canLeave { stmts := rest }) :
        Block.WF canBreak canContinue canLeave { stmts := stmt :: rest }

  inductive Stmt.WF : Bool → Bool → Bool → Stmt → Prop where
    | code {canBreak canContinue canLeave : Bool} {code : Structured.Code} :
        Stmt.WF canBreak canContinue canLeave (.code code)
    | expr {canBreak canContinue canLeave : Bool} {results : Nat}
        {expr : Expr results} :
        Stmt.WF canBreak canContinue canLeave (.expr expr)
    | if_ {canBreak canContinue canLeave : Bool} {cond : Expr 1} {body : Block}
        (hBody : Block.WF canBreak canContinue canLeave body) :
        Stmt.WF canBreak canContinue canLeave (.if_ cond body)
    | switch {canBreak canContinue canLeave : Bool} {scrutinee : Expr 1}
        {cases : List (Word × Block)}
        {defaultBody : Option Block}
        (hCases :
          ∀ value body, (value, body) ∈ cases →
            Block.WF canBreak canContinue canLeave body)
        (hDefault :
          ∀ body, defaultBody = some body →
            Block.WF canBreak canContinue canLeave body) :
        Stmt.WF canBreak canContinue canLeave
          (.switch scrutinee cases defaultBody)
    | for_ {canBreak canContinue canLeave : Bool} {init post body : Block}
        {cond : Expr 1}
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

def names (procs : List Proc) : List Name :=
  procs.map Proc.name

def NamesUnique (procs : List Proc) : Prop :=
  names procs |>.Nodup

def contains (procs : List Proc) (name : Name) : Prop :=
  ∃ proc, proc ∈ procs ∧ proc.name = name

def WF : List Proc → Prop
  | [] => True
  | proc :: rest => proc.WF ∧ WF rest

mutual
  inductive BlockCallsResolved (procs : List Proc) : Block → Prop where
    | mk {stmts : List Stmt}
        (hStmts : StmtListCallsResolved procs stmts) :
        BlockCallsResolved procs { stmts := stmts }

  inductive StmtCallsResolved (procs : List Proc) : Stmt → Prop where
    | code {code : Structured.Code} :
        StmtCallsResolved procs (.code code)
    | expr {results : Nat} {expr : Expr results} :
        StmtCallsResolved procs (.expr expr)
    | if_ {cond : Expr 1} {body : Block}
        (hBody : BlockCallsResolved procs body) :
        StmtCallsResolved procs (.if_ cond body)
    | switch {scrutinee : Expr 1} {cases : List (Word × Block)}
        {defaultBody : Option Block}
        (hCases :
          ∀ value body, (value, body) ∈ cases →
            BlockCallsResolved procs body)
        (hDefault :
          ∀ body, defaultBody = some body →
            BlockCallsResolved procs body) :
        StmtCallsResolved procs (.switch scrutinee cases defaultBody)
    | for_ {init post body : Block} {cond : Expr 1}
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
  ∀ proc, proc ∈ procs → BlockCallsResolved procs proc.body

end ProcList

namespace Program

def WF (program : Program) : Prop :=
  ProcList.NamesUnique program.procs ∧
    ProcList.WF program.procs ∧
    ProcList.CallsResolved program.procs ∧
    ProcList.BlockCallsResolved program.procs program.body ∧
    Block.WF false false false program.body

end Program

end Expressions
end EvmCompiler
