import EvmCompiler.Expressions.Syntax

namespace EvmCompiler
namespace Locals

abbrev Word := Expressions.Word
abbrev EVMState := Expressions.EVMState
abbrev EVMException := Expressions.EVMException
abbrev Name := Expressions.Name

abbrev Layout := List Name

mutual
  inductive Expr : Nat → Type where
    | lit (value : Word) : Expr 1
    | var (name : Name) : Expr 1
    | code {results : Nat} (code : Structured.Code) : Expr results
    | prim (op : Structured.BasicOp)
        (args : ExprSeq (Expressions.Structured.BasicOp.inputs op)) :
        Expr (Expressions.Structured.BasicOp.outputs op)

  inductive ExprSeq : Nat → Type where
    | nil : ExprSeq 0
    | cons {left right : Nat} (head : Expr left)
        (tail : ExprSeq right) : ExprSeq (left + right)
end

mutual
  structure Block where
    stmts : List Stmt

  inductive Stmt where
    | expr {results : Nat} (expr : Expr results)
    | exprs {results : Nat} (exprs : ExprSeq results)
    | let_ (name : Name) (value : Expr 1)
    | assign (name : Name) (value : Expr 1)
    | assignTop (name : Name)
    | assignTopWithOffset (offset : Nat) (name : Name)
    | promoteName (name : Name)
    | discardName (name : Name)
    | cleanupTo (targetLayout : Layout)
    | block (body : Block)
    | if_ (cond : Expr 1) (body : Block)
    | switch (scrutinee : Expr 1) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Expr 1) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | call (name : Name)
    | terminal (kind : Assembly.HaltKind)
    | terminalArgs (kind : Assembly.HaltKind)
        (args : ExprSeq kind.argCount)
end

structure Proc where
  name : Name
  argc : Nat
  retc : Nat
  entryLayout : Layout := []
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
    | expr {canBreak canContinue canLeave : Bool} {results : Nat}
        {expr : Expr results} :
        Stmt.WF canBreak canContinue canLeave (.expr expr)
    | exprs {canBreak canContinue canLeave : Bool} {results : Nat}
        {exprs : ExprSeq results} :
        Stmt.WF canBreak canContinue canLeave (.exprs exprs)
    | let_ {canBreak canContinue canLeave : Bool}
        {name : Name} {value : Expr 1} :
        Stmt.WF canBreak canContinue canLeave (.let_ name value)
    | assign {canBreak canContinue canLeave : Bool}
        {name : Name} {value : Expr 1} :
        Stmt.WF canBreak canContinue canLeave (.assign name value)
    | assignTop {canBreak canContinue canLeave : Bool} {name : Name} :
        Stmt.WF canBreak canContinue canLeave (.assignTop name)
    | assignTopWithOffset {canBreak canContinue canLeave : Bool}
        {offset : Nat} {name : Name} :
        Stmt.WF canBreak canContinue canLeave
          (.assignTopWithOffset offset name)
    | promoteName {canBreak canContinue canLeave : Bool} {name : Name} :
        Stmt.WF canBreak canContinue canLeave (.promoteName name)
    | discardName {canBreak canContinue canLeave : Bool} {name : Name} :
        Stmt.WF canBreak canContinue canLeave (.discardName name)
    | cleanupTo {canBreak canContinue canLeave : Bool}
        {targetLayout : Layout} :
        Stmt.WF canBreak canContinue canLeave (.cleanupTo targetLayout)
    | block {canBreak canContinue canLeave : Bool} {body : Block}
        (hBody : Block.WF canBreak canContinue canLeave body) :
        Stmt.WF canBreak canContinue canLeave (.block body)
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
    | terminal {canBreak canContinue canLeave : Bool} {kind : Assembly.HaltKind} :
        Stmt.WF canBreak canContinue canLeave (.terminal kind)
    | terminalArgs {canBreak canContinue canLeave : Bool}
        {kind : Assembly.HaltKind} {args : ExprSeq kind.argCount} :
        Stmt.WF canBreak canContinue canLeave (.terminalArgs kind args)
end

namespace Proc

def WF (proc : Proc) : Prop :=
  proc.argc ≤ 16 ∧ proc.retc < 16 ∧
    Block.WF false false true proc.body

end Proc

namespace ProcList

def NamesUnique (procs : List Proc) : Prop :=
  (procs.map Proc.name).Nodup

def WF : List Proc → Prop
  | [] => True
  | proc :: rest => proc.WF ∧ WF rest

end ProcList

namespace Program

def WF (program : Program) : Prop :=
  ProcList.NamesUnique program.procs ∧
    ProcList.WF program.procs ∧
    Block.WF false false false program.body

end Program

namespace Scope

def Contains (env : List Name) (name : Name) : Prop :=
  name ∈ env

mutual
  def ExprScoped {results : Nat} (env : List Name) :
      Expr results → Prop
    | .lit _value => True
    | .var name => Contains env name
    | .code _code => False
    | .prim _op args => ExprSeqScoped env args

  def ExprSeqScoped {results : Nat} (env : List Name) :
      ExprSeq results → Prop
    | .nil => True
    | .cons head tail =>
        ExprScoped env head ∧ ExprSeqScoped env tail
end

theorem exprScoped_code_false (env : List Name) {results : Nat}
    (code : Structured.Code) :
    ¬ ExprScoped (results := results) env (.code code) := by
  intro h
  exact h

mutual
  def Block.outEnv (env : List Name) : Block → List Name
    | ⟨stmts⟩ => StmtList.outEnv env stmts

  def Stmt.outEnv (env : List Name) : Stmt → List Name
    | .let_ name _value => name :: env
    | _ => env

  def StmtList.outEnv (env : List Name) : List Stmt → List Name
    | [] => env
    | stmt :: rest => StmtList.outEnv (Stmt.outEnv env stmt) rest
end

mutual
  def Block.Scoped (env : List Name) : Block → Prop
    | ⟨stmts⟩ => StmtList.Scoped env stmts

  def Stmt.Scoped (env : List Name) : Stmt → Prop
    | .expr expr => ExprScoped env expr
    | .exprs exprs => ExprSeqScoped env exprs
    | .let_ name value => name ∉ env ∧ ExprScoped env value
    | .assign name value => Contains env name ∧ ExprScoped env value
    | .assignTop name => Contains env name
    | .assignTopWithOffset _offset name => Contains env name
    | .promoteName name => Contains env name
    | .discardName name => Contains env name
    | .cleanupTo _targetLayout => False
    | .block body => Block.Scoped env body
    | .if_ cond body => ExprScoped env cond ∧ Block.Scoped env body
    | .switch scrutinee cases defaultBody =>
        ExprScoped env scrutinee ∧
          CaseList.Scoped env cases ∧ Default.Scoped env defaultBody
    | .for_ init cond post body =>
        Block.Scoped env init ∧
          let loopEnv := Block.outEnv env init
          ExprScoped loopEnv cond ∧
            Block.Scoped loopEnv post ∧ Block.Scoped loopEnv body
    | .brk | .cont | .leave => True
    | .call _name => True
    | .terminal _kind => True
    | .terminalArgs _kind args => ExprSeqScoped env args

  def StmtList.Scoped (env : List Name) : List Stmt → Prop
    | [] => True
    | stmt :: rest =>
        Stmt.Scoped env stmt ∧ StmtList.Scoped (Stmt.outEnv env stmt) rest

  def CaseList.Scoped (env : List Name) :
      List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        Block.Scoped env body ∧ CaseList.Scoped env rest

  def Default.Scoped (env : List Name) : Option Block → Prop
    | none => True
    | some body => Block.Scoped env body
end

end Scope

namespace Stmt

theorem scoped_outEnv_nodup {env : List Name} {stmt : Stmt}
    (hEnv : env.Nodup) (hScoped : Scope.Stmt.Scoped env stmt) :
    (Scope.Stmt.outEnv env stmt).Nodup := by
  cases stmt <;> simp [Scope.Stmt.outEnv, Scope.Stmt.Scoped] at hScoped ⊢
  all_goals first
    | exact hEnv
    | exact ⟨hScoped.1, hEnv⟩

end Stmt

namespace StmtList

theorem scoped_outEnv_nodup :
    ∀ {env : List Name} {stmts : List Stmt},
      env.Nodup → Scope.StmtList.Scoped env stmts →
        (Scope.StmtList.outEnv env stmts).Nodup
  | env, [], hEnv, _hScoped => by
      simpa [Scope.StmtList.outEnv] using hEnv
  | env, stmt :: rest, hEnv, hScoped => by
      rcases hScoped with ⟨hStmt, hRest⟩
      exact
        scoped_outEnv_nodup
          (env := Scope.Stmt.outEnv env stmt) (stmts := rest)
          (Stmt.scoped_outEnv_nodup hEnv hStmt) hRest

end StmtList

namespace Block

theorem scoped_outEnv_nodup {env : List Name} {block : Block}
    (hEnv : env.Nodup) (hScoped : Scope.Block.Scoped env block) :
    (Scope.Block.outEnv env block).Nodup := by
  cases block with
  | mk stmts =>
      exact StmtList.scoped_outEnv_nodup hEnv hScoped

end Block

namespace Scope.CaseList

theorem scoped_of_mem
    {env : List Name}
    {cases : List (Word × Block)}
    {value : Word} {body : Block}
    (hScoped : Scope.CaseList.Scoped env cases)
    (hMem : (value, body) ∈ cases) :
    Scope.Block.Scoped env body := by
  induction cases with
  | nil => simp at hMem
  | cons head rest ih =>
      rcases head with ⟨headValue, headBody⟩
      rcases hScoped with ⟨hHead, hRest⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hEq | hMem
      · rcases hEq with ⟨rfl, rfl⟩
        exact hHead
      · exact ih hRest hMem

end Scope.CaseList

namespace Program

def Scoped (program : Program) : Prop :=
  Scope.Block.Scoped [] program.body

end Program

/-
Pure lexical name discipline for the locals syntax.

Unlike `Scope`, this namespace does not decide whether a construct belongs to
the stack-free source language.  For example, raw lower `.code` expressions do
not mention names, so they are lexically scoped here; the separate
`SourceOwned`/`SourceWF` boundary rejects them for the source language.
-/
namespace Lexical

mutual
  def ExprScoped {results : Nat} (env : List Name) :
      Expr results → Prop
    | .lit _value => True
    | .var name => Scope.Contains env name
    | .code _code => True
    | .prim _op args => ExprSeqScoped env args

  def ExprSeqScoped {results : Nat} (env : List Name) :
      ExprSeq results → Prop
    | .nil => True
    | .cons head tail =>
        ExprScoped env head ∧ ExprSeqScoped env tail
end

mutual
  def BlockScoped (env : List Name) : Block → Prop
    | ⟨stmts⟩ => StmtListScoped env stmts

  def StmtScoped (env : List Name) : Stmt → Prop
    | .expr expr => ExprScoped env expr
    | .exprs exprs => ExprSeqScoped env exprs
    | .let_ name value => name ∉ env ∧ ExprScoped env value
    | .assign name value => Scope.Contains env name ∧ ExprScoped env value
    | .assignTop name => Scope.Contains env name
    | .assignTopWithOffset _offset name => Scope.Contains env name
    | .promoteName name => Scope.Contains env name
    | .discardName name => Scope.Contains env name
    | .cleanupTo _targetLayout => False
    | .block body => BlockScoped env body
    | .if_ cond body => ExprScoped env cond ∧ BlockScoped env body
    | .switch scrutinee cases defaultBody =>
        ExprScoped env scrutinee ∧
          CaseListScoped env cases ∧ DefaultScoped env defaultBody
    | .for_ init cond post body =>
        BlockScoped env init ∧
          let loopEnv := Scope.Block.outEnv env init
          ExprScoped loopEnv cond ∧
            BlockScoped loopEnv post ∧ BlockScoped loopEnv body
    | .brk | .cont | .leave => True
    | .call _name => True
    | .terminal _kind => True
    | .terminalArgs _kind args => ExprSeqScoped env args

  def StmtListScoped (env : List Name) : List Stmt → Prop
    | [] => True
    | stmt :: rest =>
        StmtScoped env stmt ∧
          StmtListScoped (Scope.Stmt.outEnv env stmt) rest

  def CaseListScoped (env : List Name) :
      List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        BlockScoped env body ∧ CaseListScoped env rest

  def DefaultScoped (env : List Name) : Option Block → Prop
    | none => True
    | some body => BlockScoped env body
end

def ProgramScoped (program : Program) : Prop :=
  BlockScoped [] program.body

end Lexical

end Locals
end EvmCompiler
