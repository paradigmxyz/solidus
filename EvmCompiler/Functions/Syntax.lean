import EvmCompiler.Core.MemoryContract
import EvmCompiler.Locals.Syntax

namespace EvmCompiler
namespace Functions

abbrev Word := Locals.Word
abbrev EVMState := Locals.EVMState
abbrev EVMException := Locals.EVMException
abbrev Name := Locals.Name
abbrev Expr := Locals.Expr

mutual
  structure Block where
    stmts : List Stmt

  /--
  Function-aware statements.

  Calls are statement-level and assign all return values to explicit caller
  targets. Later Yul-surface call expressions can lower into temporaries plus
  this statement form.
  -/
  inductive Stmt where
    | expr (expr : Expr 0)
    | let_ (name : Name) (value : Expr 1)
    | assign (name : Name) (value : Expr 1)
    | block (body : Block)
    | if_ (cond : Expr 1) (body : Block)
    | switch (scrutinee : Expr 1) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Expr 1) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | call (targets : List Name) (functionName : Name)
        (args : List (Expr 1))
    | terminal (kind : Assembly.HaltKind)
    | terminalArgs (kind : Assembly.HaltKind)
        (args : Locals.ExprSeq kind.argCount)
end

namespace Stmt

@[simp] def alwaysExits : Stmt → Bool
  | .brk | .cont | .leave | .terminal _ | .terminalArgs _ _ => true
  | _ => false

end Stmt

namespace StmtList

def hasDirectExit : List Stmt → Bool
  | [] => false
  | stmt :: rest => stmt.alwaysExits || hasDirectExit rest

end StmtList

structure FunDef where
  name : Name
  params : List Name
  returns : List Name
  body : Block

structure Program where
  functions : List FunDef
  body : Block
  memoryContract : MemoryContract.Contract :=
    MemoryContract.unrestricted

mutual
  inductive Block.WF : Bool → Bool → Bool → Block → Prop where
    | nil {canBreak canContinue inFunction : Bool} :
        Block.WF canBreak canContinue inFunction { stmts := [] }
    | cons {canBreak canContinue inFunction : Bool}
        {stmt : Stmt} {rest : List Stmt}
        (hStmt : Stmt.WF canBreak canContinue inFunction stmt)
        (hRest :
          Block.WF canBreak canContinue inFunction { stmts := rest }) :
        Block.WF canBreak canContinue inFunction { stmts := stmt :: rest }

  inductive Stmt.WF : Bool → Bool → Bool → Stmt → Prop where
    | expr {canBreak canContinue inFunction : Bool} {expr : Expr 0} :
        Stmt.WF canBreak canContinue inFunction (.expr expr)
    | let_ {canBreak canContinue inFunction : Bool}
        {name : Name} {value : Expr 1} :
        Stmt.WF canBreak canContinue inFunction (.let_ name value)
    | assign {canBreak canContinue inFunction : Bool}
        {name : Name} {value : Expr 1} :
        Stmt.WF canBreak canContinue inFunction (.assign name value)
    | block {canBreak canContinue inFunction : Bool} {body : Block}
        (hBody : Block.WF canBreak canContinue inFunction body) :
        Stmt.WF canBreak canContinue inFunction (.block body)
    | if_ {canBreak canContinue inFunction : Bool}
        {cond : Expr 1} {body : Block}
        (hBody : Block.WF canBreak canContinue inFunction body) :
        Stmt.WF canBreak canContinue inFunction (.if_ cond body)
    | switch {canBreak canContinue inFunction : Bool}
        {scrutinee : Expr 1} {cases : List (Word × Block)}
        {defaultBody : Option Block}
        (hCases : CaseList.WF canBreak canContinue inFunction cases)
        (hDefault : Default.WF canBreak canContinue inFunction defaultBody) :
        Stmt.WF canBreak canContinue inFunction
          (.switch scrutinee cases defaultBody)
    | for_ {canBreak canContinue inFunction : Bool}
        {init post body : Block} {cond : Expr 1}
        (hInit : Block.WF false false inFunction init)
        (hPost : Block.WF false false inFunction post)
        (hBody : Block.WF true true inFunction body) :
        Stmt.WF canBreak canContinue inFunction
          (.for_ init cond post body)
    | brk {canBreak canContinue inFunction : Bool}
        (hAllowed : canBreak = true) :
        Stmt.WF canBreak canContinue inFunction .brk
    | cont {canBreak canContinue inFunction : Bool}
        (hAllowed : canContinue = true) :
        Stmt.WF canBreak canContinue inFunction .cont
    | leave {canBreak canContinue inFunction : Bool}
        (hAllowed : inFunction = true) :
        Stmt.WF canBreak canContinue inFunction .leave
    | call {canBreak canContinue inFunction : Bool}
        {targets : List Name} {functionName : Name}
        {args : List (Expr 1)} :
        Stmt.WF canBreak canContinue inFunction
          (.call targets functionName args)
    | terminal {canBreak canContinue inFunction : Bool}
        {kind : Assembly.HaltKind} (hArgCount : kind.argCount = 0) :
        Stmt.WF canBreak canContinue inFunction (.terminal kind)
    | terminalArgs {canBreak canContinue inFunction : Bool}
        {kind : Assembly.HaltKind} {args : Locals.ExprSeq kind.argCount} :
        Stmt.WF canBreak canContinue inFunction (.terminalArgs kind args)

  inductive CaseList.WF :
      Bool → Bool → Bool → List (Word × Block) → Prop where
    | nil {canBreak canContinue inFunction : Bool} :
        CaseList.WF canBreak canContinue inFunction []
    | cons {canBreak canContinue inFunction : Bool}
        {value : Word} {body : Block} {rest : List (Word × Block)}
        (hBody : Block.WF canBreak canContinue inFunction body)
        (hRest : CaseList.WF canBreak canContinue inFunction rest) :
        CaseList.WF canBreak canContinue inFunction ((value, body) :: rest)

  inductive Default.WF : Bool → Bool → Bool → Option Block → Prop where
    | none {canBreak canContinue inFunction : Bool} :
        Default.WF canBreak canContinue inFunction none
    | some {canBreak canContinue inFunction : Bool} {body : Block}
        (hBody : Block.WF canBreak canContinue inFunction body) :
        Default.WF canBreak canContinue inFunction (some body)
end

namespace FunDef

def WF (fn : FunDef) : Prop :=
  Block.WF false false true fn.body

end FunDef

namespace FunList

inductive WF : List FunDef → Prop where
  | nil : WF []
  | cons {fn : FunDef} {rest : List FunDef}
      (hFn : fn.WF) (hRest : WF rest) : WF (fn :: rest)

theorem wf_of_mem
    {functions : List FunDef} {fn : FunDef}
    (hWF : WF functions) (hMem : fn ∈ functions) :
    fn.WF := by
  induction hWF with
  | nil => simp at hMem
  | cons hHead hRest ih =>
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hMem
      · exact hHead
      · exact ih hMem

end FunList

namespace Program

def WF (program : Program) : Prop :=
  FunList.WF program.functions ∧
    Block.WF false false false program.body

end Program

namespace Scope

def Contains (env : List Name) (name : Name) : Prop :=
  name ∈ env

def containsAll (env names : List Name) : Prop :=
  ∀ name, name ∈ names → Contains env name

mutual
  def ExprScoped {results : Nat} (env : List Name) :
      Expr results → Prop
    | .lit _value => True
    | .var name => Contains env name
    | .code _code => False
    | .prim _op args => ExprSeqScoped env args

  def ExprSeqScoped {results : Nat} (env : List Name) :
      Locals.ExprSeq results → Prop
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

theorem Stmt.mem_outEnv
    {env : List Name} {stmt : Stmt} {name : Name}
    (hMem : name ∈ env) :
    name ∈ Stmt.outEnv env stmt := by
  cases stmt <;> simp [Stmt.outEnv, hMem]

theorem StmtList.mem_outEnv
    {env : List Name} {stmts : List Stmt} {name : Name}
    (hMem : name ∈ env) :
    name ∈ StmtList.outEnv env stmts := by
  induction stmts generalizing env with
  | nil => exact hMem
  | cons stmt rest ih =>
      exact ih (Stmt.mem_outEnv hMem)

theorem Block.mem_outEnv
    {env : List Name} {block : Block} {name : Name}
    (hMem : name ∈ env) :
    name ∈ Block.outEnv env block := by
  cases block with
  | mk stmts => exact StmtList.mem_outEnv hMem

mutual
  def Block.Scoped (env : List Name) : Block → Prop
    | ⟨stmts⟩ => StmtList.Scoped env stmts

  def Stmt.Scoped (env : List Name) : Stmt → Prop
    | .expr expr => ExprScoped env expr
    | .let_ name value => name ∉ env ∧ ExprScoped env value
    | .assign name value => Contains env name ∧ ExprScoped env value
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
    | .brk => True
    | .cont => True
    | .leave => True
    | .call targets _functionName args =>
        targets.Nodup ∧ containsAll env targets ∧
          ∀ arg, arg ∈ args → ExprScoped env arg
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

theorem Stmt.outEnv_mem_iff
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    (stmt : Stmt) (name : Name) :
    name ∈ Stmt.outEnv before stmt ↔
      name ∈ Stmt.outEnv after stmt := by
  cases stmt <;> simp [Stmt.outEnv, hEnv]

theorem StmtList.outEnv_mem_iff
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    (stmts : List Stmt) (name : Name) :
    name ∈ StmtList.outEnv before stmts ↔
      name ∈ StmtList.outEnv after stmts := by
  induction stmts generalizing before after with
  | nil => exact hEnv name
  | cons stmt rest ih =>
      exact ih (fun current => Stmt.outEnv_mem_iff hEnv stmt current)

theorem Block.outEnv_mem_iff
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    (block : Block) (name : Name) :
    name ∈ Block.outEnv before block ↔
      name ∈ Block.outEnv after block := by
  cases block with
  | mk stmts => exact StmtList.outEnv_mem_iff hEnv stmts name

mutual

theorem ExprScoped.of_env_equiv
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    {results : Nat} {expr : Expr results}
    (hScoped : ExprScoped before expr) :
    ExprScoped after expr := by
  cases expr with
  | lit value => trivial
  | var name => exact (hEnv name).mp hScoped
  | code code => exact False.elim hScoped
  | prim op args =>
      exact ExprSeqScoped.of_env_equiv hEnv hScoped

theorem ExprSeqScoped.of_env_equiv
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    {results : Nat} {exprs : Locals.ExprSeq results}
    (hScoped : ExprSeqScoped before exprs) :
    ExprSeqScoped after exprs := by
  cases exprs with
  | nil => trivial
  | cons head tail =>
      exact
        ⟨ExprScoped.of_env_equiv hEnv hScoped.1,
          ExprSeqScoped.of_env_equiv hEnv hScoped.2⟩

end

mutual

theorem Block.Scoped.of_env_equiv
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    {block : Block}
    (hScoped : Block.Scoped before block) :
    Block.Scoped after block := by
  cases block with
  | mk stmts =>
      exact StmtList.Scoped.of_env_equiv hEnv hScoped

theorem Stmt.Scoped.of_env_equiv
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    {stmt : Stmt}
    (hScoped : Stmt.Scoped before stmt) :
    Stmt.Scoped after stmt := by
  cases stmt with
  | expr expr =>
      exact ExprScoped.of_env_equiv hEnv hScoped
  | let_ name value =>
      exact
        ⟨fun hMem => hScoped.1 ((hEnv name).mpr hMem),
          ExprScoped.of_env_equiv hEnv hScoped.2⟩
  | assign name value =>
      exact
        ⟨(hEnv name).mp hScoped.1,
          ExprScoped.of_env_equiv hEnv hScoped.2⟩
  | block body =>
      exact Block.Scoped.of_env_equiv hEnv hScoped
  | if_ cond body =>
      exact
        ⟨ExprScoped.of_env_equiv hEnv hScoped.1,
          Block.Scoped.of_env_equiv hEnv hScoped.2⟩
  | switch scrutinee cases defaultBody =>
      exact
        ⟨ExprScoped.of_env_equiv hEnv hScoped.1,
          CaseList.Scoped.of_env_equiv hEnv hScoped.2.1,
          Default.Scoped.of_env_equiv hEnv hScoped.2.2⟩
  | for_ init cond post body =>
      have hLoopEnv :
          ∀ name,
            name ∈ Block.outEnv before init ↔
              name ∈ Block.outEnv after init :=
        fun name => Block.outEnv_mem_iff hEnv init name
      exact
        ⟨Block.Scoped.of_env_equiv hEnv hScoped.1,
          ExprScoped.of_env_equiv hLoopEnv hScoped.2.1,
          Block.Scoped.of_env_equiv hLoopEnv hScoped.2.2.1,
          Block.Scoped.of_env_equiv hLoopEnv hScoped.2.2.2⟩
  | brk => trivial
  | cont => trivial
  | leave => trivial
  | call targets functionName args =>
      exact
        ⟨hScoped.1,
          fun name hName => (hEnv name).mp (hScoped.2.1 name hName),
          fun arg hArg =>
            ExprScoped.of_env_equiv hEnv (hScoped.2.2 arg hArg)⟩
  | terminal kind => trivial
  | terminalArgs kind args =>
      exact ExprSeqScoped.of_env_equiv hEnv hScoped

theorem StmtList.Scoped.of_env_equiv
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    {stmts : List Stmt}
    (hScoped : StmtList.Scoped before stmts) :
    StmtList.Scoped after stmts := by
  cases stmts with
  | nil => trivial
  | cons stmt rest =>
      exact
        ⟨Stmt.Scoped.of_env_equiv hEnv hScoped.1,
          StmtList.Scoped.of_env_equiv
            (fun name => Stmt.outEnv_mem_iff hEnv stmt name)
            hScoped.2⟩

theorem CaseList.Scoped.of_env_equiv
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    {cases : List (Word × Block)}
    (hScoped : CaseList.Scoped before cases) :
    CaseList.Scoped after cases := by
  cases cases with
  | nil => trivial
  | cons entry rest =>
      exact
        ⟨Block.Scoped.of_env_equiv hEnv hScoped.1,
          CaseList.Scoped.of_env_equiv hEnv hScoped.2⟩

theorem Default.Scoped.of_env_equiv
    {before after : List Name}
    (hEnv : ∀ name, name ∈ before ↔ name ∈ after)
    {body : Option Block}
    (hScoped : Default.Scoped before body) :
    Default.Scoped after body := by
  cases body with
  | none => trivial
  | some body =>
      exact Block.Scoped.of_env_equiv hEnv hScoped

end

end Scope

namespace FunDef

def Scoped (fn : FunDef) : Prop :=
  (fn.returns ++ fn.params).Nodup ∧
    Scope.Block.Scoped (fn.returns ++ fn.params) fn.body

theorem signatureNodup {fn : FunDef} (hScoped : fn.Scoped) :
    (fn.returns ++ fn.params).Nodup :=
  hScoped.1

theorem bodyScoped {fn : FunDef} (hScoped : fn.Scoped) :
    Scope.Block.Scoped (fn.returns ++ fn.params) fn.body :=
  hScoped.2

end FunDef

namespace FunList

def Scoped : List FunDef → Prop
  | [] => True
  | fn :: rest => fn.Scoped ∧ Scoped rest

theorem scoped_of_mem
    {functions : List FunDef} {fn : FunDef}
    (hScoped : Scoped functions)
    (hMem : fn ∈ functions) :
    fn.Scoped := by
  induction functions with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      rcases hScoped with ⟨hHead, hRest⟩
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hMem
      · exact hHead
      · exact ih hRest hMem

end FunList

namespace Program

def Scoped (program : Program) : Prop :=
  FunList.Scoped program.functions ∧ Scope.Block.Scoped [] program.body

end Program

end Functions
end EvmCompiler
