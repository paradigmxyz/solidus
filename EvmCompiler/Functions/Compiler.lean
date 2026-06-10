import EvmCompiler.Functions.Syntax
import EvmCompiler.Functions.LoweringCore
import EvmCompiler.Locals.Compiler

namespace EvmCompiler
namespace Functions

namespace ExprList

def usesCallCreate : List (Expr 1) → Bool
  | [] => false
  | expr :: rest => expr.usesCallCreate || usesCallCreate rest

end ExprList

mutual
  def Block.usesCallCreate : Block → Bool
    | ⟨stmts⟩ => StmtList.usesCallCreate stmts

  def Stmt.usesCallCreate : Stmt → Bool
    | .expr expr => expr.usesCallCreate
    | .let_ _name value => value.usesCallCreate
    | .assign _name value => value.usesCallCreate
    | .block body => body.usesCallCreate
    | .if_ cond body => cond.usesCallCreate || body.usesCallCreate
    | .switch scrutinee cases defaultBody =>
        scrutinee.usesCallCreate || CaseList.usesCallCreate cases ||
          Default.usesCallCreate defaultBody
    | .for_ init cond post body =>
        init.usesCallCreate || cond.usesCallCreate || post.usesCallCreate ||
          body.usesCallCreate
    | .brk | .cont | .leave | .terminal _ => false
    | .call _ _ args => ExprList.usesCallCreate args
    | .terminalArgs _kind args => args.usesCallCreate

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

namespace FunDef

def usesCallCreate (fn : FunDef) : Bool :=
  fn.body.usesCallCreate

end FunDef

namespace FunList

def usesCallCreate : List FunDef → Bool
  | [] => false
  | fn :: rest => fn.usesCallCreate || usesCallCreate rest

end FunList

namespace Program

def usesCallCreate (program : Program) : Bool :=
  FunList.usesCallCreate program.functions || program.body.usesCallCreate

end Program

set_option maxHeartbeats 800000 in
mutual
  def Block.toLocals (returns : List Name) (block : Block) : Locals.Block :=
    match block with
    | ⟨stmts⟩ => { stmts := StmtList.toLocals returns stmts }

  def Stmt.toLocals (returns : List Name) : Stmt → List Locals.Stmt
    | .expr expr => [Locals.Stmt.expr expr]
    | .let_ name value => [Locals.Stmt.let_ name value]
    | .assign name value => [Locals.Stmt.assign name value]
    | .block body => [Locals.Stmt.block (Block.toLocals returns body)]
    | .if_ cond body => [Locals.Stmt.if_ cond (Block.toLocals returns body)]
    | .switch scrutinee cases defaultBody =>
        [Locals.Stmt.switch scrutinee (CaseList.toLocals returns cases)
          (Default.toLocals returns defaultBody)]
    | .for_ init cond post body =>
        [Locals.Stmt.for_ (Block.toLocals returns init) cond
          (Block.toLocals returns post) (Block.toLocals returns body)]
    | .brk => [.brk]
    | .cont => [.cont]
    | .leave => Lower.pushReturns returns ++ [.leave]
    | .call targets functionName args =>
        Lower.evalArgs args ++ [Locals.Stmt.call functionName] ++
          Lower.assignReturnedTops targets
    | .terminal kind => [.terminal kind]
    | .terminalArgs kind args => [.terminalArgs kind args]

  def StmtList.toLocals (returns : List Name) : List Stmt → List Locals.Stmt
    | [] => []
    | stmt :: rest => Stmt.toLocals returns stmt ++ StmtList.toLocals returns rest

  def CaseList.toLocals (returns : List Name) :
      List (Word × Block) → List (Word × Locals.Block)
    | [] => []
    | (value, body) :: rest =>
        (value, Block.toLocals returns body) :: CaseList.toLocals returns rest

  def Default.toLocals (returns : List Name) :
      Option Block → Option Locals.Block
    | none => none
    | some body => some (Block.toLocals returns body)
end


namespace FunDef

def toLocalsProc (fn : FunDef) : Locals.Proc where
  name := fn.name
  argc := fn.params.length
  retc := fn.returns.length
  entryLayout := fn.params.reverse
  body :=
    { stmts :=
        Lower.initReturns fn.returns ++
          StmtList.toLocals fn.returns fn.body.stmts ++
          Lower.pushReturns fn.returns }

end FunDef

namespace FunList

def toLocalsProcs : List FunDef → List Locals.Proc
  | [] => []
  | fn :: rest => fn.toLocalsProc :: toLocalsProcs rest

end FunList

namespace Program

def toLocals (program : Program) : Locals.Program where
  procs := FunList.toLocalsProcs program.functions
  body := Block.toLocals [] program.body

def toLocals? (program : Program) : Option Locals.Program :=
  some program.toLocals

def toExpressions? (program : Program) : Option Expressions.Program :=
  program.toLocals.toExpressions?

def compile? (program : Program) :
    Option Assembly.TargetProgram :=
  program.toLocals.compile?

def compileExecutable? (program : Program) :
    Option Assembly.TargetProgram :=
  program.toLocals.compileExecutable?

theorem compileExecutable?_eq_compile? (program : Program) :
    compileExecutable? program = compile? program := by
  simp [compileExecutable?, compile?,
    Locals.Program.compileExecutable?_eq_compile?]

def Accepted (program : Program) : Prop :=
  program.WF ∧ program.Scoped ∧ program.toLocals.Accepted

def SourceAccepted (program : Program) : Prop :=
  program.WF ∧ program.Scoped

theorem sourceAccepted_of_accepted {program : Program}
    (hAccepted : Accepted program) :
    SourceAccepted program :=
  ⟨hAccepted.1, hAccepted.2.1⟩

end Program

namespace SourceAcceptedCheck

namespace Names

def nodup? (names : List Name) : Bool :=
  decide names.Nodup

def in? (env : List Name) (name : Name) : Bool :=
  decide (name ∈ env)

def fresh? (env : List Name) (name : Name) : Bool :=
  decide (name ∉ env)

def allIn? (env names : List Name) : Bool :=
  names.all fun name => in? env name

theorem nodup_of_check {names : List Name}
    (hCheck : nodup? names = true) :
    names.Nodup :=
  of_decide_eq_true hCheck

theorem in_of_check {env : List Name} {name : Name}
    (hCheck : in? env name = true) :
    name ∈ env :=
  of_decide_eq_true hCheck

theorem fresh_of_check {env : List Name} {name : Name}
    (hCheck : fresh? env name = true) :
    name ∉ env :=
  of_decide_eq_true hCheck

theorem allIn_of_check {env names : List Name}
    (hCheck : allIn? env names = true) :
    ∀ name, name ∈ names → name ∈ env := by
  intro name hName
  exact
    in_of_check
      ((List.all_eq_true.mp hCheck) name hName)

end Names

mutual
  def Block.wf? (canBreak canContinue inFunction : Bool) :
      Functions.Block → Bool
    | ⟨stmts⟩ => StmtList.wf? canBreak canContinue inFunction stmts

  def Stmt.wf? (canBreak canContinue inFunction : Bool) :
      Functions.Stmt → Bool
    | .expr _expr => true
    | .let_ _name _value => true
    | .assign _name _value => true
    | .block body => Block.wf? canBreak canContinue inFunction body
    | .if_ _cond body => Block.wf? canBreak canContinue inFunction body
    | .switch _scrutinee cases defaultBody =>
        CaseList.wf? canBreak canContinue inFunction cases &&
          Default.wf? canBreak canContinue inFunction defaultBody
    | .for_ init _cond post body =>
        Block.wf? false false inFunction init &&
          (Block.wf? false false inFunction post &&
            Block.wf? true true inFunction body)
    | .brk => canBreak
    | .cont => canContinue
    | .leave => inFunction
    | .call _targets _functionName _args => true
    | .terminal _kind => true
    | .terminalArgs _kind _args => true

  def StmtList.wf? (canBreak canContinue inFunction : Bool) :
      List Functions.Stmt → Bool
    | [] => true
    | stmt :: rest =>
        Stmt.wf? canBreak canContinue inFunction stmt &&
          StmtList.wf? canBreak canContinue inFunction rest

  def CaseList.wf? (canBreak canContinue inFunction : Bool) :
      List (Word × Functions.Block) → Bool
    | [] => true
    | (_value, body) :: rest =>
        Block.wf? canBreak canContinue inFunction body &&
          CaseList.wf? canBreak canContinue inFunction rest

  def Default.wf? (canBreak canContinue inFunction : Bool) :
      Option Functions.Block → Bool
    | none => true
    | some body => Block.wf? canBreak canContinue inFunction body
end

namespace FunDef

def wf? (fn : Functions.FunDef) : Bool :=
  Block.wf? false false true fn.body

end FunDef

namespace FunList

def wf? : List Functions.FunDef → Bool
  | [] => true
  | fn :: rest => FunDef.wf? fn && wf? rest

end FunList

namespace Program

def wf? (program : Functions.Program) : Bool :=
  FunList.wf? program.functions && Block.wf? false false false program.body

end Program

mutual
  theorem Block.wf_of_check {canBreak canContinue inFunction : Bool} :
      ∀ {block : Functions.Block},
        Block.wf? canBreak canContinue inFunction block = true →
          Functions.Block.WF canBreak canContinue inFunction block := by
    intro block hCheck
    cases block with
    | mk stmts =>
        exact StmtList.wf_of_check hCheck

  theorem Stmt.wf_of_check {canBreak canContinue inFunction : Bool} :
      ∀ {stmt : Functions.Stmt},
        Stmt.wf? canBreak canContinue inFunction stmt = true →
          Functions.Stmt.WF canBreak canContinue inFunction stmt := by
    intro stmt hCheck
    cases stmt with
    | expr expr =>
        exact Functions.Stmt.WF.expr
    | let_ name value =>
        exact Functions.Stmt.WF.let_
    | assign name value =>
        exact Functions.Stmt.WF.assign
    | block body =>
        exact Functions.Stmt.WF.block (Block.wf_of_check hCheck)
    | if_ cond body =>
        exact Functions.Stmt.WF.if_ (Block.wf_of_check hCheck)
    | switch scrutinee cases defaultBody =>
        have hAnd :
            CaseList.wf? canBreak canContinue inFunction cases = true ∧
              Default.wf? canBreak canContinue inFunction defaultBody = true :=
          by simpa [Stmt.wf?] using hCheck
        exact
          Functions.Stmt.WF.switch
            (CaseList.wf_of_check hAnd.1)
            (Default.wf_of_check hAnd.2)
    | for_ init cond post body =>
        have hAnd :
            Block.wf? false false inFunction init = true ∧
              (Block.wf? false false inFunction post &&
                Block.wf? true true inFunction body) = true :=
          by simpa [Stmt.wf?] using hCheck
        have hPostBody :
            Block.wf? false false inFunction post = true ∧
              Block.wf? true true inFunction body = true :=
          by simpa using hAnd.2
        exact
          Functions.Stmt.WF.for_
            (Block.wf_of_check hAnd.1)
            (Block.wf_of_check hPostBody.1)
            (Block.wf_of_check hPostBody.2)
    | brk =>
        exact
          Functions.Stmt.WF.brk
            (by simpa [Stmt.wf?] using hCheck)
    | cont =>
        exact
          Functions.Stmt.WF.cont
            (by simpa [Stmt.wf?] using hCheck)
    | leave =>
        exact
          Functions.Stmt.WF.leave
            (by simpa [Stmt.wf?] using hCheck)
    | call targets functionName args =>
        exact Functions.Stmt.WF.call
    | terminal kind =>
        exact Functions.Stmt.WF.terminal
    | terminalArgs kind args =>
        exact Functions.Stmt.WF.terminalArgs

  theorem StmtList.wf_of_check {canBreak canContinue inFunction : Bool} :
      ∀ {stmts : List Functions.Stmt},
        StmtList.wf? canBreak canContinue inFunction stmts = true →
          Functions.Block.WF canBreak canContinue inFunction
            { stmts := stmts } := by
    intro stmts hCheck
    cases stmts with
    | nil =>
        exact Functions.Block.WF.nil
    | cons stmt rest =>
        have hAnd :
            Stmt.wf? canBreak canContinue inFunction stmt = true ∧
              StmtList.wf? canBreak canContinue inFunction rest = true :=
          by simpa [StmtList.wf?] using hCheck
        exact
          Functions.Block.WF.cons
            (Stmt.wf_of_check hAnd.1)
            (StmtList.wf_of_check hAnd.2)

  theorem CaseList.wf_of_check {canBreak canContinue inFunction : Bool} :
      ∀ {cases : List (Word × Functions.Block)},
        CaseList.wf? canBreak canContinue inFunction cases = true →
          Functions.CaseList.WF canBreak canContinue inFunction cases := by
    intro cases hCheck
    cases cases with
    | nil =>
        exact Functions.CaseList.WF.nil
    | cons head rest =>
        rcases head with ⟨value, body⟩
        have hAnd :
            Block.wf? canBreak canContinue inFunction body = true ∧
              CaseList.wf? canBreak canContinue inFunction rest = true :=
          by simpa [CaseList.wf?] using hCheck
        exact
          Functions.CaseList.WF.cons
            (Block.wf_of_check hAnd.1)
            (CaseList.wf_of_check hAnd.2)

  theorem Default.wf_of_check {canBreak canContinue inFunction : Bool} :
      ∀ {defaultBody : Option Functions.Block},
        Default.wf? canBreak canContinue inFunction defaultBody = true →
          Functions.Default.WF canBreak canContinue inFunction
            defaultBody := by
    intro defaultBody hCheck
    cases defaultBody with
    | none =>
        exact Functions.Default.WF.none
    | some body =>
        exact Functions.Default.WF.some (Block.wf_of_check hCheck)
end

theorem FunDef.wf_of_check {fn : Functions.FunDef}
    (hCheck : FunDef.wf? fn = true) :
    fn.WF := by
  exact Block.wf_of_check hCheck

theorem FunList.wf_of_check :
    ∀ {functions : List Functions.FunDef},
      FunList.wf? functions = true →
        Functions.FunList.WF functions
  | [], _hCheck => by
      exact Functions.FunList.WF.nil
  | fn :: rest, hCheck => by
      have hAnd :
          FunDef.wf? fn = true ∧ FunList.wf? rest = true :=
        by simpa [FunList.wf?] using hCheck
      exact
        Functions.FunList.WF.cons
          (FunDef.wf_of_check hAnd.1)
          (FunList.wf_of_check hAnd.2)

theorem Program.wf_of_check {program : Functions.Program}
    (hCheck : Program.wf? program = true) :
    program.WF := by
  have hAnd :
      FunList.wf? program.functions = true ∧
        Block.wf? false false false program.body = true :=
    by simpa [Program.wf?] using hCheck
  exact
    ⟨FunList.wf_of_check hAnd.1, Block.wf_of_check hAnd.2⟩

mutual
  def Expr.scoped? (env : List Name) {results : Nat} :
      Functions.Expr results → Bool
    | .lit _value => true
    | .var name => Names.in? env name
    | .code _code => false
    | .prim _op args => ExprSeq.scoped? env args

  def ExprSeq.scoped? (env : List Name) {results : Nat} :
      Locals.ExprSeq results → Bool
    | .nil => true
    | .cons head tail =>
        Expr.scoped? env head && ExprSeq.scoped? env tail
end

namespace ExprList

def scoped? (env : List Name) : List (Functions.Expr 1) → Bool
  | [] => true
  | arg :: rest => Expr.scoped? env arg && scoped? env rest

end ExprList

mutual
  def Block.scoped? (env : List Name) :
      Functions.Block → Bool
    | ⟨stmts⟩ => StmtList.scoped? env stmts

  def Stmt.scoped? (env : List Name) :
      Functions.Stmt → Bool
    | .expr expr => Expr.scoped? env expr
    | .let_ name value =>
        Names.fresh? env name && Expr.scoped? env value
    | .assign name value =>
        Names.in? env name && Expr.scoped? env value
    | .block body => Block.scoped? env body
    | .if_ cond body =>
        Expr.scoped? env cond && Block.scoped? env body
    | .switch scrutinee cases defaultBody =>
        Expr.scoped? env scrutinee &&
          (CaseList.scoped? env cases && Default.scoped? env defaultBody)
    | .for_ init cond post body =>
        Block.scoped? env init &&
          (let loopEnv := Functions.Scope.Block.outEnv env init
           Expr.scoped? loopEnv cond &&
            (Block.scoped? loopEnv post && Block.scoped? loopEnv body))
    | .brk => true
    | .cont => true
    | .leave => true
    | .call targets _functionName args =>
        Names.nodup? targets &&
          (Names.allIn? env targets && ExprList.scoped? env args)
    | .terminal _kind => true
    | .terminalArgs _kind args => ExprSeq.scoped? env args

  def StmtList.scoped? (env : List Name) :
      List Functions.Stmt → Bool
    | [] => true
    | stmt :: rest =>
        Stmt.scoped? env stmt &&
          StmtList.scoped? (Functions.Scope.Stmt.outEnv env stmt) rest

  def CaseList.scoped? (env : List Name) :
      List (Word × Functions.Block) → Bool
    | [] => true
    | (_value, body) :: rest =>
        Block.scoped? env body && CaseList.scoped? env rest

  def Default.scoped? (env : List Name) :
      Option Functions.Block → Bool
    | none => true
    | some body => Block.scoped? env body
end

namespace FunDef

def scoped? (fn : Functions.FunDef) : Bool :=
  Names.nodup? (fn.returns ++ fn.params) &&
    Block.scoped? (fn.returns ++ fn.params) fn.body

end FunDef

namespace FunList

def scoped? : List Functions.FunDef → Bool
  | [] => true
  | fn :: rest => FunDef.scoped? fn && scoped? rest

end FunList

namespace Program

def scoped? (program : Functions.Program) : Bool :=
  FunList.scoped? program.functions && Block.scoped? [] program.body

def sourceAccepted? (program : Functions.Program) : Bool :=
  wf? program && scoped? program

end Program

mutual
  theorem Expr.scoped_of_check {env : List Name} :
      ∀ {results : Nat} {expr : Functions.Expr results},
        Expr.scoped? env expr = true →
          Functions.Scope.ExprScoped env expr := by
    intro results expr hCheck
    cases expr with
    | lit value =>
        trivial
    | var name =>
        exact Names.in_of_check (by simpa [Expr.scoped?] using hCheck)
    | code code =>
        simp [Expr.scoped?] at hCheck
    | prim op args =>
        exact ExprSeq.scoped_of_check hCheck

  theorem ExprSeq.scoped_of_check {env : List Name} :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results},
        ExprSeq.scoped? env exprs = true →
          Functions.Scope.ExprSeqScoped env exprs := by
    intro results exprs hCheck
    cases exprs with
    | nil =>
        trivial
    | cons head tail =>
        have hAnd :
            Expr.scoped? env head = true ∧
              ExprSeq.scoped? env tail = true :=
          by simpa [ExprSeq.scoped?] using hCheck
        exact
          ⟨Expr.scoped_of_check hAnd.1,
            ExprSeq.scoped_of_check hAnd.2⟩
end

theorem ExprList.scoped_of_check {env : List Name} :
    ∀ {args : List (Functions.Expr 1)},
      ExprList.scoped? env args = true →
        ∀ arg, arg ∈ args → Functions.Scope.ExprScoped env arg
  | [], _hCheck, arg, hArg => by
      cases hArg
  | arg :: rest, hCheck, other, hOther => by
      have hAnd :
          Expr.scoped? env arg = true ∧
            ExprList.scoped? env rest = true :=
        by simpa [ExprList.scoped?] using hCheck
      cases hOther with
      | head =>
          exact Expr.scoped_of_check hAnd.1
      | tail _ hRest =>
          exact ExprList.scoped_of_check hAnd.2 other hRest

mutual
  theorem Block.scoped_of_check {env : List Name} :
      ∀ {block : Functions.Block},
        Block.scoped? env block = true →
          Functions.Scope.Block.Scoped env block := by
    intro block hCheck
    cases block with
    | mk stmts =>
        exact StmtList.scoped_of_check hCheck

  theorem Stmt.scoped_of_check {env : List Name} :
      ∀ {stmt : Functions.Stmt},
        Stmt.scoped? env stmt = true →
          Functions.Scope.Stmt.Scoped env stmt := by
    intro stmt hCheck
    cases stmt with
    | expr expr =>
        exact Expr.scoped_of_check hCheck
    | let_ name value =>
        have hAnd :
            Names.fresh? env name = true ∧ Expr.scoped? env value = true :=
          by simpa [Stmt.scoped?] using hCheck
        exact
          ⟨Names.fresh_of_check hAnd.1,
            Expr.scoped_of_check hAnd.2⟩
    | assign name value =>
        have hAnd :
            Names.in? env name = true ∧ Expr.scoped? env value = true :=
          by simpa [Stmt.scoped?] using hCheck
        exact
          ⟨Names.in_of_check hAnd.1, Expr.scoped_of_check hAnd.2⟩
    | block body =>
        exact Block.scoped_of_check hCheck
    | if_ cond body =>
        have hAnd :
            Expr.scoped? env cond = true ∧
              Block.scoped? env body = true :=
          by simpa [Stmt.scoped?] using hCheck
        exact
          ⟨Expr.scoped_of_check hAnd.1,
            Block.scoped_of_check hAnd.2⟩
    | switch scrutinee cases defaultBody =>
        have hAnd :
            Expr.scoped? env scrutinee = true ∧
              (CaseList.scoped? env cases &&
                Default.scoped? env defaultBody) = true :=
          by simpa [Stmt.scoped?] using hCheck
        have hTail :
            CaseList.scoped? env cases = true ∧
              Default.scoped? env defaultBody = true :=
          by simpa using hAnd.2
        exact
          ⟨Expr.scoped_of_check hAnd.1,
            CaseList.scoped_of_check hTail.1,
            Default.scoped_of_check hTail.2⟩
    | for_ init cond post body =>
        have hAnd :
            Block.scoped? env init = true ∧
              (let loopEnv := Functions.Scope.Block.outEnv env init
               Expr.scoped? loopEnv cond &&
                (Block.scoped? loopEnv post &&
                  Block.scoped? loopEnv body)) = true :=
          by simpa [Stmt.scoped?] using hCheck
        let loopEnv := Functions.Scope.Block.outEnv env init
        have hLoop :
            Expr.scoped? loopEnv cond = true ∧
              (Block.scoped? loopEnv post &&
                Block.scoped? loopEnv body) = true :=
          by simpa [loopEnv] using hAnd.2
        have hPostBody :
            Block.scoped? loopEnv post = true ∧
              Block.scoped? loopEnv body = true :=
          by simpa using hLoop.2
        exact
          ⟨Block.scoped_of_check hAnd.1,
            Expr.scoped_of_check hLoop.1,
            Block.scoped_of_check hPostBody.1,
            Block.scoped_of_check hPostBody.2⟩
    | brk =>
        trivial
    | cont =>
        trivial
    | leave =>
        trivial
    | call targets functionName args =>
        have hAnd :
            Names.nodup? targets = true ∧
              (Names.allIn? env targets && ExprList.scoped? env args) =
                true :=
          by simpa [Stmt.scoped?] using hCheck
        have hTail :
            Names.allIn? env targets = true ∧
              ExprList.scoped? env args = true :=
          by simpa using hAnd.2
        exact
          ⟨Names.nodup_of_check hAnd.1,
            Names.allIn_of_check hTail.1,
            ExprList.scoped_of_check hTail.2⟩
    | terminal kind =>
        trivial
    | terminalArgs kind args =>
        exact ExprSeq.scoped_of_check hCheck

  theorem StmtList.scoped_of_check {env : List Name} :
      ∀ {stmts : List Functions.Stmt},
        StmtList.scoped? env stmts = true →
          Functions.Scope.StmtList.Scoped env stmts := by
    intro stmts hCheck
    cases stmts with
    | nil =>
        trivial
    | cons stmt rest =>
        have hAnd :
            Stmt.scoped? env stmt = true ∧
              StmtList.scoped? (Functions.Scope.Stmt.outEnv env stmt) rest =
                true :=
          by simpa [StmtList.scoped?] using hCheck
        exact
          ⟨Stmt.scoped_of_check hAnd.1,
            StmtList.scoped_of_check hAnd.2⟩

  theorem CaseList.scoped_of_check {env : List Name} :
      ∀ {cases : List (Word × Functions.Block)},
        CaseList.scoped? env cases = true →
          Functions.Scope.CaseList.Scoped env cases := by
    intro cases hCheck
    cases cases with
    | nil =>
        trivial
    | cons head rest =>
        rcases head with ⟨value, body⟩
        have hAnd :
            Block.scoped? env body = true ∧
              CaseList.scoped? env rest = true :=
          by simpa [CaseList.scoped?] using hCheck
        exact
          ⟨Block.scoped_of_check hAnd.1,
            CaseList.scoped_of_check hAnd.2⟩

  theorem Default.scoped_of_check {env : List Name} :
      ∀ {defaultBody : Option Functions.Block},
        Default.scoped? env defaultBody = true →
          Functions.Scope.Default.Scoped env defaultBody := by
    intro defaultBody hCheck
    cases defaultBody with
    | none =>
        trivial
    | some body =>
        exact Block.scoped_of_check hCheck
end

theorem FunDef.scoped_of_check {fn : Functions.FunDef}
    (hCheck : FunDef.scoped? fn = true) :
    fn.Scoped := by
  have hAnd :
      Names.nodup? (fn.returns ++ fn.params) = true ∧
        Block.scoped? (fn.returns ++ fn.params) fn.body = true :=
    by simpa [FunDef.scoped?] using hCheck
  exact
    ⟨Names.nodup_of_check hAnd.1,
      Block.scoped_of_check hAnd.2⟩

theorem FunList.scoped_of_check :
    ∀ {functions : List Functions.FunDef},
      FunList.scoped? functions = true →
        Functions.FunList.Scoped functions
  | [], _hCheck => by
      trivial
  | fn :: rest, hCheck => by
      have hAnd :
          FunDef.scoped? fn = true ∧ FunList.scoped? rest = true :=
        by simpa [FunList.scoped?] using hCheck
      exact
        ⟨FunDef.scoped_of_check hAnd.1,
          FunList.scoped_of_check hAnd.2⟩

theorem Program.scoped_of_check {program : Functions.Program}
    (hCheck : Program.scoped? program = true) :
    program.Scoped := by
  have hAnd :
      FunList.scoped? program.functions = true ∧
        Block.scoped? [] program.body = true :=
    by simpa [Program.scoped?] using hCheck
  exact
    ⟨FunList.scoped_of_check hAnd.1,
      Block.scoped_of_check hAnd.2⟩

theorem Program.sourceAccepted_of_check {program : Functions.Program}
    (hCheck : Program.sourceAccepted? program = true) :
    program.SourceAccepted := by
  have hAnd :
      Program.wf? program = true ∧ Program.scoped? program = true :=
    by simpa [Program.sourceAccepted?] using hCheck
  exact
    ⟨Program.wf_of_check hAnd.1,
      Program.scoped_of_check hAnd.2⟩

end SourceAcceptedCheck


namespace CompilerFacts

theorem exprSeq_cast_usesCallCreate {n m : Nat} (h : n = m)
    (exprs : Locals.ExprSeq n)
    (hExprs : exprs.usesCallCreate = false) :
    Locals.ExprSeq.usesCallCreate
      (cast (congrArg Locals.ExprSeq h) exprs) = false := by
  cases h
  exact hExprs

theorem Locals.StmtList.usesCallCreate_append_eq_false
    {left right : List Locals.Stmt}
    (hLeft : Locals.StmtList.usesCallCreate left = false)
    (hRight : Locals.StmtList.usesCallCreate right = false) :
    Locals.StmtList.usesCallCreate (left ++ right) = false := by
  induction left with
  | nil => simpa using hRight
  | cons head tail ih =>
      have hParts :
          head.usesCallCreate = false ∧
            Locals.StmtList.usesCallCreate tail = false := by
        simpa [Locals.StmtList.usesCallCreate] using hLeft
      simp [Locals.StmtList.usesCallCreate, hParts.1, ih hParts.2]

theorem Lower.returnExprs_noCallCreate (names : List Name) :
    (Lower.returnExprs names).usesCallCreate = false := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      unfold Lower.returnExprs
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons (.var name) (Lower.returnExprs rest)
      have hLen : 1 + rest.length = rest.length + 1 := by omega
      change Locals.ExprSeq.usesCallCreate
        (cast (congrArg Locals.ExprSeq hLen) exprs) = false
      apply exprSeq_cast_usesCallCreate hLen
      change
        (Locals.ExprSeq.cons (.var name)
          (Lower.returnExprs rest)).usesCallCreate = false
      simp [Locals.ExprSeq.usesCallCreate, Locals.Expr.usesCallCreate, ih]

theorem Lower.pushReturns_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate (Lower.pushReturns names) = false := by
  cases names with
  | nil => rfl
  | cons name rest =>
      simp [Lower.pushReturns, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, Lower.returnExprs_noCallCreate]

theorem Lower.initReturns_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate (Lower.initReturns names) = false := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp [Lower.initReturns, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, Locals.Expr.usesCallCreate, ih]

theorem Lower.assignReturnedTopsRev_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate
      (Lower.assignReturnedTopsRev names) = false := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp [Lower.assignReturnedTopsRev, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, ih]

theorem Lower.assignReturnedTops_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate
      (Lower.assignReturnedTops names) = false := by
  simpa [Lower.assignReturnedTops] using
    Lower.assignReturnedTopsRev_noCallCreate names.reverse

theorem Lower.argExprs_noCallCreate :
    ∀ {args : List (Expr 1)},
      ExprList.usesCallCreate args = false →
        (Lower.argExprs args).usesCallCreate = false
  | [], _hArgs => by rfl
  | arg :: rest, hArgs => by
      have hParts :
          arg.usesCallCreate = false ∧
            ExprList.usesCallCreate rest = false := by
        simpa [ExprList.usesCallCreate] using hArgs
      have hRest := Lower.argExprs_noCallCreate hParts.2
      unfold Lower.argExprs
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons arg (Lower.argExprs rest)
      have hLen : 1 + rest.length = rest.length + 1 := by omega
      change Locals.ExprSeq.usesCallCreate
        (cast (congrArg Locals.ExprSeq hLen) exprs) = false
      apply exprSeq_cast_usesCallCreate hLen
      change
        (Locals.ExprSeq.cons arg (Lower.argExprs rest)).usesCallCreate = false
      simp [Locals.ExprSeq.usesCallCreate, hParts.1, hRest]

theorem Lower.evalArgs_noCallCreate :
    ∀ {args : List (Expr 1)},
      ExprList.usesCallCreate args = false →
        Locals.StmtList.usesCallCreate (Lower.evalArgs args) = false
  | [], _hArgs => by rfl
  | arg :: rest, hArgs => by
      have hSeq := Lower.argExprs_noCallCreate hArgs
      simp [Lower.evalArgs, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, hSeq]

set_option linter.unusedSimpArgs false in
mutual
  theorem Block.toLocals_noCallCreate (returns : List Name)
      (block : Block) (hBlock : block.usesCallCreate = false) :
      (Block.toLocals returns block).usesCallCreate = false := by
    cases block with
    | mk stmts => exact StmtList.toLocals_noCallCreate returns stmts hBlock

  theorem Stmt.toLocals_noCallCreate (returns : List Name)
      (stmt : Stmt) (hStmt : stmt.usesCallCreate = false) :
      Locals.StmtList.usesCallCreate (Stmt.toLocals returns stmt) = false := by
    cases stmt with
    | expr expr =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt
    | let_ name value =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt
    | assign name value =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt
    | block body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        have hLower := Block.toLocals_noCallCreate returns body hBody
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hLower]
    | if_ cond body =>
        have hParts :
            cond.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        have hBody := Block.toLocals_noCallCreate returns body hParts.2
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hParts.1, hBody]
    | switch scrutinee cases defaultBody =>
        have hParts :
            scrutinee.usesCallCreate = false ∧
              CaseList.usesCallCreate cases = false ∧
                Default.usesCallCreate defaultBody = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        have hCases := CaseList.toLocals_noCallCreate returns cases hParts.2.1
        have hDefault :=
          Default.toLocals_noCallCreate returns defaultBody hParts.2.2
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hParts.1, hCases, hDefault]
    | for_ init cond post body =>
        have hParts :
            init.usesCallCreate = false ∧ cond.usesCallCreate = false ∧
              post.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        have hInit := Block.toLocals_noCallCreate returns init hParts.1
        have hPost := Block.toLocals_noCallCreate returns post hParts.2.2.1
        have hBody := Block.toLocals_noCallCreate returns body hParts.2.2.2
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hInit, hParts.2.1, hPost, hBody]
    | brk => rfl
    | cont => rfl
    | leave =>
        exact
          Locals.StmtList.usesCallCreate_append_eq_false
            (Lower.pushReturns_noCallCreate returns)
            (by simp [Locals.StmtList.usesCallCreate,
              Locals.Stmt.usesCallCreate])
    | call targets functionName args =>
        have hArgs : ExprList.usesCallCreate args = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        have hEval := Lower.evalArgs_noCallCreate hArgs
        have hCall :
            Locals.StmtList.usesCallCreate
              [Locals.Stmt.call functionName] = false := by
          simp [Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate]
        exact
          Locals.StmtList.usesCallCreate_append_eq_false
            (left := Lower.evalArgs args ++ [Locals.Stmt.call functionName])
            (right := Lower.assignReturnedTops targets)
            (Locals.StmtList.usesCallCreate_append_eq_false
              (left := Lower.evalArgs args)
              (right := [Locals.Stmt.call functionName]) hEval hCall)
            (Lower.assignReturnedTops_noCallCreate targets)
    | terminal kind => rfl
    | terminalArgs kind args =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt

  theorem StmtList.toLocals_noCallCreate (returns : List Name)
      (stmts : List Stmt) (hStmts : StmtList.usesCallCreate stmts = false) :
      Locals.StmtList.usesCallCreate
        (StmtList.toLocals returns stmts) = false := by
    cases stmts with
    | nil => rfl
    | cons stmt rest =>
        have hParts :
            stmt.usesCallCreate = false ∧
              StmtList.usesCallCreate rest = false := by
          simpa [StmtList.usesCallCreate] using hStmts
        have hStmt := Stmt.toLocals_noCallCreate returns stmt hParts.1
        have hRest := StmtList.toLocals_noCallCreate returns rest hParts.2
        exact Locals.StmtList.usesCallCreate_append_eq_false hStmt hRest

  theorem CaseList.toLocals_noCallCreate (returns : List Name)
      (cases : List (Word × Block))
      (hCases : CaseList.usesCallCreate cases = false) :
      Locals.CaseList.usesCallCreate
        (CaseList.toLocals returns cases) = false := by
    cases cases with
    | nil => rfl
    | cons head rest =>
        cases head with
        | mk value body =>
            have hParts :
                body.usesCallCreate = false ∧
                  CaseList.usesCallCreate rest = false := by
              simpa [CaseList.usesCallCreate] using hCases
            have hBody := Block.toLocals_noCallCreate returns body hParts.1
            have hRest := CaseList.toLocals_noCallCreate returns rest hParts.2
            simp [CaseList.toLocals, Locals.CaseList.usesCallCreate,
              hBody, hRest]

  theorem Default.toLocals_noCallCreate (returns : List Name)
      (defaultBody : Option Block)
      (hDefault : Default.usesCallCreate defaultBody = false) :
      Locals.Default.usesCallCreate
        (Default.toLocals returns defaultBody) = false := by
    cases defaultBody with
    | none => rfl
    | some body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Default.usesCallCreate] using hDefault
        exact Block.toLocals_noCallCreate returns body hBody
end

theorem FunDef.toLocalsProc_noCallCreate (fn : FunDef)
    (hFn : fn.usesCallCreate = false) :
    (fn.toLocalsProc).usesCallCreate = false := by
  rcases fn with ⟨name, params, returns, body⟩
  have hBody := StmtList.toLocals_noCallCreate returns body.stmts
    (by
      cases body with
      | mk stmts =>
          simpa [FunDef.usesCallCreate, Block.usesCallCreate] using hFn)
  have hInit := Lower.initReturns_noCallCreate returns
  have hPush := Lower.pushReturns_noCallCreate returns
  simp [FunDef.toLocalsProc, Locals.Proc.usesCallCreate,
    Locals.Block.usesCallCreate]
  exact Locals.StmtList.usesCallCreate_append_eq_false hInit
    (Locals.StmtList.usesCallCreate_append_eq_false hBody hPush)

theorem FunList.toLocalsProcs_noCallCreate :
    ∀ {fns : List FunDef},
      FunList.usesCallCreate fns = false →
        Locals.ProcList.usesCallCreate
          (FunList.toLocalsProcs fns) = false
  | [], _hFns => by rfl
  | fn :: rest, hFns => by
      have hParts :
          fn.usesCallCreate = false ∧
            FunList.usesCallCreate rest = false := by
        simpa [FunList.usesCallCreate] using hFns
      have hFn := FunDef.toLocalsProc_noCallCreate fn hParts.1
      have hRest := FunList.toLocalsProcs_noCallCreate hParts.2
      simp [FunList.toLocalsProcs, Locals.ProcList.usesCallCreate,
        hFn, hRest]

theorem Program.toLocals_noCallCreate (program : Program)
    (hProgram : program.usesCallCreate = false) :
    program.toLocals.usesCallCreate = false := by
  have hParts :
      FunList.usesCallCreate program.functions = false ∧
        program.body.usesCallCreate = false := by
    simpa [Program.usesCallCreate] using hProgram
  have hProcs := FunList.toLocalsProcs_noCallCreate hParts.1
  have hBody := Block.toLocals_noCallCreate [] program.body hParts.2
  simp [Program.toLocals, Locals.Program.usesCallCreate, hProcs, hBody]

end CompilerFacts

namespace Inline

namespace Program

def toLocals? (program : Functions.Program) : Option Locals.Program :=
  Functions.Program.toLocals? program

def toExpressions? (program : Functions.Program) : Option Expressions.Program :=
  Functions.Program.toExpressions? program

def compile? (program : Functions.Program) :
    Option Assembly.TargetProgram :=
  Functions.Program.compile? program

def compileExecutable? (program : Functions.Program) :
    Option Assembly.TargetProgram :=
  Functions.Program.compileExecutable? program

theorem compileExecutable?_eq_compile? (program : Functions.Program) :
    compileExecutable? program = compile? program := by
  simp [compileExecutable?, compile?,
    Functions.Program.compileExecutable?_eq_compile?]

def Accepted (program : Functions.Program) : Prop :=
  Functions.Program.Accepted program

def SourceAccepted (program : Functions.Program) : Prop :=
  Functions.Program.SourceAccepted program

theorem sourceAccepted_of_accepted {program : Functions.Program}
    (hAccepted : Accepted program) :
    SourceAccepted program :=
  Functions.Program.sourceAccepted_of_accepted hAccepted

end Program

end Inline

end Functions
end EvmCompiler
