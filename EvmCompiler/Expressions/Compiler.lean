import EvmCompiler.Expressions.Syntax
import EvmCompiler.Structured.TypedCfgCompiler
import EvmCompiler.Assembly.Accepted

namespace EvmCompiler
namespace Expressions

mutual
  def Expr.usesCallCreate {results : Nat} : Expr results → Bool
    | .lit _value => false
    | .code code => code.usesCallCreate
    | .prim op args => ExprSeq.usesCallCreate args || op.toPrimOp.isCallCreate

  def ExprSeq.usesCallCreate {results : Nat} : ExprSeq results → Bool
    | .nil => false
    | .cons head tail => head.usesCallCreate || tail.usesCallCreate
end

mutual
  def Block.usesCallCreate : Block → Bool
    | ⟨stmts⟩ => StmtList.usesCallCreate stmts

  def Stmt.usesCallCreate : Stmt → Bool
    | .code code => code.usesCallCreate
    | .expr expr => expr.usesCallCreate
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

namespace Proc

def usesCallCreate (proc : Proc) : Bool :=
  proc.body.usesCallCreate

end Proc

namespace ProcList

def usesCallCreate : List Proc → Bool
  | [] => false
  | proc :: rest => proc.usesCallCreate || usesCallCreate rest

end ProcList

namespace Program

def usesCallCreate (program : Program) : Bool :=
  ProcList.usesCallCreate program.procs || program.body.usesCallCreate

end Program

mutual
  def Expr.compile {results : Nat} : Expr results → Structured.Code
    | .lit value => [Structured.BasicInstr.push value]
    | .code code => code
    | .prim op args => ExprSeq.compile args ++ [Structured.BasicInstr.op op]

  def ExprSeq.compile {results : Nat} : ExprSeq results → Structured.Code
    | .nil => []
    | .cons head tail => Expr.compile head ++ ExprSeq.compile tail
end

mutual
  def Block.toStructured : Block → Structured.Block
    | ⟨stmts⟩ => { stmts := StmtList.toStructured stmts }

  def Stmt.toStructured : Stmt → Structured.Stmt
    | .code code => .code code
    | .expr expr => .code expr.compile
    | .if_ cond body => .if_ cond.compile body.toStructured
    | .switch scrutinee cases defaultBody =>
        .switch scrutinee.compile (CaseList.toStructured cases)
          (Default.toStructured defaultBody)
    | .for_ init cond post body =>
        .for_ init.toStructured cond.compile post.toStructured body.toStructured
    | .brk => .brk
    | .cont => .cont
    | .leave => .leave
    | .call name => .call name
    | .terminal kind => .terminal kind

  def StmtList.toStructured : List Stmt → List Structured.Stmt
    | [] => []
    | stmt :: rest => stmt.toStructured :: StmtList.toStructured rest

  def CaseList.toStructured :
      List (Word × Block) → List (Word × Structured.Block)
    | [] => []
    | (value, body) :: rest =>
        (value, body.toStructured) :: CaseList.toStructured rest

  def Default.toStructured : Option Block → Option Structured.Block
    | none => none
    | some body => some body.toStructured
end

theorem StmtList.toStructured_append
    (left right : List Stmt) :
    StmtList.toStructured (left ++ right) =
      StmtList.toStructured left ++ StmtList.toStructured right := by
  induction left with
  | nil => rfl
  | cons stmt rest ih =>
      simp [StmtList.toStructured, ih]

namespace Proc

def toStructured (proc : Proc) : Structured.Proc where
  name := proc.name
  argc := proc.argc
  retc := proc.retc
  body := proc.body.toStructured

@[simp] theorem toStructured_name (proc : Proc) :
    proc.toStructured.name = proc.name := rfl

end Proc

namespace ProcList

def toStructured : List Proc → List Structured.Proc
  | [] => []
  | proc :: rest => proc.toStructured :: toStructured rest

theorem mem_toStructured
    {proc : Proc} {procs : List Proc}
    (hMem : proc ∈ procs) :
    proc.toStructured ∈ toStructured procs := by
  induction procs with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      rcases List.mem_cons.mp hMem with hHead | hRest
      · subst proc
        simp [toStructured]
      · exact
          List.mem_cons_of_mem head.toStructured
            (ih hRest)

theorem lookup_toStructured_of_mem
    {proc : Proc} {procs : List Proc}
    (hUnique :
      Structured.ProcList.NamesUnique (toStructured procs))
    (hMem : proc ∈ procs) :
    Structured.ProcList.lookup? proc.name (toStructured procs) =
      some proc.toStructured :=
  Structured.ProcList.lookup?_eq_some_of_mem
    hUnique (mem_toStructured hMem) rfl

end ProcList

namespace Program

def toStructured (program : Program) : Structured.Program where
  procs := ProcList.toStructured program.procs
  body := program.body.toStructured

structure TypedCompileArtifact where
  cfg : TypedCfg.Program
  assembly : Assembly.Program
  target : Assembly.TargetProgram
  certificate : TypedCfg.ProgramCert

def compileTypedArtifact? (program : Program) :
    Option TypedCompileArtifact := do
  let cfg ←
    Structured.TypedCfgCompiler.compile? program.toStructured
  let certified ← cfg.compileCertified?
  let target ← Assembly.compileExecutable? certified.target
  some
    { cfg := cfg
      assembly := certified.target
      target := target
      certificate := certified.metadata }

def compileTypedExecutable? (program : Program) :
    Option Assembly.TargetProgram :=
  (compileTypedArtifact? program).map TypedCompileArtifact.target

theorem compileTypedArtifact?_certificateValid
    {program : Program} {artifact : TypedCompileArtifact}
    (hCompile : compileTypedArtifact? program = some artifact) :
    TypedCfg.Program.ProgramCert.ValidFor artifact.certificate
      artifact.cfg := by
  unfold compileTypedArtifact? at hCompile
  cases hCfg :
      Structured.TypedCfgCompiler.compile? program.toStructured with
  | none =>
      simp [hCfg] at hCompile
  | some cfg =>
      simp [hCfg] at hCompile
      cases hCertified : cfg.compileCertified? with
      | none =>
          simp [hCertified] at hCompile
      | some certified =>
          simp [hCertified] at hCompile
          cases hTarget :
              Assembly.compileExecutable? certified.target with
          | none =>
              simp [hTarget] at hCompile
          | some target =>
              simp [hTarget] at hCompile
              cases hCompile
              exact
                ⟨TypedCfg.Program.compileCertified?_wellTyped hCertified,
                  TypedCfg.Program.compileCertified?_certificate hCertified⟩

def compile? (program : Program) : Option Assembly.TargetProgram :=
  compileTypedExecutable? program

def compileExecutable? (program : Program) : Option Assembly.TargetProgram :=
  compileTypedExecutable? program

theorem compileExecutable?_eq_compile? (program : Program) :
    compileExecutable? program = compile? program := rfl

def Accepted (program : Program) : Prop :=
  ∃ artifact, compileTypedArtifact? program = some artifact

def SourceAccepted (program : Program) : Prop :=
  program.WF

end Program

namespace CompilerFacts

mutual
  theorem Expr.compile_usesCallCreate {results : Nat} (expr : Expr results) :
      Structured.Code.usesCallCreate expr.compile = expr.usesCallCreate := by
    exact Expr.rec
      (motive_1 := fun results expr =>
        Structured.Code.usesCallCreate expr.compile = expr.usesCallCreate)
      (motive_2 := fun results exprs =>
        Structured.Code.usesCallCreate exprs.compile = exprs.usesCallCreate)
      (fun value => by
        simp [Expr.compile, Expr.usesCallCreate,
          Structured.Code.usesCallCreate,
          Structured.BasicInstr.usesCallCreate])
      (fun code => by
        rfl)
      (fun op args hArgs => by
        simp [Expr.compile, Expr.usesCallCreate,
          Structured.Code.usesCallCreate,
          Structured.BasicInstr.usesCallCreate]
        change
          (Structured.Code.usesCallCreate args.compile ||
              op.toPrimOp.isCallCreate) =
            (args.usesCallCreate || op.toPrimOp.isCallCreate)
        rw [hArgs])
      (by rfl)
      (fun head tail hHead hTail => by
        simp [ExprSeq.compile, ExprSeq.usesCallCreate,
          Structured.Code.usesCallCreate]
        change
          (Structured.Code.usesCallCreate head.compile ||
              Structured.Code.usesCallCreate tail.compile) =
            (head.usesCallCreate || tail.usesCallCreate)
        rw [hHead, hTail])
      expr

  theorem ExprSeq.compile_usesCallCreate {results : Nat}
      (exprs : ExprSeq results) :
      Structured.Code.usesCallCreate exprs.compile = exprs.usesCallCreate := by
    exact ExprSeq.rec
      (motive_1 := fun results expr =>
        Structured.Code.usesCallCreate expr.compile = expr.usesCallCreate)
      (motive_2 := fun results exprs =>
        Structured.Code.usesCallCreate exprs.compile = exprs.usesCallCreate)
      (fun value => by
        simp [Expr.compile, Expr.usesCallCreate,
          Structured.Code.usesCallCreate,
          Structured.BasicInstr.usesCallCreate])
      (fun code => by
        rfl)
      (fun op args hArgs => by
        simp [Expr.compile, Expr.usesCallCreate,
          Structured.Code.usesCallCreate,
          Structured.BasicInstr.usesCallCreate]
        change
          (Structured.Code.usesCallCreate args.compile ||
              op.toPrimOp.isCallCreate) =
            (args.usesCallCreate || op.toPrimOp.isCallCreate)
        rw [hArgs])
      (by rfl)
      (fun head tail hHead hTail => by
        simp [ExprSeq.compile, ExprSeq.usesCallCreate,
          Structured.Code.usesCallCreate]
        change
          (Structured.Code.usesCallCreate head.compile ||
              Structured.Code.usesCallCreate tail.compile) =
            (head.usesCallCreate || tail.usesCallCreate)
        rw [hHead, hTail])
      exprs
end

set_option linter.unusedSimpArgs false in
theorem Block.toStructured_usesCallCreate (block : Block) :
    block.toStructured.usesCallCreate = block.usesCallCreate := by
  exact Block.rec
    (motive_1 := fun block =>
      block.toStructured.usesCallCreate = block.usesCallCreate)
    (motive_2 := fun stmt =>
      stmt.toStructured.usesCallCreate = stmt.usesCallCreate)
    (motive_3 := fun stmts =>
      Structured.StmtList.usesCallCreate (StmtList.toStructured stmts) =
        StmtList.usesCallCreate stmts)
    (motive_4 := fun cases =>
      Structured.CaseList.usesCallCreate (CaseList.toStructured cases) =
        CaseList.usesCallCreate cases)
    (motive_5 := fun defaultBody =>
      Structured.Default.usesCallCreate (Default.toStructured defaultBody) =
        Default.usesCallCreate defaultBody)
    (motive_6 := fun pair =>
      pair.2.toStructured.usesCallCreate = pair.2.usesCallCreate)
    (fun _stmts hStmts => hStmts)
    (fun _code => rfl)
    (fun expr => by
      simpa [Stmt.toStructured, Stmt.usesCallCreate] using
        Expr.compile_usesCallCreate expr)
    (fun cond body hBody => by
      simp [Stmt.toStructured, Stmt.usesCallCreate,
        Structured.Stmt.usesCallCreate, Expr.compile_usesCallCreate cond,
        hBody])
    (fun scrutinee cases defaultBody hCases hDefault => by
      simp [Stmt.toStructured, Stmt.usesCallCreate,
        Structured.Stmt.usesCallCreate, Expr.compile_usesCallCreate scrutinee,
        hCases, hDefault])
    (fun init cond post body hInit hPost hBody => by
      simp [Stmt.toStructured, Stmt.usesCallCreate,
        Structured.Stmt.usesCallCreate, Expr.compile_usesCallCreate cond,
        hInit, hPost, hBody])
    (by simp [Stmt.toStructured, Stmt.usesCallCreate,
      Structured.Stmt.usesCallCreate])
    (by simp [Stmt.toStructured, Stmt.usesCallCreate,
      Structured.Stmt.usesCallCreate])
    (by simp [Stmt.toStructured, Stmt.usesCallCreate,
      Structured.Stmt.usesCallCreate])
    (fun _name => by
      simp [Stmt.toStructured, Stmt.usesCallCreate,
        Structured.Stmt.usesCallCreate])
    (fun _kind => by
      simp [Stmt.toStructured, Stmt.usesCallCreate,
        Structured.Stmt.usesCallCreate])
    (by rfl)
    (fun stmt rest hStmt hRest => by
      simp [StmtList.toStructured, StmtList.usesCallCreate,
        Structured.StmtList.usesCallCreate, hStmt, hRest])
    (by rfl)
    (fun head rest hHead hRest => by
      rcases head with ⟨value, body⟩
      simp [CaseList.toStructured, CaseList.usesCallCreate,
        Structured.CaseList.usesCallCreate, hHead, hRest])
    (by rfl)
    (fun body hBody => by
      simp [Default.toStructured, Default.usesCallCreate,
        Structured.Default.usesCallCreate, hBody])
    (fun _value _body hBody => hBody)
    block

theorem StmtList.toStructured_usesCallCreate (stmts : List Stmt) :
    Structured.StmtList.usesCallCreate (StmtList.toStructured stmts) =
      StmtList.usesCallCreate stmts := by
  have h := Block.toStructured_usesCallCreate { stmts := stmts }
  simpa [Block.toStructured, Block.usesCallCreate] using h

theorem CaseList.toStructured_usesCallCreate
    (cases : List (Word × Block)) :
    Structured.CaseList.usesCallCreate (CaseList.toStructured cases) =
      CaseList.usesCallCreate cases := by
  induction cases with
  | nil =>
      rfl
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      simp [CaseList.toStructured, CaseList.usesCallCreate,
        Structured.CaseList.usesCallCreate,
        Block.toStructured_usesCallCreate body, ih]

theorem Default.toStructured_usesCallCreate (defaultBody : Option Block) :
    Structured.Default.usesCallCreate (Default.toStructured defaultBody) =
      Default.usesCallCreate defaultBody := by
  cases defaultBody with
  | none =>
      rfl
  | some body =>
      simp [Default.toStructured, Default.usesCallCreate,
        Structured.Default.usesCallCreate,
        Block.toStructured_usesCallCreate body]

theorem Proc.toStructured_usesCallCreate (proc : Proc) :
    proc.toStructured.usesCallCreate = proc.usesCallCreate := by
  simp [Proc.toStructured, Proc.usesCallCreate, Structured.Proc.usesCallCreate,
    Block.toStructured_usesCallCreate proc.body]

theorem ProcList.toStructured_usesCallCreate (procs : List Proc) :
    Structured.ProcList.usesCallCreate (ProcList.toStructured procs) =
      ProcList.usesCallCreate procs := by
  induction procs with
  | nil =>
      rfl
  | cons proc rest ih =>
      simp [ProcList.toStructured, ProcList.usesCallCreate,
        Structured.ProcList.usesCallCreate,
        Proc.toStructured_usesCallCreate proc, ih]

theorem Program.toStructured_usesCallCreate (program : Program) :
    program.toStructured.usesCallCreate = program.usesCallCreate := by
  simp [Program.toStructured, Program.usesCallCreate,
    Structured.Program.usesCallCreate,
    ProcList.toStructured_usesCallCreate program.procs,
    Block.toStructured_usesCallCreate program.body]

end CompilerFacts

end Expressions
end EvmCompiler
