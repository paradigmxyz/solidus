import EvmCompiler.Locals.SourceSemantics
import EvmCompiler.Locals.StackModel
import EvmCompiler.Expressions.Compiler
import EvmCompiler.Structured.EffectSemantics

namespace EvmCompiler
namespace Locals

mutual
  def Expr.usesCallCreate {results : Nat} : Expr results → Bool
    | .lit _value => false
    | .var _name => false
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
    | .expr expr => expr.usesCallCreate
    | .exprs exprs => exprs.usesCallCreate
    | .let_ _name value => value.usesCallCreate
    | .assign _name value => value.usesCallCreate
    | .assignTop _name => false
    | .assignTopWithOffset _offset _name => false
    | .promoteName _name => false
    | .cleanupTo _targetLayout => false
    | .block body => body.usesCallCreate
    | .if_ cond body => cond.usesCallCreate || body.usesCallCreate
    | .switch scrutinee cases defaultBody =>
        scrutinee.usesCallCreate || CaseList.usesCallCreate cases ||
          Default.usesCallCreate defaultBody
    | .for_ init cond post body =>
        init.usesCallCreate || cond.usesCallCreate || post.usesCallCreate ||
          body.usesCallCreate
    | .brk | .cont | .leave | .call _ | .terminal _ => false
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

def codeStmt (code : Structured.Code) : List Expressions.Stmt :=
  [Expressions.Stmt.code code]

def bindLocals (offset : Nat) (layout : Layout) : Structured.Code :=
  [Structured.BasicInstr.bindLocals offset layout]

theorem bindLocals_noCallCreate (offset : Nat) (layout : Layout) :
    (bindLocals offset layout).usesCallCreate = false := by
  simp [bindLocals, Structured.Code.usesCallCreate,
    Structured.BasicInstr.usesCallCreate]

def finishTo (final : Ctx) (targetDepth : Nat)
    (stmts : List Expressions.Stmt) :
    Option Expressions.Block := do
  let cleanup ← final.cleanupTo? targetDepth
  some { stmts := stmts ++ codeStmt cleanup }

def finishToPreserving (final : Ctx) (preserve targetDepth : Nat)
    (stmts : List Expressions.Stmt) :
    Option Expressions.Block := do
  let cleanup ← final.cleanupToPreserving? preserve targetDepth
  some { stmts := stmts ++ codeStmt cleanup }

def finishScoped (outer final : Ctx) (stmts : List Expressions.Stmt) :
    Option Expressions.Block := do
  let cleanup ← final.cleanupTo? outer.layout.length
  some { stmts := stmts ++ codeStmt cleanup }

set_option maxHeartbeats 800000 in
mutual
  def Expr.compileCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (expr : Expr results) : Option Structured.Code :=
    match expr with
    | .lit value =>
        some [Structured.BasicInstr.push value]
    | .var name => do
        let depth ← Layout.lookupDepth? name ctx.layout
        let op ← StackOp.dup? (offset + depth)
        some [Structured.BasicInstr.op op]
    | .code code =>
        some code
    | .prim op args => do
        let code ← ExprSeq.compileCode ctx offset args
        some (code ++ [Structured.BasicInstr.op op])

  def ExprSeq.compileCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (exprs : ExprSeq results) : Option Structured.Code :=
    match exprs with
    | .nil => some []
    | .cons (left := left) head tail => do
        let headCode ← Expr.compileCode ctx offset head
        let tailCode ← ExprSeq.compileCode ctx (offset + left) tail
        some (headCode ++ tailCode)
end

theorem ExprSeq.compileCode_cast
    {left right : Nat} (h : left = right)
    (ctx : Ctx) (offset : Nat) (exprs : ExprSeq left) :
    ExprSeq.compileCode ctx offset (h ▸ exprs) =
      ExprSeq.compileCode ctx offset exprs := by
  cases h
  rfl

theorem ExprSeq.compileCode_eqMpr
    {left right : Nat} (h : left = right)
    (ctx : Ctx) (offset : Nat) (exprs : ExprSeq right) :
    ExprSeq.compileCode ctx offset
        (Eq.mpr (congrArg ExprSeq h) exprs) =
      ExprSeq.compileCode ctx offset exprs := by
  cases h
  rfl

namespace Expr

def compile {results : Nat} (ctx : Ctx) (expr : Expr results) :
    Option (Expressions.Expr results) := do
  let code ← Expr.compileCode ctx 0 expr
  some (Expressions.Expr.code code)

end Expr

set_option maxHeartbeats 800000 in
mutual
  def Block.compileOpen (ctx : Ctx) (block : Block) :
      Option (List Expressions.Stmt × Ctx) :=
    match block with
    | ⟨[]⟩ => some ([], ctx)
    | ⟨stmt :: rest⟩ => do
        let (stmtCode, ctx') ← Stmt.compile ctx stmt
        let (restCode, ctx'') ← Block.compileOpen ctx' { stmts := rest }
        some (stmtCode ++ restCode, ctx'')

  def Stmt.compile (ctx : Ctx) :
      Stmt → Option (List Expressions.Stmt × Ctx)
    | .expr expr => do
        let code ← Expr.compileCode ctx 0 expr
        some (codeStmt code, ctx)
    | .exprs exprs => do
        let code ← ExprSeq.compileCode ctx 0 exprs
        some (codeStmt code, ctx)
    | .let_ name value => do
        let code ← Expr.compileCode ctx 0 value
        let layout := name :: ctx.layout
        some (codeStmt (code ++ bindLocals 0 layout), ctx.withLayout layout)
    | .assign name value => do
        let depth ← Layout.lookupDepth? name ctx.layout
        let valueCode ← Expr.compileCode ctx 0 value
        let swapOp ← StackOp.swap? depth
        let code :=
          valueCode ++
            [Structured.BasicInstr.op swapOp, Structured.BasicInstr.op .pop]
        some (codeStmt (code ++ bindLocals 0 ctx.layout), ctx)
    | .assignTop name => do
        let depth ← Layout.lookupDepth? name ctx.layout
        let swapOp ← StackOp.swap? depth
        let code := [Structured.BasicInstr.op swapOp, Structured.BasicInstr.op .pop]
        some (codeStmt (code ++ bindLocals 0 ctx.layout), ctx)
    | .assignTopWithOffset offset name => do
        let depth ← Layout.lookupDepth? name ctx.layout
        let swapOp ← StackOp.swap? (offset + depth)
        let code := [Structured.BasicInstr.op swapOp, Structured.BasicInstr.op .pop]
        some (codeStmt (code ++ bindLocals offset ctx.layout), ctx)
    | .promoteName name => do
        let (code, promoted) ← ctx.promoteNameStackOnly? name
        some (codeStmt code, ctx.withLayout promoted)
    | .cleanupTo targetLayout => do
        if targetLayout =
            ctx.layout.drop (ctx.layout.length - targetLayout.length) then
          let cleanup ← ctx.cleanupTo? targetLayout.length
          some (codeStmt cleanup, ctx.withLayout targetLayout)
        else
          none
    | .block body => do
        let (bodyCode, bodyCtx) ← Block.compileOpen ctx body
        let lowerBlock ← finishScoped ctx bodyCtx bodyCode
        some (lowerBlock.stmts, ctx)
    | .if_ cond body => do
        let condExpr ← Expr.compile ctx cond
        let (bodyCode, bodyCtx) ← Block.compileOpen ctx body
        let lowerBody ← finishScoped ctx bodyCtx bodyCode
        some ([Expressions.Stmt.if_ condExpr lowerBody], ctx)
    | .switch scrutinee cases defaultBody => do
        let scrutineeExpr ← Expr.compile ctx scrutinee
        let lowerCases ← CaseList.compile ctx cases
        let lowerDefault ← Default.compile ctx defaultBody
        some ([Expressions.Stmt.switch scrutineeExpr lowerCases lowerDefault], ctx)
    | .for_ init cond post body => do
        let initBase := ctx.withoutLoopControl
        let (initCode, initCtx) ← Block.compileOpen initBase init
        let condExpr ← Expr.compile initCtx cond
        let postBase := initCtx.withoutLoopControl
        let (postCode, postCtx) ← Block.compileOpen postBase post
        let lowerPost ← finishScoped postBase postCtx postCode
        let bodyBase := initCtx.withLoopControl initCtx.layout.length
        let (bodyCode, bodyCtx) ← Block.compileOpen bodyBase body
        let lowerBody ← finishScoped bodyBase bodyCtx bodyCode
        let loopStmt :=
          Expressions.Stmt.for_ { stmts := initCode } condExpr lowerPost lowerBody
        let cleanup ← initCtx.cleanupTo? ctx.layout.length
        some ([loopStmt] ++ codeStmt cleanup, ctx)
    | .brk => do
        let target ← ctx.breakDepth?
        let cleanup ← ctx.cleanupTo? target
        some (codeStmt cleanup ++ [Expressions.Stmt.brk], ctx)
    | .cont => do
        let target ← ctx.continueDepth?
        let cleanup ← ctx.cleanupTo? target
        some (codeStmt cleanup ++ [Expressions.Stmt.cont], ctx)
    | .leave => do
        let target ← ctx.leaveDepth?
        let cleanup ← ctx.cleanupToPreserving? ctx.leaveRetc target
        some (codeStmt cleanup ++ [Expressions.Stmt.leave], ctx)
    | .call name =>
        some ([Expressions.Stmt.call name], ctx)
    | .terminal kind =>
        some (codeStmt ctx.cleanupAll ++ [Expressions.Stmt.terminal kind], ctx)
    | .terminalArgs kind args => do
        let code ← ExprSeq.compileCode ctx 0 args
        some (codeStmt code ++ [Expressions.Stmt.terminal kind], ctx)

  def CaseList.compile (ctx : Ctx) :
      List (Word × Block) → Option (List (Word × Expressions.Block))
    | [] => some []
    | (value, body) :: rest => do
        let (bodyCode, bodyCtx) ← Block.compileOpen ctx body
        let lowerBody ← finishScoped ctx bodyCtx bodyCode
        let lowerRest ← CaseList.compile ctx rest
        some ((value, lowerBody) :: lowerRest)

  def Default.compile (ctx : Ctx) :
      Option Block → Option (Option Expressions.Block)
    | none => some none
    | some body => do
        let (bodyCode, bodyCtx) ← Block.compileOpen ctx body
        let lowerBody ← finishScoped ctx bodyCtx bodyCode
        some (some lowerBody)
end

namespace Stmt

/--
Successful compilation of a Locals lexical block exposes the adjacent open
block compiler and scoped cleanup owned by this pass.
-/
theorem compile_block_components
    {ctx final : Ctx}
    {body : Block}
    {code : List Expressions.Stmt}
    (hCompile :
      Stmt.compile ctx (.block body) = some (code, final)) :
    ∃ bodyCode bodyCtx lowerBody,
      Block.compileOpen ctx body = some (bodyCode, bodyCtx) ∧
      finishScoped ctx bodyCtx bodyCode = some lowerBody ∧
      code = lowerBody.stmts ∧
      final = ctx := by
  cases hBody : Block.compileOpen ctx body with
  | none =>
      simp [Stmt.compile, hBody] at hCompile
  | some result =>
      rcases result with ⟨bodyCode, bodyCtx⟩
      cases hFinish : finishScoped ctx bodyCtx bodyCode with
      | none =>
          simp [Stmt.compile, hBody, hFinish] at hCompile
      | some lowerBody =>
          simp [Stmt.compile, hBody, hFinish] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact ⟨bodyCode, bodyCtx, lowerBody, rfl, hFinish, rfl, rfl⟩

/--
Expression statements never change the Locals compiler context.
-/
theorem compile_expr_final
    {ctx final : Ctx} {results : Nat}
    {expr : Expr results}
    {code : List Expressions.Stmt}
    (hCompile :
      Stmt.compile ctx (.expr expr) = some (code, final)) :
    final = ctx := by
  cases hCode : Expr.compileCode ctx 0 expr with
  | none =>
      simp [Stmt.compile, hCode] at hCompile
  | some result =>
      simp [Stmt.compile, hCode] at hCompile
      exact hCompile.2.symm

/--
Promotion statements change only the Locals layout.
-/
theorem compile_promoteName_final
    {ctx final : Ctx} {name : Name}
    {code : List Expressions.Stmt}
    (hCompile :
      Stmt.compile ctx (.promoteName name) = some (code, final)) :
    ∃ layout, final = ctx.withLayout layout := by
  cases hPromote : ctx.promoteNameStackOnly? name with
  | none =>
      simp [Stmt.compile, hPromote] at hCompile
  | some result =>
      rcases result with ⟨promoteCode, layout⟩
      simp [Stmt.compile, hPromote] at hCompile
      exact ⟨layout, hCompile.2.symm⟩

/--
Successful cleanup compilation exposes the exact target layout installed by
the ordinary Locals compiler.
-/
theorem compile_cleanupTo_components
    {ctx final : Ctx}
    {target : Layout}
    {code : List Expressions.Stmt}
    (hCompile :
      Stmt.compile ctx (.cleanupTo target) = some (code, final)) :
    ∃ cleanup,
      target =
          ctx.layout.drop (ctx.layout.length - target.length) ∧
        ctx.cleanupTo? target.length = some cleanup ∧
        code = codeStmt cleanup ∧
        final = ctx.withLayout target := by
  unfold Stmt.compile at hCompile
  by_cases hTarget :
      target =
        ctx.layout.drop (ctx.layout.length - target.length)
  · rw [if_pos hTarget] at hCompile
    cases hCleanup : ctx.cleanupTo? target.length with
    | none =>
        simp [hCleanup] at hCompile
    | some cleanup =>
        simp [hCleanup] at hCompile
        rcases hCompile with ⟨rfl, rfl⟩
        exact ⟨cleanup, hTarget, rfl, rfl, rfl⟩
  · rw [if_neg hTarget] at hCompile
    contradiction

/--
Successful compilation of a Locals `if` decomposes through the ordinary
condition compiler, open-block compiler, and scoped cleanup.
-/
theorem compile_if_components
    {ctx final : Ctx}
    {cond : Expr 1} {body : Block}
    {code : List Expressions.Stmt}
    (hCompile :
      Stmt.compile ctx (.if_ cond body) = some (code, final)) :
    ∃ condCode bodyCode bodyCtx lowerBody,
      Expr.compileCode ctx 0 cond = some condCode ∧
      Block.compileOpen ctx body = some (bodyCode, bodyCtx) ∧
      finishScoped ctx bodyCtx bodyCode = some lowerBody ∧
      code = [Expressions.Stmt.if_ (.code condCode) lowerBody] ∧
      final = ctx := by
  cases hCond : Expr.compileCode ctx 0 cond with
  | none =>
      simp [Stmt.compile, Expr.compile, hCond] at hCompile
  | some condCode =>
      cases hBody : Block.compileOpen ctx body with
      | none =>
          simp [Stmt.compile, Expr.compile, hCond, hBody] at hCompile
      | some bodyResult =>
          rcases bodyResult with ⟨bodyCode, bodyCtx⟩
          cases hFinish : finishScoped ctx bodyCtx bodyCode with
          | none =>
              simp [Stmt.compile, Expr.compile, hCond, hBody, hFinish]
                at hCompile
          | some lowerBody =>
              simp [Stmt.compile, Expr.compile, hCond, hBody, hFinish]
                at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              exact
                ⟨condCode, bodyCode, bodyCtx, lowerBody,
                  rfl, rfl, hFinish, rfl, rfl⟩

/--
Successful compilation of a Locals `switch` decomposes through the ordinary
scrutinee, case-list, and default compilers.
-/
theorem compile_switch_components
    {ctx final : Ctx}
    {scrutinee : Expr 1}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {code : List Expressions.Stmt}
    (hCompile :
      Stmt.compile ctx (.switch scrutinee cases defaultBody) =
        some (code, final)) :
    ∃ scrutineeCode compiledCases compiledDefault,
      Expr.compileCode ctx 0 scrutinee = some scrutineeCode ∧
      CaseList.compile ctx cases = some compiledCases ∧
      Default.compile ctx defaultBody = some compiledDefault ∧
      code =
        [Expressions.Stmt.switch
          (.code scrutineeCode) compiledCases compiledDefault] ∧
      final = ctx := by
  cases hScrutinee : Expr.compileCode ctx 0 scrutinee with
  | none =>
      simp [Stmt.compile, Expr.compile, hScrutinee] at hCompile
  | some scrutineeCode =>
      cases hCases : CaseList.compile ctx cases with
      | none =>
          simp [Stmt.compile, Expr.compile, hScrutinee, hCases] at hCompile
      | some compiledCases =>
          cases hDefault : Default.compile ctx defaultBody with
          | none =>
              simp [Stmt.compile, Expr.compile, hScrutinee, hCases, hDefault]
                at hCompile
          | some compiledDefault =>
              simp [Stmt.compile, Expr.compile, hScrutinee, hCases, hDefault]
                at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              exact
                ⟨scrutineeCode, compiledCases, compiledDefault,
                  rfl, rfl, rfl, rfl, rfl⟩

/--
Successful compilation of a Locals `for` exposes the ordinary initializer,
condition, scoped post/body, and outer-cleanup compiler components.
-/
theorem compile_for_components
    {ctx final : Ctx}
    {init : Block} {cond : Expr 1} {post body : Block}
    {code : List Expressions.Stmt}
    (hCompile :
      Stmt.compile ctx (.for_ init cond post body) =
        some (code, final)) :
    ∃ initCode initCtx condCode
        postCode postCtx compiledPost
        bodyCode bodyCtx compiledBody cleanup,
      Block.compileOpen ctx.withoutLoopControl init =
        some (initCode, initCtx) ∧
      Expr.compileCode initCtx 0 cond = some condCode ∧
      Block.compileOpen initCtx.withoutLoopControl post =
        some (postCode, postCtx) ∧
      finishScoped initCtx.withoutLoopControl postCtx postCode =
        some compiledPost ∧
      Block.compileOpen
          (initCtx.withLoopControl initCtx.layout.length) body =
        some (bodyCode, bodyCtx) ∧
      finishScoped
          (initCtx.withLoopControl initCtx.layout.length)
          bodyCtx bodyCode =
        some compiledBody ∧
      initCtx.cleanupTo? ctx.layout.length = some cleanup ∧
      code =
        [Expressions.Stmt.for_
          { stmts := initCode } (.code condCode)
          compiledPost compiledBody] ++
          codeStmt cleanup ∧
      final = ctx := by
  let initBase := ctx.withoutLoopControl
  cases hInit : Block.compileOpen initBase init with
  | none =>
      simp [Stmt.compile, initBase, hInit] at hCompile
  | some initResult =>
      rcases initResult with ⟨initCode, initCtx⟩
      cases hCond : Expr.compileCode initCtx 0 cond with
      | none =>
          simp [Stmt.compile, Expr.compile, initBase, hInit, hCond] at hCompile
      | some condCode =>
          let postBase := initCtx.withoutLoopControl
          cases hPost : Block.compileOpen postBase post with
          | none =>
              simp [Stmt.compile, Expr.compile, initBase, postBase,
                hInit, hCond, hPost] at hCompile
          | some postResult =>
              rcases postResult with ⟨postCode, postCtx⟩
              cases hFinishPost :
                  finishScoped postBase postCtx postCode with
              | none =>
                  simp [Stmt.compile, Expr.compile, initBase, postBase,
                    hInit, hCond, hPost, hFinishPost] at hCompile
              | some compiledPost =>
                  let bodyBase :=
                    initCtx.withLoopControl initCtx.layout.length
                  cases hBody : Block.compileOpen bodyBase body with
                  | none =>
                      simp [Stmt.compile, Expr.compile, initBase, postBase,
                        bodyBase, hInit, hCond, hPost, hFinishPost, hBody]
                        at hCompile
                  | some bodyResult =>
                      rcases bodyResult with ⟨bodyCode, bodyCtx⟩
                      cases hFinishBody :
                          finishScoped bodyBase bodyCtx bodyCode with
                      | none =>
                          simp [Stmt.compile, Expr.compile, initBase, postBase,
                            bodyBase, hInit, hCond, hPost, hFinishPost, hBody,
                            hFinishBody] at hCompile
                      | some compiledBody =>
                          cases hCleanup :
                              initCtx.cleanupTo? ctx.layout.length with
                          | none =>
                              simp [Stmt.compile, Expr.compile, initBase,
                                postBase, bodyBase, hInit, hCond, hPost,
                                hFinishPost, hBody, hFinishBody, hCleanup]
                                at hCompile
                          | some cleanup =>
                              simp [Stmt.compile, Expr.compile, initBase,
                                postBase, bodyBase, hInit, hCond, hPost,
                                hFinishPost, hBody, hFinishBody, hCleanup]
                                at hCompile
                              rcases hCompile with ⟨rfl, rfl⟩
                              exact
                                ⟨initCode, initCtx, condCode,
                                  postCode, postCtx, compiledPost,
                                  bodyCode, bodyCtx, compiledBody, cleanup,
                                  by simpa [initBase] using hInit,
                                  hCond,
                                  by simpa [postBase] using hPost,
                                  by simpa [postBase] using hFinishPost,
                                  by simpa [bodyBase] using hBody,
                                  by simpa [bodyBase] using hFinishBody,
                                  hCleanup, rfl, rfl⟩

end Stmt

namespace Block

/--
The singleton open-block form used by the allocation boundary for `if`.
-/
theorem compileOpen_single_if_components
    {ctx final : Ctx}
    {cond : Expr 1} {body : Block}
    {code : List Expressions.Stmt}
    (hCompile :
      Block.compileOpen ctx { stmts := [.if_ cond body] } =
        some (code, final)) :
    ∃ condCode bodyCode bodyCtx lowerBody,
      Expr.compileCode ctx 0 cond = some condCode ∧
      Block.compileOpen ctx body = some (bodyCode, bodyCtx) ∧
      finishScoped ctx bodyCtx bodyCode = some lowerBody ∧
      code = [Expressions.Stmt.if_ (.code condCode) lowerBody] ∧
      final = ctx := by
  cases hStmt : Stmt.compile ctx (.if_ cond body) with
  | none =>
      simp [Block.compileOpen, hStmt] at hCompile
  | some stmtResult =>
      rcases stmtResult with ⟨stmtCode, stmtCtx⟩
      simp [Block.compileOpen, hStmt] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact Stmt.compile_if_components hStmt

/--
The singleton open-block form used by the allocation boundary for `switch`.
-/
theorem compileOpen_single_switch_components
    {ctx final : Ctx}
    {scrutinee : Expr 1}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {code : List Expressions.Stmt}
    (hCompile :
      Block.compileOpen ctx
          { stmts := [.switch scrutinee cases defaultBody] } =
        some (code, final)) :
    ∃ scrutineeCode compiledCases compiledDefault,
      Expr.compileCode ctx 0 scrutinee = some scrutineeCode ∧
      CaseList.compile ctx cases = some compiledCases ∧
      Default.compile ctx defaultBody = some compiledDefault ∧
      code =
        [Expressions.Stmt.switch
          (.code scrutineeCode) compiledCases compiledDefault] ∧
      final = ctx := by
  cases hStmt : Stmt.compile ctx (.switch scrutinee cases defaultBody) with
  | none =>
      simp [Block.compileOpen, hStmt] at hCompile
  | some stmtResult =>
      rcases stmtResult with ⟨stmtCode, stmtCtx⟩
      simp [Block.compileOpen, hStmt] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact Stmt.compile_switch_components hStmt

/--
The singleton open-block form used by the allocation boundary for `for`.
-/
theorem compileOpen_single_for_components
    {ctx final : Ctx}
    {init : Block} {cond : Expr 1} {post body : Block}
    {code : List Expressions.Stmt}
    (hCompile :
      Block.compileOpen ctx
          { stmts := [.for_ init cond post body] } =
        some (code, final)) :
    ∃ initCode initCtx condCode
        postCode postCtx compiledPost
        bodyCode bodyCtx compiledBody cleanup,
      Block.compileOpen ctx.withoutLoopControl init =
        some (initCode, initCtx) ∧
      Expr.compileCode initCtx 0 cond = some condCode ∧
      Block.compileOpen initCtx.withoutLoopControl post =
        some (postCode, postCtx) ∧
      finishScoped initCtx.withoutLoopControl postCtx postCode =
        some compiledPost ∧
      Block.compileOpen
          (initCtx.withLoopControl initCtx.layout.length) body =
        some (bodyCode, bodyCtx) ∧
      finishScoped
          (initCtx.withLoopControl initCtx.layout.length)
          bodyCtx bodyCode =
        some compiledBody ∧
      initCtx.cleanupTo? ctx.layout.length = some cleanup ∧
      code =
        [Expressions.Stmt.for_
          { stmts := initCode } (.code condCode)
          compiledPost compiledBody] ++
          codeStmt cleanup ∧
      final = ctx := by
  cases hStmt : Stmt.compile ctx (.for_ init cond post body) with
  | none =>
      simp [Block.compileOpen, hStmt] at hCompile
  | some stmtResult =>
      rcases stmtResult with ⟨stmtCode, stmtCtx⟩
      simp [Block.compileOpen, hStmt] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact Stmt.compile_for_components hStmt

/--
Successful open-block compilation over an appended statement list decomposes
through the ordinary compiler state produced by the left block.
-/
theorem compileOpen_append_components
    {ctx final : Ctx}
    {left right : List Stmt}
    {code : List Expressions.Stmt}
    (hCompile :
      Block.compileOpen ctx { stmts := left ++ right } =
        some (code, final)) :
    ∃ leftCode middle rightCode,
      Block.compileOpen ctx { stmts := left } =
        some (leftCode, middle) ∧
      Block.compileOpen middle { stmts := right } =
        some (rightCode, final) ∧
      code = leftCode ++ rightCode := by
  induction left generalizing ctx code final with
  | nil =>
      exact
        ⟨[], ctx, code,
          by simp [Block.compileOpen],
          by simpa using hCompile,
          by simp⟩
  | cons stmt rest ih =>
      cases hStmt : Stmt.compile ctx stmt with
      | none =>
          simp [Block.compileOpen, hStmt] at hCompile
      | some stmtResult =>
          rcases stmtResult with ⟨stmtCode, next⟩
          cases hTail :
              Block.compileOpen next { stmts := rest ++ right } with
          | none =>
              simp [Block.compileOpen, hStmt, hTail] at hCompile
          | some tailResult =>
              rcases tailResult with ⟨tailCode, tailFinal⟩
              simp [Block.compileOpen, hStmt, hTail] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              obtain
                  ⟨leftTailCode, middle, rightCode,
                    hLeftTail, hRight, hTailCode⟩ :=
                ih hTail
              subst tailCode
              refine
                ⟨stmtCode ++ leftTailCode, middle, rightCode,
                  ?_, hRight, ?_⟩
              · simp [Block.compileOpen, hStmt, hLeftTail]
              · simp [List.append_assoc]

/--
Successful compilation of a singleton block is exactly successful compilation
of its one statement.
-/
theorem compileOpen_single_components
    {ctx final : Ctx}
    {stmt : Stmt}
    {code : List Expressions.Stmt}
    (hCompile :
      Block.compileOpen ctx { stmts := [stmt] } =
        some (code, final)) :
    Stmt.compile ctx stmt = some (code, final) := by
  cases hStmt : Stmt.compile ctx stmt with
  | none =>
      simp [Block.compileOpen, hStmt] at hCompile
  | some result =>
      rcases result with ⟨stmtCode, next⟩
      simp [Block.compileOpen, hStmt] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl

/--
Compose two successful open-block compilations through the compiler context
produced by the left block.
-/
theorem compileOpen_append
    {ctx middle final : Ctx}
    {left right : List Stmt}
    {leftCode rightCode : List Expressions.Stmt}
    (hLeft :
      Block.compileOpen ctx { stmts := left } =
        some (leftCode, middle))
    (hRight :
      Block.compileOpen middle { stmts := right } =
        some (rightCode, final)) :
    Block.compileOpen ctx { stmts := left ++ right } =
      some (leftCode ++ rightCode, final) := by
  induction left generalizing ctx leftCode middle with
  | nil =>
      simp [Block.compileOpen] at hLeft
      rcases hLeft with ⟨rfl, rfl⟩
      simpa [Block.compileOpen] using hRight
  | cons stmt rest ih =>
      cases hStmt : Stmt.compile ctx stmt with
      | none =>
          simp [Block.compileOpen, hStmt] at hLeft
      | some stmtResult =>
          rcases stmtResult with ⟨stmtCode, next⟩
          cases hRest :
              Block.compileOpen next { stmts := rest } with
          | none =>
              simp [Block.compileOpen, hStmt, hRest] at hLeft
          | some restResult =>
              rcases restResult with ⟨restCode, restFinal⟩
              simp [Block.compileOpen, hStmt, hRest] at hLeft
              rcases hLeft with ⟨rfl, rfl⟩
              have hTail :=
                ih hRest hRight
              simpa [Block.compileOpen, hStmt, hTail,
                List.append_assoc]

def compileToPreserving (ctx : Ctx) (preserve targetDepth : Nat)
    (block : Block) : Option Expressions.Block := do
  let (code, finalCtx) ← Block.compileOpen ctx block
  finishToPreserving finalCtx preserve targetDepth code

/--
Successful preserving compilation exposes the ordinary open-block compiler
and the exact cleanup generated from its final context.
-/
theorem compileToPreserving_components
    {ctx : Ctx} {preserve targetDepth : Nat}
    {block : Block} {compiled : Expressions.Block}
    (hCompile :
      compileToPreserving ctx preserve targetDepth block =
        some compiled) :
    ∃ code finalCtx,
      Block.compileOpen ctx block = some (code, finalCtx) ∧
      finishToPreserving finalCtx preserve targetDepth code =
        some compiled := by
  cases hOpen : Block.compileOpen ctx block with
  | none =>
      simp [compileToPreserving, hOpen] at hCompile
  | some result =>
      rcases result with ⟨code, finalCtx⟩
      cases hFinish :
          finishToPreserving finalCtx preserve targetDepth code with
      | none =>
          simp [compileToPreserving, hOpen, hFinish] at hCompile
      | some output =>
          simp [compileToPreserving, hOpen, hFinish] at hCompile
          subst compiled
          exact ⟨code, finalCtx, rfl, hFinish⟩

def compileTo (ctx : Ctx) (targetDepth : Nat)
    (block : Block) : Option Expressions.Block := do
  compileToPreserving ctx 0 targetDepth block

def compile (ctx : Ctx) (block : Block) : Option Expressions.Block := do
  let (code, finalCtx) ← Block.compileOpen ctx block
  finishScoped ctx finalCtx code

end Block

namespace Switch

/--
Case/default compilation followed by the ordinary Expressions-to-Structured
translation preserves the absence of a selected branch.
-/
theorem select_none_of_compile
    {ctx : Ctx}
    {value : Word}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {compiledCases : List (Word × Expressions.Block)}
    {compiledDefault : Option Expressions.Block}
    (hCases :
      CaseList.compile ctx cases = some compiledCases)
    (hDefault :
      Default.compile ctx defaultBody = some compiledDefault)
    (hSelect :
      Locals.Source.Switch.select value cases defaultBody = none) :
    Structured.Switch.select value
        (Expressions.CaseList.toStructured compiledCases)
        (Expressions.Default.toStructured compiledDefault) =
      none := by
  induction cases generalizing compiledCases with
  | nil =>
      simp [CaseList.compile] at hCases
      subst compiledCases
      cases defaultBody with
      | none =>
          simp [Default.compile] at hDefault
          subst compiledDefault
          rfl
      | some body =>
          simp [Locals.Source.Switch.select] at hSelect
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases hBody : Block.compileOpen ctx body with
      | none =>
          simp [CaseList.compile, hBody] at hCases
      | some bodyResult =>
          rcases bodyResult with ⟨bodyCode, bodyCtx⟩
          cases hFinish : finishScoped ctx bodyCtx bodyCode with
          | none =>
              simp [CaseList.compile, hBody, hFinish] at hCases
          | some compiledBody =>
              cases hRest : CaseList.compile ctx rest with
              | none =>
                  simp [CaseList.compile, hBody, hFinish, hRest] at hCases
              | some compiledRest =>
                  simp [CaseList.compile, hBody, hFinish, hRest] at hCases
                  subst compiledCases
                  by_cases hMatch : caseValue = value
                  · simp [Locals.Source.Switch.select, hMatch] at hSelect
                  · have hTailSelect :
                        Locals.Source.Switch.select
                            value rest defaultBody =
                          none := by
                      simpa [Locals.Source.Switch.select, hMatch] using hSelect
                    have hCompiledTail :=
                      ih hRest hTailSelect
                    simpa [Expressions.CaseList.toStructured,
                      Structured.Switch.select, hMatch] using hCompiledTail

/--
Case/default compilation followed by the ordinary Expressions-to-Structured
translation preserves a selected branch and exposes the open-body compilation
and scoped cleanup that produced the selected target block.
-/
theorem select_some_of_compile
    {ctx : Ctx}
    {value : Word}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {selected : Block}
    {compiledCases : List (Word × Expressions.Block)}
    {compiledDefault : Option Expressions.Block}
    (hCases :
      CaseList.compile ctx cases = some compiledCases)
    (hDefault :
      Default.compile ctx defaultBody = some compiledDefault)
    (hSelect :
      Locals.Source.Switch.select value cases defaultBody = some selected) :
    ∃ selectedCompiled bodyCode bodyCtx,
      Structured.Switch.select value
          (Expressions.CaseList.toStructured compiledCases)
          (Expressions.Default.toStructured compiledDefault) =
        some selectedCompiled.toStructured ∧
      Block.compileOpen ctx selected = some (bodyCode, bodyCtx) ∧
      finishScoped ctx bodyCtx bodyCode = some selectedCompiled := by
  induction cases generalizing compiledCases with
  | nil =>
      simp [CaseList.compile] at hCases
      subst compiledCases
      cases defaultBody with
      | none =>
          simp [Locals.Source.Switch.select] at hSelect
      | some body =>
          simp [Locals.Source.Switch.select] at hSelect
          subst selected
          cases hBody : Block.compileOpen ctx body with
          | none =>
              simp [Default.compile, hBody] at hDefault
          | some bodyResult =>
              rcases bodyResult with ⟨bodyCode, bodyCtx⟩
              cases hFinish : finishScoped ctx bodyCtx bodyCode with
              | none =>
                  simp [Default.compile, hBody, hFinish] at hDefault
              | some compiledBody =>
                  simp [Default.compile, hBody, hFinish] at hDefault
                  subst compiledDefault
                  exact
                    ⟨compiledBody, bodyCode, bodyCtx,
                      rfl, rfl, hFinish⟩
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases hBody : Block.compileOpen ctx body with
      | none =>
          simp [CaseList.compile, hBody] at hCases
      | some bodyResult =>
          rcases bodyResult with ⟨bodyCode, bodyCtx⟩
          cases hFinish : finishScoped ctx bodyCtx bodyCode with
          | none =>
              simp [CaseList.compile, hBody, hFinish] at hCases
          | some compiledBody =>
              cases hRest : CaseList.compile ctx rest with
              | none =>
                  simp [CaseList.compile, hBody, hFinish, hRest] at hCases
              | some compiledRest =>
                  simp [CaseList.compile, hBody, hFinish, hRest] at hCases
                  subst compiledCases
                  by_cases hMatch : caseValue = value
                  · simp [Locals.Source.Switch.select, hMatch] at hSelect
                    subst selected
                    exact
                      ⟨compiledBody, bodyCode, bodyCtx,
                        by
                          simp [Expressions.CaseList.toStructured,
                            Structured.Switch.select, hMatch],
                        hBody, hFinish⟩
                  · have hTailSelect :
                        Locals.Source.Switch.select
                            value rest defaultBody =
                          some selected := by
                      simpa [Locals.Source.Switch.select, hMatch] using hSelect
                    obtain
                        ⟨selectedCompiled, selectedCode, selectedCtx,
                          hTargetSelect, hSelectedBody, hSelectedFinish⟩ :=
                      ih hRest hTailSelect
                    exact
                      ⟨selectedCompiled, selectedCode, selectedCtx,
                        by
                          simpa [Expressions.CaseList.toStructured,
                            Structured.Switch.select, hMatch] using
                            hTargetSelect,
                        hSelectedBody, hSelectedFinish⟩

end Switch

namespace Proc

def toExpressions? (proc : Proc) : Option Expressions.Proc := do
  let body ←
    Block.compileToPreserving
      (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
      proc.retc 0 proc.body
  some { name := proc.name, argc := proc.argc, retc := proc.retc, body := body }

theorem toExpressions?_name
    {proc : Proc} {lower : Expressions.Proc}
    (hCompile : proc.toExpressions? = some lower) :
    lower.name = proc.name := by
  cases hBody :
      Block.compileToPreserving
        (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
        proc.retc 0 proc.body with
  | none =>
      simp [toExpressions?, hBody] at hCompile
  | some body =>
      simp [toExpressions?, hBody] at hCompile
      cases hCompile
      rfl

/--
Successful procedure compilation exposes the preserving body compilation and
the exact Expressions procedure emitted by this pass.
-/
theorem toExpressions?_components
    {proc : Proc} {lower : Expressions.Proc}
    (hCompile : proc.toExpressions? = some lower) :
    ∃ body,
      Block.compileToPreserving
          (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
          proc.retc 0 proc.body =
        some body ∧
      lower =
        { name := proc.name
          argc := proc.argc
          retc := proc.retc
          body := body } := by
  cases hBody :
      Block.compileToPreserving
        (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
        proc.retc 0 proc.body with
  | none =>
      simp [toExpressions?, hBody] at hCompile
  | some body =>
      simp [toExpressions?, hBody] at hCompile
      subst lower
      exact ⟨body, rfl, rfl⟩

end Proc

namespace ProcList

def toExpressions? : List Proc → Option (List Expressions.Proc)
  | [] => some []
  | proc :: rest => do
      let lowerProc ← proc.toExpressions?
      let lowerRest ← toExpressions? rest
      some (lowerProc :: lowerRest)

theorem toExpressions?_member_components :
    ∀ {procs : List Proc} {lower : List Expressions.Proc} {proc : Proc},
      toExpressions? procs = some lower →
      proc ∈ procs →
      ∃ lowerProc,
        proc.toExpressions? = some lowerProc ∧
        lowerProc ∈ lower
  | [], _lower, _proc, hCompile, hMem => by
      simp [toExpressions?] at hCompile hMem
  | head :: rest, lower, proc, hCompile, hMem => by
      cases hHead : head.toExpressions? with
      | none =>
          simp [toExpressions?, hHead] at hCompile
      | some headLower =>
          cases hRest : toExpressions? rest with
          | none =>
              simp [toExpressions?, hHead, hRest] at hCompile
          | some tailLower =>
              simp [toExpressions?, hHead, hRest] at hCompile
              subst lower
              rcases List.mem_cons.mp hMem with hSelected | hTail
              · subst proc
                exact ⟨headLower, hHead, by simp⟩
              · obtain ⟨lowerProc, hProc, hLowerMem⟩ :=
                  toExpressions?_member_components hRest hTail
                exact
                  ⟨lowerProc, hProc,
                    List.mem_cons_of_mem headLower hLowerMem⟩

end ProcList

namespace Program

def toExpressions? (program : Program) : Option Expressions.Program := do
  let procs ← ProcList.toExpressions? program.procs
  let body ← Block.compile Ctx.initial program.body
  some { procs := procs, body := body }

def compile? (program : Program) :
    Option Assembly.TargetProgram := do
  let lower ← toExpressions? program
  lower.compile?

def compileExecutable? (program : Program) :
    Option Assembly.TargetProgram := do
  let lower ← toExpressions? program
  lower.compileExecutable?

theorem compileExecutable?_eq_compile? (program : Program) :
    compileExecutable? program = compile? program := by
  unfold compileExecutable? compile?
  cases hLower : toExpressions? program with
  | none =>
      simp [hLower]
  | some lower =>
      simp [hLower, Expressions.Program.compileExecutable?_eq_compile?]

def Accepted (program : Program) : Prop :=
  ∃ lower : Expressions.Program, toExpressions? program = some lower ∧
    lower.Accepted

def SourceAccepted (program : Program) : Prop :=
  program.WF ∧ Source.Program.SourceWF program

end Program

namespace CompilerFacts

theorem StackOp.dup?_not_callCreate :
    ∀ (depth : Nat) {op : Structured.BasicOp},
      StackOp.dup? depth = some op → op.toPrimOp.isCallCreate = false
  | 0, _op, h => by simp [StackOp.dup?] at h
  | 1, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 2, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 3, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 4, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 5, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 6, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 7, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 8, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 9, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 10, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 11, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 12, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 13, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 14, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 15, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | 16, _op, h => by simp [StackOp.dup?] at h; cases h; rfl
  | n + 17, _op, h => by simp [StackOp.dup?] at h

theorem StackOp.swap?_not_callCreate :
    ∀ (depth : Nat) {op : Structured.BasicOp},
      StackOp.swap? depth = some op → op.toPrimOp.isCallCreate = false
  | 0, _op, h => by simp [StackOp.swap?] at h
  | 1, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 2, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 3, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 4, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 5, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 6, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 7, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 8, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 9, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 10, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 11, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 12, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 13, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 14, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 15, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | 16, _op, h => by simp [StackOp.swap?] at h; cases h; rfl
  | n + 17, _op, h => by simp [StackOp.swap?] at h

theorem Structured.Code.all_false_of_usesCallCreate_false
    {code : Structured.Code}
    (hCode : code.usesCallCreate = false) :
    ∀ instr ∈ code, instr.usesCallCreate = false := by
  simpa [Structured.Code.usesCallCreate] using hCode

theorem Structured.Code.usesCallCreate_append_eq_false
    {left right : Structured.Code}
    (hLeft : Structured.Code.usesCallCreate left = false)
    (hRight : Structured.Code.usesCallCreate right = false) :
    Structured.Code.usesCallCreate (left ++ right) = false := by
  simp [Structured.Code.usesCallCreate] at hLeft hRight ⊢
  exact ⟨hLeft, hRight⟩

theorem Structured.Code.swapPop_noCallCreate {op : Structured.BasicOp}
    (hOp : op.toPrimOp.isCallCreate = false) :
    Structured.Code.usesCallCreate
      ([Structured.BasicInstr.op op, Structured.BasicInstr.op .pop] :
        Structured.Code) = false := by
  simp [Structured.Code.usesCallCreate, Structured.BasicInstr.usesCallCreate,
    Structured.BasicOp.toPrimOp, Assembly.PrimOp.isCallCreate]
  exact hOp

theorem Ctx.cleanupTo?_noCallCreate {ctx : Ctx} {targetDepth : Nat}
    {code : Structured.Code}
    (hCleanup : ctx.cleanupTo? targetDepth = some code) :
    code.usesCallCreate = false := by
  unfold Ctx.cleanupTo? at hCleanup
  split at hCleanup
  · cases hCleanup
    simp [Structured.Code.usesCallCreate,
      Structured.BasicInstr.usesCallCreate, Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isCallCreate]
  · simp at hCleanup

theorem Ctx.swapRestoreUpTo?_noCallCreate :
    ∀ {depth : Nat} {code : Structured.Code},
      Ctx.swapRestoreUpTo? depth = some code →
        code.usesCallCreate = false
  | 0, code, hCode => by
      simp [Ctx.swapRestoreUpTo?] at hCode
      cases hCode
      rfl
  | depth + 1, code, hCode => by
      simp [Ctx.swapRestoreUpTo?] at hCode
      cases hRest : Ctx.swapRestoreUpTo? depth with
      | none =>
          simp [hRest] at hCode
      | some rest =>
          cases hOp : StackOp.swap? (depth + 1) with
          | none =>
              simp [hRest, hOp] at hCode
          | some op =>
              simp [hRest, hOp] at hCode
              cases hCode
              have hRestNo :=
                Ctx.swapRestoreUpTo?_noCallCreate (depth := depth)
                  (code := rest) hRest
              have hOpNo := StackOp.swap?_not_callCreate (depth + 1) hOp
              have hRestAll :=
                Structured.Code.all_false_of_usesCallCreate_false hRestNo
              simp [Structured.Code.usesCallCreate,
                Structured.BasicInstr.usesCallCreate, hRestNo, hOpNo]
              exact hRestAll

theorem Ctx.promoteNameStackOnly?_eq_some {ctx : Ctx} {name : Name}
    {code : Structured.Code} {promoted : Layout}
    (hPromote :
      ctx.promoteNameStackOnly? name = some (code, promoted)) :
    ∃ depth idx,
      Layout.lookupDepth? name ctx.layout = some depth ∧
        idx = depth - 1 ∧
        idx ≤ 16 ∧
        Ctx.swapRestoreUpTo? idx = some code ∧
        promoted = Layout.promoteAt idx ctx.layout := by
  unfold Ctx.promoteNameStackOnly? at hPromote
  cases hDepth : Layout.lookupDepth? name ctx.layout with
  | none =>
      simp [hDepth] at hPromote
  | some depth =>
      by_cases hDepthBound : depth ≤ 17
      · have hBound : depth - 1 ≤ 16 := by omega
        simp [hDepth, hDepthBound] at hPromote
        cases hCode : Ctx.swapRestoreUpTo? (depth - 1) with
        | none =>
            simp [hCode] at hPromote
        | some promoteCode =>
            simp [hCode] at hPromote
            rcases hPromote with ⟨rfl, rfl⟩
            exact
              ⟨depth, depth - 1, rfl, rfl, hBound, hCode, rfl⟩
      · simp [hDepth, hDepthBound] at hPromote

theorem Ctx.promoteNameStackOnly?_noCallCreate {ctx : Ctx} {name : Name}
    {code : Structured.Code} {promoted : Layout}
    (hPromote :
      ctx.promoteNameStackOnly? name = some (code, promoted)) :
    code.usesCallCreate = false := by
  rcases Ctx.promoteNameStackOnly?_eq_some hPromote with
    ⟨_depth, idx, _hDepth, _hIdx, _hBound, hCode, _hPromoted⟩
  exact Ctx.swapRestoreUpTo?_noCallCreate (depth := idx) hCode

theorem Ctx.cleanupOnePreserving?_noCallCreate {temps : Nat}
    {code : Structured.Code}
    (hCleanup : Ctx.cleanupOnePreserving? temps = some code) :
    code.usesCallCreate = false := by
  cases temps with
  | zero =>
      simp [Ctx.cleanupOnePreserving?] at hCleanup
      cases hCleanup
      rfl
  | succ temps =>
      simp [Ctx.cleanupOnePreserving?] at hCleanup
      cases hOp : StackOp.swap? (temps + 1) with
      | none =>
          simp [hOp] at hCleanup
      | some op =>
          cases hRestore : Ctx.swapRestoreUpTo? temps with
          | none =>
              simp [hOp, hRestore] at hCleanup
          | some restore =>
              simp [hOp, hRestore] at hCleanup
              cases hCleanup
              have hOpNo := StackOp.swap?_not_callCreate (temps + 1) hOp
              have hRestoreNo :=
                Ctx.swapRestoreUpTo?_noCallCreate (depth := temps)
                  (code := restore) hRestore
              have hRestoreAll :=
                Structured.Code.all_false_of_usesCallCreate_false hRestoreNo
              simp [Structured.Code.usesCallCreate,
                Structured.BasicInstr.usesCallCreate,
                Structured.BasicOp.toPrimOp, Assembly.PrimOp.isCallCreate,
                hOpNo, hRestoreNo]
              exact ⟨hOpNo, hRestoreAll⟩

theorem Ctx.cleanupManyPreserving?_noCallCreate :
    ∀ {count temps : Nat} {code : Structured.Code},
      Ctx.cleanupManyPreserving? count temps = some code →
        code.usesCallCreate = false
  | 0, temps, code, hCode => by
      simp [Ctx.cleanupManyPreserving?] at hCode
      cases hCode
      rfl
  | count + 1, temps, code, hCode => by
      simp [Ctx.cleanupManyPreserving?] at hCode
      cases hHead : Ctx.cleanupOnePreserving? temps with
      | none =>
          simp [hHead] at hCode
      | some head =>
          cases hTail : Ctx.cleanupManyPreserving? count temps with
          | none =>
              simp [hHead, hTail] at hCode
          | some tail =>
              simp [hHead, hTail] at hCode
              cases hCode
              have hHeadNo := Ctx.cleanupOnePreserving?_noCallCreate hHead
              have hTailNo :=
                Ctx.cleanupManyPreserving?_noCallCreate
                  (count := count) (temps := temps) (code := tail) hTail
              have hHeadAll :=
                Structured.Code.all_false_of_usesCallCreate_false hHeadNo
              have hTailAll :=
                Structured.Code.all_false_of_usesCallCreate_false hTailNo
              simp [Structured.Code.usesCallCreate, hHeadNo, hTailNo]
              exact ⟨hHeadAll, hTailAll⟩

theorem Ctx.cleanupToPreserving?_noCallCreate {ctx : Ctx}
    {preserve targetDepth : Nat} {code : Structured.Code}
    (hCleanup : ctx.cleanupToPreserving? preserve targetDepth = some code) :
    code.usesCallCreate = false := by
  unfold Ctx.cleanupToPreserving? at hCleanup
  split at hCleanup
  · exact Ctx.cleanupManyPreserving?_noCallCreate hCleanup
  · simp at hCleanup

theorem Ctx.cleanupAll_noCallCreate (ctx : Ctx) :
    ctx.cleanupAll.usesCallCreate = false := by
  simp [Ctx.cleanupAll, Structured.Code.usesCallCreate,
    Structured.BasicInstr.usesCallCreate, Structured.BasicOp.toPrimOp,
    Assembly.PrimOp.isCallCreate]

theorem codeStmt_noCallCreate {code : Structured.Code}
    (hCode : code.usesCallCreate = false) :
    Expressions.StmtList.usesCallCreate (codeStmt code) = false := by
  simp [codeStmt, Expressions.StmtList.usesCallCreate,
    Expressions.Stmt.usesCallCreate, hCode]

theorem Expressions.StmtList.usesCallCreate_append_eq_false
    {left right : List Expressions.Stmt}
    (hLeft : Expressions.StmtList.usesCallCreate left = false)
    (hRight : Expressions.StmtList.usesCallCreate right = false) :
    Expressions.StmtList.usesCallCreate (left ++ right) = false := by
  induction left with
  | nil =>
      simpa using hRight
  | cons head tail ih =>
      have hParts :
          head.usesCallCreate = false ∧
            Expressions.StmtList.usesCallCreate tail = false := by
        simpa [Expressions.StmtList.usesCallCreate] using hLeft
      simp [Expressions.StmtList.usesCallCreate, hParts.1,
        ih hParts.2]

theorem Expressions.StmtList.cons_noCallCreate {stmt : Expressions.Stmt}
    {rest : List Expressions.Stmt}
    (hStmt : stmt.usesCallCreate = false)
    (hRest : Expressions.StmtList.usesCallCreate rest = false) :
    Expressions.StmtList.usesCallCreate (stmt :: rest) = false := by
  simp [Expressions.StmtList.usesCallCreate, hStmt, hRest]

theorem finishTo_noCallCreate {final : Ctx} {targetDepth : Nat}
    {stmts : List Expressions.Stmt} {block : Expressions.Block}
    (hStmts : Expressions.StmtList.usesCallCreate stmts = false)
    (hFinish : finishTo final targetDepth stmts = some block) :
    block.usesCallCreate = false := by
  unfold finishTo at hFinish
  cases hCleanup : final.cleanupTo? targetDepth with
  | none =>
      simp [hCleanup] at hFinish
  | some cleanup =>
      simp [hCleanup] at hFinish
      cases hFinish
      have hCleanupNo := Ctx.cleanupTo?_noCallCreate hCleanup
      have hCleanupStmtNo := codeStmt_noCallCreate hCleanupNo
      exact Expressions.StmtList.usesCallCreate_append_eq_false
        hStmts hCleanupStmtNo

theorem finishToPreserving_noCallCreate {final : Ctx}
    {preserve targetDepth : Nat} {stmts : List Expressions.Stmt}
    {block : Expressions.Block}
    (hStmts : Expressions.StmtList.usesCallCreate stmts = false)
    (hFinish :
      finishToPreserving final preserve targetDepth stmts = some block) :
    block.usesCallCreate = false := by
  unfold finishToPreserving at hFinish
  cases hCleanup : final.cleanupToPreserving? preserve targetDepth with
  | none =>
      simp [hCleanup] at hFinish
  | some cleanup =>
      simp [hCleanup] at hFinish
      cases hFinish
      have hCleanupNo := Ctx.cleanupToPreserving?_noCallCreate hCleanup
      have hCleanupStmtNo := codeStmt_noCallCreate hCleanupNo
      exact Expressions.StmtList.usesCallCreate_append_eq_false
        hStmts hCleanupStmtNo

theorem finishScoped_noCallCreate {outer final : Ctx}
    {stmts : List Expressions.Stmt} {block : Expressions.Block}
    (hStmts : Expressions.StmtList.usesCallCreate stmts = false)
    (hFinish : finishScoped outer final stmts = some block) :
    block.usesCallCreate = false := by
  unfold finishScoped at hFinish
  exact finishTo_noCallCreate (final := final)
    (targetDepth := outer.layout.length) hStmts hFinish

set_option linter.unusedSimpArgs false in
mutual
  theorem Expr.compileCode_noCallCreate {results : Nat}
      (ctx : Ctx) (offset : Nat) (expr : Expr results)
      {code : Structured.Code}
      (hExpr : expr.usesCallCreate = false)
      (hCompile : Expr.compileCode ctx offset expr = some code) :
      code.usesCallCreate = false := by
    cases expr with
    | lit value =>
        simp [Expr.compileCode] at hCompile
        cases hCompile
        try subst stmts
        simp [Structured.Code.usesCallCreate,
          Structured.BasicInstr.usesCallCreate]
    | var name =>
        simp [Expr.compileCode] at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hOp : StackOp.dup? (offset + depth) with
            | none =>
                simp [hDepth, hOp] at hCompile
            | some op =>
                simp [hDepth, hOp] at hCompile
                cases hCompile
                try subst stmts
                have hOpNo := StackOp.dup?_not_callCreate (offset + depth) hOp
                simp [Structured.Code.usesCallCreate,
                  Structured.BasicInstr.usesCallCreate, hOpNo]
    | code raw =>
        simp [Expr.compileCode] at hCompile
        cases hCompile
        try subst stmts
        simpa [Expr.usesCallCreate] using hExpr
    | prim op args =>
        have hParts :
            args.usesCallCreate = false ∧ op.toPrimOp.isCallCreate = false := by
          simpa [Expr.usesCallCreate] using hExpr
        simp [Expr.compileCode] at hCompile
        cases hArgs : ExprSeq.compileCode ctx offset args with
        | none =>
            simp [hArgs] at hCompile
        | some argsCode =>
            simp [hArgs] at hCompile
            cases hCompile
            try subst stmts
            have hArgsNo :=
              ExprSeq.compileCode_noCallCreate ctx offset args hParts.1 hArgs
            have hArgsAll :=
              Structured.Code.all_false_of_usesCallCreate_false hArgsNo
            simp [Structured.Code.usesCallCreate,
              Structured.BasicInstr.usesCallCreate, hParts.2, hArgsNo]
            exact hArgsAll

  theorem ExprSeq.compileCode_noCallCreate {results : Nat}
      (ctx : Ctx) (offset : Nat) (exprs : ExprSeq results)
      {code : Structured.Code}
      (hExprs : exprs.usesCallCreate = false)
      (hCompile : ExprSeq.compileCode ctx offset exprs = some code) :
      code.usesCallCreate = false := by
    cases exprs with
    | nil =>
        simp [ExprSeq.compileCode] at hCompile
        cases hCompile
        try subst stmts
        rfl
    | cons head tail =>
        rename_i left right
        have hParts :
            head.usesCallCreate = false ∧ tail.usesCallCreate = false := by
          simpa [ExprSeq.usesCallCreate] using hExprs
        simp [ExprSeq.compileCode] at hCompile
        cases hHead : Expr.compileCode ctx offset head with
        | none =>
            simp [hHead] at hCompile
        | some headCode =>
            cases hTail : ExprSeq.compileCode ctx (offset + left) tail with
            | none =>
                simp [hHead, hTail] at hCompile
            | some tailCode =>
                simp [hHead, hTail] at hCompile
                cases hCompile
                try subst stmts
                have hHeadNo :=
                  Expr.compileCode_noCallCreate ctx offset head hParts.1 hHead
                have hTailNo :=
                  ExprSeq.compileCode_noCallCreate ctx (offset + left) tail
                    hParts.2 hTail
                have hHeadAll :=
                  Structured.Code.all_false_of_usesCallCreate_false hHeadNo
                have hTailAll :=
                  Structured.Code.all_false_of_usesCallCreate_false hTailNo
                simp [Structured.Code.usesCallCreate, hHeadNo, hTailNo]
                exact ⟨hHeadAll, hTailAll⟩
end

theorem Expr.compile_noCallCreate {results : Nat} (ctx : Ctx)
    (expr : Expr results) {lower : Expressions.Expr results}
    (hExpr : expr.usesCallCreate = false)
    (hCompile : Expr.compile ctx expr = some lower) :
    lower.usesCallCreate = false := by
  unfold Expr.compile at hCompile
  cases hCode : Expr.compileCode ctx 0 expr with
  | none =>
      simp [hCode] at hCompile
  | some code =>
      simp [hCode] at hCompile
      cases hCompile
      try subst stmts
      have hCodeNo :=
        Expr.compileCode_noCallCreate ctx 0 expr hExpr hCode
      simpa [Expressions.Expr.usesCallCreate] using hCodeNo

set_option linter.unusedSimpArgs false in
mutual
  theorem Block.compileOpen_noCallCreate (ctx : Ctx) (block : Block)
      {stmts : List Expressions.Stmt} {final : Ctx}
      (hBlock : block.usesCallCreate = false)
      (hCompile : Block.compileOpen ctx block = some (stmts, final)) :
      Expressions.StmtList.usesCallCreate stmts = false := by
    cases block with
    | mk list =>
        cases list with
        | nil =>
            simp [Block.compileOpen] at hCompile
            cases hCompile
            try subst stmts
            rfl
        | cons stmt rest =>
            have hParts :
                stmt.usesCallCreate = false ∧
                  StmtList.usesCallCreate rest = false := by
              simpa [Block.usesCallCreate, StmtList.usesCallCreate] using
                hBlock
            simp [Block.compileOpen] at hCompile
            cases hStmt : Stmt.compile ctx stmt with
            | none =>
                simp [hStmt] at hCompile
            | some stmtOut =>
                rcases stmtOut with ⟨stmtCode, ctx'⟩
                cases hRest :
                    Block.compileOpen ctx' { stmts := rest } with
                | none =>
                    simp [hStmt, hRest] at hCompile
                | some restOut =>
                    rcases restOut with ⟨restCode, ctx''⟩
                    simp [hStmt, hRest] at hCompile
                    cases hCompile
                    try subst stmts
                    have hStmtNo :=
                      Stmt.compile_noCallCreate ctx stmt hParts.1 hStmt
                    have hRestNo :=
                      Block.compileOpen_noCallCreate ctx' { stmts := rest }
                        hParts.2 hRest
                    exact
                      Expressions.StmtList.usesCallCreate_append_eq_false
                        hStmtNo hRestNo
  termination_by sizeOf block
  decreasing_by
    all_goals subst_vars
    all_goals simp [Block.mk.sizeOf_spec, Prod.mk.sizeOf_spec,
      List.cons.sizeOf_spec]
    all_goals omega

  theorem Stmt.compile_noCallCreate (ctx : Ctx) (stmt : Stmt)
      {stmts : List Expressions.Stmt} {final : Ctx}
      (hStmt : stmt.usesCallCreate = false)
      (hCompile : Stmt.compile ctx stmt = some (stmts, final)) :
      Expressions.StmtList.usesCallCreate stmts = false := by
    cases stmt with
    | expr expr =>
        simp [Stmt.compile] at hCompile
        cases hCode : Expr.compileCode ctx 0 expr with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            try subst stmts
            exact codeStmt_noCallCreate
              (Expr.compileCode_noCallCreate ctx 0 expr
                (by simpa [Stmt.usesCallCreate] using hStmt) hCode)
    | exprs exprs =>
        simp [Stmt.compile] at hCompile
        cases hCode : ExprSeq.compileCode ctx 0 exprs with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            try subst stmts
            exact codeStmt_noCallCreate
              (ExprSeq.compileCode_noCallCreate ctx 0 exprs
                (by simpa [Stmt.usesCallCreate] using hStmt) hCode)
    | let_ name value =>
        simp [Stmt.compile] at hCompile
        cases hCode : Expr.compileCode ctx 0 value with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            have hCodeNo :=
              Expr.compileCode_noCallCreate ctx 0 value
                (by simpa [Stmt.usesCallCreate] using hStmt) hCode
            cases hCompile
            try subst stmts
            exact codeStmt_noCallCreate
              (Structured.Code.usesCallCreate_append_eq_false hCodeNo
                (bindLocals_noCallCreate 0 (name :: ctx.layout)))
    | assign name value =>
        have hValue : value.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [Stmt.compile] at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hValueCode : Expr.compileCode ctx 0 value with
            | none =>
                simp [hDepth, hValueCode] at hCompile
            | some valueCode =>
                cases hSwap : StackOp.swap? depth with
                | none =>
                    simp [hDepth, hValueCode, hSwap] at hCompile
                | some swapOp =>
                    simp [hDepth, hValueCode, hSwap] at hCompile
                    cases hCompile
                    try subst stmts
                    have hValueNo :=
                      Expr.compileCode_noCallCreate ctx 0 value hValue hValueCode
                    have hSwapNo := StackOp.swap?_not_callCreate depth hSwap
                    have hTailNo :=
                      Structured.Code.swapPop_noCallCreate hSwapNo
                    exact codeStmt_noCallCreate
                      (Structured.Code.usesCallCreate_append_eq_false
                        hValueNo hTailNo)
    | assignTop name =>
        simp [Stmt.compile] at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hSwap : StackOp.swap? depth with
            | none =>
                simp [hDepth, hSwap] at hCompile
            | some swapOp =>
                simp [hDepth, hSwap] at hCompile
                cases hCompile
                try subst stmts
                exact codeStmt_noCallCreate
                  (Structured.Code.swapPop_noCallCreate
                    (StackOp.swap?_not_callCreate depth hSwap))
    | assignTopWithOffset offset name =>
        simp [Stmt.compile] at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hSwap : StackOp.swap? (offset + depth) with
            | none =>
                simp [hDepth, hSwap] at hCompile
            | some swapOp =>
                simp [hDepth, hSwap] at hCompile
                cases hCompile
                try subst stmts
                exact codeStmt_noCallCreate
                  (Structured.Code.swapPop_noCallCreate
                    (StackOp.swap?_not_callCreate (offset + depth) hSwap))
    | promoteName name =>
        simp [Stmt.compile] at hCompile
        cases hPromote : ctx.promoteNameStackOnly? name with
        | none =>
            simp [hPromote] at hCompile
        | some promoteResult =>
            rcases promoteResult with ⟨promoteCode, promoted⟩
            simp [hPromote] at hCompile
            rcases hCompile with ⟨rfl, rfl⟩
            exact codeStmt_noCallCreate
              (Ctx.promoteNameStackOnly?_noCallCreate hPromote)
    | cleanupTo targetLayout =>
        by_cases hTarget :
            targetLayout =
              ctx.layout.drop (ctx.layout.length - targetLayout.length)
        · simp only [Stmt.compile, if_pos hTarget] at hCompile
          cases hCleanup : ctx.cleanupTo? targetLayout.length with
          | none =>
              simp [hCleanup] at hCompile
          | some cleanup =>
              simp [hCleanup] at hCompile
              cases hCompile
              try subst stmts
              exact codeStmt_noCallCreate
                (Ctx.cleanupTo?_noCallCreate hCleanup)
        · simp only [Stmt.compile, if_neg hTarget] at hCompile
          simp at hCompile
    | block body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [Stmt.compile] at hCompile
        cases hBodyCompile : Block.compileOpen ctx body with
        | none =>
            simp [hBodyCompile] at hCompile
        | some bodyOut =>
            rcases bodyOut with ⟨bodyCode, bodyCtx⟩
            cases hFinish : finishScoped ctx bodyCtx bodyCode with
            | none =>
                simp [hBodyCompile, hFinish] at hCompile
            | some lowerBlock =>
                simp [hBodyCompile, hFinish] at hCompile
                cases hCompile
                try subst stmts
                have hBodyCodeNo :=
                  Block.compileOpen_noCallCreate ctx body hBody hBodyCompile
                have hLowerBlockNo :=
                  finishScoped_noCallCreate hBodyCodeNo hFinish
                rcases lowerBlock with ⟨lowerStmts⟩
                exact hLowerBlockNo
    | if_ cond body =>
        have hParts :
            cond.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [Stmt.compile] at hCompile
        cases hCond : Expr.compile ctx cond with
        | none =>
            simp [hCond] at hCompile
        | some condExpr =>
            cases hBodyCompile : Block.compileOpen ctx body with
            | none =>
                simp [hCond, hBodyCompile] at hCompile
            | some bodyOut =>
                rcases bodyOut with ⟨bodyCode, bodyCtx⟩
                cases hFinish : finishScoped ctx bodyCtx bodyCode with
                | none =>
                    simp [hCond, hBodyCompile, hFinish] at hCompile
                | some lowerBody =>
                    simp [hCond, hBodyCompile, hFinish] at hCompile
                    cases hCompile
                    try subst stmts
                    have hCondNo :=
                      Expr.compile_noCallCreate ctx cond hParts.1 hCond
                    have hBodyCodeNo :=
                      Block.compileOpen_noCallCreate ctx body hParts.2
                        hBodyCompile
                    have hLowerBodyNo :=
                      finishScoped_noCallCreate hBodyCodeNo hFinish
                    simp [Expressions.StmtList.usesCallCreate,
                      Expressions.Stmt.usesCallCreate, hCondNo, hLowerBodyNo]
    | switch scrutinee cases defaultBody =>
        have hParts :
            scrutinee.usesCallCreate = false ∧
              CaseList.usesCallCreate cases = false ∧
                Default.usesCallCreate defaultBody = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        simp [Stmt.compile] at hCompile
        cases hScrutinee : Expr.compile ctx scrutinee with
        | none =>
            simp [hScrutinee] at hCompile
        | some scrutineeExpr =>
            cases hCases : CaseList.compile ctx cases with
            | none =>
                simp [hScrutinee, hCases] at hCompile
            | some lowerCases =>
                cases hDefault : Default.compile ctx defaultBody with
                | none =>
                    simp [hScrutinee, hCases, hDefault] at hCompile
                | some lowerDefault =>
                    simp [hScrutinee, hCases, hDefault] at hCompile
                    cases hCompile
                    try subst stmts
                    have hScrutineeNo :=
                      Expr.compile_noCallCreate ctx scrutinee hParts.1
                        hScrutinee
                    have hCasesNo :=
                      CaseList.compile_noCallCreate ctx cases hParts.2.1
                        hCases
                    have hDefaultNo :=
                      Default.compile_noCallCreate ctx defaultBody hParts.2.2
                        hDefault
                    simp [Expressions.StmtList.usesCallCreate,
                      Expressions.Stmt.usesCallCreate, hScrutineeNo,
                      hCasesNo, hDefaultNo]
    | for_ init cond post body =>
        have hParts :
            init.usesCallCreate = false ∧ cond.usesCallCreate = false ∧
              post.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        simp [Stmt.compile] at hCompile
        let initBase := ctx.withoutLoopControl
        cases hInit : Block.compileOpen initBase init with
        | none =>
            simp [initBase, hInit] at hCompile
        | some initOut =>
            rcases initOut with ⟨initCode, initCtx⟩
            cases hCond : Expr.compile initCtx cond with
            | none =>
                simp [initBase, hInit, hCond] at hCompile
            | some condExpr =>
                let postBase := initCtx.withoutLoopControl
                cases hPost : Block.compileOpen postBase post with
                | none =>
                    simp [initBase, postBase, hInit, hCond, hPost] at hCompile
                | some postOut =>
                    rcases postOut with ⟨postCode, postCtx⟩
                    cases hLowerPost : finishScoped postBase postCtx postCode with
                    | none =>
                        simp [initBase, postBase, hInit, hCond, hPost,
                          hLowerPost] at hCompile
                    | some lowerPost =>
                        let bodyBase := initCtx.withLoopControl initCtx.layout.length
                        cases hBody : Block.compileOpen bodyBase body with
                        | none =>
                            simp [initBase, postBase, bodyBase, hInit, hCond,
                              hPost, hLowerPost, hBody] at hCompile
                        | some bodyOut =>
                            rcases bodyOut with ⟨bodyCode, bodyCtx⟩
                            cases hLowerBody :
                                finishScoped bodyBase bodyCtx bodyCode with
                            | none =>
                                simp [initBase, postBase, bodyBase, hInit,
                                  hCond, hPost, hLowerPost, hBody,
                                  hLowerBody] at hCompile
                            | some lowerBody =>
                                cases hCleanup :
                                    initCtx.cleanupTo? ctx.layout.length with
                                | none =>
                                    simp [initBase, postBase, bodyBase, hInit,
                                      hCond, hPost, hLowerPost, hBody,
                                      hLowerBody, hCleanup] at hCompile
                                | some cleanup =>
                                    simp [initBase, postBase, bodyBase, hInit,
                                      hCond, hPost, hLowerPost, hBody,
                                      hLowerBody, hCleanup] at hCompile
                                    cases hCompile
                                    try subst stmts
                                    have hInitNo :=
                                      Block.compileOpen_noCallCreate initBase
                                        init hParts.1 hInit
                                    have hCondNo :=
                                      Expr.compile_noCallCreate initCtx cond
                                        hParts.2.1 hCond
                                    have hPostNo :=
                                      Block.compileOpen_noCallCreate postBase
                                        post hParts.2.2.1 hPost
                                    have hLowerPostNo :=
                                      finishScoped_noCallCreate hPostNo
                                        hLowerPost
                                    have hBodyNo :=
                                      Block.compileOpen_noCallCreate bodyBase
                                        body hParts.2.2.2 hBody
                                    have hLowerBodyNo :=
                                      finishScoped_noCallCreate hBodyNo
                                        hLowerBody
                                    have hCleanupNo :=
                                      Ctx.cleanupTo?_noCallCreate hCleanup
                                    have hCleanupStmtNo :=
                                      codeStmt_noCallCreate hCleanupNo
                                    have hLoopNo :
                                        (Expressions.Stmt.for_
                                          { stmts := initCode } condExpr
                                          lowerPost lowerBody).usesCallCreate =
                                          false := by
                                      simp [Expressions.Stmt.usesCallCreate,
                                        Expressions.Block.usesCallCreate,
                                        hInitNo, hCondNo, hLowerPostNo,
                                        hLowerBodyNo]
                                    exact
                                      Expressions.StmtList.usesCallCreate_append_eq_false
                                        (left := [Expressions.Stmt.for_
                                          { stmts := initCode } condExpr
                                          lowerPost lowerBody])
                                        (right := codeStmt cleanup)
                                        (by
                                          simpa [Expressions.StmtList.usesCallCreate,
                                            hLoopNo])
                                        hCleanupStmtNo
    | brk =>
        simp [Stmt.compile] at hCompile
        cases hTarget : ctx.breakDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupTo? target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                try subst stmts
                exact
                  Expressions.StmtList.usesCallCreate_append_eq_false
                    (codeStmt_noCallCreate
                      (Ctx.cleanupTo?_noCallCreate hCleanup))
                    (by simp [Expressions.StmtList.usesCallCreate,
                      Expressions.Stmt.usesCallCreate])
    | cont =>
        simp [Stmt.compile] at hCompile
        cases hTarget : ctx.continueDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupTo? target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                try subst stmts
                exact
                  Expressions.StmtList.usesCallCreate_append_eq_false
                    (codeStmt_noCallCreate
                      (Ctx.cleanupTo?_noCallCreate hCleanup))
                    (by simp [Expressions.StmtList.usesCallCreate,
                      Expressions.Stmt.usesCallCreate])
    | leave =>
        simp [Stmt.compile] at hCompile
        cases hTarget : ctx.leaveDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup :
                ctx.cleanupToPreserving? ctx.leaveRetc target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                try subst stmts
                exact
                  Expressions.StmtList.usesCallCreate_append_eq_false
                    (codeStmt_noCallCreate
                      (Ctx.cleanupToPreserving?_noCallCreate hCleanup))
                    (by simp [Expressions.StmtList.usesCallCreate,
                      Expressions.Stmt.usesCallCreate])
    | call name =>
        simp [Stmt.compile] at hCompile
        cases hCompile
        try subst stmts
        simp [Expressions.StmtList.usesCallCreate,
          Expressions.Stmt.usesCallCreate]
    | terminal kind =>
        simp [Stmt.compile] at hCompile
        cases hCompile
        try subst stmts
        exact
          Expressions.StmtList.usesCallCreate_append_eq_false
            (codeStmt_noCallCreate (Ctx.cleanupAll_noCallCreate ctx))
            (by simp [Expressions.StmtList.usesCallCreate,
              Expressions.Stmt.usesCallCreate])
    | terminalArgs kind args =>
        have hArgs : args.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [Stmt.compile] at hCompile
        cases hCode : ExprSeq.compileCode ctx 0 args with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            try subst stmts
            exact
              Expressions.StmtList.usesCallCreate_append_eq_false
                (codeStmt_noCallCreate
                  (ExprSeq.compileCode_noCallCreate ctx 0 args hArgs hCode))
                (by simp [Expressions.StmtList.usesCallCreate,
                  Expressions.Stmt.usesCallCreate])
  termination_by sizeOf stmt
  decreasing_by
    all_goals subst_vars
    all_goals simp [Block.mk.sizeOf_spec, Prod.mk.sizeOf_spec,
      List.cons.sizeOf_spec]
    all_goals omega

  theorem CaseList.compile_noCallCreate (ctx : Ctx)
      (cases : List (Word × Block))
      {lowerCases : List (Word × Expressions.Block)}
      (hCases : CaseList.usesCallCreate cases = false)
      (hCompile : CaseList.compile ctx cases = some lowerCases) :
      Expressions.CaseList.usesCallCreate lowerCases = false := by
    cases cases with
    | nil =>
        simp [CaseList.compile] at hCompile
        cases hCompile
        try subst stmts
        rfl
    | cons head rest =>
        cases head with
        | mk value body =>
            have hParts :
                body.usesCallCreate = false ∧
                  CaseList.usesCallCreate rest = false := by
              simpa [CaseList.usesCallCreate] using hCases
            simp [CaseList.compile] at hCompile
            cases hBody : Block.compileOpen ctx body with
            | none =>
                simp [hBody] at hCompile
            | some bodyOut =>
                rcases bodyOut with ⟨bodyCode, bodyCtx⟩
                cases hFinish : finishScoped ctx bodyCtx bodyCode with
                | none =>
                    simp [hBody, hFinish] at hCompile
                | some lowerBody =>
                    cases hRest : CaseList.compile ctx rest with
                    | none =>
                        simp [hBody, hFinish, hRest] at hCompile
                    | some lowerRest =>
                        simp [hBody, hFinish, hRest] at hCompile
                        cases hCompile
                        try subst stmts
                        have hBodyCodeNo :=
                          Block.compileOpen_noCallCreate ctx body hParts.1 hBody
                        have hLowerBodyNo :=
                          finishScoped_noCallCreate hBodyCodeNo hFinish
                        have hRestNo :=
                          CaseList.compile_noCallCreate ctx rest hParts.2 hRest
                        simp [Expressions.CaseList.usesCallCreate,
                          hLowerBodyNo, hRestNo]
  termination_by sizeOf cases
  decreasing_by
    all_goals subst_vars
    all_goals simp [Block.mk.sizeOf_spec, Prod.mk.sizeOf_spec,
      List.cons.sizeOf_spec]
    all_goals omega

  theorem Default.compile_noCallCreate (ctx : Ctx)
      (defaultBody : Option Block)
      {lowerDefault : Option Expressions.Block}
      (hDefault : Default.usesCallCreate defaultBody = false)
      (hCompile : Default.compile ctx defaultBody = some lowerDefault) :
      Expressions.Default.usesCallCreate lowerDefault = false := by
    cases defaultBody with
    | none =>
        simp [Default.compile] at hCompile
        cases hCompile
        try subst stmts
        rfl
    | some body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Default.usesCallCreate] using hDefault
        simp [Default.compile] at hCompile
        cases hBodyCompile : Block.compileOpen ctx body with
        | none =>
            simp [hBodyCompile] at hCompile
        | some bodyOut =>
            rcases bodyOut with ⟨bodyCode, bodyCtx⟩
            cases hFinish : finishScoped ctx bodyCtx bodyCode with
            | none =>
                simp [hBodyCompile, hFinish] at hCompile
            | some lowerBody =>
                simp [hBodyCompile, hFinish] at hCompile
                cases hCompile
                try subst stmts
                have hBodyCodeNo :=
                  Block.compileOpen_noCallCreate ctx body hBody hBodyCompile
                exact finishScoped_noCallCreate hBodyCodeNo hFinish
  termination_by sizeOf defaultBody
  decreasing_by
    all_goals subst_vars
    all_goals simp [Block.mk.sizeOf_spec, Prod.mk.sizeOf_spec,
      List.cons.sizeOf_spec]
    all_goals omega
end

theorem Block.compileToPreserving_noCallCreate (ctx : Ctx)
    (preserve targetDepth : Nat) (block : Block)
    {lower : Expressions.Block}
    (hBlock : block.usesCallCreate = false)
    (hCompile :
      Block.compileToPreserving ctx preserve targetDepth block = some lower) :
    lower.usesCallCreate = false := by
  unfold Block.compileToPreserving at hCompile
  cases hOpen : Block.compileOpen ctx block with
  | none =>
      simp [hOpen] at hCompile
  | some out =>
      rcases out with ⟨stmts, final⟩
      cases hFinish : finishToPreserving final preserve targetDepth stmts with
      | none =>
          simp [hOpen, hFinish] at hCompile
      | some lowerBlock =>
          simp [hOpen, hFinish] at hCompile
          cases hCompile
          have hStmtsNo :=
            Block.compileOpen_noCallCreate ctx block hBlock hOpen
          exact finishToPreserving_noCallCreate hStmtsNo hFinish

theorem Block.compile_noCallCreate (ctx : Ctx) (block : Block)
    {lower : Expressions.Block}
    (hBlock : block.usesCallCreate = false)
    (hCompile : Block.compile ctx block = some lower) :
    lower.usesCallCreate = false := by
  unfold Block.compile at hCompile
  cases hOpen : Block.compileOpen ctx block with
  | none =>
      simp [hOpen] at hCompile
  | some out =>
      rcases out with ⟨stmts, final⟩
      cases hFinish : finishScoped ctx final stmts with
      | none =>
          simp [hOpen, hFinish] at hCompile
      | some lowerBlock =>
          simp [hOpen, hFinish] at hCompile
          cases hCompile
          have hStmtsNo :=
            Block.compileOpen_noCallCreate ctx block hBlock hOpen
          exact finishScoped_noCallCreate hStmtsNo hFinish

theorem Proc.toExpressions?_noCallCreate (proc : Proc)
    {lower : Expressions.Proc}
    (hProc : proc.usesCallCreate = false)
    (hCompile : proc.toExpressions? = some lower) :
    lower.usesCallCreate = false := by
  unfold Proc.toExpressions? at hCompile
  cases hBody :
      Block.compileToPreserving
        (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
        proc.retc 0 proc.body with
  | none =>
      simp [hBody] at hCompile
  | some lowerBody =>
      simp [hBody] at hCompile
      cases hCompile
      have hBodyNo :=
        Block.compileToPreserving_noCallCreate
          (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
          proc.retc 0 proc.body
          (by simpa [Proc.usesCallCreate] using hProc) hBody
      simpa [Expressions.Proc.usesCallCreate] using hBodyNo

theorem ProcList.toExpressions?_noCallCreate :
    ∀ {procs : List Proc} {lower : List Expressions.Proc},
      ProcList.usesCallCreate procs = false →
        ProcList.toExpressions? procs = some lower →
          Expressions.ProcList.usesCallCreate lower = false
  | [], lower, _hProcs, hCompile => by
      simp [ProcList.toExpressions?] at hCompile
      cases hCompile
      rfl
  | proc :: rest, lower, hProcs, hCompile => by
      have hParts :
          proc.usesCallCreate = false ∧
            ProcList.usesCallCreate rest = false := by
        simpa [ProcList.usesCallCreate] using hProcs
      simp [ProcList.toExpressions?] at hCompile
      cases hProc : proc.toExpressions? with
      | none =>
          simp [hProc] at hCompile
      | some lowerProc =>
          cases hRest : ProcList.toExpressions? rest with
          | none =>
              simp [hProc, hRest] at hCompile
          | some lowerRest =>
              simp [hProc, hRest] at hCompile
              cases hCompile
              have hProcNo :=
                Proc.toExpressions?_noCallCreate proc hParts.1 hProc
              have hRestNo :=
                ProcList.toExpressions?_noCallCreate hParts.2 hRest
              simp [Expressions.ProcList.usesCallCreate, hProcNo, hRestNo]

theorem Program.toExpressions?_noCallCreate (program : Program)
    {lower : Expressions.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile : program.toExpressions? = some lower) :
    lower.usesCallCreate = false := by
  have hParts :
      ProcList.usesCallCreate program.procs = false ∧
        program.body.usesCallCreate = false := by
    simpa [Program.usesCallCreate] using hProgram
  unfold Program.toExpressions? at hCompile
  cases hProcs : ProcList.toExpressions? program.procs with
  | none =>
      simp [hProcs] at hCompile
  | some lowerProcs =>
      cases hBody : Block.compile Ctx.initial program.body with
      | none =>
          simp [hProcs, hBody] at hCompile
      | some lowerBody =>
          simp [hProcs, hBody] at hCompile
          cases hCompile
          have hProcsNo :=
            ProcList.toExpressions?_noCallCreate hParts.1 hProcs
          have hBodyNo :=
            Block.compile_noCallCreate Ctx.initial program.body hParts.2
              hBody
          simp [Expressions.Program.usesCallCreate, hProcsNo, hBodyNo]

end CompilerFacts

end Locals
end EvmCompiler
