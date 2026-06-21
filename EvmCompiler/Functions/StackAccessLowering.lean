import EvmCompiler.Functions.StackAccess
import EvmCompiler.Locals.Compiler

/-!
Adjacent proof that the pure accessibility checker predicts successful
ordinary Locals expression compilation.
-/

namespace EvmCompiler
namespace Functions
namespace StackAccessLowering

open StackAccess

mutual
  theorem Expr.compileCode_of_check
      {results : Nat} {layout : Locals.Layout} {offset : Nat}
      {expr : Functions.Expr results}
      (hCheck : StackAccess.Expr.check? layout offset expr = some ())
      (ctx : Locals.Ctx) (hLayout : ctx.layout = layout) :
      ∃ code, Locals.Expr.compileCode ctx offset expr = some code := by
    cases expr with
    | lit value => exact ⟨[.push value], rfl⟩
    | var name =>
        simp only [StackAccess.Expr.check?] at hCheck
        obtain ⟨depth, hDepth, hAfterDepth⟩ :=
          Option.bind_eq_some_iff.mp hCheck
        obtain ⟨op, hOp, _hDone⟩ :=
          Option.bind_eq_some_iff.mp hAfterDepth
        refine ⟨[.op op], ?_⟩
        simp [Locals.Expr.compileCode, hLayout, hDepth, hOp]
    | code code => exact ⟨code, rfl⟩
    | prim op args =>
        obtain ⟨argsCode, hArgs⟩ :=
          ExprSeq.compileCode_of_check hCheck ctx hLayout
        exact
          ⟨argsCode ++ [.op op],
            by simp [Locals.Expr.compileCode, hArgs]⟩

  theorem ExprSeq.compileCode_of_check
      {results : Nat} {layout : Locals.Layout} {offset : Nat}
      {exprs : Locals.ExprSeq results}
      (hCheck : StackAccess.ExprSeq.check? layout offset exprs = some ())
      (ctx : Locals.Ctx) (hLayout : ctx.layout = layout) :
      ∃ code, Locals.ExprSeq.compileCode ctx offset exprs = some code := by
    cases exprs with
    | nil => exact ⟨[], rfl⟩
    | @cons left right head tail =>
        simp only [StackAccess.ExprSeq.check?] at hCheck
        obtain ⟨_unit, hHead, hTail⟩ :=
          Option.bind_eq_some_iff.mp hCheck
        obtain ⟨headCode, hHeadCode⟩ :=
          Expr.compileCode_of_check hHead ctx hLayout
        obtain ⟨tailCode, hTailCode⟩ :=
          ExprSeq.compileCode_of_check hTail ctx hLayout
        exact
          ⟨headCode ++ tailCode,
            by simp [Locals.ExprSeq.compileCode, hHeadCode, hTailCode]⟩
end

theorem assign_compile_of_check
    {layout : Locals.Layout} {name : Name} {value : Functions.Expr 1}
    (hCheck : StackAccess.assign? layout name value = some ())
    (ctx : Locals.Ctx) (hLayout : ctx.layout = layout) :
    ∃ code,
      Locals.Stmt.compile ctx (.assign name value) = some (code, ctx) := by
  unfold StackAccess.assign? at hCheck
  obtain ⟨_unit, hValue, hAfterValue⟩ :=
    Option.bind_eq_some_iff.mp hCheck
  obtain ⟨depth, hDepth, hAfterDepth⟩ :=
    Option.bind_eq_some_iff.mp hAfterValue
  obtain ⟨swap, hSwap, _hDone⟩ :=
    Option.bind_eq_some_iff.mp hAfterDepth
  obtain ⟨valueCode, hValueCode⟩ :=
    Expr.compileCode_of_check hValue ctx hLayout
  refine
    ⟨Locals.codeStmt
        (valueCode ++ [.op swap, .op .pop] ++
          Locals.bindLocals 0 ctx.layout), ?_⟩
  simp [Locals.Stmt.compile, hLayout, hDepth, hValueCode, hSwap]

theorem assignTopWithOffset_compile_of_check
    {layout : Locals.Layout} {offset : Nat} {name : Name}
    (hCheck :
      StackAccess.assignTopWithOffset? layout offset name = some ())
    (ctx : Locals.Ctx) (hLayout : ctx.layout = layout) :
    ∃ code,
      Locals.Stmt.compile ctx (.assignTopWithOffset offset name) =
        some (code, ctx) := by
  unfold StackAccess.assignTopWithOffset? at hCheck
  obtain ⟨depth, hDepth, hAfterDepth⟩ :=
    Option.bind_eq_some_iff.mp hCheck
  obtain ⟨swap, hSwap, _hDone⟩ :=
    Option.bind_eq_some_iff.mp hAfterDepth
  refine
    ⟨Locals.codeStmt
        ([.op swap, .op .pop] ++ Locals.bindLocals offset ctx.layout), ?_⟩
  simp [Locals.Stmt.compile, hLayout, hDepth, hSwap]

theorem returnedTargetsRev_compile_of_check
    {layout : Locals.Layout} {names : List Name}
    (hCheck : StackAccess.returnedTargetsRev? layout names = some ())
    (ctx : Locals.Ctx) (hLayout : ctx.layout = layout) :
    ∃ code,
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTopsRev names } =
        some (code, ctx) := by
  induction names with
  | nil => exact ⟨[], by simp [Lower.assignReturnedTopsRev,
      Locals.Block.compileOpen]⟩
  | cons name rest ih =>
      simp only [StackAccess.returnedTargetsRev?] at hCheck
      obtain ⟨_unit, hHead, hTail⟩ :=
        Option.bind_eq_some_iff.mp hCheck
      obtain ⟨headCode, hHeadCode⟩ :=
        assignTopWithOffset_compile_of_check hHead ctx hLayout
      obtain ⟨tailCode, hTailCode⟩ := ih hTail
      exact
        ⟨headCode ++ tailCode,
          by simp [Lower.assignReturnedTopsRev, Locals.Block.compileOpen,
            hHeadCode, hTailCode]⟩

theorem returnedTargets_compile_of_check
    {layout : Locals.Layout} {targets : List Name}
    (hCheck : StackAccess.returnedTargets? layout targets = some ())
    (ctx : Locals.Ctx) (hLayout : ctx.layout = layout) :
    ∃ code,
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTops targets } =
        some (code, ctx) := by
  exact returnedTargetsRev_compile_of_check hCheck ctx hLayout

theorem callSequence_compile_of_check
    {layout : Locals.Layout} {targets : List Name}
    {functionName : Name} {args : List (Functions.Expr 1)}
    (hCheck : StackAccess.call? layout targets args = some ())
    (ctx : Locals.Ctx) (hLayout : ctx.layout = layout) :
    ∃ code,
      Locals.Block.compileOpen ctx
          { stmts :=
              [.exprs (Lower.argExprs args), .call functionName] ++
                Lower.assignReturnedTops targets } =
        some (code, ctx) := by
  unfold StackAccess.call? at hCheck
  obtain ⟨_unit, hArgs, hTargets⟩ :=
    Option.bind_eq_some_iff.mp hCheck
  obtain ⟨argsCode, hArgsCode⟩ :=
    ExprSeq.compileCode_of_check hArgs ctx hLayout
  obtain ⟨targetsCode, hTargetsCode⟩ :=
    returnedTargets_compile_of_check hTargets ctx hLayout
  refine
    ⟨Locals.codeStmt argsCode ++ [.call functionName] ++ targetsCode, ?_⟩
  simp [Locals.Block.compileOpen, Locals.Stmt.compile, hArgsCode,
    hTargetsCode]

end StackAccessLowering
end Functions
end EvmCompiler
