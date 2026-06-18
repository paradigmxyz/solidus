import EvmCompiler.Yul.FunctionsInteractionExpression

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionStatement

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation

def ResultRel (ctx : Functions.Source.Ctx)
    (source : Yul.InteractionSemantics.State)
    (target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) : Prop :=
  FunctionsInteractionRelation.OutcomeRel source target.1 ∧
    target.2 = ctx

abbrev DoneRel (ctx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel ErrorRel (ResultRel ctx)

theorem expr
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {fuel targetFuel : Nat}
    {expr : AstExpr} {lower : Locals.Expr 0}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 0 expr = some lower)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel ctx)
      (Yul.InteractionSemantics.exec fuel (.ExprStmtCall expr)
        codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.expr lower) target) := by
  cases expr with
  | Lit value =>
      simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
  | Var name =>
      simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
  | Call callee args =>
      cases callee with
      | inr functionName =>
          simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
      | inl prim =>
          rw [Yul.InteractionSemantics.Exec.expr_primitive,
            Functions.InteractionSemantics.Stmt.openRun_expr]
          have hEval :=
            (FunctionsInteractionExpression.directAt
              hPrimitive codeOverride fuel).evalValues hLower hRel
          apply Simulation.Interaction.ForwardRel.bind hEval
          intro sourceResult targetResult hResult
          have hMultifill :
              Yul.InteractionSemantics.stateModel.multifill []
                  sourceResult.1 sourceResult.2 =
                sourceResult.1 := by
            cases sourceResult.1 <;> rfl
          simpa [hMultifill] using
            (Simulation.Interaction.ForwardRel.done
              (truncated := Truncated)
              (Simulation.Interaction.ExceptRel.ok
                (show
                  ResultRel ctx sourceResult.1
                    (Functions.Source.Effectful.Outcome.regular
                      targetResult.1, ctx) from
                  ⟨FunctionsInteractionRelation.OutcomeRel.regular hResult.1,
                    rfl⟩)))

theorem brk
    {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hScope : ctx.breakScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel ctx)
      (Yul.InteractionSemantics.exec fuel .Break codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel .brk target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.brk_zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel .brk target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hRestricted :
          FunctionsInteractionRelation.StateRel
            (.Ok sourceShared sourceVars) (target.restrictTo scope) :=
        hRel.restrictTarget hSubset
      have hDone :
          DoneRel ctx
            (.ok (.Checkpoint (.Break sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.brk
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.OutcomeRel.brk hRestricted, rfl⟩
      rw [Yul.InteractionSemantics.Exec.brk_succ,
        Functions.InteractionSemantics.Stmt.openRun_brk
          program ctx targetFuel target hScope]
      exact Simulation.Interaction.ForwardRel.done hDone

theorem cont
    {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hScope : ctx.continueScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel ctx)
      (Yul.InteractionSemantics.exec fuel .Continue codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel .cont target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel .cont target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hRestricted :
          FunctionsInteractionRelation.StateRel
            (.Ok sourceShared sourceVars) (target.restrictTo scope) :=
        hRel.restrictTarget hSubset
      have hDone :
          DoneRel ctx
            (.ok (.Checkpoint (.Continue sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.cont
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.OutcomeRel.cont hRestricted, rfl⟩
      rw [Yul.InteractionSemantics.Exec.cont_succ,
        Functions.InteractionSemantics.Stmt.openRun_cont
          program ctx targetFuel target hScope]
      exact Simulation.Interaction.ForwardRel.done hDone

theorem leave
    {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hScope : ctx.leaveScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (DoneRel ctx)
      (Yul.InteractionSemantics.exec fuel .Leave codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel .leave target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := DoneRel ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel .leave target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hRestricted :
          FunctionsInteractionRelation.StateRel
            (.Ok sourceShared sourceVars) (target.restrictTo scope) :=
        hRel.restrictTarget hSubset
      have hDone :
          DoneRel ctx
            (.ok (.Checkpoint (.Leave sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.leave
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.OutcomeRel.leave hRestricted, rfl⟩
      rw [Yul.InteractionSemantics.Exec.leave_succ,
        Functions.InteractionSemantics.Stmt.openRun_leave
          program ctx targetFuel target hScope]
      exact Simulation.Interaction.ForwardRel.done hDone

end FunctionsInteractionStatement
end Yul
end EvmCompiler
