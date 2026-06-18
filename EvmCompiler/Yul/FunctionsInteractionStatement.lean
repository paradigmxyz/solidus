import EvmCompiler.Yul.CompilerStatementDecomposition
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

def ScopedResultRel (layout : List Functions.Name)
    (ctx : Functions.Source.Ctx)
    (source : Yul.InteractionSemantics.State)
    (target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) : Prop :=
  FunctionsInteractionRelation.ScopedOutcomeRel layout source target.1 ∧
    target.2 = ctx

abbrev ScopedDoneRel (layout : List Functions.Name)
    (ctx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel ErrorRel (ScopedResultRel layout ctx)

/-- Path-sensitive scoped result for recursive statement/list composition.
Abrupt control may skip declarations in the static suffix, so only regular
completion must reach `regularLayout`. -/
def PathScopedResultRel (regularLayout : List Functions.Name)
    (source : Yul.InteractionSemantics.State)
    (target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) : Prop :=
  ∃ finalLayout,
    FunctionsInteractionRelation.ScopedOutcomeRel
        finalLayout source target.1 ∧
      (target.1.mode = .regular → finalLayout = regularLayout)

abbrev PathScopedDoneRel (regularLayout : List Functions.Name) :=
  Simulation.Interaction.ExceptRel ErrorRel
    (PathScopedResultRel regularLayout)

namespace PathScopedResultRel

theorem of_fixed
    {layout : List Functions.Name} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx}
    (hRel : ScopedResultRel layout ctx source target) :
    PathScopedResultRel layout source target :=
  ⟨layout, hRel.1, fun _ => rfl⟩

theorem regular_state
    {regularLayout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hRel : PathScopedResultRel regularLayout source
      (Functions.Source.Effectful.Outcome.regular target, ctx)) :
    FunctionsInteractionRelation.ScopedStateRel
      regularLayout source target := by
  rcases hRel with ⟨finalLayout, hScoped, hFinal⟩
  have hLayout : finalLayout = regularLayout := hFinal rfl
  subst finalLayout
  exact hScoped.of_regular_target

end PathScopedResultRel

namespace PathScopedDoneRel

theorem of_fixed
    {layout : List Functions.Name} {ctx : Functions.Source.Ctx}
    {sourceOpen :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State}
    {targetOpen :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hRel : Simulation.Interaction.ForwardRel Truncated
      (ScopedDoneRel layout ctx) sourceOpen targetOpen) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout) sourceOpen targetOpen := by
  apply Simulation.Interaction.ForwardRel.mono hRel
  intro source target hDone
  cases hDone with
  | error hError => exact .error hError
  | ok hResult => exact .ok (PathScopedResultRel.of_fixed hResult)

theorem nil
    {layout : List Functions.Name} {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.execSeq
        (fuel + 1) [] codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 1) { stmts := [] } target) := by
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ,
    Functions.InteractionSemantics.Block.openRun_nil]
  exact Simulation.Interaction.ForwardRel.done
    (.ok
      ⟨layout,
        FunctionsInteractionRelation.ScopedOutcomeRel.regular hRel,
        by simp⟩)

theorem singleton
    {layout : List Functions.Name} {targetFuel : Nat}
    {sourceOpen :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {target : Functions.InteractionSemantics.State}
    (hStmt :
      Simulation.Interaction.ForwardRel Truncated
        (PathScopedDoneRel layout) sourceOpen
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx (targetFuel + 1) stmt target)) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout) sourceOpen
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := [stmt] } target) := by
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (PathScopedDoneRel layout)
        (Simulation.Interaction.bind sourceOpen fun sourceResult =>
          pure sourceResult)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Stmt.openRun
            program ctx (targetFuel + 1) stmt target)
          fun targetResult =>
            match targetResult.1.mode with
            | .regular =>
                Functions.InteractionSemantics.Block.openRun
                  program targetResult.2 (targetFuel + 1)
                    { stmts := [] } targetResult.1.state
            | .brk | .cont | .leave | .halt _ =>
                pure (targetResult.1, ctx)) := by
    apply Simulation.Interaction.ForwardRel.bind hStmt
    intro sourceResult targetResult hResult
    ·
        rcases targetResult with ⟨targetOutcome, ctxMid⟩
        rcases targetOutcome with ⟨targetMid, mode⟩
        rcases hResult with ⟨finalLayout, hScoped, hRegular⟩
        cases mode with
        | regular =>
            dsimp
            rw [Functions.InteractionSemantics.Block.openRun_nil]
            exact Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.ok
                ⟨finalLayout, hScoped, hRegular⟩)
        | brk =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
        | cont =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
        | leave =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
        | halt kind =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
  rw [show targetFuel + 2 = (targetFuel + 1) + 1 by omega,
    Functions.InteractionSemantics.Block.openRun_cons]
  have hSourceBind :
      Simulation.Interaction.bind sourceOpen
          (fun sourceResult => pure sourceResult) = sourceOpen := by
    change Simulation.Interaction.bind sourceOpen pure = sourceOpen
    exact EvmCompiler.Simulation.Interaction.bind_pure sourceOpen
  rw [hSourceBind] at hBound
  simpa [Functions.InteractionSemantics.Stmt.openRun,
    Functions.InteractionSemantics.Block.openRun_nil] using hBound

/-- Compose one source statement with its residual source list while allowing
the ordinary compiler to emit an arbitrary target prefix for that statement. -/
theorem cons
    {headLayout finalLayout : List Functions.Name}
    {fuel targetFuel : Nat}
    {stmt : AstStmt} {rest : List AstStmt}
    {lowerHead lowerRest : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hHead :
      Simulation.Interaction.ForwardRel Truncated
        (PathScopedDoneRel headLayout)
        (Yul.InteractionSemantics.exec fuel stmt codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := lowerHead } target))
    (hTail :
      ∀ {sourceMid : Yul.InteractionSemantics.State}
        {targetMid : Functions.InteractionSemantics.State}
        {ctxMid : Functions.Source.Ctx},
        FunctionsInteractionRelation.ScopedStateRel
            headLayout sourceMid targetMid →
          Simulation.Interaction.ForwardRel Truncated
            (PathScopedDoneRel finalLayout)
            (Yul.InteractionSemantics.execSeq
              fuel rest codeOverride sourceMid)
            (Functions.InteractionSemantics.Block.openRun
              program ctxMid (targetFuel - lowerHead.length)
                { stmts := lowerRest } targetMid)) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel finalLayout)
      (Yul.InteractionSemantics.execSeq
        (fuel + 1) (stmt :: rest) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
          { stmts := lowerHead ++ lowerRest } target) := by
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ,
    Functions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind hHead
  intro sourceMid targetResult hResult
  rcases targetResult with ⟨targetOutcome, ctxMid⟩
  rcases targetOutcome with ⟨targetMid, mode⟩
  cases mode with
  | regular =>
      have hState := PathScopedResultRel.regular_state hResult
      rcases hState.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst sourceMid
      simpa using hTail hState
  | brk =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint with
          | Break sourceShared sourceVars =>
              exact Simulation.Interaction.ForwardRel.done
                (.ok ⟨branchLayout, hScoped, by simp⟩)
          | Continue sourceShared sourceVars => simp [ModeRel] at hMode
          | Leave sourceShared sourceVars => simp [ModeRel] at hMode
  | cont =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint with
          | Break sourceShared sourceVars => simp [ModeRel] at hMode
          | Continue sourceShared sourceVars =>
              exact Simulation.Interaction.ForwardRel.done
                (.ok ⟨branchLayout, hScoped, by simp⟩)
          | Leave sourceShared sourceVars => simp [ModeRel] at hMode
  | leave =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint with
          | Break sourceShared sourceVars => simp [ModeRel] at hMode
          | Continue sourceShared sourceVars => simp [ModeRel] at hMode
          | Leave sourceShared sourceVars =>
              exact Simulation.Interaction.ForwardRel.done
                (.ok ⟨branchLayout, hScoped, by simp⟩)
  | halt kind =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint <;> simp [ModeRel] at hMode

end PathScopedDoneRel

theorem expr
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {fuel targetFuel : Nat}
    {expr : AstExpr} {lower : Locals.Expr 0}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 0 expr = some lower)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
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
              hPrimitive codeOverride fuel).evalValues hLower hRel.state
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
                  ScopedResultRel layout ctx sourceResult.1
                    (Functions.Source.Effectful.Outcome.regular
                      targetResult.1, ctx) from
                  ⟨FunctionsInteractionRelation.ScopedOutcomeRel.regular
                      (FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
                        hRel hResult.1 hResult.2.2.2),
                    rfl⟩)))

theorem let_one
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {fuel targetFuel : Nat}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {lower : Locals.Expr 1}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 valueExpr = some lower)
    (hFresh : name ∉ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ScopedDoneRel (name :: layout)
        { ctx with scope := name :: ctx.scope })
      (Yul.InteractionSemantics.exec fuel
        (.Let [name] (some valueExpr)) codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.let_ name lower) target) := by
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
          (doneRel := ScopedDoneRel (name :: layout)
            { ctx with scope := name :: ctx.scope })
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel (.let_ name lower) target)
          hTruncated)
  | succ exprFuel =>
      have hCheck :=
        FunctionsInteractionRelation.ScopedStateRel.declarationCheck
          hRel hFresh
      rw [Yul.InteractionSemantics.Exec.let_one_succ
          exprFuel name valueExpr codeOverride source hCheck,
        Functions.InteractionSemantics.Stmt.openRun_let]
      have hEval :=
        (FunctionsInteractionExpression.directAt
          hPrimitive codeOverride exprFuel).evalValues hLower hRel.state
      apply Simulation.Interaction.ForwardRel.bind
        (by simpa [Functions.InteractionSemantics.Expr.openEval] using hEval)
      intro sourceResult targetResult hResult
      rcases hResult with ⟨hState, hValues, hLength, hStore⟩
      obtain ⟨value, hSourceValues⟩ := List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hValues, hSourceValues]
      have hScopedAfterExpr :=
        FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
          hRel hState hStore
      have hFinal :=
        FunctionsInteractionRelation.ScopedStateRel.multifill_single_cons
          hScopedAfterExpr name value
      have hDone :
          ScopedDoneRel (name :: layout)
              { ctx with scope := name :: ctx.scope }
            (.ok (sourceResult.1.multifill [name] [value]))
            (.ok
              (Functions.Source.Effectful.Outcome.regular
                  (targetResult.1.insert name value),
                { ctx with scope := name :: ctx.scope })) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinal,
            rfl⟩
      rw [hSourceValues, hTargetValues]
      simpa [Yul.InteractionSemantics.stateModel,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.insert] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

theorem assign_one
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {fuel targetFuel : Nat}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {lower : Locals.Expr 1}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 valueExpr = some lower)
    (hName : name ∈ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
      (Yul.InteractionSemantics.exec fuel
        (.Assign [name] valueExpr) codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.assign name lower) target) := by
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
          (doneRel := ScopedDoneRel layout ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel (.assign name lower) target)
          hTruncated)
  | succ exprFuel =>
      have hCheck :=
        FunctionsInteractionRelation.ScopedStateRel.assignmentCheck
          hRel hName
      have hContains :=
        FunctionsInteractionRelation.ScopedStateRel.targetContains
          hRel hName
      rw [Yul.InteractionSemantics.Exec.assign_one_succ
          exprFuel name valueExpr codeOverride source hCheck,
        Functions.InteractionSemantics.Stmt.openRun_assign
          program ctx targetFuel name lower target hContains]
      have hEval :=
        (FunctionsInteractionExpression.directAt
          hPrimitive codeOverride exprFuel).evalValues hLower hRel.state
      apply Simulation.Interaction.ForwardRel.bind
        (by simpa [Functions.InteractionSemantics.Expr.openEval] using hEval)
      intro sourceResult targetResult hResult
      rcases hResult with ⟨hState, hValues, hLength, hStore⟩
      obtain ⟨value, hSourceValues⟩ := List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hValues, hSourceValues]
      have hScopedAfterExpr :=
        FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
          hRel hState hStore
      have hFinal :=
        FunctionsInteractionRelation.ScopedStateRel.multifill_single_visible
          hScopedAfterExpr hName value
      have hDone :
          ScopedDoneRel layout ctx
            (.ok (sourceResult.1.multifill [name] [value]))
            (.ok
              (Functions.Source.Effectful.Outcome.regular
                  (targetResult.1.insert name value), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinal,
            rfl⟩
      rw [hSourceValues, hTargetValues]
      simpa [Yul.InteractionSemantics.stateModel,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.withVars,
        Locals.Source.State.withVars] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

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
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
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
          (doneRel := ScopedDoneRel layout ctx)
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
          ScopedDoneRel layout ctx
            (.ok (.Checkpoint (.Break sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.brk
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.brk_restrict
              { state := ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
                domain := hRel.domain
                defined := hRel.defined }
              hSubset,
            rfl⟩
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
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
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
          (doneRel := ScopedDoneRel layout ctx)
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
          ScopedDoneRel layout ctx
            (.ok (.Checkpoint (.Continue sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.cont
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.cont_restrict
              { state := ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
                domain := hRel.domain
                defined := hRel.defined }
              hSubset,
            rfl⟩
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
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
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
          (doneRel := ScopedDoneRel layout ctx)
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
          ScopedDoneRel layout ctx
            (.ok (.Checkpoint (.Leave sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.leave
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.leave_restrict
              { state := ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
                domain := hRel.domain
                defined := hRel.defined }
              hSubset,
            rfl⟩
      rw [Yul.InteractionSemantics.Exec.leave_succ,
        Functions.InteractionSemantics.Stmt.openRun_leave
          program ctx targetFuel target hScope]
      exact Simulation.Interaction.ForwardRel.done hDone

theorem compiled_brk
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Break =
        some (lower, after))
    (hScope : ctx.breakScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel .Break codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_break_parts hLower with
    ⟨rfl, rfl⟩
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact brk hScope hSubset hRel

theorem compiled_cont
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Continue =
        some (lower, after))
    (hScope : ctx.continueScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel .Continue codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_continue_parts hLower with
    ⟨rfl, rfl⟩
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact cont hScope hSubset hRel

theorem compiled_leave
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Leave =
        some (lower, after))
    (hScope : ctx.leaveScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel .Leave codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_leave_parts hLower with
    ⟨rfl, rfl⟩
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact leave hScope hSubset hRel

end FunctionsInteractionStatement
end Yul
end EvmCompiler
