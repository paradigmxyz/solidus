import EvmCompiler.Functions.AllocationInteractionRecursive

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionSuccessful

open AllocationInteractionCursor
open AllocationInteractionRelation
open AllocationInteractionRecursive

theorem successful_head
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {source : SourceState}
    (hFuel : 0 < fuel)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program ctx fuel
          { stmts := stmt :: rest } source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Stmt.openRun program ctx (fuel - 1)
        stmt source) := by
  have hFuelEq : fuel - 1 + 1 = fuel := by omega
  have hWhole :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program ctx
          (fuel - 1 + 1) { stmts := stmt :: rest } source) := by
    rw [hFuelEq]
    exact hSuccess
  have hHead :=
    Functions.InteractionSemantics.Block.successful_openRun_cons_head hWhole
  simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead

theorem successful_expr_eval
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {expr : Functions.Expr 0} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.expr expr) source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval expr source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  exact Simulation.Interaction.Successful.bind_left hSuccess

theorem successful_let_eval
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {name : Functions.Name} {value : Functions.Expr 1}
    {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.let_ name value) source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval value source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  have hOne := Simulation.Interaction.Successful.bind_left hSuccess
  unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
  exact Simulation.Interaction.Successful.bind_left hOne

theorem successful_assign_eval
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {name : Functions.Name} {value : Functions.Expr 1}
    {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.assign name value) source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval value source) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  split at hSuccess
  next hContains =>
    have hOne := Simulation.Interaction.Successful.bind_left hSuccess
    unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
    exact Simulation.Interaction.Successful.bind_left hOne
  next hContains =>
    exact False.elim
      (Simulation.Interaction.Successful.error_false _ hSuccess)

theorem successful_if_condition
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {cond : Functions.Expr 1} {body : Functions.Block}
    {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel (.if_ cond body) source)) :
    0 < fuel ∧
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Expr.openEval cond source) := by
  cases fuel with
  | zero =>
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | succ fuel =>
      rw [Functions.InteractionSemantics.Stmt.openRun_if] at hSuccess
      have hCond := Simulation.Interaction.Successful.bind_left hSuccess
      unfold Functions.InteractionSemantics.Expr.openEvalCondition at hCond
      unfold Locals.InteractionSemantics.Expr.openEvalCondition at hCond
      unfold Locals.Source.Effectful.Expr.Control.evalCondition at hCond
      have hOne := Simulation.Interaction.Successful.bind_left hCond
      unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
      exact ⟨by omega, Simulation.Interaction.Successful.bind_left hOne⟩

theorem successful_switch_scrutinee
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program ctx fuel
          (.switch scrutinee cases defaultBody) source)) :
    0 < fuel ∧
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Expr.openEval scrutinee source) := by
  cases fuel with
  | zero =>
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | succ fuel =>
      rw [Functions.InteractionSemantics.Stmt.openRun_switch] at hSuccess
      have hOne := Simulation.Interaction.Successful.bind_left hSuccess
      unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
      exact ⟨by omega, Simulation.Interaction.Successful.bind_left hOne⟩

theorem successful_condition_eval
    {cond : Functions.Expr 1} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Expr.openEvalCondition cond source)) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Expr.openEval cond source) := by
  unfold Functions.InteractionSemantics.Expr.openEvalCondition at hSuccess
  unfold Locals.InteractionSemantics.Expr.openEvalCondition at hSuccess
  unfold Locals.Source.Effectful.Expr.Control.evalCondition at hSuccess
  have hOne := Simulation.Interaction.Successful.bind_left hSuccess
  unfold Locals.Source.Effectful.Expr.Control.evalOne at hOne
  exact Simulation.Interaction.Successful.bind_left hOne

theorem successful_brk_scope
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel .brk source)) :
    ∃ afterLive, ctx.breakScope? = some afterLive := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  cases hScope : ctx.breakScope? with
  | none =>
      rw [hScope] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | some afterLive => exact ⟨afterLive, rfl⟩

theorem successful_cont_scope
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel .cont source)) :
    ∃ afterLive, ctx.continueScope? = some afterLive := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  cases hScope : ctx.continueScope? with
  | none =>
      rw [hScope] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | some afterLive => exact ⟨afterLive, rfl⟩

theorem successful_leave_scope
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {source : SourceState}
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel .leave source)) :
    ∃ functionScope, ctx.leaveScope? = some functionScope := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  cases hScope : ctx.leaveScope? with
  | none =>
      rw [hScope] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hSuccess)
  | some functionScope => exact ⟨functionScope, rfl⟩

end AllocationInteractionSuccessful
end Functions
end EvmCompiler

