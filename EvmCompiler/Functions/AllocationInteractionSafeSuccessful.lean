import EvmCompiler.Functions.AllocationInteractionSafeExpression
import EvmCompiler.Functions.AllocationInteractionSafety

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionSafeSuccessful

abbrev SourceState := Functions.InteractionSemantics.State

theorem successful_head
    {contract : MemoryContract.Contract} {program : Functions.Program}
    {ctx : Functions.Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {source : SourceState}
    (hFuel : 0 < fuel)
    (hSafe : AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
      program ctx fuel { stmts := stmt :: rest } source) :
    Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Stmt.openRun contract program ctx
        (fuel - 1) stmt source) := by
  have hFuelEq : fuel - 1 + 1 = fuel := by omega
  unfold AllocationInteractionSafeSemantics.Block.ExecutionSafe at hSafe
  have hWhole : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Block.openRun contract program ctx
        (fuel - 1 + 1) { stmts := stmt :: rest } source) := by
    rwa [hFuelEq]
  rw [AllocationInteractionSafeSemantics.Block.openRun_cons] at hWhole
  exact Simulation.Interaction.Successful.bind_left hWhole

theorem successful_expr_eval
    {contract : MemoryContract.Contract} {program : Functions.Program}
    {ctx : Functions.Source.Ctx} {fuel : Nat}
    {expr : Functions.Expr 0} {source : SourceState}
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Stmt.openRun contract program ctx
        fuel (.expr expr) source)) :
    Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Expr.openEval contract expr source) := by
  rw [AllocationInteractionSafeSemantics.Stmt.openRun_expr] at hSuccess
  exact Simulation.Interaction.Successful.bind_left hSuccess

theorem successful_let_value
    {contract : MemoryContract.Contract} {program : Functions.Program}
    {ctx : Functions.Source.Ctx} {fuel : Nat} {name : Functions.Name}
    {value : Functions.Expr 1} {source : SourceState}
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Stmt.openRun contract program ctx
        fuel (.let_ name value) source)) :
    Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Expr.openEvalOne
        contract value source) := by
  rw [AllocationInteractionSafeSemantics.Stmt.openRun_let] at hSuccess
  exact Simulation.Interaction.Successful.bind_left hSuccess

theorem successful_assign_value
    {contract : MemoryContract.Contract} {program : Functions.Program}
    {ctx : Functions.Source.Ctx} {fuel : Nat} {name : Functions.Name}
    {value : Functions.Expr 1} {source : SourceState}
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Stmt.openRun contract program ctx
        fuel (.assign name value) source)) :
    Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Expr.openEvalOne
        contract value source) := by
  unfold AllocationInteractionSafeSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  split at hSuccess
  next hContains => exact Simulation.Interaction.Successful.bind_left hSuccess
  next hContains =>
    exact False.elim
      (Simulation.Interaction.Successful.error_false _ hSuccess)

theorem successful_terminal
    {contract : MemoryContract.Contract} {program : Functions.Program}
    {ctx : Functions.Source.Ctx} {fuel : Nat} {kind : Assembly.HaltKind}
    {source : SourceState}
    (hSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Stmt.openRun contract program ctx
        fuel (.terminal kind) source)) :
    Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.openTerminal
        contract kind source []) := by
  unfold AllocationInteractionSafeSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  exact Simulation.Interaction.Successful.bind_left hSuccess

end AllocationInteractionSafeSuccessful
end Functions
end EvmCompiler
