import EvmCompiler.Functions.AllocationInteractionRelation
import EvmCompiler.Functions.AllocationLowering
import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionExpression

open AllocationInteractionRelation

abbrev ExprOutcomeRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase results : Nat)
    (initialTarget : TargetState) :
    Except EVMException (SourceState × List Word) →
      Except EVMException TargetState → Prop :=
  Simulation.Interaction.ExceptRel Eq
    (fun sourceResult targetFinal =>
      ExprResultRel contract plan live stackOffset frameBase results
        sourceResult.1 initialTarget targetFinal sourceResult.2)

/--
The allocation pass preserves a literal expression through the ordinary
Locals compiler. This is the base case for the recursive allocation-owned open
expression theorem; it changes only the target stack and program counter.
-/
theorem literal_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    (value : Word) {source : SourceState} {target : TargetState}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    Simulation.Interaction.Rel
      (ExprOutcomeRel contract plan live stackOffset frameBase 1 target)
      (Functions.InteractionSemantics.Expr.openEval (.lit value) source)
      (Structured.InteractionSemantics.Code.openRun [.push value] target) := by
  rw [Locals.InteractionPreservation.Code.openRun_push]
  change
    Simulation.Interaction.Rel
      (ExprOutcomeRel contract plan live stackOffset frameBase 1 target)
      (.done (.ok (source, [value])))
      (.done
        (.ok
          (AllocationInteractionRelation.StateRel.pushTargetBy
            33 value target)))
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact ExprResultRel.literal value hRel

/-- Compiler-facing literal preservation through the ordinary allocation pass. -/
theorem literal_of_lower_compile
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {value : Word}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    {source : SourceState} {target : TargetState}
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState (.lit value) =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    Simulation.Interaction.Rel
      (ExprOutcomeRel contract plan live stackOffset frameBase 1 target)
      (Functions.InteractionSemantics.Expr.openEval (.lit value) source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  have hLowered : lowered = .lit value := by
    simpa [AllocationLowering.lowerExpr] using hLower.symm
  subst lowered
  have hCode : code = [.push value] := by
    simpa [Locals.Expr.compileCode] using hCompile.symm
  subst code
  exact literal_open value hRel

/-- A live stack-allocated local is read by the exact compiler-selected DUP. -/
theorem stack_var_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase planDepth depth : Nat}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    {source : SourceState} {target : TargetState}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth?
          name (AllocationInteractionRelation.currentStackOrder plan live) =
        some (depth + 1))
    (hSource : source.vars name = some value)
    (hDup : Locals.StackOp.dup? (stackOffset + depth + 1) = some op) :
    Simulation.Interaction.Rel
      (ExprOutcomeRel contract plan live stackOffset frameBase 1 target)
      (Functions.InteractionSemantics.Expr.openEval (.var name) source)
      (Structured.InteractionSemantics.Code.openRun [.op op] target) := by
  obtain ⟨actualDepth, hActualDepth, hTargetValue⟩ :=
    hRel.store name (.stack planDepth) hLive hLocation
  rw [hDepth] at hActualDepth
  cases hActualDepth
  have hTarget :
      target.evm.stack[stackOffset + depth]? = some value := by
    rw [hTargetValue, hSource]
  rw [Locals.InteractionPreservation.Code.openRun_dup hDup hTarget]
  unfold Functions.InteractionSemantics.Expr.openEval
    Locals.InteractionSemantics.Expr.openEval
    Locals.Source.Effectful.Expr.Control.eval
  simp only [Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.vars, id_eq, hSource]
  change
    Simulation.Interaction.Rel
      (ExprOutcomeRel contract plan live stackOffset frameBase 1 target)
      (.done (.ok (source, [value])))
      (.done
        (.ok
          (AllocationInteractionRelation.StateRel.pushTargetBy
            1 value target)))
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ⟨StateRel.push_target_by 1 value hRel, rfl, ?_⟩
  simp [StateRel.pushTargetBy,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

end AllocationInteractionExpression
end Functions
end EvmCompiler
