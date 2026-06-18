import EvmCompiler.Functions.AllocationInteractionRelation
import EvmCompiler.Functions.AllocationInteractionPrimitive
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

/-- Compose recursively checked arguments with one primitive capability. -/
theorem prim_of_args
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    (op : Structured.BasicOp)
    (hPrimitive : AllocationInteractionPrimitive.OpenForward contract op)
    (args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op))
    (argsCode : Structured.Code)
    (hArgs :
      Simulation.Interaction.Rel
        (AllocationInteractionPrimitive.ActivationExprOutcomeRel
          contract plan live stackOffset frameBase
          (Expressions.Structured.BasicOp.inputs op) mode target)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (Structured.InteractionSemantics.Code.openRun argsCode target))
    (hSafe :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase
        (Expressions.Structured.BasicOp.outputs op) mode target)
      (Functions.InteractionSemantics.Expr.openEval (.prim op args) source)
      (Structured.InteractionSemantics.Code.openRun
        (argsCode ++ [.op op]) target) := by
  rw [Structured.InteractionSemantics.Code.openRun_append]
  change
    Simulation.Interaction.Rel _
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (fun result =>
          Locals.InteractionSemantics.Primitive.openEval
            op result.1 result.2))
      (Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun argsCode target)
        (Structured.InteractionSemantics.Code.openRun [.op op]))
  have hArgsSafe :=
    Simulation.Interaction.Rel.strengthen_left hArgs hSafe
  apply Simulation.Interaction.Rel.bind_custom hArgsSafe
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hArgsDone, hSafeDone⟩
  cases hArgsDone with
  | @error left right hError =>
      cases hError
      exact Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.error rfl)
  | @ok sourceArgs targetArgs hArgsResult =>
      simp only
      rw [Structured.InteractionSemantics.Code.openRun_single]
      apply hPrimitive.preserve hArgsResult.valuesLength hArgsResult.state
        hArgsResult.stack
      simpa [AllocationInteractionPrimitive.PrimitiveArgsSafe] using hSafeDone

/--
Compiler-facing primitive composition. The recursive argument premise is the
structural induction hypothesis and is discharged inside this pass owner.
-/
theorem prim_of_lower_compile
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {source : SourceState} {target : TargetState}
    (op : Structured.BasicOp)
    (hPrimitive : AllocationInteractionPrimitive.OpenForward contract op)
    (args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op))
    {lowered : Locals.Expr (Expressions.Structured.BasicOp.outputs op)}
    {code : Structured.Code}
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState (.prim op args) =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hArgsPreserve :
      ∀ {loweredArgs :
          Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
        {argsCode : Structured.Code},
      AllocationLowering.lowerExprSeq lowerCtx lowerState args =
          some loweredArgs →
      Locals.ExprSeq.compileCode localsCtx stackOffset loweredArgs =
          some argsCode →
      Simulation.Interaction.Rel
        (AllocationInteractionPrimitive.ActivationExprOutcomeRel
          contract plan live stackOffset frameBase
          (Expressions.Structured.BasicOp.inputs op) mode target)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (Structured.InteractionSemantics.Code.openRun argsCode target))
    (hSafe :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase
        (Expressions.Structured.BasicOp.outputs op) mode target)
      (Functions.InteractionSemantics.Expr.openEval (.prim op args) source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  cases hLowerArgs :
      AllocationLowering.lowerExprSeq lowerCtx lowerState args with
  | none =>
      simp [AllocationLowering.lowerExpr, hLowerArgs] at hLower
  | some loweredArgs =>
      have hLowered : lowered = .prim op loweredArgs := by
        simpa [AllocationLowering.lowerExpr, hLowerArgs] using hLower.symm
      subst lowered
      cases hArgsCode :
          Locals.ExprSeq.compileCode localsCtx stackOffset loweredArgs with
      | none =>
          simp [Locals.Expr.compileCode, hArgsCode] at hCompile
      | some argsCode =>
          have hCode : code = argsCode ++ [.op op] := by
            simpa [Locals.Expr.compileCode, hArgsCode] using hCompile.symm
          subst code
          exact prim_of_args op hPrimitive args argsCode
            (hArgsPreserve hLowerArgs hArgsCode) hSafe

/-- Compose recursively checked arguments with one CALL-family primitive. -/
theorem call_prim_of_args
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    (kind : Simulation.CallKind)
    (args : Locals.ExprSeq
      (Expressions.Structured.BasicOp.inputs
        (AllocationInteractionPrimitive.callOp kind)))
    (argsCode : Structured.Code)
    (hArgs :
      Simulation.Interaction.Rel
        (AllocationInteractionPrimitive.ActivationExprOutcomeRel
          contract plan live stackOffset frameBase
          (Expressions.Structured.BasicOp.inputs
            (AllocationInteractionPrimitive.callOp kind)) mode target)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (Structured.InteractionSemantics.Code.openRun argsCode target))
    (hSafe :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.CallArgsSafe contract kind)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase 1 mode target)
      (Functions.InteractionSemantics.Expr.openEval
        (.prim (AllocationInteractionPrimitive.callOp kind) args) source)
      (Structured.InteractionSemantics.Code.openRun
        (argsCode ++ [.op (AllocationInteractionPrimitive.callOp kind)])
        target) := by
  have hSafe' :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.PrimitiveArgsSafe contract
          (AllocationInteractionPrimitive.callOp kind))
        (Functions.InteractionSemantics.ExprSeq.openEval args source) := by
    apply Simulation.Interaction.AllDone.mono hSafe
    intro outcome hOutcome
    cases outcome with
    | error error => trivial
    | ok result =>
        simpa [AllocationInteractionPrimitive.PrimitiveArgsSafe,
          AllocationInteractionPrimitive.CallArgsSafe] using hOutcome
  simpa using
    (prim_of_args _
      (AllocationInteractionPrimitive.call_openForward contract kind)
      args argsCode hArgs hSafe')

/-- Compose recursively checked arguments with one CREATE-family primitive. -/
theorem create_prim_of_args
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    (kind : Simulation.CreateKind)
    (args : Locals.ExprSeq
      (Expressions.Structured.BasicOp.inputs
        (AllocationInteractionPrimitive.createOp kind)))
    (argsCode : Structured.Code)
    (hArgs :
      Simulation.Interaction.Rel
        (AllocationInteractionPrimitive.ActivationExprOutcomeRel
          contract plan live stackOffset frameBase
          (Expressions.Structured.BasicOp.inputs
            (AllocationInteractionPrimitive.createOp kind)) mode target)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (Structured.InteractionSemantics.Code.openRun argsCode target))
    (hSafe :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.CreateArgsSafe contract kind)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase 1 mode target)
      (Functions.InteractionSemantics.Expr.openEval
        (.prim (AllocationInteractionPrimitive.createOp kind) args) source)
      (Structured.InteractionSemantics.Code.openRun
        (argsCode ++ [.op (AllocationInteractionPrimitive.createOp kind)])
        target) := by
  have hSafe' :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.PrimitiveArgsSafe contract
          (AllocationInteractionPrimitive.createOp kind))
        (Functions.InteractionSemantics.ExprSeq.openEval args source) := by
    apply Simulation.Interaction.AllDone.mono hSafe
    intro outcome hOutcome
    cases outcome with
    | error error => trivial
    | ok result =>
        simpa [AllocationInteractionPrimitive.PrimitiveArgsSafe,
          AllocationInteractionPrimitive.CreateArgsSafe] using hOutcome
  simpa using
    (prim_of_args _
      (AllocationInteractionPrimitive.create_openForward contract kind)
      args argsCode hArgs hSafe')

end AllocationInteractionExpression
end Functions
end EvmCompiler
