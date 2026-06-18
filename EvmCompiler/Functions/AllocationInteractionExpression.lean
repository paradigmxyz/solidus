import EvmCompiler.Functions.AllocationInteractionRelation
import EvmCompiler.Functions.AllocationInteractionPrimitive
import EvmCompiler.Functions.AllocationInteractionOrdinaryPrimitive
import EvmCompiler.Functions.AllocationInteractionSafety
import EvmCompiler.Functions.AllocationContext
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

theorem literal_activation_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode} {source : SourceState} {target : TargetState}
    (value : Word)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase 1 mode target)
      (Functions.InteractionSemantics.Expr.openEval (.lit value) source)
      (Structured.InteractionSemantics.Code.openRun [.push value] target) := by
  rw [Locals.InteractionPreservation.Code.openRun_push]
  change
    Simulation.Interaction.Rel _
      (.done (.ok (source, [value])))
      (.done (.ok (StateRel.pushTargetBy 33 value target)))
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact ActivationExprResultRel.literal value hRel

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

theorem stack_var_activation_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase planDepth depth : Nat}
    {mode : ActivationMode}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    {source : SourceState} {target : TargetState}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth?
          name (AllocationInteractionRelation.currentStackOrder plan live) =
        some (depth + 1))
    (hSource : source.vars name = some value)
    (hDup : Locals.StackOp.dup? (stackOffset + depth + 1) = some op) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase 1 mode target)
      (Functions.InteractionSemantics.Expr.openEval (.var name) source)
      (Structured.InteractionSemantics.Code.openRun [.op op] target) := by
  obtain ⟨actualDepth, hActualDepth, hTargetValue⟩ :=
    hRel.state.store name (.stack planDepth) hLive hLocation
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
    Simulation.Interaction.Rel _
      (.done (.ok (source, [value])))
      (.done (.ok (StateRel.pushTargetBy 1 value target)))
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ⟨hRel.push_target_by 1 value, rfl, ?_⟩
  simp [StateRel.pushTargetBy,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

private theorem openRun_add
    {target : TargetState} {right left : Word} {rest : List Word}
    (hStack : target.evm.stack = right :: left :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .add] target =
      .done
        (.ok
          (StateRel.contractTargetBy 1
            (EvmYul.UInt256.add right left) rest target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
    Structured.InteractionSemantics.BasicInstr.openStepEVM
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
    (by rfl) (by decide) (by decide)]
  rw [Assembly.PrimOp.step_eq_continuingStep_run
    (by rfl : Assembly.PrimOp.add.continuingStep? =
      some (.bin EvmYul.UInt256.add))]
  unfold Assembly.PrimStep.run EvmYul.EVM.execBinOp
  rw [hStack]
  simp [Simulation.Interaction.map,
    Simulation.Interaction.pure, EvmYul.Stack.pop2, EvmYul.Stack.push,
    Id.run, StateRel.contractTargetBy,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

private theorem openRun_mload
    {target : TargetState} {address value : Word} {rest : List Word}
    (hStack : target.evm.stack = address :: rest)
    (hLoad :
      target.evm.toMachineState.mload address =
        (value, target.evm.toMachineState)) :
    Structured.InteractionSemantics.Code.openRun [.op .mload] target =
      .done (.ok (StateRel.contractTargetBy 1 value rest target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
    Structured.InteractionSemantics.BasicInstr.openStepEVM
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
    (by rfl) (by decide) (by decide)]
  rw [Assembly.PrimOp.step_eq_continuingStep_run
    (by rfl : Assembly.PrimOp.mload.continuingStep? = some .mload)]
  unfold Assembly.PrimStep.run
  rw [hStack]
  simp only [EvmYul.Stack.pop]
  rw [hLoad]
  simp [Simulation.Interaction.map,
    Simulation.Interaction.pure, StateRel.contractTargetBy,
    EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

/-- A scratch-allocated local is read through the exact emitted frame load. -/
theorem scratch_var_activation_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    {source : SourceState} {target : TargetState}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hSource : source.vars name = some value)
    (hDup : Locals.StackOp.dup? (stackOffset + frameDepth + 1) = some op) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase 1
        (.scratch frameDepth frameWords) target)
      (Functions.InteractionSemantics.Expr.openEval (.var name) source)
      (Structured.InteractionSemantics.Code.openRun
        [.op op, .push (AllocationSupport.slotOffset slot),
          .op .add, .op .mload]
        target) := by
  let frameWord := EvmYul.UInt256.ofNat frameBase
  let offsetWord := AllocationSupport.slotOffset slot
  let address := EvmYul.UInt256.add offsetWord frameWord
  let afterDup := StateRel.pushTarget frameWord target
  let afterPush := StateRel.pushTargetBy 33 offsetWord afterDup
  let afterAdd :=
    StateRel.contractTargetBy 1 address target.evm.stack afterPush
  let targetFinal :=
    StateRel.contractTargetBy 1 value target.evm.stack afterAdd
  have hAddress :
      address = EvmYul.UInt256.ofNat (scratchAddress frameBase slot) := by
    change
      EvmYul.UInt256.ofNat (32 * slot) + EvmYul.UInt256.ofNat frameBase =
        EvmYul.UInt256.ofNat
          (frameBase + MemoryContract.wordBytes * slot)
    rw [Assembly.UInt256_ofNat_add]
    simp [MemoryContract.wordBytes, Nat.add_comm]
  have hAfterDupRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source afterDup :=
    hRel.push_target_by 1 frameWord
  have hAfterPushRel :
      ScratchStateRel contract plan live (stackOffset + 2) frameBase
        frameDepth frameWords source afterPush :=
    hAfterDupRel.push_target_by 33 offsetWord
  have hAfterPushStack :
      afterPush.evm.stack = offsetWord :: frameWord :: target.evm.stack := by
    rfl
  have hAfterAddRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source afterAdd :=
    hAfterPushRel.contract_target_by hAfterPushStack 1
  have hAfterAddStack :
      afterAdd.evm.stack = address :: target.evm.stack := by
    rfl
  have hLoad :
      afterAdd.evm.toMachineState.mload address =
        (value, afterAdd.evm.toMachineState) := by
    have hMachine := hAfterAddRel.mload_machine_eq hLive hLocation
    have hStored :=
      hAfterAddRel.base.store name (.scratch slot) hLive hLocation
    rw [hSource] at hStored
    simp only [Option.getD_some] at hStored
    simpa [hAddress, hStored] using hMachine
  have hFinalRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source targetFinal :=
    hAfterAddRel.replace_top_by hAfterAddStack 1
  have hTargetRun :
      Structured.InteractionSemantics.Code.openRun
          [.op op, .push offsetWord, .op .add, .op .mload] target =
        .done (.ok targetFinal) := by
    calc
      Structured.InteractionSemantics.Code.openRun
          [.op op, .push offsetWord, .op .add, .op .mload] target =
          Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun [.op op] target)
            (Structured.InteractionSemantics.Code.openRun
              [.push offsetWord, .op .add, .op .mload]) := by
                simpa using
                  Structured.InteractionSemantics.Code.openRun_append
                    [.op op] [.push offsetWord, .op .add, .op .mload] target
      _ = Structured.InteractionSemantics.Code.openRun
            [.push offsetWord, .op .add, .op .mload] afterDup := by
              rw [Locals.InteractionPreservation.Code.openRun_dup
                hDup hRel.framePointer]
              rfl
      _ = Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun
              [.push offsetWord] afterDup)
            (Structured.InteractionSemantics.Code.openRun
              [.op .add, .op .mload]) := by
                simpa using
                  Structured.InteractionSemantics.Code.openRun_append
                    [.push offsetWord] [.op .add, .op .mload] afterDup
      _ = Structured.InteractionSemantics.Code.openRun
            [.op .add, .op .mload] afterPush := by
              rw [Locals.InteractionPreservation.Code.openRun_push]
              rfl
      _ = Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun [.op .add] afterPush)
            (Structured.InteractionSemantics.Code.openRun [.op .mload]) := by
                simpa using
                  Structured.InteractionSemantics.Code.openRun_append
                    [.op .add] [.op .mload] afterPush
      _ = Structured.InteractionSemantics.Code.openRun [.op .mload] afterAdd := by
              rw [openRun_add hAfterPushStack]
              rfl
      _ = .done (.ok targetFinal) := openRun_mload hAfterAddStack hLoad
  unfold Functions.InteractionSemantics.Expr.openEval
    Locals.InteractionSemantics.Expr.openEval
    Locals.Source.Effectful.Expr.Control.eval
  simp only [Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.vars, id_eq, hSource]
  rw [hTargetRun]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ⟨ActivationStateRel.scratch hFinalRel, rfl, ?_⟩
  rfl

/--
Compiler-facing variable preservation. The ordinary allocation artifact and
compiler decide between a stack `DUP` and the scratch-frame load sequence.
-/
theorem var_of_lower_compile
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {name : Locals.Name} {value : Word}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    {source : SourceState} {target : TargetState}
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState (.var name) =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hSource : source.vars name = some value) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase 1 mode target)
      (Functions.InteractionSemantics.Expr.openEval (.var name) source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  cases AllocationContext.classify_activation_var
      hCtx hLive hLower hCompile with
  | @stack _ planDepth depth op hLocation hDepth _hDepthValid hDup =>
      exact stack_var_activation_open hRel hLive hLocation hDepth hSource hDup
  | scratch frameDepth frameWords slot op hLocation hDup =>
      cases hRel with
      | scratch state =>
          exact scratch_var_activation_open
            state hLive hLocation hSource hDup

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

/-- Compose a checked expression head with every safe continuation of its tail. -/
theorem exprSeq_cons_of_parts
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase left right : Nat}
    {mode : ActivationMode}
    {head : Functions.Expr left} {tail : Locals.ExprSeq right}
    {source : SourceState} {target : TargetState}
    (headCode tailCode : Structured.Code)
    (hHead :
      Simulation.Interaction.Rel
        (AllocationInteractionPrimitive.ActivationExprOutcomeRel
          contract plan live stackOffset frameBase left mode target)
        (Functions.InteractionSemantics.Expr.openEval head source)
        (Structured.InteractionSemantics.Code.openRun headCode target))
    (hTailSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              AllocationInteractionSafety.ExprSeqSafe contract tail result.1)
        (Functions.InteractionSemantics.Expr.openEval head source))
    (hTail :
      ∀ {sourceHead : SourceState} {targetHead : TargetState}
        {headValues : List Word},
        ActivationExprResultRel contract plan live stackOffset frameBase left
            mode sourceHead target targetHead headValues →
        AllocationInteractionSafety.ExprSeqSafe contract tail sourceHead →
        Simulation.Interaction.Rel
          (AllocationInteractionPrimitive.ActivationExprOutcomeRel
            contract plan live (stackOffset + left) frameBase right mode
            targetHead)
          (Functions.InteractionSemantics.ExprSeq.openEval tail sourceHead)
          (Structured.InteractionSemantics.Code.openRun tailCode targetHead)) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase (left + right) mode target)
      (Functions.InteractionSemantics.ExprSeq.openEval (.cons head tail) source)
      (Structured.InteractionSemantics.Code.openRun
        (headCode ++ tailCode) target) := by
  rw [Structured.InteractionSemantics.Code.openRun_append]
  unfold Functions.InteractionSemantics.ExprSeq.openEval
    Locals.InteractionSemantics.ExprSeq.openEval
    Locals.Source.Effectful.Expr.Control.ExprSeq.eval
  have hHeadSafe :=
    Simulation.Interaction.Rel.strengthen_left hHead hTailSafe
  apply Simulation.Interaction.Rel.bind_custom hHeadSafe
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hHeadDone, hSafeDone⟩
  cases hHeadDone with
  | @error sourceError targetError hError =>
      cases hError
      exact Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.error rfl)
  | @ok sourceHeadResult targetHead hHeadResult =>
      rcases sourceHeadResult with ⟨sourceHead, headValues⟩
      simp only [Prod.fst, Prod.snd] at hHeadResult hSafeDone
      have hTailRel := hTail hHeadResult hSafeDone
      have hMapped :
          Simulation.Interaction.Rel
            (AllocationInteractionPrimitive.ActivationExprOutcomeRel
              contract plan live stackOffset frameBase (left + right) mode
              target)
            (Simulation.Interaction.bind
              (Functions.InteractionSemantics.ExprSeq.openEval tail sourceHead)
              (fun result =>
                Simulation.Interaction.pure
                  (result.1, headValues ++ result.2)))
            (Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun tailCode targetHead)
              Simulation.Interaction.pure) := by
        apply Simulation.Interaction.Rel.bind_custom hTailRel
        intro sourceTailDone targetTailDone hTailDone
        cases hTailDone with
        | @error sourceError targetError hError =>
            cases hError
            exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error rfl)
        | @ok sourceTailResult targetFinal hTailResult =>
            rcases sourceTailResult with ⟨sourceFinal, tailValues⟩
            simp only
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            exact ActivationExprResultRel.append hHeadResult hTailResult
      simpa using hMapped

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
