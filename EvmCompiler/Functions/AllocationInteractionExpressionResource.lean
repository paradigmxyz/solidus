import EvmCompiler.Functions.AllocationInteractionExpressionRecursive
import EvmCompiler.Functions.AllocationInteractionFrameExecution

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionExpressionResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionFrameExecution

abbrev ResultRel
    (contract : MemoryContract.Contract) (config : Config)
    (allocatorDepth : Nat) (plan : Plan) (live : List Locals.Name)
    (stackOffset frameBase results : Nat) (mode : ActivationMode)
    (semanticInitial resourceInitial : TargetState)
    (source : SourceState × List Word) (targetFinal : TargetState) : Prop :=
  ActivationExprResultRel contract plan live stackOffset frameBase results
      mode source.1 semanticInitial targetFinal source.2 ∧
    AllocatorEffect config allocatorDepth resourceInitial targetFinal

abbrev OutcomeRel
    (contract : MemoryContract.Contract) (config : Config)
    (allocatorDepth : Nat) (plan : Plan) (live : List Locals.Name)
    (stackOffset frameBase results : Nat) (mode : ActivationMode)
    (semanticInitial resourceInitial : TargetState) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (ResultRel contract config allocatorDepth plan live stackOffset
      frameBase results mode semanticInitial resourceInitial)

/-- Resource companion implemented once per primitive semantic family. -/
structure PrimitiveForward (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  preserve :
    ∀ {globalFrameWords allocatorDepth : Nat} {config : Config}
      {plan : Plan} {live : List Locals.Name}
      {stackOffset frameBase : Nat} {mode : ActivationMode}
      {sourceArgs : SourceState}
      {initialTarget targetArgs : TargetState} {values : List Word},
    AllocationSupport.scratchFrameConfig?
        contract globalFrameWords = some config →
    values.length = Expressions.Structured.BasicOp.inputs op →
    ActivationStateRel contract plan live
        (stackOffset + Expressions.Structured.BasicOp.inputs op)
        frameBase mode sourceArgs targetArgs →
    targetArgs.evm.stack = values.reverse ++ initialTarget.evm.stack →
    AllocationInteractionPrimitive.PrimitiveSafe
        contract op sourceArgs values →
    AllocatorReady config allocatorDepth targetArgs →
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase (Expressions.Structured.BasicOp.outputs op) mode
        initialTarget targetArgs)
      (Locals.InteractionSemantics.Primitive.openEval op sourceArgs values)
      (Structured.InteractionSemantics.BasicInstr.openStep (.op op)
        targetArgs)

/-- Literals alter only target stack/control metadata. -/
theorem literal
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat} {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    (value : Word)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase 1 mode target target)
      (Functions.InteractionSemantics.Expr.openEval (.lit value) source)
      (Structured.InteractionSemantics.Code.openRun [.push value] target) := by
  rw [Locals.InteractionPreservation.Code.openRun_push]
  change
    Simulation.Interaction.Rel _
      (.done (.ok (source, [value])))
      (.done (.ok (StateRel.pushTargetBy 33 value target)))
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ⟨ActivationExprResultRel.literal value hRel, ?_⟩
  apply AllocatorEffect.of_machine_eq hReady
  rfl

/-- Stack-local reads alter only target stack/control metadata. -/
theorem stackVar
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat} {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase planDepth depth : Nat} {mode : ActivationMode}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    {source : SourceState} {target : TargetState}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth?
          name (currentStackOrder plan live) =
        some (depth + 1))
    (hSource : source.vars name = some value)
    (hDup : Locals.StackOp.dup? (stackOffset + depth + 1) = some op)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase 1 mode target target)
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
  refine ⟨⟨hRel.push_target_by 1 value, rfl, ?_⟩, ?_⟩
  · simp [StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · apply AllocatorEffect.of_machine_eq hReady
    rfl

/-- Scratch-local loads read the frame without changing its machine state. -/
theorem scratchVar
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat} {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    {source : SourceState} {target : TargetState}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hSource : source.vars name = some value)
    (hDup : Locals.StackOp.dup? (stackOffset + frameDepth + 1) = some op)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase 1 (.scratch frameDepth frameWords) target target)
      (Functions.InteractionSemantics.Expr.openEval (.var name) source)
      (Structured.InteractionSemantics.Code.openRun
        [.op op, .push (AllocationSupport.slotOffset slot),
          .op .add, .op .mload] target) := by
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
      afterPush.evm.stack = offsetWord :: frameWord :: target.evm.stack := rfl
  have hAfterAddRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source afterAdd :=
    hAfterPushRel.contract_target_by hAfterPushStack 1
  have hAfterAddStack :
      afterAdd.evm.stack = address :: target.evm.stack := rfl
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
              simpa using Structured.InteractionSemantics.Code.openRun_append
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
              simpa using Structured.InteractionSemantics.Code.openRun_append
                [.push offsetWord] [.op .add, .op .mload] afterDup
      _ = Structured.InteractionSemantics.Code.openRun
            [.op .add, .op .mload] afterPush := by
              rw [Locals.InteractionPreservation.Code.openRun_push]
              rfl
      _ = Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun [.op .add] afterPush)
            (Structured.InteractionSemantics.Code.openRun [.op .mload]) := by
              simpa using Structured.InteractionSemantics.Code.openRun_append
                [.op .add] [.op .mload] afterPush
      _ = Structured.InteractionSemantics.Code.openRun
            [.op .mload] afterAdd := by
              rw [Code.openRun_add hAfterPushStack]
              rfl
      _ = .done (.ok targetFinal) := Code.openRun_mload hAfterAddStack hLoad
  unfold Functions.InteractionSemantics.Expr.openEval
    Locals.InteractionSemantics.Expr.openEval
    Locals.Source.Effectful.Expr.Control.eval
  simp only [Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.vars, id_eq, hSource]
  rw [hTargetRun]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ⟨⟨ActivationStateRel.scratch hFinalRel, rfl, ?_⟩, ?_⟩
  · rfl
  · apply AllocatorEffect.of_machine_eq hReady
    rfl

/-- Compiler-selected variable resource preservation in either activation. -/
theorem var_of_lower_compile
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat} {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
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
    (hSource : source.vars name = some value)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase 1 mode target target)
      (Functions.InteractionSemantics.Expr.openEval (.var name) source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  cases AllocationContext.classify_activation_var
      hCtx hLive hLower hCompile with
  | @stack _ planDepth depth op hLocation hDepth _hDepthValid hDup =>
      exact stackVar hRel hLive hLocation hDepth hSource hDup hReady
  | scratch frameDepth frameWords slot op hLocation hDup =>
      cases hRel with
      | scratch state =>
          exact scratchVar state hLive hLocation hSource hDup hReady

/-- Compose resource-preserving arguments with one primitive capability. -/
theorem prim_of_args
    {contract : MemoryContract.Contract} {config : Config}
    {globalFrameWords allocatorDepth : Nat}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    (op : Structured.BasicOp)
    (hPrimitive : PrimitiveForward contract op)
    (args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op))
    (argsCode : Structured.Code)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hArgs :
      Simulation.Interaction.Rel
        (OutcomeRel contract config allocatorDepth plan live stackOffset
          frameBase (Expressions.Structured.BasicOp.inputs op) mode
          target target)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (Structured.InteractionSemantics.Code.openRun argsCode target))
    (hSafe :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase (Expressions.Structured.BasicOp.outputs op) mode
        target target)
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
      rcases hArgsResult with ⟨hArgsSemantic, hArgsEffect⟩
      simp only
      rw [Structured.InteractionSemantics.Code.openRun_single]
      have hPrim :=
        hPrimitive.preserve hConfig hArgsSemantic.valuesLength
          hArgsSemantic.state hArgsSemantic.stack
          (by simpa [AllocationInteractionPrimitive.PrimitiveArgsSafe] using
            hSafeDone)
          hArgsEffect.ready
      apply Simulation.Interaction.Rel.mono hPrim
      intro sourceFinal targetFinal hDone
      cases hDone with
      | error hError =>
          exact Simulation.Interaction.ExceptRel.error hError
      | ok hResult =>
          exact Simulation.Interaction.ExceptRel.ok
            ⟨hResult.1, hArgsEffect.trans hResult.2⟩

/-- Compose one resource-preserving expression with its safe tail. -/
theorem exprSeq_cons_of_parts
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat} {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase left right : Nat} {mode : ActivationMode}
    {head : Functions.Expr left} {tail : Locals.ExprSeq right}
    {source : SourceState} {target : TargetState}
    (headCode tailCode : Structured.Code)
    (hHead :
      Simulation.Interaction.Rel
        (OutcomeRel contract config allocatorDepth plan live stackOffset
          frameBase left mode target target)
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
        AllocatorReady config allocatorDepth targetHead →
        AllocationInteractionSafety.ExprSeqSafe contract tail sourceHead →
        Simulation.Interaction.Rel
          (OutcomeRel contract config allocatorDepth plan live
            (stackOffset + left) frameBase right mode targetHead targetHead)
          (Functions.InteractionSemantics.ExprSeq.openEval tail sourceHead)
          (Structured.InteractionSemantics.Code.openRun tailCode targetHead)) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase (left + right) mode target target)
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
      rcases hHeadResult with ⟨hHeadSemantic, hHeadEffect⟩
      simp only [Prod.fst, Prod.snd] at hHeadSemantic hSafeDone
      have hTailRel :=
        hTail hHeadSemantic hHeadEffect.ready hSafeDone
      have hMapped :
          Simulation.Interaction.Rel
            (OutcomeRel contract config allocatorDepth plan live stackOffset
              frameBase (left + right) mode target target)
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
            rcases hTailResult with ⟨hTailSemantic, hTailEffect⟩
            simp only
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            exact
              ⟨ActivationExprResultRel.append
                  hHeadSemantic hTailSemantic,
                hHeadEffect.trans hTailEffect⟩
      simpa using hMapped

/-- Compiler-facing primitive resource composition. -/
theorem prim_of_lower_compile
    {contract : MemoryContract.Contract} {config : Config}
    {globalFrameWords allocatorDepth : Nat}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {source : SourceState} {target : TargetState}
    (op : Structured.BasicOp)
    (hPrimitive : PrimitiveForward contract op)
    (args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op))
    {lowered : Locals.Expr (Expressions.Structured.BasicOp.outputs op)}
    {code : Structured.Code}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
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
        (OutcomeRel contract config allocatorDepth plan live stackOffset
          frameBase (Expressions.Structured.BasicOp.inputs op) mode
          target target)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (Structured.InteractionSemantics.Code.openRun argsCode target))
    (hSafe :
      Simulation.Interaction.AllDone
        (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
        (Functions.InteractionSemantics.ExprSeq.openEval args source)) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase (Expressions.Structured.BasicOp.outputs op) mode
        target target)
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
          exact prim_of_args op hPrimitive args argsCode hConfig
            (hArgsPreserve hLowerArgs hArgsCode) hSafe

mutual
  private def exprHeight :
      {results : Nat} → Functions.Expr results → Nat
    | _, .lit _ => 1
    | _, .var _ => 1
    | _, .code _ => 1
    | _, .prim _ args => exprSeqHeight args + 1

  private def exprSeqHeight :
      {results : Nat} → Locals.ExprSeq results → Nat
    | _, .nil => 1
    | _, .cons head tail => exprHeight head + exprSeqHeight tail + 1
end

set_option maxHeartbeats 800000 in
mutual
  theorem forwardExprFuel
      {contract : MemoryContract.Contract}
      (primitiveOwner : ∀ op, PrimitiveForward contract op)
      (fuel : Nat)
      {globalFrameWords allocatorDepth : Nat} {config : Config}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
      {plan : Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat} {mode : ActivationMode}
      {expr : Functions.Expr results}
      {lowered : Locals.Expr results} {code : Structured.Code}
      {source : SourceState} {target : TargetState}
      (hConfig :
        AllocationSupport.scratchFrameConfig? contract globalFrameWords =
          some config)
      (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
      (hFuel : exprHeight expr ≤ fuel)
      (hCtx :
        AllocationContext.ActivationExprContext
          lowerCtx lowerState localsCtx plan live mode)
      (hScoped : Functions.Scope.ExprScoped live expr)
      (hLower :
        AllocationLowering.lowerExpr lowerCtx lowerState expr = some lowered)
      (hCompile :
        Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
      (hRel :
        ActivationStateRel contract plan live stackOffset frameBase mode
          source target)
      (hReady : AllocatorReady config allocatorDepth target) :
      Simulation.Interaction.Rel
        (OutcomeRel contract config allocatorDepth plan live stackOffset
          frameBase results mode target target)
        (Functions.InteractionSemantics.Expr.openEval expr source)
        (Structured.InteractionSemantics.Code.openRun code target) := by
    cases expr with
    | lit value =>
        have hLowered : lowered = .lit value := by
          simpa [AllocationLowering.lowerExpr] using hLower.symm
        subst lowered
        have hCode : code = [.push value] := by
          simpa [Locals.Expr.compileCode] using hCompile.symm
        subst code
        exact literal value hRel hReady
    | var name =>
        obtain ⟨value, hValue⟩ := hSafe
        have hLive : name ∈ live := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        exact var_of_lower_compile hCtx hLive hLower hCompile hRel hValue hReady
    | code rawCode =>
        simp [AllocationInteractionSafety.ExprSafe] at hSafe
    | prim op args =>
        rcases hSafe with ⟨_hSupported, hArgsSafe, hPrimitiveSafe⟩
        have hArgsScoped : Functions.Scope.ExprSeqScoped live args := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        apply prim_of_lower_compile op (primitiveOwner op) args hConfig
          hLower hCompile
        · intro loweredArgs argsCode hLowerArgs hArgsCode
          exact forwardExprSeqFuel primitiveOwner (fuel - 1) hConfig
            hArgsSafe (by
              simp only [exprHeight] at hFuel
              omega)
            hCtx hArgsScoped hLowerArgs hArgsCode hRel hReady
        · exact hPrimitiveSafe
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega

  theorem forwardExprSeqFuel
      {contract : MemoryContract.Contract}
      (primitiveOwner : ∀ op, PrimitiveForward contract op)
      (fuel : Nat)
      {globalFrameWords allocatorDepth : Nat} {config : Config}
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
      {plan : Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat} {mode : ActivationMode}
      {exprs : Locals.ExprSeq results}
      {lowered : Locals.ExprSeq results} {code : Structured.Code}
      {source : SourceState} {target : TargetState}
      (hConfig :
        AllocationSupport.scratchFrameConfig? contract globalFrameWords =
          some config)
      (hSafe :
        AllocationInteractionSafety.ExprSeqSafe contract exprs source)
      (hFuel : exprSeqHeight exprs ≤ fuel)
      (hCtx :
        AllocationContext.ActivationExprContext
          lowerCtx lowerState localsCtx plan live mode)
      (hScoped : Functions.Scope.ExprSeqScoped live exprs)
      (hLower :
        AllocationLowering.lowerExprSeq lowerCtx lowerState exprs =
          some lowered)
      (hCompile :
        Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
      (hRel :
        ActivationStateRel contract plan live stackOffset frameBase mode
          source target)
      (hReady : AllocatorReady config allocatorDepth target) :
      Simulation.Interaction.Rel
        (OutcomeRel contract config allocatorDepth plan live stackOffset
          frameBase results mode target target)
        (Functions.InteractionSemantics.ExprSeq.openEval exprs source)
        (Structured.InteractionSemantics.Code.openRun code target) := by
    cases exprs with
    | nil =>
        have hLowered : lowered = .nil := by
          simpa [AllocationLowering.lowerExprSeq] using hLower.symm
        subst lowered
        have hCode : code = [] := by
          simpa [Locals.ExprSeq.compileCode] using hCompile.symm
        subst code
        change
          Simulation.Interaction.Rel _
            (.done (.ok (source, []))) (.done (.ok target))
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        exact ⟨ActivationExprResultRel.nil hRel,
          AllocatorEffect.refl hReady⟩
    | @cons left right head tail =>
        rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
        have hScopedParts :
            Functions.Scope.ExprScoped live head ∧
              Functions.Scope.ExprSeqScoped live tail := by
          simpa [Functions.Scope.ExprSeqScoped] using hScoped
        cases hLowerHead :
            AllocationLowering.lowerExpr lowerCtx lowerState head with
        | none =>
            simp [AllocationLowering.lowerExprSeq, hLowerHead] at hLower
        | some loweredHead =>
            cases hLowerTail :
                AllocationLowering.lowerExprSeq lowerCtx lowerState tail with
            | none =>
                simp [AllocationLowering.lowerExprSeq, hLowerHead,
                  hLowerTail] at hLower
            | some loweredTail =>
                have hLowered :
                    lowered = .cons loweredHead loweredTail := by
                  simpa [AllocationLowering.lowerExprSeq, hLowerHead,
                    hLowerTail] using hLower.symm
                subst lowered
                cases hHeadCode :
                    Locals.Expr.compileCode localsCtx stackOffset loweredHead with
                | none =>
                    simp [Locals.ExprSeq.compileCode, hHeadCode] at hCompile
                | some headCode =>
                    cases hTailCode :
                        Locals.ExprSeq.compileCode
                          localsCtx (stackOffset + left) loweredTail with
                    | none =>
                        simp [Locals.ExprSeq.compileCode, hHeadCode,
                          hTailCode] at hCompile
                    | some tailCode =>
                        have hCode : code = headCode ++ tailCode := by
                          simpa [Locals.ExprSeq.compileCode, hHeadCode,
                            hTailCode] using hCompile.symm
                        subst code
                        apply exprSeq_cons_of_parts headCode tailCode
                        · exact forwardExprFuel primitiveOwner (fuel - 1)
                            hConfig hHeadSafe (by
                              simp only [exprSeqHeight] at hFuel
                              omega)
                            hCtx hScopedParts.1 hLowerHead hHeadCode hRel hReady
                        · exact hTailSafe
                        · intro sourceHead targetHead headValues hHeadRel
                            hHeadReady hTailSafeAt
                          exact forwardExprSeqFuel primitiveOwner (fuel - 1)
                            hConfig hTailSafeAt (by
                              simp only [exprSeqHeight] at hFuel
                              omega)
                            hCtx hScopedParts.2 hLowerTail hTailCode
                            hHeadRel.state hHeadReady
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega
end

theorem forwardExpr
    {contract : MemoryContract.Contract}
    (primitiveOwner : ∀ op, PrimitiveForward contract op)
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat} {mode : ActivationMode}
    {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr = some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase results mode target target)
      (Functions.InteractionSemantics.Expr.openEval expr source)
      (Structured.InteractionSemantics.Code.openRun code target) :=
  forwardExprFuel primitiveOwner (exprHeight expr) hConfig hSafe
    (Nat.le_refl _) hCtx hScoped hLower hCompile hRel hReady

theorem forwardExprSeq
    {contract : MemoryContract.Contract}
    (primitiveOwner : ∀ op, PrimitiveForward contract op)
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat} {mode : ActivationMode}
    {exprs : Locals.ExprSeq results}
    {lowered : Locals.ExprSeq results} {code : Structured.Code}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSeqSafe contract exprs source)
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hLower :
      AllocationLowering.lowerExprSeq lowerCtx lowerState exprs = some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OutcomeRel contract config allocatorDepth plan live stackOffset
        frameBase results mode target target)
      (Functions.InteractionSemantics.ExprSeq.openEval exprs source)
      (Structured.InteractionSemantics.Code.openRun code target) :=
  forwardExprSeqFuel primitiveOwner (exprSeqHeight exprs) hConfig hSafe
    (Nat.le_refl _) hCtx hScoped hLower hCompile hRel hReady

end AllocationInteractionExpressionResource
end Functions
end EvmCompiler
