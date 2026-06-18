import EvmCompiler.Functions.AllocationInteractionRelation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionPrimitive

open AllocationInteractionRelation

def callOp : Simulation.CallKind → Structured.BasicOp
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .staticcall => .staticcall

def createOp : Simulation.CreateKind → Structured.BasicOp
  | .create => .create
  | .create2 => .create2

abbrev ScratchExprOutcomeRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name)
    (stackOffset frameBase frameDepth frameWords results : Nat)
    (initialTarget : TargetState) :
    Except EVMException (SourceState × List Word) →
      Except EVMException TargetState → Prop :=
  Simulation.Interaction.ExceptRel Eq
    (fun sourceResult targetFinal =>
      ScratchExprResultRel contract plan live stackOffset frameBase
        frameDepth frameWords results sourceResult.1 initialTarget
        targetFinal sourceResult.2)

/-- One CALL-family request and every possible response preserve allocation. -/
theorem call_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {initialTarget target : TargetState}
    (kind : Simulation.CallKind) (operands : Simulation.CallOperands)
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + kind.inputArity) frameBase
        frameDepth frameWords source target)
    (hStack :
      target.evm.stack = kind.args operands ++ initialTarget.evm.stack)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        (kind.canonicalOperands operands).inputOffset.toNat
        (kind.canonicalOperands operands).inputSize.toNat)
    (hOutput :
      Simulation.MemorySafety.WindowSafe contract
        (kind.canonicalOperands operands).outputOffset.toNat
        (kind.canonicalOperands operands).outputSize.toNat) :
    Simulation.Interaction.Rel
      (ScratchExprOutcomeRel contract plan live stackOffset frameBase
        frameDepth frameWords 1 initialTarget)
      (Locals.InteractionSemantics.Primitive.openEval (callOp kind) source
        (kind.args operands).reverse)
      (Structured.InteractionSemantics.BasicInstr.openStep
        (.op (callOp kind)) target) := by
  let parsed := kind.canonicalOperands operands
  let sourceEVM :=
    Locals.InteractionSemantics.Primitive.isolated source
      (kind.args operands).reverse
  have hSourceStack : sourceEVM.stack = kind.args operands := by
    simp [sourceEVM, Locals.InteractionSemantics.Primitive.isolated]
  have hSourceOperands :
      kind.evmOperands? sourceEVM.stack = some ([], parsed) := by
    rw [hSourceStack]
    simpa [parsed] using kind.evmOperands?_args operands []
  have hTargetOperands :
      kind.evmOperands? target.evm.stack =
        some (initialTarget.evm.stack, parsed) := by
    rw [hStack]
    simp [parsed]
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    simpa [sourceEVM,
      Locals.InteractionSemantics.Primitive.isolated] using hRel.base.shared
  have hAllowed :
      kind.allowedIn
          (Simulation.ExternalFrame.ofShared sourceEVM.toSharedState) parsed =
        kind.allowedIn
          (Simulation.ExternalFrame.ofShared target.evm.toSharedState) parsed := by
    have hEnv := hInputRel.executionEnv_eq
    cases kind <;>
      simp [Simulation.CallKind.allowedIn,
        Simulation.ExternalFrame.ofShared, hEnv]
  have hWorld := hInputRel.openWorld_eq
  have hRequest := hInputRel.callRequest_eq kind parsed hInput
  cases kind with
  | call =>
      simp only [callOp]
      rw [Locals.InteractionSemantics.Primitive.openEval_call]
      · change
          Simulation.Interaction.Rel _
            (Simulation.Interaction.map
              (Locals.InteractionSemantics.Primitive.finish source)
              (Assembly.InteractionSemantics.PrimOp.callStep .call sourceEVM))
            (Simulation.Interaction.map target.withEVM
              (Assembly.InteractionSemantics.PrimOp.callStep .call target.evm))
        unfold Assembly.InteractionSemantics.PrimOp.callStep
        rw [hSourceOperands, hTargetOperands]
        simp only
        rw [hAllowed, hWorld, hRequest]
        split
        · apply Simulation.Interaction.Rel.request
          intro response
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨?_, rfl, ?_⟩
          · exact hRel.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simp [Simulation.CallKind.args]
  | callcode =>
      simp only [callOp]
      rw [Locals.InteractionSemantics.Primitive.openEval_callcode]
      · change
          Simulation.Interaction.Rel _
            (Simulation.Interaction.map
              (Locals.InteractionSemantics.Primitive.finish source)
              (Assembly.InteractionSemantics.PrimOp.callStep .callcode sourceEVM))
            (Simulation.Interaction.map target.withEVM
              (Assembly.InteractionSemantics.PrimOp.callStep .callcode target.evm))
        unfold Assembly.InteractionSemantics.PrimOp.callStep
        rw [hSourceOperands, hTargetOperands]
        simp only
        rw [hAllowed, hWorld, hRequest]
        split
        · apply Simulation.Interaction.Rel.request
          intro response
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨?_, rfl, ?_⟩
          · exact hRel.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simp [Simulation.CallKind.args]
  | delegatecall =>
      simp only [callOp]
      rw [Locals.InteractionSemantics.Primitive.openEval_delegatecall]
      · change
          Simulation.Interaction.Rel _
            (Simulation.Interaction.map
              (Locals.InteractionSemantics.Primitive.finish source)
              (Assembly.InteractionSemantics.PrimOp.callStep .delegatecall sourceEVM))
            (Simulation.Interaction.map target.withEVM
              (Assembly.InteractionSemantics.PrimOp.callStep .delegatecall target.evm))
        unfold Assembly.InteractionSemantics.PrimOp.callStep
        rw [hSourceOperands, hTargetOperands]
        simp only
        rw [hAllowed, hWorld, hRequest]
        split
        · apply Simulation.Interaction.Rel.request
          intro response
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨?_, rfl, ?_⟩
          · exact hRel.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simp [Simulation.CallKind.args]
  | staticcall =>
      simp only [callOp]
      rw [Locals.InteractionSemantics.Primitive.openEval_staticcall]
      · change
          Simulation.Interaction.Rel _
            (Simulation.Interaction.map
              (Locals.InteractionSemantics.Primitive.finish source)
              (Assembly.InteractionSemantics.PrimOp.callStep .staticcall sourceEVM))
            (Simulation.Interaction.map target.withEVM
              (Assembly.InteractionSemantics.PrimOp.callStep .staticcall target.evm))
        unfold Assembly.InteractionSemantics.PrimOp.callStep
        rw [hSourceOperands, hTargetOperands]
        simp only
        rw [hAllowed, hWorld, hRequest]
        split
        · apply Simulation.Interaction.Rel.request
          intro response
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨?_, rfl, ?_⟩
          · exact hRel.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simp [Simulation.CallKind.args]

/-- One CREATE-family request and every possible response preserve allocation. -/
theorem create_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {initialTarget target : TargetState}
    (kind : Simulation.CreateKind) (operands : Simulation.CreateOperands)
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + kind.inputArity) frameBase
        frameDepth frameWords source target)
    (hStack :
      target.evm.stack = kind.args operands ++ initialTarget.evm.stack)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        (kind.canonicalOperands operands).initOffset.toNat
        (kind.canonicalOperands operands).initSize.toNat) :
    Simulation.Interaction.Rel
      (ScratchExprOutcomeRel contract plan live stackOffset frameBase
        frameDepth frameWords 1 initialTarget)
      (Locals.InteractionSemantics.Primitive.openEval (createOp kind) source
        (kind.args operands).reverse)
      (Structured.InteractionSemantics.BasicInstr.openStep
        (.op (createOp kind)) target) := by
  let parsed := kind.canonicalOperands operands
  let sourceEVM :=
    Locals.InteractionSemantics.Primitive.isolated source
      (kind.args operands).reverse
  have hSourceStack : sourceEVM.stack = kind.args operands := by
    simp [sourceEVM, Locals.InteractionSemantics.Primitive.isolated]
  have hSourceOperands :
      kind.evmOperands? sourceEVM.stack = some ([], parsed) := by
    rw [hSourceStack]
    simpa [parsed] using kind.evmOperands?_args operands []
  have hTargetOperands :
      kind.evmOperands? target.evm.stack =
        some (initialTarget.evm.stack, parsed) := by
    rw [hStack]
    simp [parsed]
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    simpa [sourceEVM,
      Locals.InteractionSemantics.Primitive.isolated] using hRel.base.shared
  have hPermission :
      (Simulation.ExternalFrame.ofShared sourceEVM.toSharedState).permission =
        (Simulation.ExternalFrame.ofShared target.evm.toSharedState).permission := by
    have hEnv := hInputRel.executionEnv_eq
    simpa [Simulation.ExternalFrame.ofShared] using
      congrArg EvmYul.ExecutionEnv.perm hEnv
  have hWorld := hInputRel.openWorld_eq
  have hRequest := hInputRel.createRequest_eq kind parsed hInput
  cases kind with
  | create =>
      simp only [createOp]
      rw [Locals.InteractionSemantics.Primitive.openEval_create]
      · change
          Simulation.Interaction.Rel _
            (Simulation.Interaction.map
              (Locals.InteractionSemantics.Primitive.finish source)
              (Assembly.InteractionSemantics.PrimOp.createStep .create sourceEVM))
            (Simulation.Interaction.map target.withEVM
              (Assembly.InteractionSemantics.PrimOp.createStep .create target.evm))
        unfold Assembly.InteractionSemantics.PrimOp.createStep
        rw [hSourceOperands, hTargetOperands]
        simp only
        rw [hPermission, hWorld, hRequest]
        split
        · apply Simulation.Interaction.Rel.request
          intro response
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨?_, rfl, ?_⟩
          · exact hRel.finishCreate sourceEVM rfl parsed.createLocal response
              hStack hInput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCreate,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simp [Simulation.CreateKind.args]
  | create2 =>
      simp only [createOp]
      rw [Locals.InteractionSemantics.Primitive.openEval_create2]
      · change
          Simulation.Interaction.Rel _
            (Simulation.Interaction.map
              (Locals.InteractionSemantics.Primitive.finish source)
              (Assembly.InteractionSemantics.PrimOp.createStep .create2 sourceEVM))
            (Simulation.Interaction.map target.withEVM
              (Assembly.InteractionSemantics.PrimOp.createStep .create2 target.evm))
        unfold Assembly.InteractionSemantics.PrimOp.createStep
        rw [hSourceOperands, hTargetOperands]
        simp only
        rw [hPermission, hWorld, hRequest]
        split
        · apply Simulation.Interaction.Rel.request
          intro response
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨?_, rfl, ?_⟩
          · exact hRel.finishCreate sourceEVM rfl parsed.createLocal response
              hStack hInput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCreate,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simp [Simulation.CreateKind.args]

end AllocationInteractionPrimitive
end Functions
end EvmCompiler
