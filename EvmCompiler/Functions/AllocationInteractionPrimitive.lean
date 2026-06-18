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

@[simp] theorem callOp_inputs (kind : Simulation.CallKind) :
    Expressions.Structured.BasicOp.inputs (callOp kind) = kind.inputArity := by
  cases kind <;> rfl

@[simp] theorem callOp_outputs (kind : Simulation.CallKind) :
    Expressions.Structured.BasicOp.outputs (callOp kind) = 1 := by
  cases kind <;> rfl

@[simp] theorem createOp_inputs (kind : Simulation.CreateKind) :
    Expressions.Structured.BasicOp.inputs (createOp kind) = kind.inputArity := by
  cases kind <;> rfl

@[simp] theorem createOp_outputs (kind : Simulation.CreateKind) :
    Expressions.Structured.BasicOp.outputs (createOp kind) = 1 := by
  cases kind <;> rfl

abbrev ActivationExprOutcomeRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name)
    (stackOffset frameBase results : Nat)
    (mode : ActivationMode) (initialTarget : TargetState) :
    Except EVMException (SourceState × List Word) →
      Except EVMException TargetState → Prop :=
  Simulation.Interaction.ExceptRel Eq
    (fun sourceResult targetFinal =>
      ActivationExprResultRel contract plan live stackOffset frameBase
        results mode sourceResult.1 initialTarget targetFinal sourceResult.2)

def CallMemorySafe (contract : MemoryContract.Contract)
    (kind : Simulation.CallKind) (values : List Word) : Prop :=
  ∀ operands,
    kind.evmOperands? values.reverse = some ([], operands) →
    Simulation.MemorySafety.WindowSafe contract
        operands.inputOffset.toNat operands.inputSize.toNat ∧
      Simulation.MemorySafety.WindowSafe contract
        operands.outputOffset.toNat operands.outputSize.toNat

def CreateMemorySafe (contract : MemoryContract.Contract)
    (kind : Simulation.CreateKind) (values : List Word) : Prop :=
  ∀ operands,
    kind.evmOperands? values.reverse = some ([], operands) →
    Simulation.MemorySafety.WindowSafe contract
      operands.initOffset.toNat operands.initSize.toNat

def CallArgsSafe (contract : MemoryContract.Contract)
    (kind : Simulation.CallKind) :
    Except EVMException (SourceState × List Word) → Prop
  | .error _ => True
  | .ok result => CallMemorySafe contract kind result.2

def CreateArgsSafe (contract : MemoryContract.Contract)
    (kind : Simulation.CreateKind) :
    Except EVMException (SourceState × List Word) → Prop
  | .error _ => True
  | .ok result => CreateMemorySafe contract kind result.2

def PrimitiveSafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (source : SourceState)
    (values : List Word) : Prop :=
  match Simulation.ExternalKind.ofEVMOperation? op.toPrimOp.toEVM with
  | some (.call kind) => CallMemorySafe contract kind values
  | some (.create kind) => CreateMemorySafe contract kind values
  | none =>
      Simulation.MemorySafety.OpenPrimitiveMemorySafe contract op
        source.shared.toMachineState values

def PrimitiveArgsSafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) :
    Except EVMException (SourceState × List Word) → Prop
  | .error _ => True
  | .ok result => PrimitiveSafe contract op result.1 result.2

@[simp] theorem primitiveSafe_callOp
    (contract : MemoryContract.Contract) (kind : Simulation.CallKind)
    (source : SourceState) (values : List Word) :
    PrimitiveSafe contract (callOp kind) source values =
      CallMemorySafe contract kind values := by
  cases kind <;> rfl

@[simp] theorem primitiveSafe_createOp
    (contract : MemoryContract.Contract) (kind : Simulation.CreateKind)
    (source : SourceState) (values : List Word) :
    PrimitiveSafe contract (createOp kind) source values =
      CreateMemorySafe contract kind values := by
  cases kind <;> rfl

/-- Stable adjacent interface implemented once per primitive semantic family. -/
structure OpenForward (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  preserve :
    ∀ {plan : Plan} {live : List Locals.Name}
      {stackOffset frameBase : Nat} {mode : ActivationMode}
      {source : SourceState} {initialTarget target : TargetState}
      {values : List Word},
    values.length = Expressions.Structured.BasicOp.inputs op →
    ActivationStateRel contract plan live
        (stackOffset + Expressions.Structured.BasicOp.inputs op)
        frameBase mode source target →
    target.evm.stack = values.reverse ++ initialTarget.evm.stack →
    PrimitiveSafe contract op source values →
    Simulation.Interaction.Rel
      (ActivationExprOutcomeRel contract plan live stackOffset frameBase
        (Expressions.Structured.BasicOp.outputs op) mode initialTarget)
      (Locals.InteractionSemantics.Primitive.openEval op source values)
      (Structured.InteractionSemantics.BasicInstr.openStep (.op op) target)

private theorem callOperands_of_length
    (kind : Simulation.CallKind) (stack : List Word)
    (hLength : stack.length = kind.inputArity) :
    ∃ operands, kind.evmOperands? stack = some ([], operands) := by
  cases kind with
  | call =>
      obtain ⟨rest, gas, address, value, inputOffset, inputSize,
          outputOffset, outputSize, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop7_of_seven_le
          (stack := stack)
          (by simp [Simulation.CallKind.inputArity] at hLength; omega)
      have hRestLength :=
        Assembly.PrimStep.Stack.length_of_pop7_some hPop
      have hRest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [Simulation.CallKind.inputArity] at hLength
        omega
      subst rest
      refine ⟨{
        requestedGas := gas, address := address, valueArg := value,
        inputOffset := inputOffset, inputSize := inputSize,
        outputOffset := outputOffset, outputSize := outputSize }, ?_⟩
      simp [Simulation.CallKind.evmOperands?, hPop]
  | callcode =>
      obtain ⟨rest, gas, address, value, inputOffset, inputSize,
          outputOffset, outputSize, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop7_of_seven_le
          (stack := stack)
          (by simp [Simulation.CallKind.inputArity] at hLength; omega)
      have hRestLength :=
        Assembly.PrimStep.Stack.length_of_pop7_some hPop
      have hRest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [Simulation.CallKind.inputArity] at hLength
        omega
      subst rest
      refine ⟨{
        requestedGas := gas, address := address, valueArg := value,
        inputOffset := inputOffset, inputSize := inputSize,
        outputOffset := outputOffset, outputSize := outputSize }, ?_⟩
      simp [Simulation.CallKind.evmOperands?, hPop]
  | delegatecall =>
      obtain ⟨rest, gas, address, inputOffset, inputSize,
          outputOffset, outputSize, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop6_of_six_le
          (stack := stack)
          (by simp [Simulation.CallKind.inputArity] at hLength; omega)
      have hRestLength :=
        Assembly.PrimStep.Stack.length_of_pop6_some hPop
      have hRest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [Simulation.CallKind.inputArity] at hLength
        omega
      subst rest
      refine ⟨{
        requestedGas := gas, address := address,
        valueArg := EvmYul.UInt256.ofNat 0,
        inputOffset := inputOffset, inputSize := inputSize,
        outputOffset := outputOffset, outputSize := outputSize }, ?_⟩
      simp [Simulation.CallKind.evmOperands?, hPop]
  | staticcall =>
      obtain ⟨rest, gas, address, inputOffset, inputSize,
          outputOffset, outputSize, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop6_of_six_le
          (stack := stack)
          (by simp [Simulation.CallKind.inputArity] at hLength; omega)
      have hRestLength :=
        Assembly.PrimStep.Stack.length_of_pop6_some hPop
      have hRest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [Simulation.CallKind.inputArity] at hLength
        omega
      subst rest
      refine ⟨{
        requestedGas := gas, address := address,
        valueArg := EvmYul.UInt256.ofNat 0,
        inputOffset := inputOffset, inputSize := inputSize,
        outputOffset := outputOffset, outputSize := outputSize }, ?_⟩
      simp [Simulation.CallKind.evmOperands?, hPop]

private theorem createOperands_of_length
    (kind : Simulation.CreateKind) (stack : List Word)
    (hLength : stack.length = kind.inputArity) :
    ∃ operands, kind.evmOperands? stack = some ([], operands) := by
  cases kind with
  | create =>
      obtain ⟨rest, value, initOffset, initSize, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop3_of_three_le
          (stack := stack)
          (by simp [Simulation.CreateKind.inputArity] at hLength; omega)
      have hRestLength :=
        Assembly.PrimStep.Stack.length_of_pop3_some hPop
      have hRest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [Simulation.CreateKind.inputArity] at hLength
        omega
      subst rest
      refine ⟨{
        value := value, initOffset := initOffset, initSize := initSize,
        saltArg := EvmYul.UInt256.ofNat 0 }, ?_⟩
      simp [Simulation.CreateKind.evmOperands?, hPop]
  | create2 =>
      obtain ⟨rest, value, initOffset, initSize, salt, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop4_of_four_le
          (stack := stack)
          (by simp [Simulation.CreateKind.inputArity] at hLength; omega)
      have hRestLength :=
        Assembly.PrimStep.Stack.length_of_pop4_some hPop
      have hRest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [Simulation.CreateKind.inputArity] at hLength
        omega
      subst rest
      refine ⟨{
        value := value, initOffset := initOffset, initSize := initSize,
        saltArg := salt }, ?_⟩
      simp [Simulation.CreateKind.evmOperands?, hPop]

/-- One CALL-family request and every possible response preserve allocation. -/
theorem call_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {initialTarget target : TargetState}
    (kind : Simulation.CallKind) (values : List Word)
    (hLength : values.length = kind.inputArity)
    (hRel :
      ActivationStateRel contract plan live
        (stackOffset + kind.inputArity) frameBase mode source target)
    (hStack :
      target.evm.stack = values.reverse ++ initialTarget.evm.stack)
    (hSafe : CallMemorySafe contract kind values) :
    Simulation.Interaction.Rel
      (ActivationExprOutcomeRel contract plan live stackOffset frameBase
        1 mode initialTarget)
      (Locals.InteractionSemantics.Primitive.openEval (callOp kind) source
        values)
      (Structured.InteractionSemantics.BasicInstr.openStep
        (.op (callOp kind)) target) := by
  obtain ⟨parsed, hDecoded⟩ :=
    callOperands_of_length kind values.reverse (by
      simpa [List.length_reverse] using hLength)
  obtain ⟨hInput, hOutput⟩ := hSafe parsed hDecoded
  have hRelPrefix :
      ActivationStateRel contract plan live
        (stackOffset + values.reverse.length) frameBase mode source target := by
    simpa [List.length_reverse, hLength] using hRel
  let sourceEVM :=
    Locals.InteractionSemantics.Primitive.isolated source values
  have hSourceOperands :
      kind.evmOperands? sourceEVM.stack = some ([], parsed) := by
    simpa [sourceEVM, Locals.InteractionSemantics.Primitive.isolated] using
      hDecoded
  have hTargetOperands :
      kind.evmOperands? target.evm.stack =
        some (initialTarget.evm.stack, parsed) := by
    rw [hStack]
    exact kind.evmOperands?_append_of_some initialTarget.evm.stack hDecoded
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    simpa [sourceEVM,
      Locals.InteractionSemantics.Primitive.isolated] using hRel.shared
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
          · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simpa [Simulation.CallKind.inputArity] using hLength
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
          · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simpa [Simulation.CallKind.inputArity] using hLength
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
          · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simpa [Simulation.CallKind.inputArity] using hLength
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
          · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal response
              hStack hInput hOutput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCall,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simpa [Simulation.CallKind.inputArity] using hLength

/-- One CREATE-family request and every possible response preserve allocation. -/
theorem create_open
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {initialTarget target : TargetState}
    (kind : Simulation.CreateKind) (values : List Word)
    (hLength : values.length = kind.inputArity)
    (hRel :
      ActivationStateRel contract plan live
        (stackOffset + kind.inputArity) frameBase mode source target)
    (hStack :
      target.evm.stack = values.reverse ++ initialTarget.evm.stack)
    (hSafe : CreateMemorySafe contract kind values) :
    Simulation.Interaction.Rel
      (ActivationExprOutcomeRel contract plan live stackOffset frameBase
        1 mode initialTarget)
      (Locals.InteractionSemantics.Primitive.openEval (createOp kind) source
        values)
      (Structured.InteractionSemantics.BasicInstr.openStep
        (.op (createOp kind)) target) := by
  obtain ⟨parsed, hDecoded⟩ :=
    createOperands_of_length kind values.reverse (by
      simpa [List.length_reverse] using hLength)
  have hInput := hSafe parsed hDecoded
  have hRelPrefix :
      ActivationStateRel contract plan live
        (stackOffset + values.reverse.length) frameBase mode source target := by
    simpa [List.length_reverse, hLength] using hRel
  let sourceEVM :=
    Locals.InteractionSemantics.Primitive.isolated source values
  have hSourceOperands :
      kind.evmOperands? sourceEVM.stack = some ([], parsed) := by
    simpa [sourceEVM, Locals.InteractionSemantics.Primitive.isolated] using
      hDecoded
  have hTargetOperands :
      kind.evmOperands? target.evm.stack =
        some (initialTarget.evm.stack, parsed) := by
    rw [hStack]
    exact kind.evmOperands?_append_of_some initialTarget.evm.stack hDecoded
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    simpa [sourceEVM,
      Locals.InteractionSemantics.Primitive.isolated] using hRel.shared
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
          · exact hRelPrefix.finishCreate sourceEVM rfl parsed.createLocal response
              hStack hInput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCreate,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simpa [Simulation.CreateKind.inputArity] using hLength
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
          · exact hRelPrefix.finishCreate sourceEVM rfl parsed.createLocal response
              hStack hInput
          · simp [Locals.InteractionSemantics.Primitive.finish,
              Structured.RunState.withEVM,
              Assembly.InteractionSemantics.EVMState.finishCreate,
              Assembly.InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC]
        · exact Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.error rfl)
      · simpa [Simulation.CreateKind.inputArity] using hLength

theorem call_openForward (contract : MemoryContract.Contract)
    (kind : Simulation.CallKind) : OpenForward contract (callOp kind) where
  preserve := by
    intro plan live stackOffset frameBase mode source initialTarget target
      values hLength hRel hStack hSafe
    simpa using
      call_open (contract := contract) (plan := plan) (live := live)
        (stackOffset := stackOffset) (frameBase := frameBase)
        (mode := mode) (source := source) (initialTarget := initialTarget)
        (target := target) kind values (by simpa using hLength)
        (by simpa using hRel) hStack (by simpa using hSafe)

theorem create_openForward (contract : MemoryContract.Contract)
    (kind : Simulation.CreateKind) : OpenForward contract (createOp kind) where
  preserve := by
    intro plan live stackOffset frameBase mode source initialTarget target
      values hLength hRel hStack hSafe
    simpa using
      create_open (contract := contract) (plan := plan) (live := live)
        (stackOffset := stackOffset) (frameBase := frameBase)
        (mode := mode) (source := source) (initialTarget := initialTarget)
        (target := target) kind values (by simpa using hLength)
        (by simpa using hRel) hStack (by simpa using hSafe)

end AllocationInteractionPrimitive
end Functions
end EvmCompiler
