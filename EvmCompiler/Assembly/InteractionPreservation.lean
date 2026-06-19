import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Assembly.Preservation

namespace EvmCompiler
namespace Assembly
namespace InteractionPreservation

open InteractionSemantics

namespace EVMState

@[simp] theorem finishCall_pc
    (state : EVMState) (rest : EvmYul.Stack Word)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse) :
    (InteractionSemantics.EVMState.finishCall
      state rest callLocal response).pc =
        state.pc + EvmYul.UInt256.ofNat 1 := by
  simp [InteractionSemantics.EVMState.finishCall,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]

@[simp] theorem finishCreate_pc
    (state : EVMState) (rest : EvmYul.Stack Word)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse) :
    (InteractionSemantics.EVMState.finishCreate
      state rest createLocal response).pc =
        state.pc + EvmYul.UInt256.ofNat 1 := by
  simp [InteractionSemantics.EVMState.finishCreate,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]

theorem finishCall_sameRuntimeData
    {target source : EVMState}
    (rest : EvmYul.Stack Word)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse)
    (hRel : SameRuntimeData target source) :
    SameRuntimeData
      (InteractionSemantics.EVMState.finishCall
        target rest callLocal response)
      (InteractionSemantics.EVMState.finishCall
        source rest callLocal response) := by
  have hShared : target.toSharedState = source.toSharedState :=
    SameRuntimeData.shared_eq hRel
  cases target
  cases source
  simp_all [SameRuntimeData, eraseRuntimeControl,
    InteractionSemantics.EVMState.finishCall,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]

theorem finishCreate_sameRuntimeData
    {target source : EVMState}
    (rest : EvmYul.Stack Word)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse)
    (hRel : SameRuntimeData target source) :
    SameRuntimeData
      (InteractionSemantics.EVMState.finishCreate
        target rest createLocal response)
      (InteractionSemantics.EVMState.finishCreate
        source rest createLocal response) := by
  have hShared : target.toSharedState = source.toSharedState :=
    SameRuntimeData.shared_eq hRel
  cases target
  cases source
  simp_all [SameRuntimeData, eraseRuntimeControl,
    InteractionSemantics.EVMState.finishCreate,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]

theorem finishCall_append_stack
    (state : EVMState) (rest hidden : EvmYul.Stack Word)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse) :
    SameRuntimeData
      (InteractionSemantics.EVMState.finishCall
        { state with stack := state.stack ++ hidden }
        (rest ++ hidden) callLocal response)
      { InteractionSemantics.EVMState.finishCall
          state rest callLocal response with
        stack :=
          (InteractionSemantics.EVMState.finishCall
            state rest callLocal response).stack ++ hidden } := by
  cases state
  simp [SameRuntimeData, eraseRuntimeControl,
    InteractionSemantics.EVMState.finishCall,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC, List.append_assoc]

theorem finishCreate_append_stack
    (state : EVMState) (rest hidden : EvmYul.Stack Word)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse) :
    SameRuntimeData
      (InteractionSemantics.EVMState.finishCreate
        { state with stack := state.stack ++ hidden }
        (rest ++ hidden) createLocal response)
      { InteractionSemantics.EVMState.finishCreate
          state rest createLocal response with
        stack :=
          (InteractionSemantics.EVMState.finishCreate
            state rest createLocal response).stack ++ hidden } := by
  cases state
  simp [SameRuntimeData, eraseRuntimeControl,
    InteractionSemantics.EVMState.finishCreate,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC, List.append_assoc]

end EVMState

namespace PrimOp

abbrev RuntimeStateRel :
    Except EVMException EVMState →
      Except EVMException EVMState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    Assembly.SameRuntimeData

/--
The target may carry compiler-owned words below the complete source-visible
stack. Errors need only agree as failures; successful states preserve that
suffix modulo compiler-owned runtime counters.
-/
def StackSuffixStateRel (hidden : EvmYul.Stack Word)
    (source target : EVMState) : Prop :=
  SameRuntimeData target
    { source with stack := source.stack ++ hidden }

abbrev StackSuffixRuntimeRel (hidden : EvmYul.Stack Word) :
    Except EVMException EVMState →
      Except EVMException EVMState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (StackSuffixStateRel hidden)

def AdvancesPC (state : EVMState) :
    Except EVMException EVMState → Prop
  | .error _ => True
  | .ok final =>
      final.pc = state.pc + EvmYul.UInt256.ofNat 1

def RealizesStackArity (state : EVMState)
    (input output : Nat) :
    Except EVMException EVMState → Prop
  | .error _ => True
  | .ok final =>
      final.stack.length =
        state.stack.length - input + output

theorem resourceStep_advancesPC
    (kind : Simulation.ResourceQuery) (state : EVMState) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.resourceStep kind state) := by
  apply Simulation.Interaction.AllDone.request
  intro value
  apply Simulation.Interaction.AllDone.done
  simp [AdvancesPC,
    InteractionSemantics.PrimOp.resourceStep,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem resourceStep_realizesStackArity
    (kind : Simulation.ResourceQuery) (state : EVMState) :
    Simulation.Interaction.AllDone
      (RealizesStackArity state 0 1)
      (InteractionSemantics.PrimOp.resourceStep kind state) := by
  apply Simulation.Interaction.AllDone.request
  intro value
  apply Simulation.Interaction.AllDone.done
  simp [RealizesStackArity,
    InteractionSemantics.PrimOp.resourceStep,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, EvmYul.Stack.push]

theorem callStep_advancesPC
    (kind : Simulation.CallKind) (state : EVMState) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.callStep kind state) := by
  unfold InteractionSemantics.PrimOp.callStep
  cases hOperands : kind.evmOperands? state.stack with
  | none =>
      exact .done trivial
  | some result =>
      rcases result with ⟨rest, operands⟩
      simp only [hOperands]
      split
      · apply Simulation.Interaction.AllDone.request
        intro response
        exact .done (EVMState.finishCall_pc _ _ _ _)
      · exact .done trivial

theorem callStep_realizesStackArity
    (kind : Simulation.CallKind) (state : EVMState) :
    Simulation.Interaction.AllDone
      (RealizesStackArity state kind.inputArity 1)
      (InteractionSemantics.PrimOp.callStep kind state) := by
  cases kind with
  | call =>
      unfold InteractionSemantics.PrimOp.callStep
      cases hPop : state.stack.pop7 with
      | none =>
          simp only [Simulation.CallKind.evmOperands?, hPop]
          apply Simulation.Interaction.AllDone.done
          exact True.intro
      | some popped =>
          rcases popped with
            ⟨rest, gas, address, value, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp only [Simulation.CallKind.evmOperands?, hPop]
          split
          · apply Simulation.Interaction.AllDone.request
            intro response
            apply Simulation.Interaction.AllDone.done
            have hLength :=
              Assembly.PrimStep.Stack.length_of_pop7_some hPop
            simp [RealizesStackArity,
              InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC,
              Simulation.CallKind.inputArity, hLength]
          · apply Simulation.Interaction.AllDone.done
            exact True.intro
  | callcode =>
      unfold InteractionSemantics.PrimOp.callStep
      cases hPop : state.stack.pop7 with
      | none =>
          simp only [Simulation.CallKind.evmOperands?, hPop]
          apply Simulation.Interaction.AllDone.done
          exact True.intro
      | some popped =>
          rcases popped with
            ⟨rest, gas, address, value, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp only [Simulation.CallKind.evmOperands?, hPop]
          split
          · apply Simulation.Interaction.AllDone.request
            intro response
            apply Simulation.Interaction.AllDone.done
            have hLength :=
              Assembly.PrimStep.Stack.length_of_pop7_some hPop
            simp [RealizesStackArity,
              InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC,
              Simulation.CallKind.inputArity, hLength]
          · apply Simulation.Interaction.AllDone.done
            exact True.intro
  | delegatecall =>
      unfold InteractionSemantics.PrimOp.callStep
      cases hPop : state.stack.pop6 with
      | none =>
          simp only [Simulation.CallKind.evmOperands?, hPop]
          apply Simulation.Interaction.AllDone.done
          exact True.intro
      | some popped =>
          rcases popped with
            ⟨rest, gas, address, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp only [Simulation.CallKind.evmOperands?, hPop]
          split
          · apply Simulation.Interaction.AllDone.request
            intro response
            apply Simulation.Interaction.AllDone.done
            have hLength :=
              Assembly.PrimStep.Stack.length_of_pop6_some hPop
            simp [RealizesStackArity,
              InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC,
              Simulation.CallKind.inputArity, hLength]
          · apply Simulation.Interaction.AllDone.done
            exact True.intro
  | staticcall =>
      unfold InteractionSemantics.PrimOp.callStep
      cases hPop : state.stack.pop6 with
      | none =>
          simp only [Simulation.CallKind.evmOperands?, hPop]
          apply Simulation.Interaction.AllDone.done
          exact True.intro
      | some popped =>
          rcases popped with
            ⟨rest, gas, address, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp only [Simulation.CallKind.evmOperands?, hPop]
          split
          · apply Simulation.Interaction.AllDone.request
            intro response
            apply Simulation.Interaction.AllDone.done
            have hLength :=
              Assembly.PrimStep.Stack.length_of_pop6_some hPop
            simp [RealizesStackArity,
              InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC,
              Simulation.CallKind.inputArity, hLength]
          · apply Simulation.Interaction.AllDone.done
            exact True.intro

theorem createStep_advancesPC
    (kind : Simulation.CreateKind) (state : EVMState) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.createStep kind state) := by
  unfold InteractionSemantics.PrimOp.createStep
  cases hOperands : kind.evmOperands? state.stack with
  | none =>
      exact .done trivial
  | some result =>
      rcases result with ⟨rest, operands⟩
      simp only [hOperands]
      split
      · apply Simulation.Interaction.AllDone.request
        intro response
        exact .done (EVMState.finishCreate_pc _ _ _ _)
      · exact .done trivial

theorem createStep_realizesStackArity
    (kind : Simulation.CreateKind) (state : EVMState) :
    Simulation.Interaction.AllDone
      (RealizesStackArity state kind.inputArity 1)
      (InteractionSemantics.PrimOp.createStep kind state) := by
  cases kind with
  | create =>
      unfold InteractionSemantics.PrimOp.createStep
      cases hPop : state.stack.pop3 with
      | none =>
          simp only [Simulation.CreateKind.evmOperands?, hPop]
          apply Simulation.Interaction.AllDone.done
          exact True.intro
      | some popped =>
          rcases popped with
            ⟨rest, value, inputOffset, inputSize⟩
          simp only [Simulation.CreateKind.evmOperands?, hPop]
          split
          · apply Simulation.Interaction.AllDone.request
            intro response
            apply Simulation.Interaction.AllDone.done
            have hLength :=
              Assembly.PrimStep.Stack.length_of_pop3_some hPop
            simp [RealizesStackArity,
              InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC,
              Simulation.CreateKind.inputArity, hLength]
          · apply Simulation.Interaction.AllDone.done
            exact True.intro
  | create2 =>
      unfold InteractionSemantics.PrimOp.createStep
      cases hPop : state.stack.pop4 with
      | none =>
          simp only [Simulation.CreateKind.evmOperands?, hPop]
          apply Simulation.Interaction.AllDone.done
          exact True.intro
      | some popped =>
          rcases popped with
            ⟨rest, value, inputOffset, inputSize, salt⟩
          simp only [Simulation.CreateKind.evmOperands?, hPop]
          split
          · apply Simulation.Interaction.AllDone.request
            intro response
            apply Simulation.Interaction.AllDone.done
            have hLength :=
              Assembly.PrimStep.Stack.length_of_pop4_some hPop
            simp [RealizesStackArity,
              InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              EvmYul.EVM.State.incrPC,
              Simulation.CreateKind.inputArity, hLength]
          · apply Simulation.Interaction.AllDone.done
            exact True.intro

theorem resourceStep_runtimeRel
    (kind : Simulation.ResourceQuery)
    {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (InteractionSemantics.PrimOp.resourceStep kind target)
      (InteractionSemantics.PrimOp.resourceStep kind source) := by
  apply Simulation.Interaction.Rel.request
  intro value
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    SameRuntimeData.replaceStackAndIncrPC hRel
      (congrArg (fun stack => stack.push value)
        (SameRuntimeData.stack_eq hRel))

theorem resourceStep_append_stack_rel
    (kind : Simulation.ResourceQuery) (state : EVMState)
    (hidden : EvmYul.Stack Word) :
    Simulation.Interaction.Rel (StackSuffixRuntimeRel hidden)
      (InteractionSemantics.PrimOp.resourceStep kind state)
      (InteractionSemantics.PrimOp.resourceStep kind
        { state with stack := state.stack ++ hidden }) := by
  apply Simulation.Interaction.Rel.request
  intro value
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  cases state
  simp [StackSuffixStateRel, SameRuntimeData, eraseRuntimeControl,
    InteractionSemantics.PrimOp.resourceStep,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, EvmYul.Stack.push]

theorem callStep_runtimeRel
    (kind : Simulation.CallKind)
    {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (InteractionSemantics.PrimOp.callStep kind target)
      (InteractionSemantics.PrimOp.callStep kind source) := by
  have hStack : target.stack = source.stack :=
    SameRuntimeData.stack_eq hRel
  have hShared : target.toSharedState = source.toSharedState :=
    SameRuntimeData.shared_eq hRel
  unfold InteractionSemantics.PrimOp.callStep
  rw [hStack, hShared]
  cases hOperands : kind.evmOperands? source.stack with
  | none =>
      exact
        .done
          (Simulation.Interaction.ExceptRel.error rfl)
  | some result =>
      rcases result with ⟨rest, operands⟩
      simp only [hOperands]
      split
      · apply Simulation.Interaction.Rel.request
        intro response
        exact
          .done
            (Simulation.Interaction.ExceptRel.ok
              (EVMState.finishCall_sameRuntimeData
                rest operands.callLocal response hRel))
      · exact
          .done
            (Simulation.Interaction.ExceptRel.error rfl)

theorem callStep_append_stack_rel
    (kind : Simulation.CallKind) (state : EVMState)
    (hidden : EvmYul.Stack Word)
    (hBound : kind.inputArity ≤ state.stack.length) :
    Simulation.Interaction.Rel (StackSuffixRuntimeRel hidden)
      (InteractionSemantics.PrimOp.callStep kind state)
      (InteractionSemantics.PrimOp.callStep kind
        { state with stack := state.stack ++ hidden }) := by
  have hExists :
      ∃ rest operands,
        kind.evmOperands? state.stack = some (rest, operands) := by
    cases kind with
    | call =>
        obtain ⟨rest, gas, address, value, inputOffset, inputSize,
            outputOffset, outputSize, hPop⟩ :=
          Assembly.PrimStep.Stack.exists_pop7_of_seven_le
            (by simpa [Simulation.CallKind.inputArity] using hBound)
        exact
          ⟨rest,
            { requestedGas := gas
              address := address
              valueArg := value
              inputOffset := inputOffset
              inputSize := inputSize
              outputOffset := outputOffset
              outputSize := outputSize },
            by simp [Simulation.CallKind.evmOperands?, hPop]⟩
    | callcode =>
        obtain ⟨rest, gas, address, value, inputOffset, inputSize,
            outputOffset, outputSize, hPop⟩ :=
          Assembly.PrimStep.Stack.exists_pop7_of_seven_le
            (by simpa [Simulation.CallKind.inputArity] using hBound)
        exact
          ⟨rest,
            { requestedGas := gas
              address := address
              valueArg := value
              inputOffset := inputOffset
              inputSize := inputSize
              outputOffset := outputOffset
              outputSize := outputSize },
            by simp [Simulation.CallKind.evmOperands?, hPop]⟩
    | delegatecall =>
        obtain ⟨rest, gas, address, inputOffset, inputSize,
            outputOffset, outputSize, hPop⟩ :=
          Assembly.PrimStep.Stack.exists_pop6_of_six_le
            (by simpa [Simulation.CallKind.inputArity] using hBound)
        exact
          ⟨rest,
            { requestedGas := gas
              address := address
              valueArg := EvmYul.UInt256.ofNat 0
              inputOffset := inputOffset
              inputSize := inputSize
              outputOffset := outputOffset
              outputSize := outputSize },
            by simp [Simulation.CallKind.evmOperands?, hPop]⟩
    | staticcall =>
        obtain ⟨rest, gas, address, inputOffset, inputSize,
            outputOffset, outputSize, hPop⟩ :=
          Assembly.PrimStep.Stack.exists_pop6_of_six_le
            (by simpa [Simulation.CallKind.inputArity] using hBound)
        exact
          ⟨rest,
            { requestedGas := gas
              address := address
              valueArg := EvmYul.UInt256.ofNat 0
              inputOffset := inputOffset
              inputSize := inputSize
              outputOffset := outputOffset
              outputSize := outputSize },
            by simp [Simulation.CallKind.evmOperands?, hPop]⟩
  rcases hExists with ⟨rest, operands, hOperands⟩
  have hAppend :=
    Simulation.CallKind.evmOperands?_append_of_some
      kind hidden hOperands
  unfold InteractionSemantics.PrimOp.callStep
  simp only [hOperands, hAppend]
  split
  · apply Simulation.Interaction.Rel.request
    intro response
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      EVMState.finishCall_append_stack
        state rest hidden operands.callLocal response
  · exact
      .done
        (Simulation.Interaction.ExceptRel.error True.intro)

theorem createStep_runtimeRel
    (kind : Simulation.CreateKind)
    {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (InteractionSemantics.PrimOp.createStep kind target)
      (InteractionSemantics.PrimOp.createStep kind source) := by
  have hStack : target.stack = source.stack :=
    SameRuntimeData.stack_eq hRel
  have hShared : target.toSharedState = source.toSharedState :=
    SameRuntimeData.shared_eq hRel
  unfold InteractionSemantics.PrimOp.createStep
  rw [hStack, hShared]
  cases hOperands : kind.evmOperands? source.stack with
  | none =>
      exact
        .done
          (Simulation.Interaction.ExceptRel.error rfl)
  | some result =>
      rcases result with ⟨rest, operands⟩
      simp only [hOperands]
      split
      · apply Simulation.Interaction.Rel.request
        intro response
        exact
          .done
            (Simulation.Interaction.ExceptRel.ok
              (EVMState.finishCreate_sameRuntimeData
                rest operands.createLocal response hRel))
      · exact
          .done
            (Simulation.Interaction.ExceptRel.error rfl)

theorem createStep_append_stack_rel
    (kind : Simulation.CreateKind) (state : EVMState)
    (hidden : EvmYul.Stack Word)
    (hBound : kind.inputArity ≤ state.stack.length) :
    Simulation.Interaction.Rel (StackSuffixRuntimeRel hidden)
      (InteractionSemantics.PrimOp.createStep kind state)
      (InteractionSemantics.PrimOp.createStep kind
        { state with stack := state.stack ++ hidden }) := by
  have hExists :
      ∃ rest operands,
        kind.evmOperands? state.stack = some (rest, operands) := by
    cases kind with
    | create =>
        obtain ⟨rest, value, inputOffset, inputSize, hPop⟩ :=
          Assembly.PrimStep.Stack.exists_pop3_of_three_le
            (by simpa [Simulation.CreateKind.inputArity] using hBound)
        exact
          ⟨rest,
            { value := value
              initOffset := inputOffset
              initSize := inputSize
              saltArg := EvmYul.UInt256.ofNat 0 },
            by simp [Simulation.CreateKind.evmOperands?, hPop]⟩
    | create2 =>
        obtain ⟨rest, value, inputOffset, inputSize, salt, hPop⟩ :=
          Assembly.PrimStep.Stack.exists_pop4_of_four_le
            (by simpa [Simulation.CreateKind.inputArity] using hBound)
        exact
          ⟨rest,
            { value := value
              initOffset := inputOffset
              initSize := inputSize
              saltArg := salt },
            by simp [Simulation.CreateKind.evmOperands?, hPop]⟩
  rcases hExists with ⟨rest, operands, hOperands⟩
  have hAppend :=
    Simulation.CreateKind.evmOperands?_append_of_some
      kind hidden hOperands
  unfold InteractionSemantics.PrimOp.createStep
  simp only [hOperands, hAppend]
  split
  · apply Simulation.Interaction.Rel.request
    intro response
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      EVMState.finishCreate_append_stack
        state rest hidden operands.createLocal response
  · exact
      .done
        (Simulation.Interaction.ExceptRel.error True.intro)

theorem noExternalCallCreate_of_unclassified
    {op : Assembly.PrimOp}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none) :
    op.isExternalCallCreate = false := by
  cases op <;>
    simp [Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Assembly.PrimOp.isExternalCallCreate] at hExternal ⊢

theorem closedStep_runtimeRel
    {op : Assembly.PrimOp} {target source : EVMState}
    (hArity : ∃ arity, op.stackArity? = some arity)
    (hNoPc : op ≠ .pc)
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (InteractionSemantics.PrimOp.openStep op target)
      (InteractionSemantics.PrimOp.openStep op source) := by
  rw [InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize,
    InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize]
  apply Simulation.Interaction.Rel.done
  have hRun :=
    Assembly.PrimOp.step_map_eraseRuntimeControl
      hArity hNoPc
        (noExternalCallCreate_of_unclassified hExternal) hRel
  cases hTarget : op.step target with
  | error targetError =>
      cases hSource : op.step source with
      | error sourceError =>
          simp [hTarget, hSource, Except.map] at hRun
          exact
            Simulation.Interaction.ExceptRel.error hRun
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hRun
  | ok targetFinal =>
      cases hSource : op.step source with
      | error sourceError =>
          simp [hTarget, hSource, Except.map] at hRun
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hRun
          exact
            Simulation.Interaction.ExceptRel.ok hRun

theorem closedStep_append_stack_rel
    {op : Assembly.PrimOp} {input output : Nat}
    (state : EVMState) (hidden : EvmYul.Stack Word)
    (hArity : op.stackArity? = some (input, output))
    (hBound : input ≤ state.stack.length)
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize) :
    Simulation.Interaction.Rel (StackSuffixRuntimeRel hidden)
      (InteractionSemantics.PrimOp.openStep op state)
      (InteractionSemantics.PrimOp.openStep op
        { state with stack := state.stack ++ hidden }) := by
  rw [InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize,
    InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize]
  cases hSource : op.step state with
  | error sourceError =>
      cases hTarget :
          op.step { state with stack := state.stack ++ hidden } with
      | error targetError =>
          exact
            .done
              (Simulation.Interaction.ExceptRel.error True.intro)
      | ok targetFinal =>
          obtain ⟨sourceFinal, hSourceFinal⟩ :=
            Assembly.PrimOp.exists_step_of_stackArity_le_of_append_step
              hArity hBound hTarget
          rw [hSource] at hSourceFinal
          contradiction
  | ok sourceFinal =>
      obtain ⟨targetFinal, hTarget⟩ :=
        Assembly.PrimOp.exists_append_step_of_stackArity_le_of_step
          (hidden := hidden) hArity hBound hSource
      rw [hTarget]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        Assembly.PrimOp.step_append_stack_rel_of_stackArity_le
          hArity hBound hSource hTarget

theorem call_inputArity_eq_of_classified
    {op : Assembly.PrimOp} {kind : Simulation.CallKind}
    {input output : Nat}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM =
        some (.call kind))
    (hArity : op.stackArity? = some (input, output)) :
    kind.inputArity = input := by
  cases op <;> cases kind <;>
    simp [Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Assembly.PrimOp.stackArity?,
      EvmYul.EVM.δ, EvmYul.EVM.α,
      Simulation.CallKind.inputArity] at hExternal hArity ⊢
  all_goals exact hArity.1

theorem call_outputArity_eq_one_of_classified
    {op : Assembly.PrimOp} {kind : Simulation.CallKind}
    {input output : Nat}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM =
        some (.call kind))
    (hArity : op.stackArity? = some (input, output)) :
    output = 1 := by
  cases op <;> cases kind <;>
    simp [Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Assembly.PrimOp.stackArity?,
      EvmYul.EVM.δ, EvmYul.EVM.α] at hExternal hArity ⊢
  all_goals omega

theorem create_inputArity_eq_of_classified
    {op : Assembly.PrimOp} {kind : Simulation.CreateKind}
    {input output : Nat}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM =
        some (.create kind))
    (hArity : op.stackArity? = some (input, output)) :
    kind.inputArity = input := by
  cases op <;> cases kind <;>
    simp [Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Assembly.PrimOp.stackArity?,
      EvmYul.EVM.δ, EvmYul.EVM.α,
      Simulation.CreateKind.inputArity] at hExternal hArity ⊢
  all_goals exact hArity.1

theorem create_outputArity_eq_one_of_classified
    {op : Assembly.PrimOp} {kind : Simulation.CreateKind}
    {input output : Nat}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM =
        some (.create kind))
    (hArity : op.stackArity? = some (input, output)) :
    output = 1 := by
  cases op <;> cases kind <;>
    simp [Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Assembly.PrimOp.stackArity?,
      EvmYul.EVM.δ, EvmYul.EVM.α] at hExternal hArity ⊢
  all_goals omega

/--
Open primitive execution is insensitive to compiler-owned PC and execution
counters. External calls and creates remain in scope: related states issue the
same request and remain related for every shared response.
-/
theorem openStep_runtimeRel
    {op : Assembly.PrimOp} {target source : EVMState}
    (hArity : ∃ arity, op.stackArity? = some arity)
    (hNoPc : op ≠ .pc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (InteractionSemantics.PrimOp.openStep op target)
      (InteractionSemantics.PrimOp.openStep op source) := by
  cases hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some external =>
      cases external with
      | call kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op target =
              InteractionSemantics.PrimOp.callStep kind target by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          rw [show
            InteractionSemantics.PrimOp.openStep op source =
              InteractionSemantics.PrimOp.callStep kind source by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          exact callStep_runtimeRel kind hRel
      | create kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op target =
              InteractionSemantics.PrimOp.createStep kind target by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          rw [show
            InteractionSemantics.PrimOp.openStep op source =
              InteractionSemantics.PrimOp.createStep kind source by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          exact createStep_runtimeRel kind hRel
  | none =>
      by_cases hGas : op = .gas
      · subst op
        exact resourceStep_runtimeRel .gas hRel
      · by_cases hMsize : op = .msize
        · subst op
          exact resourceStep_runtimeRel .msize hRel
        · exact
            closedStep_runtimeRel
              hArity hNoPc hExternal hGas hMsize hRel

/--
Open primitive execution preserves compiler-owned words below the complete
source-visible operand prefix. CALL/CREATE requests remain exactly equal and
the suffix is restored for every shared open-world response.
-/
theorem openStep_append_stack_rel_of_stackArity_le
    {op : Assembly.PrimOp} {input output : Nat}
    (state : EVMState) (hidden : EvmYul.Stack Word)
    (hArity : op.stackArity? = some (input, output))
    (hBound : input ≤ state.stack.length) :
    Simulation.Interaction.Rel (StackSuffixRuntimeRel hidden)
      (InteractionSemantics.PrimOp.openStep op state)
      (InteractionSemantics.PrimOp.openStep op
        { state with stack := state.stack ++ hidden }) := by
  cases hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some external =>
      cases external with
      | call kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.callStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          rw [show
            InteractionSemantics.PrimOp.openStep op
                { state with stack := state.stack ++ hidden } =
              InteractionSemantics.PrimOp.callStep kind
                { state with stack := state.stack ++ hidden } by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          apply callStep_append_stack_rel
          rw [call_inputArity_eq_of_classified hExternal hArity]
          exact hBound
      | create kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.createStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          rw [show
            InteractionSemantics.PrimOp.openStep op
                { state with stack := state.stack ++ hidden } =
              InteractionSemantics.PrimOp.createStep kind
                { state with stack := state.stack ++ hidden } by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          apply createStep_append_stack_rel
          rw [create_inputArity_eq_of_classified hExternal hArity]
          exact hBound
  | none =>
      by_cases hGas : op = .gas
      · subst op
        exact resourceStep_append_stack_rel .gas state hidden
      · by_cases hMsize : op = .msize
        · subst op
          exact resourceStep_append_stack_rel .msize state hidden
        · exact
            closedStep_append_stack_rel
              state hidden hArity hBound hExternal hGas hMsize

/--
Closed primitive execution realizes the stack transition declared by
`stackArity?` on every terminal branch.
-/
theorem closedStep_realizesStackArity
    {op : Assembly.PrimOp} {input output : Nat}
    {state : EVMState}
    (hArity : op.stackArity? = some (input, output))
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize) :
    Simulation.Interaction.AllDone
      (RealizesStackArity state input output)
      (InteractionSemantics.PrimOp.openStep op state) := by
  rw [InteractionSemantics.PrimOp.openStep_closed
    hExternal hGas hMsize]
  cases hRun : op.step state with
  | error err =>
      apply Simulation.Interaction.AllDone.done
      exact True.intro
  | ok final =>
      apply Simulation.Interaction.AllDone.done
      exact
        Assembly.PrimOp.step_stack_length_of_stackArity
          hArity hRun

/--
Every successful branch of an open, well-typed Assembly primitive realizes
its declared stack transition. This is the stack contract consumed by the
adjacent Structured-to-TypedCfg proof.
-/
theorem openStep_realizesStackArity
    {op : Assembly.PrimOp} {input output : Nat}
    {state : EVMState}
    (hArity : op.stackArity? = some (input, output)) :
    Simulation.Interaction.AllDone
      (RealizesStackArity state input output)
      (InteractionSemantics.PrimOp.openStep op state) := by
  cases hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some external =>
      cases external with
      | call kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.callStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          have hInput :=
            call_inputArity_eq_of_classified hExternal hArity
          have hOutput :=
            call_outputArity_eq_one_of_classified hExternal hArity
          simpa [hInput, hOutput] using
            callStep_realizesStackArity kind state
      | create kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.createStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          have hInput :=
            create_inputArity_eq_of_classified hExternal hArity
          have hOutput :=
            create_outputArity_eq_one_of_classified hExternal hArity
          simpa [hInput, hOutput] using
            createStep_realizesStackArity kind state
  | none =>
      by_cases hGas : op = .gas
      · subst op
        simp [Assembly.PrimOp.stackArity?,
          Assembly.PrimOp.toEVM, EvmYul.EVM.δ,
          EvmYul.EVM.α] at hArity
        rcases hArity with ⟨rfl, rfl⟩
        exact resourceStep_realizesStackArity .gas state
      · by_cases hMsize : op = .msize
        · subst op
          simp [Assembly.PrimOp.stackArity?,
            Assembly.PrimOp.toEVM, EvmYul.EVM.δ,
            EvmYul.EVM.α] at hArity
          rcases hArity with ⟨rfl, rfl⟩
          exact resourceStep_realizesStackArity .msize state
        · exact
            closedStep_realizesStackArity
              hArity hExternal hGas hMsize

/--
Every successful branch of an open, well-typed Assembly primitive advances
the program counter by its one-byte instruction width. The theorem quantifies
over every resource answer and every external-world response.
-/
theorem openStep_advancesPC
    {op : Assembly.PrimOp} {input output : Nat}
    {state : EVMState}
    (hArity : op.stackArity? = some (input, output)) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.openStep op state) := by
  cases hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some external =>
      cases external with
      | call kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.callStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          exact callStep_advancesPC kind state
      | create kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.createStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          exact createStep_advancesPC kind state
  | none =>
      by_cases hGas : op = .gas
      · subst op
        exact resourceStep_advancesPC .gas state
      · by_cases hMsize : op = .msize
        · subst op
          exact resourceStep_advancesPC .msize state
        · rw [InteractionSemantics.PrimOp.openStep_closed
            hExternal hGas hMsize]
          cases hRun : op.step state with
          | error err =>
              exact .done trivial
          | ok final =>
              exact
                .done
                  (Assembly.PrimOp.step_pc_of_stackArity
                    hArity hRun)

end PrimOp

theorem openRunList_single (instr : TargetInstr) (state : EVMState) :
    InteractionSemantics.Target.openRunList [instr] state =
      InteractionSemantics.Target.openStepInstr instr state := by
  unfold InteractionSemantics.Target.openRunList Target.runListWith
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Target.openStepInstr instr state)
        Simulation.Interaction.pure =
      InteractionSemantics.Target.openStepInstr instr state
  exact Simulation.Interaction.bind_pure _

theorem open_run_push_jump (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .done (.ok (Source.jumpPc dest state)) := by
  unfold InteractionSemantics.Target.openRunList Target.runListWith
    InteractionSemantics.Target.openStepInstr Target.stepInstrWith
  rfl

theorem open_run_push_jumpi (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      .done
        (match state.stack.pop with
        | some (stack, cond) =>
            .ok
              { state with
                pc :=
                  if cond != EvmYul.UInt256.ofNat 0 then
                    EvmYul.UInt256.ofNat dest
                  else
                    Source.jumpiFallthroughPc state
                stack := stack }
        | none => .error .StackUnderflow) := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons cond rest => rfl

theorem openRunListResult_single (instr : TargetInstr) (state : EVMState) :
    InteractionSemantics.Target.openRunListResult [instr] state =
      InteractionSemantics.Target.openStepInstrResult instr state := by
  unfold InteractionSemantics.Target.openRunListResult
    Target.runListResultWith
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Target.openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' =>
              Simulation.Interaction.pure
                (Error := EVMException) (.running state')
          | .halted halt =>
              Simulation.Interaction.pure
                (Error := EVMException) (.halted halt)) =
      InteractionSemantics.Target.openStepInstrResult instr state
  have hContinuation :
      (fun result : StepResult =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure
              (Error := EVMException) (.running state')
        | .halted halt =>
            Simulation.Interaction.pure
              (Error := EVMException) (.halted halt)) =
        (Simulation.Interaction.pure (Error := EVMException) :
          StepResult → InteractionSemantics.OpenStepResult) := by
    funext result
    cases result <;> rfl
  rw [hContinuation]
  exact Simulation.Interaction.bind_pure _

theorem target_openRunNResult_single_of_fetch
    {target : TargetProgram} {state : EVMState} {instr : TargetInstr}
    (hFetch : TargetProgram.fetch target state.pc.toNat = some instr) :
    InteractionSemantics.Target.openRunNResult target 1 state =
      InteractionSemantics.Target.openRunListResult [instr] state := by
  rw [openRunListResult_single]
  unfold InteractionSemantics.Target.openRunNResult
    Assembly.Target.runNResultWith Assembly.Control.runNResultWith
    Assembly.Target.stepResultWith
  rw [hFetch]
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Target.openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' =>
              Simulation.Interaction.pure
                (Error := EVMException) (.running state')
          | .halted halt =>
              Simulation.Interaction.pure
                (Error := EVMException) (.halted halt)) =
      InteractionSemantics.Target.openStepInstrResult instr state
  have hContinuation :
      (fun result : StepResult =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure
              (Error := EVMException) (.running state')
        | .halted halt =>
            Simulation.Interaction.pure
              (Error := EVMException) (.halted halt)) =
        (Simulation.Interaction.pure (Error := EVMException) :
          StepResult → InteractionSemantics.OpenStepResult) := by
    funext result
    cases result <;> rfl
  rw [hContinuation]
  exact Simulation.Interaction.bind_pure _

theorem target_openRunNResult_push_jump_of_fetch
    {target : TargetProgram} {state : EVMState} {dest : Nat}
    (hFetchPush :
      TargetProgram.fetch target state.pc.toNat =
        some (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)))
    (hFetchJump :
      TargetProgram.fetch target (state.pc.toNat + Instr.push32Size) =
        some TargetInstr.jump)
    (hNoOverflow :
      state.pc.toNat + Instr.push32Size < EvmYul.UInt256.size) :
    InteractionSemantics.Target.openRunNResult target 2 state =
      InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state := by
  let post :=
    state.replaceStackAndIncrPC
      (state.stack.push (EvmYul.UInt256.ofNat dest)) (pcΔ := 33)
  have hPostPc :
      post.pc.toNat = state.pc.toNat + 33 :=
    Preservation.replaceStackAndIncrPC_pc_toNat_of_no_overflow
      (state := state)
      (stack := state.stack.push (EvmYul.UInt256.ofNat dest))
      (pcΔ := 33) (by simpa [Instr.push32Size] using hNoOverflow)
  have hFetchJump' :
      TargetProgram.fetch target post.pc.toNat =
        some TargetInstr.jump := by
    rw [hPostPc]
    simpa [Instr.push32Size] using hFetchJump
  have hPush :
      InteractionSemantics.Target.openStepInstrResult
          (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state =
        .done (.ok (.running post)) := by
    rfl
  calc
    InteractionSemantics.Target.openRunNResult target 2 state =
        InteractionSemantics.Target.openRunNResult target 1 post := by
      change
        (do
          let result ←
            InteractionSemantics.Target.openStepResult target state
          match result with
          | .running state' =>
              InteractionSemantics.Target.openRunNResult target 1 state'
          | .halted halt =>
              pure (.halted halt)) =
          InteractionSemantics.Target.openRunNResult target 1 post
      unfold InteractionSemantics.Target.openStepResult
        Assembly.Target.stepResultWith
      rw [hFetchPush]
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.jump] post :=
      target_openRunNResult_single_of_fetch hFetchJump'
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
          state := by
      change
        InteractionSemantics.Target.openRunListResult
            [TargetInstr.jump] post =
          (do
            let result ←
              InteractionSemantics.Target.openStepInstrResult
                (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state
            match result with
            | .running state' =>
                InteractionSemantics.Target.openRunListResult
                  [TargetInstr.jump] state'
            | .halted halt =>
                pure (.halted halt))
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl

theorem target_openRunNResult_push_jumpi_of_fetch
    {target : TargetProgram} {state : EVMState} {dest : Nat}
    (hFetchPush :
      TargetProgram.fetch target state.pc.toNat =
        some (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)))
    (hFetchJumpi :
      TargetProgram.fetch target (state.pc.toNat + Instr.push32Size) =
        some TargetInstr.jumpi)
    (hNoOverflow :
      state.pc.toNat + Instr.push32Size < EvmYul.UInt256.size) :
    InteractionSemantics.Target.openRunNResult target 2 state =
      InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state := by
  let post :=
    state.replaceStackAndIncrPC
      (state.stack.push (EvmYul.UInt256.ofNat dest)) (pcΔ := 33)
  have hPostPc :
      post.pc.toNat = state.pc.toNat + 33 :=
    Preservation.replaceStackAndIncrPC_pc_toNat_of_no_overflow
      (state := state)
      (stack := state.stack.push (EvmYul.UInt256.ofNat dest))
      (pcΔ := 33) (by simpa [Instr.push32Size] using hNoOverflow)
  have hFetchJumpi' :
      TargetProgram.fetch target post.pc.toNat =
        some TargetInstr.jumpi := by
    rw [hPostPc]
    simpa [Instr.push32Size] using hFetchJumpi
  have hPush :
      InteractionSemantics.Target.openStepInstrResult
          (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state =
        .done (.ok (.running post)) := by
    rfl
  calc
    InteractionSemantics.Target.openRunNResult target 2 state =
        InteractionSemantics.Target.openRunNResult target 1 post := by
      change
        (do
          let result ←
            InteractionSemantics.Target.openStepResult target state
          match result with
          | .running state' =>
              InteractionSemantics.Target.openRunNResult target 1 state'
          | .halted halt =>
              pure (.halted halt)) =
          InteractionSemantics.Target.openRunNResult target 1 post
      unfold InteractionSemantics.Target.openStepResult
        Assembly.Target.stepResultWith
      rw [hFetchPush]
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.jumpi] post :=
      target_openRunNResult_single_of_fetch hFetchJumpi'
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
          state := by
      change
        InteractionSemantics.Target.openRunListResult
            [TargetInstr.jumpi] post =
          (do
            let result ←
              InteractionSemantics.Target.openStepInstrResult
                (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state
            match result with
            | .running state' =>
                InteractionSemantics.Target.openRunListResult
                  [TargetInstr.jumpi] state'
            | .halted halt =>
                pure (.halted halt))
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl

theorem open_run_push_jump_result (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .done (.ok (.running (Source.jumpPc dest state))) := by
  unfold InteractionSemantics.Target.openRunListResult
    Target.runListResultWith
    InteractionSemantics.Target.openStepInstrResult
    Target.stepInstrResultWith
    InteractionSemantics.Target.openStepInstr
    Target.stepInstrWith
  rfl

theorem open_run_push_jumpi_result (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      .done
        (match state.stack.pop with
        | some (stack, cond) =>
            .ok
              (.running
                { state with
                  pc :=
                    if cond != EvmYul.UInt256.ofNat 0 then
                      EvmYul.UInt256.ofNat dest
                    else
                      Source.jumpiFallthroughPc state
                  stack := stack })
        | none => .error .StackUnderflow) := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons cond rest => rfl

/--
Resolving and emitting one Assembly instruction preserves its complete open
interaction tree. In particular, an emitted CALL/CREATE-family primitive
exposes the same request and the same continuation for every shared answer.
-/
theorem stepAt_emit_open_eq
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    InteractionSemantics.Source.openStepAt program pc instr state =
      InteractionSemantics.Target.openRunList
        (located.map LocatedTarget.instr) state := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAt program pc (.label name) state =
          InteractionSemantics.Target.openRunList
            [TargetInstr.jumpdest] state
      rw [openRunList_single]
      rfl
  | prim op =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAt program pc (.prim op) state =
          InteractionSemantics.Target.openRunList
            [TargetInstr.prim op] state
      rw [openRunList_single]
      rfl
  | push value =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAt program pc (.push value) state =
          InteractionSemantics.Target.openRunList
            [TargetInstr.push32 value] state
      rw [openRunList_single]
      rfl
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAt program pc
                (.jump target) state =
              InteractionSemantics.Target.openRunList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jump]
                state
          rw [open_run_push_jump]
          simp [InteractionSemantics.Source.openStepAt, Source.stepAt,
            hDest, Source.jumpPc]
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAt program pc
                (.jumpi target) state =
              InteractionSemantics.Target.openRunList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jumpi]
                state
          rw [open_run_push_jumpi]
          simp [InteractionSemantics.Source.openStepAt, Source.stepAt, hDest]
          rfl

theorem stepAt_emit_open_rel
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStepAt program pc instr state)
      (InteractionSemantics.Target.openRunList
        (located.map LocatedTarget.instr) state) := by
  rw [stepAt_emit_open_eq hEmit]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem stepAt_emit_open_result_eq
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    InteractionSemantics.Source.openStepAtResult program pc instr state =
      InteractionSemantics.Target.openRunListResult
        (located.map LocatedTarget.instr) state := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAtResult program pc
            (.label name) state =
          InteractionSemantics.Target.openRunListResult
            [TargetInstr.jumpdest] state
      rw [openRunListResult_single]
      rfl
  | prim op =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAtResult program pc
            (.prim op) state =
          InteractionSemantics.Target.openRunListResult
            [TargetInstr.prim op] state
      rw [openRunListResult_single]
      rfl
  | push value =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAtResult program pc
            (.push value) state =
          InteractionSemantics.Target.openRunListResult
            [TargetInstr.push32 value] state
      rw [openRunListResult_single]
      rfl
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAtResult program pc
                (.jump target) state =
              InteractionSemantics.Target.openRunListResult
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jump]
                state
          rw [open_run_push_jump_result]
          simp [InteractionSemantics.Source.openStepAtResult,
            InteractionSemantics.Source.openStepAt, Source.stepAt,
            Instr.haltKind?, hDest, Source.jumpPc]
          change Simulation.Interaction.bind _ _ = _
          rfl
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAtResult program pc
                (.jumpi target) state =
              InteractionSemantics.Target.openRunListResult
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jumpi]
                state
          rw [open_run_push_jumpi_result]
          simp [InteractionSemantics.Source.openStepAtResult,
            InteractionSemantics.Source.openStepAt, Source.stepAt,
            Instr.haltKind?, hDest]
          change Simulation.Interaction.bind _ _ = _
          cases hPop : state.stack.pop <;> simp [hPop]
          change Simulation.Interaction.pure _ = _
          rfl

theorem stepAt_emit_open_result_rel
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStepAtResult program pc instr state)
      (InteractionSemantics.Target.openRunListResult
        (located.map LocatedTarget.instr) state) := by
  rw [stepAt_emit_open_result_eq hEmit]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

/--
Executing one emitted source instruction through resolved target fetches is
exactly the same open interaction as executing its emitted block directly.
-/
theorem target_openRunNResult_eq_openRunList_of_emitInstr?
    {program : Program} {target : TargetProgram}
    {state : EVMState} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hSafe : Preservation.TargetBlockPcSafe instr state) :
    InteractionSemantics.Target.openRunNResult
        target emitted.length state =
      InteractionSemantics.Target.openRunListResult
        (emitted.map LocatedTarget.instr) state := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .label name)
            (emitted := [{ pc := pc, instr := TargetInstr.jumpdest }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_openRunNResult_single_of_fetch hFetch
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .prim op)
            (emitted := [{ pc := pc, instr := TargetInstr.prim op }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_openRunNResult_single_of_fetch hFetch
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .push value)
            (emitted := [{ pc := pc, instr := TargetInstr.push32 value }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_openRunNResult_single_of_fetch hFetch
  | jump targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          rcases
              assemble?_fetch_first_of_instrAtPc
                (program := program) (target := target)
                (query := state.pc.toNat) (pc := pc)
                (instr := .jump targetLabel)
                (emitted :=
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) }
                  , { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jump }
                  ])
                hAsm hAt (by simp [emitInstr?, hDest]) with
            ⟨targetInstr, restEmitted, hFirst, hFetchPush⟩
          cases hFirst
          have hFetchJump :
              TargetProgram.fetch target
                  (state.pc.toNat + Instr.push32Size) =
                some TargetInstr.jump :=
            assemble?_fetch_jump_second_of_instrAtPc
              (program := program) (targetProgram := target)
              (query := state.pc.toNat) (pc := state.pc.toNat)
              (target := targetLabel)
              (emitted :=
                [ { pc := state.pc.toNat,
                    instr := TargetInstr.push32
                      (EvmYul.UInt256.ofNat dest) }
                , { pc := state.pc.toNat + Instr.push32Size,
                    instr := TargetInstr.jump }
                ])
              hAsm hAt (by simp [emitInstr?, hDest])
          have hNoOverflow :
              state.pc.toNat + Instr.push32Size <
                EvmYul.UInt256.size := by
            simpa [Preservation.TargetBlockPcSafe] using hSafe
          exact
            target_openRunNResult_push_jump_of_fetch
              hFetchPush hFetchJump hNoOverflow
  | jumpi targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          rcases
              assemble?_fetch_first_of_instrAtPc
                (program := program) (target := target)
                (query := state.pc.toNat) (pc := pc)
                (instr := .jumpi targetLabel)
                (emitted :=
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) }
                  , { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jumpi }
                  ])
                hAsm hAt (by simp [emitInstr?, hDest]) with
            ⟨targetInstr, restEmitted, hFirst, hFetchPush⟩
          cases hFirst
          have hFetchJumpi :
              TargetProgram.fetch target
                  (state.pc.toNat + Instr.push32Size) =
                some TargetInstr.jumpi :=
            assemble?_fetch_jumpi_second_of_instrAtPc
              (program := program) (targetProgram := target)
              (query := state.pc.toNat) (pc := state.pc.toNat)
              (target := targetLabel)
              (emitted :=
                [ { pc := state.pc.toNat,
                    instr := TargetInstr.push32
                      (EvmYul.UInt256.ofNat dest) }
                , { pc := state.pc.toNat + Instr.push32Size,
                    instr := TargetInstr.jumpi }
                ])
              hAsm hAt (by simp [emitInstr?, hDest])
          have hNoOverflow :
              state.pc.toNat + Instr.push32Size <
                EvmYul.UInt256.size := by
            simpa [Preservation.TargetBlockPcSafe] using hSafe
          exact
            target_openRunNResult_push_jumpi_of_fetch
              hFetchPush hFetchJumpi hNoOverflow

/--
One concrete branch through emitted-block execution. The transcript is the
external world's exact ordered query/answer history; the trace stores only
pass-owned block decomposition facts.
-/
inductive OpenBlockTraceResult
    (program : Program) (target : TargetProgram) :
    Nat → EVMState → Simulation.Interaction.Transcript → StepResult → Prop where
  | done (state : EVMState) :
      OpenBlockTraceResult program target 0 state [] (.running state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {headTranscript restTranscript : Simulation.Interaction.Transcript}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Simulation.Interaction.Executes
          (InteractionSemantics.Target.openRunListResult
            (emitted.map LocatedTarget.instr) state)
          headTranscript (.ok (.running mid)))
      (hRest :
        OpenBlockTraceResult program target fuel mid restTranscript result) :
      OpenBlockTraceResult program target (fuel + 1) state
        (headTranscript ++ restTranscript) result
  | stepHalted {fuel : Nat} {state : EVMState}
      {transcript : Simulation.Interaction.Transcript} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Simulation.Interaction.Executes
          (InteractionSemantics.Target.openRunListResult
            (emitted.map LocatedTarget.instr) state)
          transcript (.ok (.halted halt))) :
      OpenBlockTraceResult program target (fuel + 1) state transcript
        (.halted halt)

namespace OpenBlockTraceResult

/--
Every emitted-block branch is realized by the ordinary fetched target runner
within two target instructions per source instruction.
-/
theorem target_executes_bounded
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hTrace :
      OpenBlockTraceResult program target fuel state transcript result)
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    ∃ targetFuel,
      targetFuel <= 2 * fuel /\
        Simulation.Interaction.Executes
          (InteractionSemantics.Target.openRunNResult
            target targetFuel state)
          transcript (.ok result) := by
  induction hTrace with
  | done state =>
      refine ⟨0, by omega, ?_⟩
      change
        Simulation.Interaction.Executes
          (.done (.ok (StepResult.running state))) []
          (.ok (StepResult.running state))
      exact Simulation.Interaction.Executes.done _
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid headTranscript restTranscript result
        pc instr emitted before after
      have hSafe : Preservation.TargetBlockPcSafe instr state :=
        Preservation.targetBlockPcSafe_of_instrAtPc_of_byteLength_lt
          hAt hLen
      have hHead :
          Simulation.Interaction.Executes
            (InteractionSemantics.Target.openRunNResult
              target emitted.length state)
            headTranscript (.ok (.running mid)) := by
        rw [target_openRunNResult_eq_openRunList_of_emitInstr?
          hAsm hAt hEmit hSafe]
        exact hRun
      rcases ih with ⟨tailFuel, hTailLe, hTail⟩
      have hHeadLe : emitted.length <= 2 :=
        emitInstr?_length_le_two hEmit
      refine ⟨emitted.length + tailFuel, by omega, ?_⟩
      rw [InteractionSemantics.Target.openRunNResult_add]
      exact Simulation.Interaction.Executes.bind_ok hHead hTail
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state transcript halt pc instr emitted before after
      have hSafe : Preservation.TargetBlockPcSafe instr state :=
        Preservation.targetBlockPcSafe_of_instrAtPc_of_byteLength_lt
          hAt hLen
      have hHeadLe : emitted.length <= 2 :=
        emitInstr?_length_le_two hEmit
      refine ⟨emitted.length, by omega, ?_⟩
      rw [target_openRunNResult_eq_openRunList_of_emitInstr?
        hAsm hAt hEmit hSafe]
      exact hRun

/-- Every emitted-block branch is realized by the ordinary fetched target
runner. The exact instruction fuel is selected internally. -/
theorem target_executes_exists
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hTrace :
      OpenBlockTraceResult program target fuel state transcript result)
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    ∃ targetFuel,
      Simulation.Interaction.Executes
        (InteractionSemantics.Target.openRunNResult
          target targetFuel state)
        transcript (.ok result) := by
  obtain ⟨targetFuel, _hLe, hExec⟩ :=
    target_executes_bounded hAsm hTrace hLen
  exact ⟨targetFuel, hExec⟩

end OpenBlockTraceResult

theorem assemble_compiled_openStepResult_executes
    {program : Program} {target : TargetProgram}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Compiled.openStepResult program state)
        transcript (.ok result)) :
    ∃ pc instr emitted before after,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
          target.code = before ++ emitted ++ after ∧
            Simulation.Interaction.Executes
              (InteractionSemantics.Target.openRunListResult
                (emitted.map LocatedTarget.instr) state)
              transcript (.ok result) := by
  unfold InteractionSemantics.Compiled.openStepResult
    Assembly.Compiled.stepResultWith at hExec
  cases hCurrent : emitCurrent? program state with
  | none =>
      rw [hCurrent] at hExec
      change
        Simulation.Interaction.Executes
          (.done (.error (.InvalidInstruction : EVMException)))
          transcript (.ok result) at hExec
      cases hExec
  | some code =>
      rw [hCurrent] at hExec
      unfold emitCurrent? at hCurrent
      cases hAt : Program.instrAtPc program state.pc.toNat with
      | none =>
          simp [hAt] at hCurrent
      | some current =>
          rcases current with ⟨pc, instr⟩
          simp only [hAt, Option.bind_some] at hCurrent
          cases hEmit : emitInstr? program pc instr with
          | none =>
              simp [hEmit] at hCurrent
          | some emitted =>
              simp [hEmit] at hCurrent
              subst code
              rcases Preservation.assemble_covers_current_pc hAsm hAt with
                ⟨before, assembled, after, hTargetBlock, hAssembled⟩
              rw [hEmit] at hAssembled
              cases hAssembled
              exact
                ⟨pc, instr, emitted, before, after, rfl, hEmit,
                  hTargetBlock, hExec⟩

theorem source_openStep_eq_compiled (program : Program) (state : EVMState) :
    InteractionSemantics.Source.openStep program state =
      InteractionSemantics.Compiled.openStep program state := by
  unfold InteractionSemantics.Source.openStep
    InteractionSemantics.Compiled.openStep
    Assembly.Source.stepWith Assembly.Compiled.stepWith emitCurrent?
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt]
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp only [hAt]
      cases hEmit : emitInstr? program pc instr with
      | none =>
          cases instr with
          | label name =>
              simp [emitInstr?] at hEmit
          | prim op =>
              simp [emitInstr?] at hEmit
          | push value =>
              simp [emitInstr?] at hEmit
          | jump target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    emitInstr?, hDest, Simulation.Interaction.error]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
          | jumpi target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    emitInstr?, hDest, Simulation.Interaction.error]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
      | some located =>
          simpa [hEmit] using stepAt_emit_open_eq hEmit

theorem source_openStep_rel_compiled (program : Program) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStep program state)
      (InteractionSemantics.Compiled.openStep program state) := by
  rw [source_openStep_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem source_openStepResult_eq_compiled
    (program : Program) (state : EVMState) :
    InteractionSemantics.Source.openStepResult program state =
      InteractionSemantics.Compiled.openStepResult program state := by
  unfold InteractionSemantics.Source.openStepResult
    InteractionSemantics.Compiled.openStepResult
    Assembly.Source.stepResultWith Assembly.Compiled.stepResultWith
    emitCurrent?
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt]
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp only [hAt]
      cases hEmit : emitInstr? program pc instr with
      | none =>
          cases instr with
          | label name =>
              simp [emitInstr?] at hEmit
          | prim op =>
              simp [emitInstr?] at hEmit
          | push value =>
              simp [emitInstr?] at hEmit
          | jump target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAtResult,
                    InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    Instr.haltKind?, emitInstr?, hDest,
                    Simulation.Interaction.error,
                    Simulation.Interaction.bind]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
          | jumpi target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAtResult,
                    InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    Instr.haltKind?, emitInstr?, hDest,
                    Simulation.Interaction.error,
                    Simulation.Interaction.bind]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
      | some located =>
          simpa [hEmit] using stepAt_emit_open_result_eq hEmit

theorem source_openStepResult_rel_compiled
    (program : Program) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStepResult program state)
      (InteractionSemantics.Compiled.openStepResult program state) := by
  rw [source_openStepResult_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

/--
Whole-program open Assembly execution is exactly the execution of the target
instruction blocks selected by the existing emitter. Both sides use the shared
control kernel, so the equality covers every request continuation rather than
only a particular replay strategy.
-/
theorem source_openRunN_eq_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    InteractionSemantics.Source.openRunN program fuel state =
      InteractionSemantics.Compiled.openRunN program fuel state := by
  unfold InteractionSemantics.Source.openRunN
    InteractionSemantics.Compiled.openRunN
  have hStep :
      InteractionSemantics.Source.openStep program =
        InteractionSemantics.Compiled.openStep program := by
    funext current
    exact source_openStep_eq_compiled program current
  rw [hStep]

theorem source_openRunN_rel_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openRunN program fuel state)
      (InteractionSemantics.Compiled.openRunN program fuel state) := by
  rw [source_openRunN_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem source_openRunNResult_eq_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    InteractionSemantics.Source.openRunNResult program fuel state =
      InteractionSemantics.Compiled.openRunNResult program fuel state := by
  unfold InteractionSemantics.Source.openRunNResult
    InteractionSemantics.Compiled.openRunNResult
  have hStep :
      InteractionSemantics.Source.openStepResult program =
        InteractionSemantics.Compiled.openStepResult program := by
    funext current
    exact source_openStepResult_eq_compiled program current
  rw [hStep]

theorem source_openRunNResult_rel_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openRunNResult program fuel state)
      (InteractionSemantics.Compiled.openRunNResult program fuel state) := by
  rw [source_openRunNResult_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem source_openStepResult_at_boundary
    {pre post : Program} {instr : Instr} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    InteractionSemantics.Source.openStepResult
        (pre ++ instr :: post) state =
      InteractionSemantics.Source.openStepAtResult
        (pre ++ instr :: post) pre.byteLength instr state := by
  unfold InteractionSemantics.Source.openStepResult
    Source.stepResultWith
  have hAt :
      Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  rw [hAt]

theorem source_stepResult_at_boundary
    {pre post : Program} {instr : Instr} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    Source.stepResult (pre ++ instr :: post) state =
      Source.stepAtResult
        (pre ++ instr :: post) pre.byteLength instr state := by
  unfold Source.stepResult Source.stepResultWith
  have hAt :
      Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  rw [hAt]

theorem source_runNResult_one_at_boundary
    {pre post : Program} {instr : Instr} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    Source.runNResult (pre ++ instr :: post) 1 state =
      Source.stepAtResult
        (pre ++ instr :: post) pre.byteLength instr state := by
  unfold Source.runNResult Control.runNResultWith
  rw [source_stepResult_at_boundary hFits hPc]
  cases hStep :
      Source.stepAtResult
        (pre ++ instr :: post) pre.byteLength instr state with
  | error err =>
      simp only [Bind.bind, Except.bind]
  | ok result =>
      cases result <;>
        simp only [Bind.bind, Except.bind, Source.runNResult,
          Control.runNResultWith, pure_except]

theorem source_openRunNResult_one_at_boundary
    {pre post : Program} {instr : Instr} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    InteractionSemantics.Source.openRunNResult
        (pre ++ instr :: post) 1 state =
      InteractionSemantics.Source.openStepAtResult
        (pre ++ instr :: post) pre.byteLength instr state := by
  unfold InteractionSemantics.Source.openRunNResult
    Control.runNResultWith
  rw [source_openStepResult_at_boundary hFits hPc]
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state)
        (fun result =>
          match result with
          | .running state' =>
              Simulation.Interaction.pure
                (Error := EVMException) (.running state')
          | .halted halt =>
              Simulation.Interaction.pure
                (Error := EVMException) (.halted halt)) =
      InteractionSemantics.Source.openStepAtResult
        (pre ++ instr :: post) pre.byteLength instr state
  have hContinuation :
      (fun result : StepResult =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure
              (Error := EVMException) (.running state')
        | .halted halt =>
            Simulation.Interaction.pure
              (Error := EVMException) (.halted halt)) =
        (Simulation.Interaction.pure (Error := EVMException) :
          StepResult →
            Simulation.Interaction EVMException StepResult) := by
    funext result
    cases result <;> rfl
  rw [hContinuation]
  exact Simulation.Interaction.bind_pure _

theorem source_openRunUntilTransferWithPolicy_one_at_boundary
    (continueTransfer : Instr → Bool)
    {pre post : Program} {instr : Instr} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ instr :: post) 1 state =
      (do
        let result ←
          InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state
        pure
          (instr.classifyFlowWith
            continueTransfer state result).result) := by
  unfold
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
    Source.runUntilTransferWithPolicy
    Control.runUntilTransferWith
    Source.flowStepWithPolicy
  have hAt :
      Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  rw [hAt]
  unfold InteractionSemantics.Source.openStepResult
    Source.stepResultWith
  rw [hAt]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state)
          (fun result =>
            Simulation.Interaction.pure
              (instr.classifyFlowWith
                continueTransfer state result)))
        (fun flow =>
          match flow with
          | .next state' =>
              Simulation.Interaction.pure
                (StepResult.running state')
          | .exit result =>
              Simulation.Interaction.pure result) =
      Simulation.Interaction.bind
        (InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state)
        (fun result =>
          Simulation.Interaction.pure
            (instr.classifyFlowWith
              continueTransfer state result).result)
  rw [Simulation.Interaction.bind_assoc]
  congr 1
  funext result
  cases instr.classifyFlowWith continueTransfer state result <;> rfl

theorem source_openRunUntilTransfer_one_at_boundary
    {pre post : Program} {instr : Instr} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    InteractionSemantics.Source.openRunUntilTransfer
        (pre ++ instr :: post) 1 state =
      (do
        let result ←
          InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state
        pure (instr.classifyFlow state result).result) := by
  unfold
    InteractionSemantics.Source.openRunUntilTransfer
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
    Source.runUntilTransferWithPolicy
    Control.runUntilTransferWith
    Source.flowStepWithPolicy
  have hAt :
      Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  rw [hAt]
  unfold InteractionSemantics.Source.openStepResult
    Source.stepResultWith
  rw [hAt]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state)
          (fun result =>
            Simulation.Interaction.pure
              (instr.classifyFlow state result)))
        (fun flow =>
          match flow with
          | .next state' =>
              Simulation.Interaction.pure
                (StepResult.running state')
          | .exit result =>
              Simulation.Interaction.pure result) =
      Simulation.Interaction.bind
        (InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state)
        (fun result =>
          Simulation.Interaction.pure
            (instr.classifyFlow state result).result)
  rw [Simulation.Interaction.bind_assoc]
  congr 1
  funext result
  cases instr.classifyFlow state result <;> rfl

theorem source_openRunUntilTransferWithPolicy_succ_at_boundary
    (continueTransfer : Instr → Bool)
    {pre post : Program} {instr : Instr} {state : EVMState}
    (fuel : Nat)
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ instr :: post) (fuel + 1) state =
      (do
        let result ←
          InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state
        match instr.classifyFlowWith
            continueTransfer state result with
        | .next state' =>
            InteractionSemantics.Source.openRunUntilTransferWithPolicy
              continueTransfer (pre ++ instr :: post) fuel state'
        | .exit result =>
            pure result) := by
  change
    (do
      let flow ←
        Source.flowStepWithPolicy continueTransfer
          (InteractionSemantics.Source.openStepResult
            (pre ++ instr :: post))
          (pre ++ instr :: post) state
      match flow with
      | .next state' =>
          InteractionSemantics.Source.openRunUntilTransferWithPolicy
            continueTransfer (pre ++ instr :: post) fuel state'
      | .exit result =>
          Simulation.Interaction.pure result) =
      _
  have hAt :
      Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  unfold Source.flowStepWithPolicy
  rw [hAt]
  unfold InteractionSemantics.Source.openStepResult
    Source.stepResultWith
  rw [hAt]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state)
          (fun result =>
            Simulation.Interaction.pure
              (instr.classifyFlowWith
                continueTransfer state result)))
        (fun flow =>
          match flow with
          | .next state' =>
              InteractionSemantics.Source.openRunUntilTransferWithPolicy
                continueTransfer (pre ++ instr :: post) fuel state'
          | .exit result =>
              Simulation.Interaction.pure result) =
      Simulation.Interaction.bind
        (InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state)
        (fun result =>
          match instr.classifyFlowWith
              continueTransfer state result with
          | .next state' =>
              InteractionSemantics.Source.openRunUntilTransferWithPolicy
                continueTransfer (pre ++ instr :: post) fuel state'
          | .exit result =>
              Simulation.Interaction.pure result)
  rw [Simulation.Interaction.bind_assoc]
  congr 1

theorem source_openRunUntilTransferWithPolicy_succ_of_step_running
    (continueTransfer : Instr → Bool)
    {pre post : Program} {instr : Instr}
    {state final : EVMState} (fuel : Nat)
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hStep :
      InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state =
        .done (.ok (.running final)))
    (hFlow :
      instr.classifyFlowWith continueTransfer state (.running final) =
        .next final) :
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ instr :: post) (fuel + 1) state =
      InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ instr :: post) fuel final := by
  rw [source_openRunUntilTransferWithPolicy_succ_at_boundary
    continueTransfer fuel hFits hPc]
  rw [hStep]
  change
    (match instr.classifyFlowWith
        continueTransfer state (.running final) with
    | .next state' =>
        InteractionSemantics.Source.openRunUntilTransferWithPolicy
          continueTransfer (pre ++ instr :: post) fuel state'
    | .exit result =>
        Simulation.Interaction.pure result) =
      InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ instr :: post) fuel final
  rw [hFlow]

theorem source_openRunUntilTransferWithPolicy_succ_of_step_exit
    (continueTransfer : Instr → Bool)
    {pre post : Program} {instr : Instr}
    {state : EVMState} {result : StepResult} (fuel : Nat)
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hStep :
      InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state =
        .done (.ok result))
    (hFlow :
      instr.classifyFlowWith continueTransfer state result =
        .exit result) :
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ instr :: post) (fuel + 1) state =
      .done (.ok result) := by
  rw [source_openRunUntilTransferWithPolicy_succ_at_boundary
    continueTransfer fuel hFits hPc]
  rw [hStep]
  change
    (match instr.classifyFlowWith
        continueTransfer state result with
    | .next state' =>
        InteractionSemantics.Source.openRunUntilTransferWithPolicy
          continueTransfer (pre ++ instr :: post) fuel state'
    | .exit result =>
        Simulation.Interaction.pure result) =
      .done (.ok result)
  rw [hFlow]
  rfl

theorem source_openRunUntilTransferWithPolicy_succ_of_step_error
    (continueTransfer : Instr → Bool)
    {pre post : Program} {instr : Instr}
    {state : EVMState} {err : EVMException} (fuel : Nat)
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hStep :
      InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state =
        .done (.error err)) :
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ instr :: post) (fuel + 1) state =
      .done (.error err) := by
  rw [source_openRunUntilTransferWithPolicy_succ_at_boundary
    continueTransfer fuel hFits hPc]
  rw [hStep]
  rfl

theorem source_openRunUntilTransfer_succ_at_boundary
    {pre post : Program} {instr : Instr} {state : EVMState}
    (fuel : Nat)
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    InteractionSemantics.Source.openRunUntilTransfer
        (pre ++ instr :: post) (fuel + 1) state =
      (do
        let result ←
          InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state
        match instr.classifyFlow state result with
        | .next state' =>
            InteractionSemantics.Source.openRunUntilTransfer
              (pre ++ instr :: post) fuel state'
        | .exit result =>
            pure result) := by
  change
    (do
      let flow ←
        Source.flowStepWith
          (InteractionSemantics.Source.openStepResult
            (pre ++ instr :: post))
          (pre ++ instr :: post) state
      match flow with
      | .next state' =>
          InteractionSemantics.Source.openRunUntilTransfer
            (pre ++ instr :: post) fuel state'
      | .exit result =>
          Simulation.Interaction.pure result) =
      _
  have hAt :
      Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  unfold Source.flowStepWith Source.flowStepWithPolicy
  rw [hAt]
  unfold InteractionSemantics.Source.openStepResult
    Source.stepResultWith
  rw [hAt]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (InteractionSemantics.Source.openStepAtResult
            (pre ++ instr :: post) pre.byteLength instr state)
          (fun result =>
            Simulation.Interaction.pure
              (instr.classifyFlow state result)))
        (fun flow =>
          match flow with
          | .next state' =>
              InteractionSemantics.Source.openRunUntilTransfer
                (pre ++ instr :: post) fuel state'
          | .exit result =>
              Simulation.Interaction.pure result) =
      Simulation.Interaction.bind
        (InteractionSemantics.Source.openStepAtResult
          (pre ++ instr :: post) pre.byteLength instr state)
        (fun result =>
          match instr.classifyFlow state result with
          | .next state' =>
              InteractionSemantics.Source.openRunUntilTransfer
                (pre ++ instr :: post) fuel state'
          | .exit result =>
              Simulation.Interaction.pure result)
  rw [Simulation.Interaction.bind_assoc]
  congr 1

theorem source_openStepAtResult_eq_done_of_stepAt
    {program : Program} {pc : Nat} {instr : Instr} {state : EVMState}
    (hOpen :
      InteractionSemantics.Source.openStepAt
          program pc instr state =
        .done (Source.stepAt program pc instr state)) :
    InteractionSemantics.Source.openStepAtResult
        program pc instr state =
      .done (Source.stepAtResult program pc instr state) := by
  unfold
    InteractionSemantics.Source.openStepAtResult
    Source.stepAtResult
  rw [hOpen]
  cases hStep : Source.stepAt program pc instr state with
  | error err =>
      rfl
  | ok state' =>
      cases instr.haltKind? <;> rfl

theorem source_openRunNResult_one_eq_done
    {pre post : Program} {instr : Instr} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hOpen :
      InteractionSemantics.Source.openStepAt
          (pre ++ instr :: post) pre.byteLength instr state =
        .done
          (Source.stepAt
            (pre ++ instr :: post) pre.byteLength instr state)) :
    InteractionSemantics.Source.openRunNResult
        (pre ++ instr :: post) 1 state =
      .done
        (Source.runNResult
          (pre ++ instr :: post) 1 state) := by
  rw [source_openRunNResult_one_at_boundary hFits hPc]
  rw [source_runNResult_one_at_boundary hFits hPc]
  exact source_openStepAtResult_eq_done_of_stepAt hOpen

theorem source_openStepAt_prim_closed
    {program : Program} {pc : Nat} {op : PrimOp} {state : EVMState}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize) :
    InteractionSemantics.Source.openStepAt
        program pc (.prim op) state =
      .done (Source.stepAt program pc (.prim op) state) := by
  change
    InteractionSemantics.PrimOp.openStep op state =
      .done (op.step state)
  exact
    InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize

theorem source_openRunUntilTransfer_one_prim_closed
    {pre post : Program} {op : PrimOp} {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize) :
    InteractionSemantics.Source.openRunUntilTransfer
        (pre ++ Instr.prim op :: post) 1 state =
      .done
        (Target.stepInstrResult (.prim op) state) := by
  rw [source_openRunUntilTransfer_one_at_boundary hFits hPc]
  rw [source_openStepAtResult_eq_done_of_stepAt
    (source_openStepAt_prim_closed hExternal hGas hMsize)]
  cases hStep : op.step state with
  | error err =>
      simp [Source.stepAtResult,
        Source.stepAt,
        Target.stepInstrResult,
        Instr.haltKind?,
        TargetInstr.haltKind?,
        hStep]
      rfl
  | ok final =>
      cases hHalt : op.haltKind? <;>
        simp [Source.stepAtResult,
          Source.stepAt,
          Target.stepInstrResult,
          Instr.haltKind?,
          TargetInstr.haltKind?,
          Instr.classifyFlow,
          Instr.classifyFlowWith,
          FlowStep.result,
          hStep, hHalt] <;>
        rfl

theorem source_openRunUntilTransfer_eq_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    InteractionSemantics.Source.openRunUntilTransfer
        program fuel state =
      InteractionSemantics.Compiled.openRunUntilTransfer
        program fuel state := by
  unfold InteractionSemantics.Source.openRunUntilTransfer
    InteractionSemantics.Compiled.openRunUntilTransfer
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
    InteractionSemantics.Compiled.openRunUntilTransferWithPolicy
    Source.runUntilTransferWithPolicy
  have hStep :
      InteractionSemantics.Source.openStepResult program =
        InteractionSemantics.Compiled.openStepResult program := by
    funext current
    exact source_openStepResult_eq_compiled program current
  rw [hStep]

theorem source_openRunUntilTransferWithPolicy_eq_compiled
    (continueTransfer : Instr → Bool)
    (program : Program) (fuel : Nat) (state : EVMState) :
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer program fuel state =
      InteractionSemantics.Compiled.openRunUntilTransferWithPolicy
        continueTransfer program fuel state := by
  unfold
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
    InteractionSemantics.Compiled.openRunUntilTransferWithPolicy
    Source.runUntilTransferWithPolicy
  have hStep :
      InteractionSemantics.Source.openStepResult program =
        InteractionSemantics.Compiled.openStepResult program := by
    funext current
    exact source_openStepResult_eq_compiled program current
  rw [hStep]

theorem source_openRunUntilTransferWithPolicy_rel_compiled
    (continueTransfer : Instr → Bool)
    (program : Program) (fuel : Nat) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer program fuel state)
      (InteractionSemantics.Compiled.openRunUntilTransferWithPolicy
        continueTransfer program fuel state) := by
  rw [source_openRunUntilTransferWithPolicy_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem source_openRunUntilTransfer_rel_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openRunUntilTransfer
        program fuel state)
      (InteractionSemantics.Compiled.openRunUntilTransfer
        program fuel state) := by
  rw [source_openRunUntilTransfer_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

/--
Every concrete source branch induces a pass-owned trace of the emitted
instruction blocks. The structural relation supplies the same external-world
answers; the trace records only the assembler decomposition needed by the
adjacent target boundary.
-/
theorem assemble_source_openRunNResult_block_trace
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Source.openRunNResult program fuel state)
        transcript (.ok result)) :
    OpenBlockTraceResult program target fuel state transcript result := by
  obtain ⟨compiledOutcome, hCompiled, hOutcome⟩ :=
    Simulation.Interaction.Rel.executes
      (source_openRunNResult_rel_compiled program fuel state) hExec
  cases hOutcome
  induction fuel generalizing state transcript result with
  | zero =>
      change
        Simulation.Interaction.Executes
          (.done (.ok (StepResult.running state)))
          transcript (.ok result) at hCompiled
      cases hCompiled
      exact OpenBlockTraceResult.done state
  | succ fuel ih =>
      change
        Simulation.Interaction.Executes
          (Simulation.Interaction.bind
            (InteractionSemantics.Compiled.openStepResult program state)
            (fun stepResult =>
              match stepResult with
              | .running mid =>
                  InteractionSemantics.Compiled.openRunNResult
                    program fuel mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)))
          transcript (.ok result) at hCompiled
      rcases Simulation.Interaction.Executes.bind_cases hCompiled with
        hError | hOk
      · rcases hError with ⟨err, hOutcome, hStep⟩
        cases hOutcome
      · rcases hOk with
          ⟨stepResult, headTranscript, restTranscript,
            hTranscript, hStep, hRest⟩
        rcases assemble_compiled_openStepResult_executes hAsm hStep with
          ⟨pc, instr, emitted, before, after,
            hAt, hEmit, hTargetBlock, hBlock⟩
        subst transcript
        cases stepResult with
        | running mid =>
            have hSourceRest :
                Simulation.Interaction.Executes
                  (InteractionSemantics.Source.openRunNResult
                    program fuel mid)
                  restTranscript (.ok result) := by
              rw [source_openRunNResult_eq_compiled]
              exact hRest
            exact
              OpenBlockTraceResult.stepRunning
                hAt hEmit hTargetBlock hBlock (ih hSourceRest hRest)
        | halted halt =>
            change
              Simulation.Interaction.Executes
                (.done (.ok (StepResult.halted halt)))
                restTranscript (.ok result) at hRest
            cases hRest
            simpa using
              (OpenBlockTraceResult.stepHalted
                (fuel := fuel) hAt hEmit hTargetBlock hBlock)

/--
Compiler-artifact form of the whole-program open Assembly theorem.

The generated target program is connected to the block interpreter by the
existing emitter equation; no generated proof object is accepted as a premise.
-/
theorem compile_openRunNResult_block_rel
    {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target)
    (fuel : Nat) (state : EVMState) :
    Accepted program ∧
      ∃ code,
        emit? program = some code ∧
          target.code = code ∧
            Simulation.Interaction.Rel Eq
              (InteractionSemantics.Source.openRunNResult
                program fuel state)
              (InteractionSemantics.Compiled.openRunNResult
                program fuel state) := by
  refine ⟨Preservation.compile?_some_accepted hCompile, ?_⟩
  obtain ⟨code, hEmit, hCode⟩ :=
    Preservation.assemble_emits_code
      (Preservation.compile?_some_assemble hCompile)
  exact
    ⟨code, hEmit, hCode,
      source_openRunNResult_rel_compiled program fuel state⟩

/--
Concrete-branch form of Assembly compiler correctness.

For every branch selected by an external world on the accepted source
program, the fetched target program realizes the exact same dependent
query/answer transcript and terminal result. The target instruction budget is
derived from the emitted blocks rather than supplied as compiler evidence.
-/
theorem compile_openRunNResult_target_executes
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hLen : Program.byteLength program < EvmYul.UInt256.size)
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Source.openRunNResult program fuel state)
        transcript (.ok result)) :
    Accepted program ∧
      ∃ targetFuel,
        Simulation.Interaction.Executes
          (InteractionSemantics.Target.openRunNResult
            target targetFuel state)
          transcript (.ok result) := by
  have hAsm : assemble? program = some target :=
    Preservation.compile?_some_assemble hCompile
  refine ⟨Preservation.compile?_some_accepted hCompile, ?_⟩
  exact
    OpenBlockTraceResult.target_executes_exists
      hAsm
      (assemble_source_openRunNResult_block_trace hAsm hExec)
      hLen

/--
Uniform structural Assembly-to-bytecode preservation for terminal open-world
executions. Two target instructions per source instruction cover every emitted
path; branches using less fuel have already halted, so the remaining target
budget is inert.
-/
theorem compile_openRunNResult_target_rel_terminal
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    (hCompile : compile? program = some target)
    (hLen : Program.byteLength program < EvmYul.UInt256.size)
    (hTerminal : Simulation.Interaction.AllDone
      InteractionSemantics.Terminal
      (InteractionSemantics.Source.openRunNResult
        program fuel state)) :
    Accepted program /\
      Simulation.Interaction.Rel Eq
        (InteractionSemantics.Source.openRunNResult
          program fuel state)
        (InteractionSemantics.Target.openRunNResult
          target (2 * fuel) state) := by
  have hAsm : assemble? program = some target :=
    Preservation.compile?_some_assemble hCompile
  refine ⟨Preservation.compile?_some_accepted hCompile, ?_⟩
  apply Simulation.Interaction.Rel.of_successful_executes
    (InteractionSemantics.Terminal.successful hTerminal)
  intro transcript sourceResult hSourceExec
  have hSourceTerminal :=
    Simulation.Interaction.AllDone.property_of_executes
      hTerminal hSourceExec
  cases sourceResult with
  | running sourceFinal => cases hSourceTerminal
  | halted halt =>
      obtain ⟨targetFuel, hTargetFuel, hTargetExec⟩ :=
        OpenBlockTraceResult.target_executes_bounded hAsm
          (assemble_source_openRunNResult_block_trace hAsm hSourceExec)
          hLen
      let extra := 2 * fuel - targetFuel
      have hFuel : targetFuel + extra = 2 * fuel := by
        exact Nat.add_sub_of_le hTargetFuel
      have hPadded :=
        InteractionSemantics.Target.openRunNResult_halted_add_executes
          (extra := extra) hTargetExec
      rw [hFuel] at hPadded
      exact ⟨.ok (.halted halt), hPadded, rfl⟩

end InteractionPreservation
end Assembly
end EvmCompiler
