import EvmCompiler.Assembly.GasfulBridge

/-! Relational gasful/open preservation for terminal EVM instructions. -/

namespace EvmCompiler.Assembly.GasfulBridge

open Simulation

def openStopStateHere (state : EVMState) : EVMState :=
  { state with
    toMachineState :=
      (state.toMachineState.setReturnData ByteArray.empty).setHReturn
        ByteArray.empty }

def openStopHaltHere (state : EVMState) : Halt :=
  { kind := .stop, state := openStopStateHere state, output := ByteArray.empty }

theorem MachineDataRel.clearReturn
    {left right : EvmYul.MachineState} (hRel : MachineDataRel left right) :
    MachineDataRel
      ((left.setReturnData ByteArray.empty).setHReturn ByteArray.empty)
      ((right.setReturnData ByteArray.empty).setHReturn ByteArray.empty) := by
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.setReturnData,
    EvmYul.MachineState.setHReturn]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem stopState_openStateRel
    {gasful openState : EVMState} (hRel : OpenStateRel gasful openState) :
    OpenStateRel (openStopStateAt gasful) (openStopStateHere openState) := by
  have hCharged := afterDynamicChargeAt_openStateRel_left hRel
  simpa [openStopStateAt, openStopStateHere] using
    hCharged.withMachineState hCharged.machineDataRel.clearReturn

theorem raw_stop_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .stop))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.halted (openStopHaltHere state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .stop) trivial hDecode hPc]
  exact Interaction.Executes.done _

theorem runRefinesOpen_stop_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat}
    {state openState gasfulFinal : EVMState}
    (hRel : OpenStateRel state openState)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStop : decodedOperationAt state = EvmYul.Operation.STOP)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.STOP,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal)
    (hDecode : Compact.decodeAt bytes pc (.prim .stop))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) openState)
      [] := by
  rw [x_stop_success_after_charges hPrefix hStop hStep]
  have hOne := raw_stop_executes_at
    (bytes := bytes) (pc := pc) (state := openState) hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_halted_add_executes
      (extra := fuel) hOne
  have hCanonical :=
    OpenSameData.of_sameData (sameData_stop_step_after_charges hStep)
  have hFinal := hCanonical.trans (stopState_openStateRel hRel).openData
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.success hFinal

theorem OpenSameData.hReturn_eq
    {left right : EVMState} (hRel : OpenSameData left right) :
    left.toMachineState.H_return = right.toMachineState.H_return := by
  have hFrame := hRel.frame
  cases left
  cases right
  simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame
  exact hFrame.1.2.2.2.2

theorem machineBinaryCompatible_evmReturn :
    MachineBinaryCompatible EvmYul.MachineState.evmReturn := by
  intro left right a b hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.evmReturn]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem machineBinaryCompatible_evmRevert :
    MachineBinaryCompatible EvmYul.MachineState.evmRevert := by
  intro left right a b hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.evmRevert,
    EvmYul.MachineState.evmReturn]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem binaryMachineStateStepState_openStateRel
    {op : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hCompatible : MachineBinaryCompatible op)
    {left right : EVMState} (hRel : OpenStateRel left right) :
    OpenStateRel (binaryMachineStateStepState op left)
      (binaryMachineStateStepState op right) := by
  have hStack := hRel.stack_eq
  cases hPop : left.stack.pop2 with
  | none =>
      have hRightPop : right.stack.pop2 = none := by simpa [hStack] using hPop
      simp [binaryMachineStateStepState, hPop, hRightPop, hRel]
  | some values =>
      rcases values with ⟨rest, a, b⟩
      have hRightPop : right.stack.pop2 = some (rest, a, b) := by
        simpa [hStack] using hPop
      let leftMachine := op left.toMachineState a b
      let rightMachine := op right.toMachineState a b
      have hMachine : MachineDataRel leftMachine rightMachine :=
        hCompatible a b hRel.machineDataRel
      simpa [binaryMachineStateStepState, hPop, hRightPop,
        leftMachine, rightMachine] using
        (OpenStateRel.replaceStackAndIncrPC
          (hRel.withMachineState hMachine)
          (leftStack := rest) (rightStack := rest) rfl)

def openReturnStateHere (state : EVMState) : EVMState :=
  binaryMachineStateStepState EvmYul.MachineState.evmReturn state

def openReturnHaltHere (state : EVMState) : Halt :=
  { kind := .return
    state := openReturnStateHere state
    output := (openReturnStateHere state).toMachineState.H_return }

def openRevertStateHere (state : EVMState) : EVMState :=
  binaryMachineStateStepState EvmYul.MachineState.evmRevert state

def openRevertHaltHere (state : EVMState) : Halt :=
  { kind := .revert
    state := openRevertStateHere state
    output := (openRevertStateHere state).toMachineState.H_return }

theorem returnState_openStateRel
    {gasful openState : EVMState} (hRel : OpenStateRel gasful openState) :
    OpenStateRel (openReturnStateAt gasful) (openReturnStateHere openState) := by
  exact binaryMachineStateStepState_openStateRel
    machineBinaryCompatible_evmReturn
    (afterDynamicChargeAt_openStateRel_left hRel)

theorem revertState_openStateRel
    {gasful openState : EVMState} (hRel : OpenStateRel gasful openState) :
    OpenStateRel (openRevertStateAt gasful) (openRevertStateHere openState) := by
  exact binaryMachineStateStepState_openStateRel
    machineBinaryCompatible_evmRevert
    (afterDynamicChargeAt_openStateRel_left hRel)

theorem raw_return_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {offset size : Word}
    (hPop : state.stack.pop2 = some (rest, offset, size))
    (hDecode : Compact.decodeAt bytes pc (.prim .return))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.halted (openReturnHaltHere state))) := by
  have hPrim : PrimOp.return.step state = .ok (openReturnStateHere state) := by
    change EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmReturn
      state = .ok (openReturnStateHere state)
    simp [EvmYul.EVM.binaryMachineStateOp, openReturnStateHere,
      binaryMachineStateStepState, hPop]
    rfl
  have hOpen :
      InteractionSemantics.PrimOp.openStep .return state =
        Interaction.done (.ok (openReturnStateHere state)) := by
    simp [InteractionSemantics.PrimOp.openStep, PrimOp.toEVM,
      ExternalKind.ofEVMOperation?, CallKind.ofEVMOperation?,
      CreateKind.ofEVMOperation?, hPrim]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .return) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep, hPrim,
    InteractionSemantics.Target.openStepInstrResult,
    Target.stepInstrResultWith, InteractionSemantics.Target.openStepInstr,
    Target.stepInstrWith, hOpen, Interaction.bind, Interaction.pure,
    Interaction.bind_done_ok, PrimOp.haltKind?, Compact.Instr.haltKind?,
    HaltKind.output, openReturnHaltHere] using
    (Interaction.Executes.done
      (.ok (StepResult.halted (openReturnHaltHere state))))

theorem raw_revert_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {offset size : Word}
    (hPop : state.stack.pop2 = some (rest, offset, size))
    (hDecode : Compact.decodeAt bytes pc (.prim .revert))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.halted (openRevertHaltHere state))) := by
  have hPrim : PrimOp.revert.step state = .ok (openRevertStateHere state) := by
    change EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmRevert
      state = .ok (openRevertStateHere state)
    simp [EvmYul.EVM.binaryMachineStateOp, openRevertStateHere,
      binaryMachineStateStepState, hPop]
    rfl
  have hOpen :
      InteractionSemantics.PrimOp.openStep .revert state =
        Interaction.done (.ok (openRevertStateHere state)) := by
    simp [InteractionSemantics.PrimOp.openStep, PrimOp.toEVM,
      ExternalKind.ofEVMOperation?, CallKind.ofEVMOperation?,
      CreateKind.ofEVMOperation?, hPrim]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .revert) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep, hPrim,
    InteractionSemantics.Target.openStepInstrResult,
    Target.stepInstrResultWith, InteractionSemantics.Target.openStepInstr,
    Target.stepInstrWith, hOpen, Interaction.bind, Interaction.pure,
    Interaction.bind_done_ok, PrimOp.haltKind?, Compact.Instr.haltKind?,
    HaltKind.output, openRevertHaltHere] using
    (Interaction.Executes.done
      (.ok (StepResult.halted (openRevertHaltHere state))))

theorem runRefinesOpen_return_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat}
    {state openState gasfulFinal : EVMState}
    (hRel : OpenStateRel state openState)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hReturn : decodedOperationAt state = EvmYul.Operation.RETURN)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.RETURN,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal)
    (hDecode : Compact.decodeAt bytes pc (.prim .return))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) openState)
      [] := by
  rcases afterDynamic_pop2_of_return_step_ok hStep with
    ⟨rest, offset, size, hPop⟩
  have hCharged := afterDynamicChargeAt_openStateRel_left hRel
  have hOpenPop : openState.stack.pop2 = some (rest, offset, size) := by
    simpa [← hCharged.stack_eq] using hPop
  have hOne := raw_return_executes_at
    (bytes := bytes) (pc := pc) (state := openState)
    hOpenPop hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_halted_add_executes
      (extra := fuel) hOne
  have hCanonical :=
    OpenSameData.of_sameData (sameData_return_step_after_charges hStep)
  have hFinal := hCanonical.trans (returnState_openStateRel hRel).openData
  have hOutput := hFinal.hReturn_eq
  have hExec' :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) openState)
        []
        (.ok (.halted
          { kind := .return
            state := openReturnStateHere openState
            output := gasfulFinal.toMachineState.H_return })) := by
    simpa [Nat.add_comm, openReturnHaltHere, hOutput.symm] using hExec
  rw [x_return_success_after_charges hPrefix hReturn hStep]
  exact RunRefinesOpen.completed hExec' (DoneRel.success hFinal)

theorem runRefinesOpen_revert_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat}
    {state openState gasfulFinal : EVMState}
    (hRel : OpenStateRel state openState)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hRevert : decodedOperationAt state = EvmYul.Operation.REVERT)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.REVERT,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal)
    (hDecode : Compact.decodeAt bytes pc (.prim .revert))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) openState)
      [] := by
  rcases afterDynamic_pop2_of_revert_step_ok hStep with
    ⟨rest, offset, size, hPop⟩
  have hCharged := afterDynamicChargeAt_openStateRel_left hRel
  have hOpenPop : openState.stack.pop2 = some (rest, offset, size) := by
    simpa [← hCharged.stack_eq] using hPop
  have hOne := raw_revert_executes_at
    (bytes := bytes) (pc := pc) (state := openState)
    hOpenPop hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_halted_add_executes
      (extra := fuel) hOne
  have hCanonical :=
    OpenSameData.of_sameData (sameData_revert_step_after_charges hStep)
  have hFinal := hCanonical.trans (revertState_openStateRel hRel).openData
  have hOutput := hFinal.hReturn_eq
  have hExec' :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) openState)
        []
        (.ok (.halted
          { kind := .revert
            state := openRevertStateHere openState
            output := gasfulFinal.toMachineState.H_return })) := by
    simpa [Nat.add_comm, openRevertHaltHere, hOutput.symm] using hExec
  rw [x_revert_success_after_charges hPrefix hRevert hStep]
  exact RunRefinesOpen.completed hExec' DoneRel.revert

def OpenAccountMapRel
    (left right : EvmYul.AccountMap EvmYul.OperationType.EVM) : Prop :=
  left.mapVal (fun _ account => OpenAccount.ofEVM account) =
    right.mapVal (fun _ account => OpenAccount.ofEVM account)

theorem openAccountMapRel_find
    {left right : EvmYul.AccountMap EvmYul.OperationType.EVM}
    (hRel : OpenAccountMapRel left right)
    (address : EvmYul.AccountAddress) :
    (left.find? address).map OpenAccount.ofEVM =
      (right.find? address).map OpenAccount.ofEVM := by
  have hFind := congrArg (fun accounts => accounts.find? address) hRel
  simpa [OpenAccountMapRel, OpenWorld.find?_mapVal_const] using hFind

theorem openAccountMapRel_insert
    {left right : EvmYul.AccountMap EvmYul.OperationType.EVM}
    (hRel : OpenAccountMapRel left right)
    (address : EvmYul.AccountAddress)
    {leftAccount rightAccount : EvmYul.Account EvmYul.OperationType.EVM}
    (hAccount : OpenAccount.ofEVM leftAccount = OpenAccount.ofEVM rightAccount) :
    OpenAccountMapRel
      (left.insert address leftAccount)
      (right.insert address rightAccount) := by
  change
    (left.insert address leftAccount).mapVal
        (fun _ account => OpenAccount.ofEVM account) =
      (right.insert address rightAccount).mapVal
        (fun _ account => OpenAccount.ofEVM account)
  rw [OpenWorld.mapVal_insert, OpenWorld.mapVal_insert, hRel, hAccount]

theorem openAccount_ofEVM_withBalance
    {left right : EvmYul.Account EvmYul.OperationType.EVM}
    (hAccount : OpenAccount.ofEVM left = OpenAccount.ofEVM right)
    (balance : Word) :
    OpenAccount.ofEVM { left with balance := balance } =
      OpenAccount.ofEVM { right with balance := balance } := by
  cases left
  cases right
  simp_all [OpenAccount.ofEVM]

theorem openAccountMapRel_selfdestruct
    {left right : EvmYul.AccountMap EvmYul.OperationType.EVM}
    (hRel : OpenAccountMapRel left right)
    (owner recipient : EvmYul.AccountAddress)
    (created : Bool) :
    OpenAccountMapRel
      (EvmYul.selfdestructAccountMap left owner recipient created)
      (EvmYul.selfdestructAccountMap right owner recipient created) := by
  unfold EvmYul.selfdestructAccountMap
  cases hLeftOwner : left.find? owner with
  | none =>
      have hOwner := openAccountMapRel_find hRel owner
      rw [hLeftOwner] at hOwner
      cases hRightOwner : right.find? owner with
      | none => simpa [hLeftOwner, hRightOwner] using hRel
      | some rightOwner => simp [hRightOwner] at hOwner
  | some leftOwner =>
      have hOwner := openAccountMapRel_find hRel owner
      rw [hLeftOwner] at hOwner
      cases hRightOwner : right.find? owner with
      | none => simp [hRightOwner] at hOwner
      | some rightOwner =>
          rw [hRightOwner] at hOwner
          have hOwnerAccount :
              OpenAccount.ofEVM leftOwner = OpenAccount.ofEVM rightOwner := by
            simpa using Option.some.inj hOwner
          cases hLeftRecipient : left.find? recipient with
          | none =>
              have hRecipient := openAccountMapRel_find hRel recipient
              rw [hLeftRecipient] at hRecipient
              cases hRightRecipient : right.find? recipient with
              | none =>
                  have hBalance : leftOwner.balance = rightOwner.balance :=
                    congrArg OpenAccount.balance hOwnerAccount
                  simp only
                  rw [hBalance]
                  by_cases hZero :
                      (rightOwner.balance == (default : EvmYul.UInt256)) = true
                  · have hZero' :
                        (rightOwner.balance ==
                          (⟨0⟩ : EvmYul.UInt256)) = true := by
                        simpa using hZero
                    simp only [hZero', if_true]
                    exact hRel
                  · have hZero' :
                        ¬(rightOwner.balance ==
                          (⟨0⟩ : EvmYul.UInt256)) = true := by
                        simpa using hZero
                    simp only [hZero']
                    apply openAccountMapRel_insert
                    · apply openAccountMapRel_insert hRel
                      simp [OpenAccount.ofEVM]
                    · exact openAccount_ofEVM_withBalance hOwnerAccount _
              | some rightRecipient => simp [hRightRecipient] at hRecipient
          | some leftRecipient =>
              have hRecipient := openAccountMapRel_find hRel recipient
              rw [hLeftRecipient] at hRecipient
              cases hRightRecipient : right.find? recipient with
              | none => simp [hRightRecipient] at hRecipient
              | some rightRecipient =>
                  rw [hRightRecipient] at hRecipient
                  have hRecipientAccount :
                      OpenAccount.ofEVM leftRecipient =
                        OpenAccount.ofEVM rightRecipient := by
                    simpa using Option.some.inj hRecipient
                  have hOwnerBalance : leftOwner.balance = rightOwner.balance :=
                    congrArg OpenAccount.balance hOwnerAccount
                  have hRecipientBalance :
                      leftRecipient.balance = rightRecipient.balance :=
                    congrArg OpenAccount.balance hRecipientAccount
                  simp only
                  rw [hOwnerBalance, hRecipientBalance]
                  by_cases hDistinct : recipient ≠ owner
                  · simp [hDistinct]
                    apply openAccountMapRel_insert
                    · apply openAccountMapRel_insert hRel
                      exact openAccount_ofEVM_withBalance hRecipientAccount _
                    · exact openAccount_ofEVM_withBalance hOwnerAccount _
                  · simp [hDistinct]
                    by_cases hCreated : created = true
                    · simp [hCreated]
                      apply openAccountMapRel_insert
                      · apply openAccountMapRel_insert hRel
                        exact openAccount_ofEVM_withBalance hRecipientAccount _
                      · exact openAccount_ofEVM_withBalance hOwnerAccount _
                    · have hCreatedFalse : created = false := by
                        cases created <;> simp_all
                      simp [hCreatedFalse]
                      exact hRel

def selfdestructStateDataHere
    (state : EvmYul.State EvmYul.OperationType.EVM)
    (recipient : Word) : EvmYul.State EvmYul.OperationType.EVM :=
  let source := state.executionEnv.codeOwner
  let target := EvmYul.AccountAddress.ofUInt256 recipient
  let created := state.createdAccounts.contains source
  let substate' : EvmYul.Substate :=
    if created then
      { state.substate with
        selfDestructSet := state.substate.selfDestructSet.insert source
        accessedAccounts := state.substate.accessedAccounts.insert target }
    else
      { state.substate with
        accessedAccounts := state.substate.accessedAccounts.insert target }
  { state with
    accountMap :=
      EvmYul.selfdestructAccountMap state.accountMap source target created
    substate := substate' }

theorem StateDataRel.selfdestructStateDataHere
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) (recipient : Word) :
    StateDataRel
      (selfdestructStateDataHere left recipient)
      (selfdestructStateDataHere right recipient) := by
  have hOwner : right.executionEnv.codeOwner = left.executionEnv.codeOwner := by
    simpa using congrArg EvmYul.ExecutionEnv.codeOwner hRel.executionEnv.symm
  have hCreated :
      right.createdAccounts.contains right.executionEnv.codeOwner =
        left.createdAccounts.contains left.executionEnv.codeOwner := by
    rw [hOwner, hRel.createdAccounts]
  have hCreatedAtOwner :
      right.createdAccounts.contains left.executionEnv.codeOwner =
        left.createdAccounts.contains left.executionEnv.codeOwner := by
    rw [hRel.createdAccounts]
  exact
    { world := by
        apply OpenWorld.ext_of_fields
        · change OpenAccountMapRel
            (EvmYul.selfdestructAccountMap left.accountMap
              left.executionEnv.codeOwner
              (EvmYul.AccountAddress.ofUInt256 recipient)
              (left.createdAccounts.contains left.executionEnv.codeOwner))
            (EvmYul.selfdestructAccountMap right.accountMap
              right.executionEnv.codeOwner
              (EvmYul.AccountAddress.ofUInt256 recipient)
              (right.createdAccounts.contains right.executionEnv.codeOwner))
          rw [hOwner, hCreatedAtOwner]
          exact openAccountMapRel_selfdestruct hRel.accounts _ _ _
        · change
            (GasfulBridge.selfdestructStateDataHere left recipient).substate =
              (GasfulBridge.selfdestructStateDataHere right recipient).substate
          dsimp [GasfulBridge.selfdestructStateDataHere]
          rw [hOwner, hCreatedAtOwner, hRel.substate]
        · simpa [selfdestructStateDataHere, OpenWorld.ofEVMState]
            using hRel.createdAccounts
      initialAccounts := by
        simpa [selfdestructStateDataHere] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [selfdestructStateDataHere] using hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [selfdestructStateDataHere] using hRel.transactionReceipts
      executionEnv := by
        simpa [selfdestructStateDataHere] using hRel.executionEnv
      blocks := by simpa [selfdestructStateDataHere] using hRel.blocks
      genesisBlockHeader := by
        simpa [selfdestructStateDataHere] using hRel.genesisBlockHeader }

theorem MachineDataRel.setHReturnEmpty
    {left right : EvmYul.MachineState} (hRel : MachineDataRel left right) :
    MachineDataRel
      (left.setHReturn ByteArray.empty)
      (right.setHReturn ByteArray.empty) := by
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.setHReturn]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem selfdestructState_openStateRel
    {left right : EVMState} (hRel : OpenStateRel left right)
    (recipient : Word) (rest : EvmYul.Stack Word) :
    OpenStateRel
      (EvmYul.EVM.selfdestructState left recipient rest)
      (EvmYul.EVM.selfdestructState right recipient rest) := by
  have hState := hRel.stateDataRel.selfdestructStateDataHere recipient
  have hCore := hRel.withState hState
  have hStack := OpenStateRel.replaceStackAndIncrPC
    (pcDelta := 1) hCore (rfl : rest = rest)
  have hMachine := hStack.withMachineState
    hStack.machineDataRel.setHReturnEmpty
  simpa [EvmYul.EVM.selfdestructState,
    GasfulBridge.selfdestructStateDataHere] using hMachine

def openSelfdestructNextHere (state : EVMState)
    (recipient : Word) (rest : EvmYul.Stack Word) : EVMState :=
  EvmYul.EVM.selfdestructState state recipient rest

theorem raw_selfdestruct_success_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {recipient : Word} {rest : EvmYul.Stack Word}
    (hPerm : state.executionEnv.perm = true)
    (hStack : state.stack = recipient :: rest)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      []
      (.ok
        (.halted
          { kind := .selfdestruct
            state := openSelfdestructNextHere state recipient rest
            output := ByteArray.empty })) := by
  have hPrim :
      PrimOp.selfdestruct.step state =
        .ok (openSelfdestructNextHere state recipient rest) := by
    rw [PrimOp.step_selfdestruct_of_permitted _ hPerm]
    exact EvmYul.EVM.step_selfdestruct_of_stack _ recipient rest hStack
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .selfdestruct) trivial hDecode hPc]
  simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
    InteractionSemantics.Target.openStepInstr,
    Target.stepInstrWith, InteractionSemantics.PrimOp.openStep,
    PrimOp.toEVM, ExternalKind.ofEVMOperation?, hPrim,
    PrimOp.haltKind?, Compact.Instr.haltKind?, HaltKind.output]
  exact Interaction.Executes.done _

theorem runRefinesOpen_selfdestruct_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state openState : EVMState}
    {recipient : Word} {rest : EvmYul.Stack Word}
    (hRel : OpenStateRel state openState)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) =
          (EvmYul.Operation.SELFDESTRUCT, none))
    (hPerm : state.executionEnv.perm = true)
    (hStack : state.stack = recipient :: rest)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      [] := by
  have hDecodedOp :
      decodedOperationAt state = EvmYul.Operation.SELFDESTRUCT := by
    simp [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hOpenPerm : openState.executionEnv.perm = true := by
    simpa [← hRel.executionEnv_eq] using hPerm
  have hOpenStack : openState.stack = recipient :: rest := by
    simpa [← hRel.stack_eq] using hStack
  have hOne := raw_selfdestruct_success_executes_at
    (bytes := bytes) (pc := pc) (state := openState)
    hOpenPerm hOpenStack hDecode hPc
  have hExec :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) openState)
        []
        (.ok
          (.halted
            { kind := .selfdestruct
              state := openSelfdestructNextHere openState recipient rest
              output := ByteArray.empty })) := by
    have hExtended :=
      Compact.InteractionSemantics.openRunNResult_halted_add_executes
        (extra := fuel + 1) hOne
    simpa [show 1 + (fuel + 1) = fuel + 1 + 1 by omega] using hExtended
  have hFinal :
      OpenStateRel (gasfulSelfdestructNext state recipient rest)
        (openSelfdestructNextHere openState recipient rest) := by
    exact selfdestructState_openStateRel
      (afterEVMInstructionChargeAt_openStateRel_left hRel) recipient rest
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state)
          (.ok (gasfulSelfdestructNext state recipient rest)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) openState)
        [] := by
    apply RunRefinesOpen.completed hExec
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      haltOutputAt] using
      (DoneRel.success hFinal.openData
        (output := ByteArray.empty) (haltKind := HaltKind.selfdestruct))
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) =
          .ok (gasfulSelfdestructNext state recipient rest) := by
    simpa [hDecodedPair] using
      evm_step_selfdestruct_eq_next fuel state recipient rest hStack
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok (gasfulSelfdestructNext state recipient rest))
      hPrefix hCreateOk hStepActual hPostBridge

end EvmCompiler.Assembly.GasfulBridge
